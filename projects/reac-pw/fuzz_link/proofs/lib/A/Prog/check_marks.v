(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the tail of pcap_source_open (fuzz_pcap.asan-ubsan 0x811e0, listing offset
   AF_pcap_source_open = 0xa58, 246 instructions) on libreac v1.9.0's ASan+UBSan build: lib/A's PcapSourceOpenB.v, the
   walk from the two semantic cuts of lib/B/Prog/PcapSourceOpenPh.v to the return. op_from_null and op_from_read prove
   `op_from op_gi_null` and `op_from op_gi_read`, i.e. lib/A's image-generic post tpcap_source_open_post (with
   topen_kept, lib/A/Prog/PcapSourceOpenDefs.v) at this image (SEGS = pa_segs, the relro window pa_relro_lo /
   pa_relro_hi of the lib/B PAImg instance PI); PcapSourceOpen.v (the head) composes them. At ossv/recipes 25e3d17bdb50 (2026-10-29), this image had no released
   proof (rule 24, a Theorem Labs lane, 22:35Z); the released v1.8 UBSan proof lib/U/Prog/pcap_source_open.v is the guard
   template only.

   The paths, at this image's pcs:
   - the empty input (cut 0x813f8, f = NULL): a0 := -1, `j 0x81474`, the epilogue without the buffer re-poison;
   - the short read (cut 0x8138c, kr <> 24): `bne a0,s9` to 0x81400, the shadow test of ps (0x81400 `lbu`, 0x81404
     `bnez`), f = ps->f (0x81408), the fclose wrapper's call (0x8140c), the second shadow test (0x81410, 0x81414
     `beqz` to 0x8145c), ps->f := NULL (0x8145c), a0 := -1, the epilogue from 0x81464 (op_fclose);
   - kr = 24: the UBSan guard G6 (below), the magic of the four header bytes F + 32 .. F + 35 (0x81398..0x813c4, the
     top byte through `slliw`, magic_U), then 0xd4c3b2a1 (0x813c8 `beq` to 0x81420: ps->swapped := 1, a0 := 0,
     `j 0x81464`), 0xa1b2c3d4 (0x813d4 `bne` falls to 0x813d8: ps->swapped := 0, a0 := 0, `j 0x81464`), or the bad
     magic (0x81444: as the short read, fclose at 0x81450);
   - the epilogue (op_epi): the buffer out of scope (0x81464..0x81470, 3 shadow bytes 0xf8), the retired magic
     0x45e0360e at F (0x8147c); 0x81480 `beqz s2` NOT taken (s2 = F >= 4096, atom 18's fact), so the machine-frame
     arm 0x814d4..0x81500 is dead; F's 16 shadow bytes 0xf5 (0x81484..0x814c4); the flag through `ld a1,0x78(s2)` and
     `sb zero,0(a1)` (0x814c8, 0x814cc), which gives the frame back (lib/B/Prog/PcapFrame.v aj_flag_store_pi:
     astack_free_law, frame_flag_lawP); the restores and `ret` (0x81504..0x81538).
   The two guards on ps (G5, 0x812f8 and 0x81300 / 0x81304) are before the cuts, in the head.

   THE GUARD G6. 0x81390 `addi a0,zero,-3`, 0x81394 `bgeu s4,a0` branches to the `unimp` at 0x8153c when the header
   buffer s4 = F + 32 lies within 3 bytes of 2^64. The symbolic run decides it, NOT taken: decide_cond2
   (Reusable/YP0e.v:932) maps BC_GEU to the negation of decide_ltu2 (:922), and decide_ltu (Reusable/YP0m.v:673) finds
   atom 20 (s4) below the literal 2^64 - 3 from its range fact [4128, 0x7fffff800020] (rd_facts), which rd_entry
   proves from frames_bounds on the class-1 frame (F + 128 <= alloc_ceiling <= 0x7fffff800000). Templates: the released
   UBSan proof of the v1.8 image, proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v on origin/ossv/recipes
   c8557374ad2e, open_mid :286 (premise bv_unsigned sp0 < 2 ^ 63 at :291, frame bounds :295-299), which decides the
   guard at :410-412; and the earlier walk of this image, on a working branch
   (a8ccd33b1a7) pcap_source_open_tl.v (sha256 4aaa5af08467; internal record) pso_rdchk :36-67 (premise bv_unsigned s4 < 2 ^ 64 - 3 at :44,
   `step; step; if_false` at :65).

   THE REPORT PATHS are proved unreachable; no run steps into one. Every shadow test of ps in this stretch
   (0x81400 / 0x81404 and 0x81410 / 0x81414 on the short read, 0x81444 / 0x81448 and 0x81454 / 0x81458 on the bad
   magic, 0x813e4 / 0x813e8 and 0x8142c / 0x81430 on ps + 8 before the slow checks 0x81570 / 0x81584) is decided by
   the shadow entry of ps (rd_SH: ps's 24 bytes addressable; shent_rd_ok from op_pre's range_addressable, kept to the
   cut by op_mid's topen_kept and across fclose by its journal, shok_transfer), so the token run reads a 0 shadow byte
   and takes the non-report successor: the report calls 0x8141c, 0x81580, 0x81594 and 0x815a0..0x815b4 are never
   reached.

   The callees are Section hypotheses of their exact statement types: the fclose wrapper AFCLOSE, of
   lib/A/Stdio/PFclose.v's image-generic afclose_source_spec (= afclose_source_spec_stk PFCLOSE_STK) at this image,
   bound as lib/B/Prog/PcapSourceClose.v binds it (its data-buffer premise from op_pre's input block); the file meter
   FM (lib/A/Stdio/PSourceMeter.v asrc_file_meter); the frame give-back laws astack_free_law (Reusable/YG0d.v:301) and
   frame_flag_lawP (Reusable/YCbq.v:797) with model_laws; the meter laws (Reusable/YC5d.v ameter_laws,
   ameter_fs_laws); ASIL (lib/A/Stdio/PSourceMeta.v asource_img_laws). The stream predicates' frame lemmas are copied
   from lib/B/Prog/PcapSourceClose.v (not required). getr / mkst / seg_rom come from YK11; nothing from lib/Lib is
   imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpenB.v, with its module paths, module names and numbers changed; 660 of its 725 lines of code are new or changed and 1681 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v; 1027 of its 1110 lines of code are new or changed and 642 lines of the source are left out. *)
(* check_marks on image A (fuzz_link.asan 0x8848c, listing offset AF_check_marks = 0x62c0; listing
   (internal path) (internal record, sha256 0a5790c7d7c2)): the walk of its contract
   lib/A/Prog/check_marks_c.v `check_marks_acontract` (link_amem.v `aleaf_rd`, K = 32 + 2 * ESTACK = 8224,
   EV 0, SIDE [], write set []).

   +0x00..+0x10 push the 32-byte frame (ra, s0, s1, s2); +0x14..+0x1c the shadow base through the .got word;
   +0x20..+0x2c the instrumented check of the 4-byte load of got->n and +0x30..+0x4c the same of m->n_mark at
   m + MD_N_MARK, each a token load the run's shadow entry covers, so the error path at +0xac / +0xbc is not
   taken; +0x48 `lw s2, 0(a0)` and +0x50 `lw a2, 0(m + 8852)` read the two counts, which `marks_are` makes
   equal, so +0x54 `bne` falls through; +0x58 `blez s2` leaves on an empty marks block; +0x5c..+0x68 the two
   slot pointers; the loop +0x6c..+0x88 (cm_loop, by induction on the marks left) calls
   wrapper_strcmp(got->name[i], m->mark[i]) (0x4304c, CheckMarksCall.v cm_call over LinkWalkStrcmp.v
   aj_gx_astrcmp_at and Reusable/AStrcmpDef.v astrcmp_realizes; each slot string's premises from the Pre by
   cm_slot_acstr / cm_slot_arg) and `bnez a0` to the abort path, which `marks_are` refutes since the two slot
   strings are equal (cm_slots_eq); +0x8c..+0xa0 restore, pop, ret (CheckMarksCall.v cm_exit).

   THE REGIONS, phase by phase. The run needs the .got word and its cell to load the shadow base, and the two
   counts through the caller's pointers; the contract does not separate the marks block from the model block,
   nor either from the image, so no two of those may be regions of one state. They do not have to be: each
   token and the branch that reads it sit in one run, so the walk runs three phases, each with the frame and at
   most one of them, moving between them by LinkWalkPi.v st_ok_pi_submem (drop) and LinkPaLib.v
   st_ok_pi_add_region (add):
     A  +0x00..+0x30  [frame; .got word; its cell]   the shadow base, the first check
     B  +0x30..+0x50  [frame; got->n]                the second check (its token and `bnez` both inside), got->n
     C  +0x50..        [frame; m->n_mark]            m->n_mark, `bne`, `blez`, the slot pointers
   and the loop runs on the frame alone. Both count regions hold the SAME atom (33), which is what makes the
   runner decide +0x54 `bne` without a branch; `blez` at +0x58 is a branch on that atom (range [0, 32]): an empty
   block returns, else the run reaches the loop head (cm_start).

   Section hypotheses: LAWS, TL (PALib), LV (LinkVals) are the image instance's facts; STRCMP
   (Reusable/AStrcmpDef.v astrcmp_realizes at the wrapper) is discharged on the image by lib/A/Rt/RtStrcmpClosed.v
   `link_astrcmp_closed` (check_marks_aproof_img).

   Proves check_marks (kind: function proof). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkStrArg index_of_c check_marks_c
CheckMarksKit CheckMarksCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString RtStrcmpClosed.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. A mark slot's C string, on byte lists
   ========================================================================== *)

Lemma cm_nth_firstn : forall A (l : list A) n j, (j < n)%nat -> nth_error (firstn n l) j = nth_error l j.
Proof.
  intros A l. induction l as [|x l IH]; intros [|n] [|j] H; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.

Lemma cm_nth_skipn : forall A off (l : list A) j, nth_error (skipn off l) j = nth_error l (off + j).
Proof.
  intros A. induction off as [|off IH]; intros l j; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

Lemma cm_nth_slice : forall (bs : list byte) off n j, (j < n)%nat ->
  nth_error (firstn n (skipn off bs)) j = nth_error bs (off + j).
Proof. intros bs off n j Hj. rewrite cm_nth_firstn by exact Hj. apply cm_nth_skipn. Qed.

Lemma cm_slice_len : forall (bs : list byte) off n, (off + n <= length bs)%nat ->
  length (firstn n (skipn off bs)) = n.
Proof. intros bs off n H. rewrite firstn_length, length_skipn. lia. Qed.

(* a byte list with a NUL inside holds its C string, then the NUL *)
Lemma cm_cstr_split : forall l, (nul_at l < length l)%nat ->
  exists rest, l = cstr l ++ zb 0 :: rest /\ ~ In (zb 0) (cstr l).
Proof.
  induction l as [|b l IH]; intros H; [cbn in H; lia|].
  unfold cstr in *. cbn [nul_at firstn length] in *.
  destruct (Z.eqb_spec (bz b) 0) as [Hb|Hb].
  - exists l. cbn [firstn app]. split; [|intros []].
    f_equal. rewrite <- Hb. symmetry. apply Z_to_bv_bv_unsigned.
  - destruct (IH ltac:(lia)) as (rest & Heq & Hn).
    exists rest. cbn [app firstn]. split; [f_equal; exact Heq|].
    intros [Hin|Hin]; [apply Hb; rewrite Hin; reflexivity | exact (Hn Hin)].
Qed.

Lemma cm_cstr_len : forall l, (nul_at l < length l)%nat -> length (cstr l) = nul_at l.
Proof. intros l H. unfold cstr. rewrite firstn_length. lia. Qed.

Lemma cm_amem_sub : forall p n p' n', amem_range p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n ->
  amem_range p' n'.
Proof.
  intros p n p' n' H H1 H2 H3. unfold amem_range in *.
  destruct H as [H|[H H']]; [left; lia | right; split; lia].
Qed.

Lemma cm_ra_sub : forall (rd : reader) a n a' n',
  range_addressable rd SHADOW_OFF a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  range_addressable rd SHADOW_OFF a' n'.
Proof. intros rd a n a' n' H H1 H2 H3 x Hx. apply H. lia. Qed.

Lemma cm_hull_sub : forall (rd : reader) a n a' n',
  shadow_hull_vis rd a n -> a <= a' -> 1 <= n' -> a' + n' <= a + n -> shadow_hull_vis rd a' n'.
Proof.
  intros rd a n a' n' H H1 H2 H3 s Hs. apply H.
  pose proof (shadow_mono a a' ltac:(lia)) as M1.
  pose proof (shadow_mono (a' + n' - 1) (a + n - 1) ltac:(lia)) as M2.
  pose proof (Z.div_le_mono (shadow_addr a) (shadow_addr a') 8 ltac:(lia) M1) as D1.
  pose proof (Z.div_le_mono (shadow_addr (a' + n' - 1)) (shadow_addr (a + n - 1)) 8 ltac:(lia) M2) as D2.
  lia.
Qed.

Section v. Variable segs : list Segment.

Lemma cm_blk_vis : forall (m : word -> option byte) p bs a,
  abytes segs m p bs -> p <= a < p + Z.of_nat (length bs) -> ard segs m a <> None.
Proof.
  intros m p bs a (_ & _ & Hb) Ha.
  pose proof (Hb (Z.to_nat (a - p)) ltac:(lia)) as Hby.
  replace (p + Z.of_nat (Z.to_nat (a - p))) with a in Hby by lia.
  unfold ard. rewrite Hby.
  destruct (nth_error bs (Z.to_nat (a - p))) eqn:E; [discriminate|].
  exfalso. apply nth_error_None in E. lia.
Qed.

(* the C string of the i-th 16-byte slot of a block *)
Lemma cm_slot_acstr : forall (m : word -> option byte) p bs base i,
  au8arr segs m p bs -> 0 <= base -> 0 <= i ->
  base + MARK_LEN * i + MARK_LEN <= Z.of_nat (length bs) ->
  (nul_at (slice bs (base + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat ->
  acstr_at segs m (p + base + MARK_LEN * i) (cstr (slice bs (base + MARK_LEN * i) MARK_LEN)).
Proof.
  intros m p bs base i (Hab & _) Hb Hi Hlen Hnul.
  unfold MARK_LEN, slice in *. change (Z.to_nat 16) with 16%nat in *.
  pose proof Hab as (Hp0 & Hpl & Hbyte).
  set (o := Z.to_nat (base + 16 * i)) in *.
  assert (Ho : Z.of_nat o = base + 16 * i) by (unfold o; lia).
  assert (Hlim : (o + 16 <= length bs)%nat) by lia.
  assert (Hsl16 : length (firstn 16 (skipn o bs)) = 16%nat)
    by (rewrite firstn_length, length_skipn; lia).
  assert (HclN : (length (cstr (firstn 16 (skipn o bs))) <= 15)%nat)
    by (rewrite cm_cstr_len by (rewrite Hsl16; exact Hnul); apply Nat.lt_succ_r; exact Hnul).
  destruct (cm_cstr_split (firstn 16 (skipn o bs)) ltac:(rewrite Hsl16; exact Hnul))
    as (rest & Heq & Hnz).
  split; [|exact Hnz]. split; [lia|]. split.
  { rewrite length_app. cbn [length]. lia. }
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
  replace (p + base + 16 * i + Z.of_nat j) with (p + Z.of_nat (o + j)) by lia.
  rewrite (Hbyte (o + j)%nat ltac:(lia)).
  rewrite <- (cm_nth_slice bs o 16 j ltac:(lia)).
  rewrite Heq at 1.
  replace (cstr (firstn 16 (skipn o bs)) ++ zb 0 :: rest)
    with ((cstr (firstn 16 (skipn o bs)) ++ [zb 0]) ++ rest)
    by (rewrite <- app_assoc; reflexivity).
  rewrite nth_error_app1 by (rewrite length_app; cbn [length]; lia). reflexivity.
Qed.

(* the slot string's premises for the strcmp wrapper, from the block's *)
Lemma cm_slot_arg : forall (regs : bvmap 5 word) (m : word -> option byte) p bs base i BL,
  au8arr segs m p bs -> Z.of_nat (length bs) = BL ->
  amem_range p BL -> range_addressable (ard segs m) SHADOW_OFF p BL ->
  shadow_hull_vis (ard segs m) p BL -> apart_frame regs CHECK_MARKS_AK p BL ->
  (forall b, p + BL <= b < (p + BL + 7) / 8 * 8 -> ard segs m b <> None) ->
  0 < base -> 0 <= i -> base + MARK_LEN * i + MARK_LEN <= BL -> 0 < BL ->
  (nul_at (slice bs (base + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat ->
  astrcmp_arg segs regs CHECK_MARKS_AK m (p + base + MARK_LEN * i)
    (cstr (slice bs (base + MARK_LEN * i) MARK_LEN)).
Proof.
  intros regs m p bs base i BL Hau Hlen Hmem Hra Hhull Hpart Htail Hb Hi Hsl HBL Hnul.
  unfold MARK_LEN, slice in *. change (Z.to_nat 16) with 16%nat in *.
  pose proof Hau as (Hab & _). pose proof Hab as (Hp0 & Hpl & _).
  set (o := Z.to_nat (base + 16 * i)) in *.
  assert (Ho : Z.of_nat o = base + 16 * i) by (unfold o; lia).
  assert (Hsl16 : length (firstn 16 (skipn o bs)) = 16%nat)
    by (rewrite firstn_length, length_skipn; lia).
  assert (HclN : (length (cstr (firstn 16 (skipn o bs))) <= 15)%nat)
    by (rewrite cm_cstr_len by (rewrite Hsl16; exact Hnul); apply Nat.lt_succ_r; exact Hnul).
  assert (HclZ : Z.of_nat (length (cstr (firstn 16 (skipn o bs)))) <= 15) by lia.
  unfold astrcmp_arg.
  split; [lia|]. split; [lia|].

  set (s := cstr (firstn 16 (skipn o bs))) in *.
  set (q := p + base + 16 * i) in *.
  split; [exact (cm_amem_sub p BL q (Z.of_nat (length s) + 1) Hmem
                   ltac:(unfold q; lia) ltac:(lia) ltac:(unfold q; lia))|].
  split; [exact (cm_ra_sub (ard segs m) p BL q (Z.of_nat (length s) + 1) Hra
                   ltac:(unfold q; lia) ltac:(lia) ltac:(unfold q; lia))|].
  split; [exact (cm_hull_sub (ard segs m) p BL q (Z.of_nat (length s) + 1) Hhull
                   ltac:(unfold q; lia) ltac:(lia) ltac:(unfold q; lia))|].
  split; [unfold apart_frame in *; unfold q; lia|].
  intros a Ha.
  destruct (Z_lt_le_dec a (p + BL)) as [Hin|Hout].
  - apply (cm_blk_vis m p bs a Hab). unfold q in Ha. lia.
  - apply Htail. split; [exact Hout|].
    unfold q in Ha. lia.
Qed.

End v.

Lemma cm_seq_nth : forall len i, (i < len)%nat -> nth_error (seq 0 len) i = Some i.
Proof.
  intros len. induction len as [|len IH]; intros [|i] H; cbn [seq nth_error]; try lia; [reflexivity|].
  rewrite <- seq_shift, nth_error_map, IH by lia. reflexivity.
Qed.

(* the i-th slot string of a block, as mk_names / md_marks list it *)
Lemma cm_names_nth : forall bs base cnt i, 0 <= i < cnt ->
  nth_error (map (fun j => cstr (slice bs (base + MARK_LEN * Z.of_nat j) MARK_LEN))
                 (seq 0 (Z.to_nat cnt))) (Z.to_nat i)
  = Some (cstr (slice bs (base + MARK_LEN * i) MARK_LEN)).
Proof.
  intros bs base cnt i Hi.
  rewrite (map_nth_error _ (Z.to_nat i) _ (cm_seq_nth (Z.to_nat cnt) (Z.to_nat i) ltac:(lia))).
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma cm_slots_eq : forall gbs mbs i, marks_are gbs mbs -> 0 <= i < mk_n gbs ->
  cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)
  = cstr (slice mbs (MD_MARK + MARK_LEN * i) MARK_LEN).
Proof.
  intros gbs mbs i (Hn & Hnames) Hi.
  pose proof (cm_names_nth gbs MK_NAME (mk_n gbs) i Hi) as Hg.
  pose proof (cm_names_nth mbs MD_MARK (md_n_mark mbs) i ltac:(lia)) as Hm.
  unfold mk_names in Hnames. unfold md_marks in Hnames.
  rewrite Hnames in Hg. rewrite Hm in Hg. injection Hg as Hg. exact (eq_sym Hg).
Qed.

(* ==========================================================================
   2. The three entry regions and the loop head
   ========================================================================== *)

Definition cm_gotn : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition cm_mdn : YP09.region :=
  YP09.mkRegion (Some 11%nat) MD_N_MARK (MD_N_MARK + 4) 0 0
    [YP09.mkChunk MD_N_MARK (CVal 4 (SOff 33 0))].
Definition cm_SHa : list shent := [mkSHE 10 0 4].
Definition cm_SHb : list shent := [mkSHE 11 MD_N_MARK (MD_N_MARK + 4)].
Definition cm_e_facts (clo chi : Z) : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SB SB 0);
           (10%nat, mkAF 0 (2 ^ 47 - 517) 0); (11%nat, mkAF 0 (2 ^ 47 - 8857) 0);
           (33%nat, mkAF clo chi 0)] [] [].
Definition cm_e_ss (AF clo chi : Z) : sstate :=
  mkSS AF sr_atoms [stack_region 32; got_regionP; bcell_regionP 32] None (cm_e_facts clo chi).
Definition cm_e_extra (n : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 n].

Definition cm_sr : list sv :=
  [SLit 0;
   SOff 36 0; SOff 2 (-32); SOff 3 0; SOff 4 0;
   SOff 37 0; SOff 38 0; SOff 39 0;
   SOff 33 0; SOff 34 0;
   SOff 40 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 44 0; SOff 45 0; SOff 46 0; SOff 47 0;
   SOff 35 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0;
   SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0].
Definition cm_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) (-32) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0))].
Definition cm_l_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (35%nat, mkAF 1 MARKS_MAX 0)] [] [].
Definition cm_ss (AF : Z) : sstate := mkSS (AF + 0x6c) cm_sr [cm_frame] None cm_l_facts.

Lemma cm_soff0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
  intros E n. apply bv_eq. change (U E (SOff n 0) = bv_unsigned (ew E n)).
  rewrite U_SOff, Z.add_0_r. apply YP0m.zcanon_small.
  pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia.
Qed.

Lemma cm_soffc : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n c v Hn Hv Hc. apply bv_eq. change (U E (SOff n c) = bv_unsigned (Z_to_bv 64 (v + c))).
  rewrite U_SOff, Hn, unsigned_lit_small by lia. rewrite unsigned_lit_small by lia.
  apply YP0m.zcanon_small. lia.
Qed.

Lemma cm_ne_zero : forall E n (r : word), ew E n = r -> r = w64 0 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> False.
Proof. intros E n r Er Hr Hc. rewrite branch_ne_U, U_SOff, Z.add_0_r, U_SLit, Er, Hr in Hc. vm_compute in Hc. discriminate. Qed.

(* the bytes a run left as they were: the loop's runs write nothing *)
Ltac cm_nokept HFr W UNn :=
  let sg := lazymatch type of W with world ?s => s end in
  pose proof (kept_of_frame (segs := sg) _ _ _ _ _ (fun _ : Z => False) HFr
    ltac:(let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in
          let Hin := fresh in let Hrr := fresh in let H0 := fresh in
          intros bb wl wh aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [H0 | Hin];
                  [ inversion H0; subst; cbn [base_val] in Hrr; exfalso; lia | ]);
          exact Hin)) as UNn.

Ltac cm_jour HJ :=
  first [ exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ
        | apply (ajournal_gx_materialize _ _ ltac:(eassumption) pa_segs_low);
          first [exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ] ].

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
Hypothesis STRCMP : AStrcmpDef.astrcmp_realizes SEGS B (pa_sigma LS___interceptor_trampoline_strcmp).

Lemma cm_vals : VAL (A_OBJ 1) = LA_GOT_SHADOW /\ VAL (A_OBJ 64) = LA_SHADOW_CELL /\ BASE = link_text.
Proof.
  split; [rewrite (lv_obj LV 1) by (unfold link_nobj; lia); reflexivity|].
  split; [rewrite (lv_obj LV 64) by (unfold link_nobj; lia); reflexivity | exact (lv_text LV)].
Qed.

(* the registers at the loop head, for the turn with index i *)
Definition cm_inv (regs_e regs : bvmap 5 word) (got mp n i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs_e - 32) /\
  getr regs 3 = getr regs_e 3 /\ getr regs 4 = getr regs_e 4 /\
  getr regs 8 = Z_to_bv 64 (got + MK_NAME + MARK_LEN * i) /\
  getr regs 9 = Z_to_bv 64 (mp + MD_MARK + MARK_LEN * i) /\
  getr regs 18 = Z_to_bv 64 (n - i) /\
  getr regs 19 = getr regs_e 19 /\ getr regs 20 = getr regs_e 20 /\
  getr regs 21 = getr regs_e 21 /\ getr regs 22 = getr regs_e 22 /\
  getr regs 23 = getr regs_e 23 /\ getr regs 24 = getr regs_e 24 /\
  getr regs 25 = getr regs_e 25 /\ getr regs 26 = getr regs_e 26 /\
  getr regs 27 = getr regs_e 27.

Definition cm_saved (W : world SEGS) (mem : word -> option byte) (regs_e : bvmap 5 word) : Prop :=
  val_mem SEGS (rdW W mem) (spZ regs_e - 8) 8 (bv_unsigned (getr regs_e 1)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 16) 8 (bv_unsigned (getr regs_e 8)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 24) 8 (bv_unsigned (getr regs_e 9)) /\
  val_mem SEGS (rdW W mem) (spZ regs_e - 32) 8 (bv_unsigned (getr regs_e 18)).

Definition cm_extra (regs : bvmap 5 word) (got mp n i : Z) : list word :=
  [Z_to_bv 64 SB; Z_to_bv 64 (got + MK_NAME + MARK_LEN * i);
   Z_to_bv 64 (mp + MD_MARK + MARK_LEN * i); Z_to_bv 64 (n - i);
   getr regs 1; getr regs 5; getr regs 6; getr regs 7;
   getr regs 10; getr regs 11; getr regs 12; getr regs 13;
   getr regs 14; getr regs 15; getr regs 16; getr regs 17;
   getr regs 28; getr regs 29; getr regs 30; getr regs 31].

Definition cm_E (regs_e regs : bvmap 5 word) (got mp n i : Z) : env :=
  Eimg (Ereg regs_e (cm_extra regs got mp n i)).

Lemma cm_E_img : forall regs_e regs got mp n i, img_env VAL A_LIM (cm_E regs_e regs got mp n i).
Proof. intros. apply Eimg_env. Qed.

Lemma cm_E_reg : forall regs_e regs got mp n i m (r : bv 5),
  Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew (cm_E regs_e regs got mp n i) m = getr regs_e r.
Proof.
  intros regs_e regs got mp n i m r Hm Hlt. unfold cm_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs_e _ m r Hm).
Qed.

Lemma cm_E_ext : forall regs_e regs got mp n i j, (j < 20)%nat ->
  ew (cm_E regs_e regs got mp n i) (32 + j) = nth j (cm_extra regs got mp n i) (Z_to_bv 64 0).
Proof.
  intros regs_e regs got mp n i j Hj. unfold cm_E.
  rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs_e _ j).
Qed.

Lemma cm_aarg0 : forall (regs : bvmap 5 word), aarg regs 0 = bv_unsigned (getr regs 10).
Proof. intros regs. reflexivity. Qed.
Lemma cm_aarg1 : forall (regs : bvmap 5 word), aarg regs 1 = bv_unsigned (getr regs 11).
Proof. intros regs. reflexivity. Qed.

(* THE ENTRY STATE: the frame's write window, the .got word of the shadow base and its cell *)
Lemma cm_entry : forall AF clo chi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) n,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CHECK_MARKS_AK -> spZ regs <= sp0 ->
  amem_range (aarg regs 0) MK_SIZE -> amem_range (aarg regs 1) MD_SIZE ->
  0 <= clo -> clo <= n <= chi -> chi < 2 ^ 31 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (cm_e_extra n))) (cm_e_ss AF clo chi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF)) memc (seg_rom SEGS))).
Proof.
intros AF clo chi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n
  HJ H16 Hwlo Hwhi MRg MRm Hclo Hmid Hchi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B TL) in Kgot. rewrite (pal_cell B TL) in Kgot, Kcell.
destruct cm_vals as (V1 & V64 & VB). rewrite V1, V64 in Kgot. rewrite V64 in Kcell.
assert (Hg0 : 0 <= aarg regs 0)
  by (rewrite cm_aarg0; pose proof (bv_unsigned_in_range 64 (getr regs 10)) as HR; lia).
assert (Hm0 : 0 <= aarg regs 1)
  by (rewrite cm_aarg1; pose proof (bv_unsigned_in_range 64 (getr regs 11)) as HR; lia).
unfold amem_range, MK_SIZE, MD_SIZE, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRg, MRm.
set (E := Eimg (Ereg regs (cm_e_extra n))).
assert (EL : forall m, (m < A_TEXT)%nat -> ew E m = ew (Ereg regs (cm_e_extra n)) m)
  by (intros m Hm; apply Eimg_low; exact Hm).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2%nat 2%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10%nat 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11%nat 11%bv eq_refl)).
assert (X32 : ew E 32 = Z_to_bv 64 SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (X33 : ew E 33 = Z_to_bv 64 n)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (Egot : ew E (A_OBJ 1) = Z_to_bv 64 LA_GOT_SHADOW)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V1; reflexivity).
assert (Ecell : ew E (A_OBJ 64) = Z_to_bv 64 LA_SHADOW_CELL)
  by (unfold E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia); rewrite V64; reflexivity).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = aarg regs 0) by (rewrite E10, cm_aarg0; reflexivity).
assert (U11 : bv_unsigned (ew E 11) = aarg regs 1) by (rewrite E11, cm_aarg1; reflexivity).
assert (VBv : forall m v, ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some m) = v)
  by (intros m v Hm Hv; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hv).
rewrite restrict_mkst_fx. unfold cm_e_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. cbn [ms_mem restrict mkst]. apply (apresent_writable SEGS). apply Hpres. lia.
  + fold E. rewrite (VBv _ _ Egot) by (unfold LA_GOT_SHADOW; lia).
    split; [unfold LA_GOT_SHADOW; lia|]. split; [unfold LA_GOT_SHADOW; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_GOT_SHADOW 0 8 (SOff (A_OBJ 64) 0) LA_SHADOW_CELL);
      [rewrite cm_soff0, Ecell; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold LA_SHADOW_CELL; lia | cbn; lia |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBv _ _ Ecell) by (unfold LA_SHADOW_CELL; lia).
    split; [unfold LA_SHADOW_CELL; lia|]. split; [unfold LA_SHADOW_CELL; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ LA_SHADOW_CELL 0 8 (SOff 32 0) SB);
      [rewrite cm_soff0, X32; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst]. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
- apply pairwise_disjoint_of_extents.
  unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. fold E.
  rewrite (VBv _ _ Egot) by (unfold LA_GOT_SHADOW; lia).
  rewrite (VBv _ _ Ecell) by (unfold LA_SHADOW_CELL; lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold LA_GOT_SHADOW, LA_SHADOW_CELL. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [cm_e_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, X32, X33, U10, U11.
  rewrite !unsigned_lit_small by (try unfold SB; lia).
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 4) with 16. unfold SB.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* THE LOOP HEAD at +0x6c, for the turn with index i *)
Lemma cm_seat : forall AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k
    (regs_e regs : bvmap 5 word) got mp n i,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k ->
  spZ regs_e mod 16 = 0 -> sp0 - STK <= spZ regs_e - CHECK_MARKS_AK -> spZ regs_e <= sp0 ->
  cm_inv regs_e regs got mp n i -> cm_saved W mem regs_e ->
  0 <= i -> i + 1 <= n -> n <= MARKS_MAX ->
  st_ok_pi SEGS VAL (cm_E regs_e regs got mp n i) (cm_ss AF)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + (AF + 0x6c))) mem (seg_rom SEGS))).
Proof.
intros AF G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs_e regs got mp n i
  HJ H16 Hwlo Hwhi HINV HSV Hi0 Hin Hn32.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
unfold MARKS_MAX in Hn32.
assert (Hsp46 : 2 ^ 46 <= spZ regs_e <= 2 ^ 47) by lia.
destruct HINV as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
destruct HSV as (S1 & S8 & S9 & S18).
set (E := cm_E regs_e regs got mp n i).
assert (E1 : ew E 1 = getr regs_e 1) by (apply (cm_E_reg _ _ _ _ _ _ 1%nat 1%bv); [reflexivity | lia]).
assert (E2 : ew E 2 = getr regs_e 2) by (apply (cm_E_reg _ _ _ _ _ _ 2%nat 2%bv); [reflexivity | lia]).
assert (E3 : ew E 3 = getr regs_e 3) by (apply (cm_E_reg _ _ _ _ _ _ 3%nat 3%bv); [reflexivity | lia]).
assert (E4 : ew E 4 = getr regs_e 4) by (apply (cm_E_reg _ _ _ _ _ _ 4%nat 4%bv); [reflexivity | lia]).
assert (E8 : ew E 8 = getr regs_e 8) by (apply (cm_E_reg _ _ _ _ _ _ 8%nat 8%bv); [reflexivity | lia]).
assert (E9 : ew E 9 = getr regs_e 9) by (apply (cm_E_reg _ _ _ _ _ _ 9%nat 9%bv); [reflexivity | lia]).
assert (E18 : ew E 18 = getr regs_e 18) by (apply (cm_E_reg _ _ _ _ _ _ 18%nat 18%bv); [reflexivity | lia]).
assert (E19 : ew E 19 = getr regs_e 19) by (apply (cm_E_reg _ _ _ _ _ _ 19%nat 19%bv); [reflexivity | lia]).
assert (E20 : ew E 20 = getr regs_e 20) by (apply (cm_E_reg _ _ _ _ _ _ 20%nat 20%bv); [reflexivity | lia]).
assert (E21 : ew E 21 = getr regs_e 21) by (apply (cm_E_reg _ _ _ _ _ _ 21%nat 21%bv); [reflexivity | lia]).
assert (E22 : ew E 22 = getr regs_e 22) by (apply (cm_E_reg _ _ _ _ _ _ 22%nat 22%bv); [reflexivity | lia]).
assert (E23 : ew E 23 = getr regs_e 23) by (apply (cm_E_reg _ _ _ _ _ _ 23%nat 23%bv); [reflexivity | lia]).
assert (E24 : ew E 24 = getr regs_e 24) by (apply (cm_E_reg _ _ _ _ _ _ 24%nat 24%bv); [reflexivity | lia]).
assert (E25 : ew E 25 = getr regs_e 25) by (apply (cm_E_reg _ _ _ _ _ _ 25%nat 25%bv); [reflexivity | lia]).
assert (E26 : ew E 26 = getr regs_e 26) by (apply (cm_E_reg _ _ _ _ _ _ 26%nat 26%bv); [reflexivity | lia]).
assert (E27 : ew E 27 = getr regs_e 27) by (apply (cm_E_reg _ _ _ _ _ _ 27%nat 27%bv); [reflexivity | lia]).
assert (X33 : ew E 33 = Z_to_bv 64 (got + MK_NAME + MARK_LEN * i))
  by exact (cm_E_ext _ _ _ _ _ _ 1%nat ltac:(lia)).
assert (X34 : ew E 34 = Z_to_bv 64 (mp + MD_MARK + MARK_LEN * i))
  by exact (cm_E_ext _ _ _ _ _ _ 2%nat ltac:(lia)).
assert (X35 : ew E 35 = Z_to_bv 64 (n - i)) by exact (cm_E_ext _ _ _ _ _ _ 3%nat ltac:(lia)).
assert (X36 : ew E 36 = getr regs 1) by exact (cm_E_ext _ _ _ _ _ _ 4%nat ltac:(lia)).
assert (X37 : ew E 37 = getr regs 5) by exact (cm_E_ext _ _ _ _ _ _ 5%nat ltac:(lia)).
assert (X38 : ew E 38 = getr regs 6) by exact (cm_E_ext _ _ _ _ _ _ 6%nat ltac:(lia)).
assert (X39 : ew E 39 = getr regs 7) by exact (cm_E_ext _ _ _ _ _ _ 7%nat ltac:(lia)).
assert (X40 : ew E 40 = getr regs 10) by exact (cm_E_ext _ _ _ _ _ _ 8%nat ltac:(lia)).
assert (X41 : ew E 41 = getr regs 11) by exact (cm_E_ext _ _ _ _ _ _ 9%nat ltac:(lia)).
assert (X42 : ew E 42 = getr regs 12) by exact (cm_E_ext _ _ _ _ _ _ 10%nat ltac:(lia)).
assert (X43 : ew E 43 = getr regs 13) by exact (cm_E_ext _ _ _ _ _ _ 11%nat ltac:(lia)).
assert (X44 : ew E 44 = getr regs 14) by exact (cm_E_ext _ _ _ _ _ _ 12%nat ltac:(lia)).
assert (X45 : ew E 45 = getr regs 15) by exact (cm_E_ext _ _ _ _ _ _ 13%nat ltac:(lia)).
assert (X46 : ew E 46 = getr regs 16) by exact (cm_E_ext _ _ _ _ _ _ 14%nat ltac:(lia)).
assert (X47 : ew E 47 = getr regs 17) by exact (cm_E_ext _ _ _ _ _ _ 15%nat ltac:(lia)).
assert (X48 : ew E 48 = getr regs 28) by exact (cm_E_ext _ _ _ _ _ _ 16%nat ltac:(lia)).
assert (X49 : ew E 49 = getr regs 29) by exact (cm_E_ext _ _ _ _ _ _ 17%nat ltac:(lia)).
assert (X50 : ew E 50 = getr regs 30) by exact (cm_E_ext _ _ _ _ _ _ 18%nat ltac:(lia)).
assert (X51 : ew E 51 = getr regs 31) by exact (cm_E_ext _ _ _ _ _ _ 19%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs_e) by (rewrite E2; reflexivity).
rewrite restrict_mkst_fx. unfold cm_ss. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr]); [..|destruct Hr];
    [ lazymatch goal with |- _ = sv_denot ?EE (sr_get ?L ?R) =>
        let v := eval vm_compute in (sr_get L R) in change (sr_get L R) with v end .. ];
    [ rewrite getr_zero; reflexivity
    | rewrite cm_soff0, X36; reflexivity
    | rewrite (cm_soffc E 2 (-32) (spZ regs_e));
        [exact R2 | rewrite E2; symmetry; apply Z_to_bv_bv_unsigned | lia | lia]
    | rewrite cm_soff0, E3; exact R3
    | rewrite cm_soff0, E4; exact R4
    | rewrite cm_soff0, X37; reflexivity
    | rewrite cm_soff0, X38; reflexivity
    | rewrite cm_soff0, X39; reflexivity
    | rewrite cm_soff0, X33; exact R8
    | rewrite cm_soff0, X34; exact R9
    | rewrite cm_soff0, X40; reflexivity
    | rewrite cm_soff0, X41; reflexivity
    | rewrite cm_soff0, X42; reflexivity
    | rewrite cm_soff0, X43; reflexivity
    | rewrite cm_soff0, X44; reflexivity
    | rewrite cm_soff0, X45; reflexivity
    | rewrite cm_soff0, X46; reflexivity
    | rewrite cm_soff0, X47; reflexivity
    | rewrite cm_soff0, X35; exact R18
    | rewrite cm_soff0, E19; exact R19
    | rewrite cm_soff0, E20; exact R20
    | rewrite cm_soff0, E21; exact R21
    | rewrite cm_soff0, E22; exact R22
    | rewrite cm_soff0, E23; exact R23
    | rewrite cm_soff0, E24; exact R24
    | rewrite cm_soff0, E25; exact R25
    | rewrite cm_soff0, E26; exact R26
    | rewrite cm_soff0, E27; exact R27
    | rewrite cm_soff0, X48; reflexivity
    | rewrite cm_soff0, X49; reflexivity
    | rewrite cm_soff0, X50; reflexivity
    | rewrite cm_soff0, X51; reflexivity ].
- vm_compute. reflexivity.
- unfold cm_frame. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil; cbn [ms_mem restrict mkst];
    [ apply (chunk_ok_val SEGS E _ (spZ regs_e) (-8) 8 (SOff 1 0) (bv_unsigned (getr regs_e 1)))
    | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-16) 8 (SOff 8 0) (bv_unsigned (getr regs_e 8)))
    | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-24) 8 (SOff 9 0) (bv_unsigned (getr regs_e 9)))
    | apply (chunk_ok_val SEGS E _ (spZ regs_e) (-32) 8 (SOff 18 0) (bv_unsigned (getr regs_e 18))) ];
    try (rewrite cm_soff0; first [rewrite E1 | rewrite E8 | rewrite E9 | rewrite E18];
         symmetry; apply Z_to_bv_bv_unsigned);
    try (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range);
    try (cbn; lia);
    first [exact S1 | exact S8 | exact S9 | exact S18].
- apply pairwise_disjoint_of_extents. unfold cm_frame, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [cm_l_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite Usp, X35. rewrite unsigned_lit_small by lia.
  rewrite ?Z.pow_0_r, ?Z.mod_1_r. change (2 ^ 4) with 16. unfold MARKS_MAX.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* the write permission of a run whose only window is this frame *)
Ltac cm_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs _ _ _ _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_x_cons;
    [ intros ?a ?Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
      first
      [ exfalso; lia
      | lazymatch type of Ha with context [ew _ 2%nat] =>
          match goal with U : bv_unsigned (ew _ 2%nat) = _ |- _ => rewrite U in Ha end;
          left; split; [left; lia | lia] end ]
    | ]);
  apply awr_ok_x_nil.

(* one shadow entry over a block the Pre gives the shadow of *)
Lemma cm_shok1 : forall (E : env) (W : world SEGS) (mem : word -> option byte) (mm : nat) (p lo hi : Z),
  ew E 32 = Z_to_bv 64 SB -> ew E mm = Z_to_bv 64 p ->
  0 <= lo -> lo <= hi -> 0 <= p -> amem_range p hi ->
  range_addressable (ard SEGS (rdW W mem)) SHADOW_OFF (p + lo) (hi - lo) ->
  sh_ok SEGS (SOff 32 0) [mkSHE mm lo hi] E (rdW W mem).
Proof.
  intros E W mem mm p lo hi E32 Em Hlo Hhi Hp0 HMR HRA.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 32 SB E32) by (unfold SB; lia).
  rewrite (U_atom E mm p Em)
    by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HMR; lia).
  split.
  - rewrite <- (aview_rd_of SEGS). change SB with SHADOW_OFF.
    apply (ra_shadow_eq (ard SEGS (rdW W mem))); [exact HRA|].
    intros x Hx. rewrite (ard_aview SEGS). reflexivity.
  - intros a Ha. rewrite Z.min_l in Ha by lia. rewrite Z.max_r in Ha by lia.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HMR.
    unfold SB. lia.
Qed.

(* a 4-byte field of a block, as a region chunk needs it *)
Lemma cm_u32_at : forall (m : word -> option byte) p bs off,
  au8arr SEGS m p bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  val_mem SEGS m (p + off) 4 (fld_u32 bs off).
Proof.
  intros m p bs off (Hab & _) Hoff Hn. unfold fld_u32.
  exact (val_mem_of_abytes SEGS m p bs off 4%nat Hab Hoff ltac:(cbn; lia)).
Qed.

(* the bytes the entry run left as they were: all but its own 32-byte frame *)
Ltac cm_kept_fr HFr sp UNn :=
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a : Z => sp - 32 <= a < sp) HFr
    ltac:(let bb := fresh in let wl := fresh in let wh := fresh in let aa := fresh in
          let Hin := fresh in let Hrr := fresh in let H0 := fresh in
          intros bb wl wh aa Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [H0 | Hin];
                  [ inversion H0; subst; cbn [base_val] in Hrr;
                    repeat match goal with U : bv_unsigned (ew _ ?n) = _ |- _ =>
                      lazymatch type of Hrr with context [ew _ n] => rewrite U in Hrr end end;
                    cbv beta; lia | ]);
          destruct Hin)) as UNn.

(* the contract's postcondition, as every exit of the walk reaches it *)
Definition cm_Q G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word) :=
  apost SK SEGS B CHECK_MARKS_AK 0 (fun a => inFP (check_marks_awr regs (rdW W memc)) a)
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2' mem2' md2' =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       check_marks_apost regs (rdW W memc) regs2' (rdW W2 mem2')).

(* THE ENTRY RUN: the frame, the shadow base, the two instrumented checks, the two counts, `bne` (decided),
   `blez`: an empty marks block returns; else the run reaches the loop head at +0x6c (KONT) *)
Lemma cm_start : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
    (regs : bvmap 5 word) gbs mbs,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CHECK_MARKS_AK -> spZ regs <= sp0 ->
  amarks_at SEGS (rdW W memc) (aarg regs 0) gbs -> amodel_at SEGS (rdW W memc) (aarg regs 1) mbs ->
  marks_wf gbs -> model_marks_wf mbs -> marks_are gbs mbs ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs 0) MK_SIZE ->
  amem_range (aarg regs 0) MK_SIZE ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs 1) MD_SIZE ->
  amem_range (aarg regs 1) MD_SIZE ->
  apart_frame regs CHECK_MARKS_AK (aarg regs 0) MK_SIZE ->
  apart_frame regs CHECK_MARKS_AK (aarg regs 1) MD_SIZE ->
  (1 <= mk_n gbs -> forall (mem1 : word -> option byte) md1 (regs1 : bvmap 5 word),
     ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
        aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
     (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem1 a) ->
     m_fds md1 = m_fds mdc -> m_fs md1 = m_fs mdc ->
     cm_inv regs regs1 (aarg regs 0) (aarg regs 1) (mk_n gbs) 0 -> cm_saved W mem1 regs ->
     SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_marks + 0x6c))) mem1 (seg_rom SEGS)) md1)
       (cm_Q G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_marks)) memc (seg_rom SEGS)) mdc)
    (cm_Q G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs mbs
  HGX HJ Hret H16 Hwlo Hwhi HMK HMD HWF HMWF HARE RAg MRg RAm MRm PFg PFm KONT.
pose proof HJ as HJ0. unfold YK0s.ret_ok in Hret.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof HWF as (HWFn & _). pose proof HMWF as (HMWFn & _).
pose proof HARE as (HAREn & HAREs).
pose proof HMK as (HMKa & HMKl). pose proof HMD as (HMDa & HMDl).
assert (Hg0 : 0 <= aarg regs 0)
  by (rewrite cm_aarg0; pose proof (bv_unsigned_in_range 64 (getr regs 10)) as HR; lia).
assert (Hm0 : 0 <= aarg regs 1)
  by (rewrite cm_aarg1; pose proof (bv_unsigned_in_range 64 (getr regs 11)) as HR; lia).
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* the entry state *)
pose proof (cm_entry AF_check_marks 0 MARKS_MAX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
              regs (mk_n gbs) HJ H16 Hwlo Hwhi MRg MRm ltac:(lia) ltac:(unfold MARKS_MAX in *; lia)
              ltac:(unfold MARKS_MAX; lia)) as HS.
set (E0 := Eimg (Ereg regs (cm_e_extra (mk_n gbs)))) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE1 : ew E0 1 = getr regs 1)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1%nat 1%bv eq_refl)).
assert (EE2 : ew E0 2 = getr regs 2)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2%nat 2%bv eq_refl)).
assert (EE3 : ew E0 3 = getr regs 3)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3%nat 3%bv eq_refl)).
assert (EE4 : ew E0 4 = getr regs 4)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4%nat 4%bv eq_refl)).
assert (EE10 : ew E0 10 = getr regs 10)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10%nat 10%bv eq_refl)).
assert (EE11 : ew E0 11 = getr regs 11)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11%nat 11%bv eq_refl)).
assert (X32 : ew E0 32 = Z_to_bv 64 SB)
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (X33 : ew E0 33 = Z_to_bv 64 (mk_n gbs))
  by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (G10 : ew E0 10 = Z_to_bv 64 (aarg regs 0))
  by (rewrite EE10, cm_aarg0; symmetry; apply Z_to_bv_bv_unsigned).
assert (G11 : ew E0 11 = Z_to_bv 64 (aarg regs 1))
  by (rewrite EE11, cm_aarg1; symmetry; apply Z_to_bv_bv_unsigned).
assert (Usp : bv_unsigned (ew E0 2) = spZ regs) by (rewrite EE2; reflexivity).
assert (HAE0 : env_agree 32 (Ereg regs (cm_e_extra (mk_n gbs))) E0)
  by (unfold E0; split; [ intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity ]).
(* the two counts, as the two regions carry them *)
assert (VNg : val_mem SEGS (rdW W memc) (aarg regs 0 + MK_N) 4 (mk_n gbs))
  by (unfold mk_n; apply (cm_u32_at _ _ gbs MK_N HMKa); unfold MK_N, MK_SIZE in *; lia).
assert (VNm : val_mem SEGS (rdW W memc) (aarg regs 1 + MD_N_MARK) 4 (mk_n gbs)).
{ rewrite HAREn. unfold md_n_mark. apply (cm_u32_at _ _ mbs MD_N_MARK HMDa);
    unfold MD_N_MARK, MD_SIZE in *; lia. }
(* phase A: the frame, the shadow base, the check of the marks count, to +0x30 *)
assert (SHOKa : sh_ok SEGS (SOff 32 0) cm_SHa E0 (rdW W memc)).
{ unfold cm_SHa. apply (cm_shok1 E0 W memc 10%nat (aarg regs 0) 0 4 X32 G10 ltac:(lia) ltac:(lia) Hg0
    (cm_amem_sub (aarg regs 0) MK_SIZE (aarg regs 0) 4 MRg ltac:(lia) ltac:(lia) ltac:(unfold MK_SIZE; lia))).
  rewrite Z.add_0_r, Z.sub_0_r.
  exact (cm_ra_sub (ard SEGS (rdW W memc)) (aarg regs 0) MK_SIZE (aarg regs 0) 4 RAg
           ltac:(lia) ltac:(lia) ltac:(unfold MK_SIZE; lia)). }
paj_run_to_tok RUNTO HS HJ SHOKa Bspan (AF_check_marks + 0x30); [ cm_awr | ].
cm_kept_fr HFr (spZ regs) UNa. clear HF HFr.
lazymatch type of HS with st_ok_pi _ _ ?EV ?ss1 (restrict _ ?ms1) =>
  set (E1 := EV) in HS; set (ssA := ss1) in HS; rename ms1 into msA; rename HG into HGA end.
assert (EW1 : forall a, (a < 512)%nat -> ew E1 a = ew E0 a)
  by (intros a Ha; unfold E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (UNA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem msA) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; apply UNa; [exact Ha | cbv beta; exact Hw]).
assert (MBA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          mbyte SEGS (rdW W (ms_mem msA)) a = mbyte SEGS (rdW W memc) a)
  by (intros a Ha Hw; apply (mbyte_of_aview SEGS); exact (UNA a Ha Hw)).
assert (MRg' := MRg). assert (MRm' := MRm). assert (PFg' := PFg). assert (PFm' := PFm).
unfold amem_range, MK_SIZE, MD_SIZE, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRg', MRm'.
unfold apart_frame, MK_SIZE, MD_SIZE in PFg', PFm'.
assert (U10 : bv_unsigned (ew E1 10) = aarg regs 0)
  by (rewrite EW1 by lia; rewrite G10; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E1 11) = aarg regs 1)
  by (rewrite EW1 by lia; rewrite G11; apply unsigned_lit_small; lia).
assert (Y32 : ew E1 32 = Z_to_bv 64 SB) by (rewrite EW1 by lia; exact X32).
assert (Y33 : ew E1 33 = Z_to_bv 64 (mk_n gbs)) by (rewrite EW1 by lia; exact X33).
assert (Y11 : ew E1 11 = Z_to_bv 64 (aarg regs 1)) by (rewrite EW1 by lia; exact G11).
assert (UspA : bv_unsigned (ew E1 2) = spZ regs) by (rewrite EW1 by lia; exact Usp).
(* drop the .got and cell regions, add the marks count *)
assert (HSA : st_ok_pi SEGS VAL E1
          (mkSS (ss_pc ssA) (ss_regs ssA) (cm_gotn :: pick (ss_mem ssA) [0]%nat) (ss_resv ssA) (ss_facts ssA))
          (restrict (w_H W) msA)).
{ apply (st_ok_pi_add_region E1
           (mkSS (ss_pc ssA) (ss_regs ssA) (pick (ss_mem ssA) [0]%nat) (ss_resv ssA) (ss_facts ssA))).
  - apply st_ok_pi_submem; [exact HS | unfold ssA; vm_compute; submem_tac | vm_compute; reflexivity].
  - vm_compute; reflexivity.
  - unfold region_ok, cm_gotn.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U10. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E1 _ (aarg regs 0) 0 4 (SOff 33 0) (mk_n gbs));
      [ rewrite cm_soff0, Y33; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); unfold MARKS_MAX in *; lia | cbn; lia |].
    cbn [ms_mem restrict mkst]. unfold MK_N in VNg.
    intros j Hj. rewrite (MBA (aarg regs 0 + 0 + Z.of_nat j) ltac:(cbn in Hj; lia) ltac:(cbn in Hj; lia)).
    exact (VNg j Hj).
  - apply all_disjoint_of_extents. unfold cm_gotn, extent_of_region.
    cbn [ss_mem pick nth_error map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    lazymatch goal with |- context [ss_mem ssA] => unfold ssA end.
    cbn [ss_mem pick nth_error map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U10, UspA. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. lia. }
clear HS. rename HSA into HS.
assert (HEI1 : img_env VAL A_LIM E1)
  by (unfold E1; apply img_env_ewset_hi; [apply img_env_ewset_hi; [exact HEI | cbv; lia] | cbv; lia]).
clear HEI. rename HEI1 into HEI.
(* phase B: the check of the model count, to +0x50 *)
assert (SHOKb : sh_ok SEGS (SOff 32 0) cm_SHb E1 (rdW W (ms_mem msA))).
{ unfold cm_SHb.
  apply (cm_shok1 E1 W (ms_mem msA) 11%nat (aarg regs 1) MD_N_MARK (MD_N_MARK + 4) Y32 Y11
           ltac:(unfold MD_N_MARK; lia) ltac:(lia) Hm0
           (cm_amem_sub (aarg regs 1) MD_SIZE (aarg regs 1) (MD_N_MARK + 4) MRm ltac:(lia)
              ltac:(unfold MD_N_MARK; lia) ltac:(unfold MD_N_MARK, MD_SIZE; lia))).
  replace (MD_N_MARK + 4 - MD_N_MARK) with 4 by lia.
  apply (ra_shadow_eq (ard SEGS (rdW W memc))).
  - exact (cm_ra_sub (ard SEGS (rdW W memc)) (aarg regs 1) MD_SIZE (aarg regs 1 + MD_N_MARK) 4 RAm
             ltac:(unfold MD_N_MARK; lia) ltac:(lia) ltac:(unfold MD_N_MARK, MD_SIZE; lia)).
  - intros x Hx.
    assert (Hx' : 0 <= x < kHighMemEnd) by (unfold kHighMemEnd, MD_N_MARK in *; lia).
    pose proof (shadow_addr_bounds x Hx') as Hsb. unfold kHighShadowEnd in Hsb.
    apply UNA; lia. }
clear SHOKa.
paj_run_to_tok RUNTO HS HJ SHOKb Bspan (AF_check_marks + 0x50); [ cm_awr | ].
cm_kept_fr HFr (spZ regs) UNb. clear HF HFr.
lazymatch type of HS with st_ok_pi _ _ ?EV ?ss2 (restrict _ ?ms2) =>
  set (E2 := EV) in HS; set (ssB := ss2) in HS; rename ms2 into msB; rename HG into HGB end.
assert (EW2 : forall a, (a < 512)%nat -> ew E2 a = ew E0 a)
  by (intros a Ha; unfold E2; rewrite !ew_ewset_other by lia; apply EW1; exact Ha).
assert (UNB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite (UNb a Ha ltac:(cbv beta; exact Hw)); exact (UNA a Ha Hw)).
assert (MBB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          mbyte SEGS (rdW W (ms_mem msB)) a = mbyte SEGS (rdW W memc) a)
  by (intros a Ha Hw; apply (mbyte_of_aview SEGS); exact (UNB a Ha Hw)).
assert (U11B : bv_unsigned (ew E2 11) = aarg regs 1)
  by ((rewrite EW2 by lia); rewrite G11; apply unsigned_lit_small; lia).
assert (UspB : bv_unsigned (ew E2 2) = spZ regs) by ((rewrite EW2 by lia); exact Usp).
assert (Y33B : ew E2 33 = Z_to_bv 64 (mk_n gbs)) by ((rewrite EW2 by lia); exact X33).
(* drop the marks count, add the model count *)
assert (HSB : st_ok_pi SEGS VAL E2
          (mkSS (ss_pc ssB) (ss_regs ssB) (cm_mdn :: pick (ss_mem ssB) [1]%nat) (ss_resv ssB) (ss_facts ssB))
          (restrict (w_H W) msB)).
{ apply (st_ok_pi_add_region E2
           (mkSS (ss_pc ssB) (ss_regs ssB) (pick (ss_mem ssB) [1]%nat) (ss_resv ssB) (ss_facts ssB))).
  - apply st_ok_pi_submem; [exact HS | unfold ssB; vm_compute; submem_tac | vm_compute; reflexivity].
  - vm_compute; reflexivity.
  - unfold region_ok, cm_mdn.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11B. split; [unfold MD_N_MARK; lia|]. split; [unfold MD_N_MARK; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E2 _ (aarg regs 1) MD_N_MARK 4 (SOff 33 0) (mk_n gbs));
      [ rewrite cm_soff0, Y33B; reflexivity
      | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); unfold MARKS_MAX in *; lia | cbn; lia |].
    cbn [ms_mem restrict mkst].
    intros jj Hjj. rewrite (MBB (aarg regs 1 + MD_N_MARK + Z.of_nat jj) ltac:(unfold MD_N_MARK; cbn in Hjj; lia)
                          ltac:(unfold MD_N_MARK; cbn in Hjj; lia)).
    exact (VNm jj Hjj).
  - apply all_disjoint_of_extents. unfold cm_mdn, extent_of_region.
    cbn [ss_mem pick nth_error map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    lazymatch goal with |- context [ss_mem ssB] => unfold ssB end.
    cbn [ss_mem pick nth_error map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U11B, UspB. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold MD_N_MARK. lia. }
clear HS. rename HSB into HS.
assert (HEI2 : img_env VAL A_LIM E2)
  by (unfold E2; apply img_env_ewset_hi; [apply img_env_ewset_hi; [exact HEI | cbv; lia] | cbv; lia]).
assert (SHOKc : sh_ok SEGS (SOff 32 0) [] E2 (rdW W (ms_mem msB))) by constructor.
clear SHOKb.
(* phase C: m->n_mark, `bne` (decided equal), `blez` *)
paj_run_tok RUN HS HJ SHOKc Bspan; [ cm_awr | ].
cm_kept_fr HFr (spZ regs) UNc. clear HF HFr. rename HG into HGC.
assert (UNC : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 32 <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem (msB)) a = aview SEGS (w_H W) memc a) by exact UNB.
psrr_branch_tok RUN BR HS SHOKc Bspan.
- (* n = 0: +0x8c .. +0xa0 restore, pop, ret *)
  paj_run_tok RUN HS HJ SHOKc Bspan; [ cm_awr | ].
  cm_kept_fr HFr (spZ regs) UNd. clear HF HFr. rename HG into HGD.
  lazymatch type of HS with st_ok_pi _ _ ?EV _ (restrict _ ?msF) =>
    rename msF into msD;
    assert (HAE4 : env_agree 32 (Ereg regs (cm_e_extra (mk_n gbs))) EV)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; unfold E2; rewrite ?ew_ewset_other by lia;
                  unfold E1; rewrite ?ew_ewset_other by lia; unfold E0; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    pose proof (aregs_preserved_of_st_ok SEGS _ EV _ _ regs (cm_e_extra (mk_n gbs)) HS HAE4
                  ltac:(vm_compute; reflexivity)) as HPr
  end.
  prreg HS (1%bv : bv 5) R1.
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite R1; rewrite ?ew_ewset_other by lia; unfold E2; rewrite ?ew_ewset_other by lia;
    unfold E1; rewrite ?ew_ewset_other by lia; rewrite EE1, Hret.
  apply (cm_exit SK B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ HJ0).
  + first [ exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ] ].
  + exact Hwlo.
  + exact Hwhi.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
  + exact HPr.
  + intros a Ha Hw. rewrite (UNd a Ha ltac:(cbv beta; lia)), (UNc a Ha ltac:(cbv beta; lia)).
    exact (UNB a Ha ltac:(lia)).
  + intros a Ha. apply (cm_grow _ _ _ HGD), (cm_grow _ _ _ HGC), (cm_grow _ _ _ HGB), (cm_grow _ _ _ HGA), Ha.
- (* n > 0: +0x5c .. +0x68 the two slot pointers, to the loop head *)
  assert (Hnpos : 1 <= mk_n gbs).
  { destruct (Z.eq_dec (mk_n gbs) 0) as [Hn0|Hn0]; [|lia]. exfalso.
    rewrite cm_soff0 in Hc. rewrite ?ew_ewset_other in Hc by lia. rewrite Y33B, Hn0 in Hc.
    vm_compute in Hc. discriminate. }
  paj_run_to_tok RUNTO HS HJ SHOKc Bspan (AF_check_marks + 0x6c); [ cm_awr | ].
  cm_kept_fr HFr (spZ regs) UNd. clear HF HFr. rename HG into HGD.
  lazymatch type of HS with st_ok_pi _ _ ?EV ?ssF (restrict _ ?msF) =>
    rename msF into msD; set (E4 := EV) in HS; set (ssD := ssF) in HS end.
  assert (EW4 : forall a, (a < 512)%nat -> ew E4 a = ew E0 a)
    by (intros a Ha; unfold E4; rewrite ?ew_ewset_other by lia; apply EW2; exact Ha).
  assert (ER0 : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew E0 m = getr regs r)
    by (intros m r Hm Hl; unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
  assert (BREG : forall r : bv 5, getr (ms_regs msD) r = sv_denot E4 (sr_get (ss_regs ssD) r))
    by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E4 ssD msD r HS)).
  assert (HINV : cm_inv regs (ms_regs msD) (aarg regs 0) (aarg regs 1) (mk_n gbs) 0).
  { assert (W10 : ew E4 10 = Z_to_bv 64 (aarg regs 0)) by ((rewrite EW4 by lia); exact G10).
    assert (W11 : ew E4 11 = Z_to_bv 64 (aarg regs 1)) by ((rewrite EW4 by lia); exact G11).
    assert (W33 : ew E4 33 = Z_to_bv 64 (mk_n gbs)) by ((rewrite EW4 by lia); exact X33).
    assert (W2 : ew E4 2 = Z_to_bv 64 (spZ regs))
      by ((rewrite EW4 by lia); rewrite EE2; symmetry; apply Z_to_bv_bv_unsigned).
    unfold cm_inv; rewrite !BREG; unfold ssD.
    repeat split;
    lazymatch goal with |- sv_denot _ (sr_get ?LL ?RR) = _ =>
      let v := eval vm_compute in (sr_get LL RR) in change (sr_get LL RR) with v end;
    first
    [ rewrite (cm_soffc E4 2 (-32) (spZ regs) W2) by lia; reflexivity
    | rewrite cm_soff0; (rewrite EW4 by lia); first [exact EE3 | exact EE4 | apply ER0; [reflexivity | lia] ]
    | rewrite (cm_soffc E4 10 _ (aarg regs 0) W10) by lia; f_equal; unfold MK_NAME, MARK_LEN; lia
    | rewrite (cm_soffc E4 11 _ (aarg regs 1) W11) by lia; f_equal; unfold MD_MARK, MARK_LEN; lia
    | rewrite cm_soff0, W33; f_equal; lia
    | rewrite (cm_soffc E4 33 _ (mk_n gbs) W33) by (unfold MARKS_MAX in *; lia); f_equal; lia ]. }
  assert (HSV : cm_saved W (ms_mem msD) regs).
  { pose proof (st_ok_region_nth (segs := SEGS) E4 (abs_ss VAL ssD) (restrict (w_H W) msD) 1 _ HS eq_refl) as HR.
    unfold ssD in HR. cbn [ss_mem nth_error ms_mem restrict] in HR.
    unfold cm_saved.
    repeat split;
    (eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 8%N);
       [ exact HR
       | (rewrite EW4 by lia); exact Usp
       | repeat (first [left; reflexivity | right])
       | rewrite cm_soff0; (rewrite EW4 by lia); rewrite Z_to_bv_bv_unsigned; apply ER0; [reflexivity | lia]
       | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply bv_unsigned_in_range
       | cbn; lia ]). }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
    replace pcl with (AF_check_marks + 0x6c) by (vm_compute; reflexivity) end.
  apply (KONT Hnpos (ms_mem msD) _ (ms_regs msD)).
  + first [ exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ | (repeat rewrite wvb_collapse in HJ); exact HJ] ].
  + intros a Ha Hw. rewrite (UNd a Ha ltac:(cbv beta; lia)), (UNc a Ha ltac:(cbv beta; lia)).
    exact (UNB a Ha ltac:(lia)).
  + intros a Ha. apply (cm_grow _ _ _ HGD), (cm_grow _ _ _ HGC), (cm_grow _ _ _ HGB), (cm_grow _ _ _ HGA), Ha.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
  + exact HINV.
  + exact HSV.
Qed.


(* THE LOOP at +0x6c: one turn per mark, by induction on the marks left *)
Lemma cm_loop : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) gbs mbs,
  gx_ok SEGS B G ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - CHECK_MARKS_AK -> spZ regs <= sp0 ->
  amarks_at SEGS (rdW W memc) (aarg regs 0) gbs -> amodel_at SEGS (rdW W memc) (aarg regs 1) mbs ->
  marks_wf gbs -> model_marks_wf mbs -> marks_are gbs mbs ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs 0) MK_SIZE ->
  shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs 0) MK_SIZE ->
  amem_range (aarg regs 0) MK_SIZE ->
  range_addressable (ard SEGS (rdW W memc)) SHADOW_OFF (aarg regs 1) MD_SIZE ->
  shadow_hull_vis (ard SEGS (rdW W memc)) (aarg regs 1) MD_SIZE ->
  amem_range (aarg regs 1) MD_SIZE ->
  apart_frame regs CHECK_MARKS_AK (aarg regs 0) MK_SIZE ->
  apart_frame regs CHECK_MARKS_AK (aarg regs 1) MD_SIZE ->
  (forall b, aarg regs 0 + MK_SIZE <= b < (aarg regs 0 + MK_SIZE + 7) / 8 * 8 -> ard SEGS (rdW W memc) b <> None) ->
  (forall b, aarg regs 1 + MD_SIZE <= b < (aarg regs 1 + MD_SIZE + 7) / 8 * 8 -> ard SEGS (rdW W memc) b <> None) ->
  forall (ni : nat) i (mem1 : word -> option byte) md1 (regs1 : bvmap 5 word),
  (Z.to_nat (mk_n gbs - i) = ni)%nat -> 0 <= i -> i < mk_n gbs ->
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
     aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) memc a) ->
  (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem1 a) ->
  m_fds md1 = m_fds mdc -> m_fs md1 = m_fs mdc ->
  cm_inv regs regs1 (aarg regs 0) (aarg regs 1) (mk_n gbs) i -> cm_saved W mem1 regs ->
  SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + (AF_check_marks + 0x6c))) mem1 (seg_rom SEGS)) md1)
    (cm_Q G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs mbs
  HGX HJ0 Hret Hgp Htp H16 Hwlo Hwhi HMK HMD HWF HMWF HARE RAg HUg MRg RAm HUm MRm PFg PFm Tg Tm.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
pose proof HJ0 as (HSTK0 & HXO0 & (memS0 & HJi0 & _) & _).
pose proof HJi0 as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HK : CHECK_MARKS_AK = 8224) by reflexivity.
assert (Hceil' : alloc_ceiling <= spZ regs - CHECK_MARKS_AK) by lia.
assert (Hsp46 : 2 ^ 46 <= spZ regs - 8224 /\ spZ regs <= 2 ^ 47) by (unfold alloc_ceiling in Hceil'; lia).
unfold YK0s.ret_ok in Hret.
pose proof HWF as (HWFn & HWFs). pose proof HMWF as (HMWFn & HMWFs).
pose proof HARE as (HAREn & _).
unfold MARKS_MAX in HWFn, HMWFn.
set (n := mk_n gbs) in *. set (g := aarg regs 0) in *. set (mp := aarg regs 1) in *.
assert (Hg : 0 <= g /\ g + MK_SIZE <= 2 ^ 47 - 1).
{ split; [unfold g, aarg, argZ; apply bv_unsigned_in_range|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRg. unfold MK_SIZE in *. lia. }
assert (Hm : 0 <= mp /\ mp + MD_SIZE <= 2 ^ 47 - 1).
{ split; [unfold mp, aarg, argZ; apply bv_unsigned_in_range|].
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in MRm. unfold MD_SIZE in *. lia. }
pose proof (paj_run_x SK B LAWS G HGX XO OUT) as RUN.
pose proof (paj_run_to_x SK B LAWS G HGX XO OUT) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
intros ni; induction ni as [|ni IH];
  intros i mem1 md1 regs1 Hni Hi0 Hilt HJ1 UN HGR Hfd1 Hfs1 HINV HSV; [exfalso; lia|].
(* the two slot strings and their premises *)
set (n2 := cstr (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN)).
set (nm := cstr (slice mbs (MD_MARK + MARK_LEN * i) MARK_LEN)).
assert (Heqs : n2 = nm) by (exact (cm_slots_eq gbs mbs i HARE ltac:(lia))).
assert (Hnulg : (nul_at (slice gbs (MK_NAME + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat)
  by (apply HWFs; lia).
assert (Hnulm : (nul_at (slice mbs (MD_MARK + MARK_LEN * i) MARK_LEN) < Z.to_nat MARK_LEN)%nat)
  by (apply HMWFs; lia).
assert (CSq : acstr_at SEGS (rdW W memc) (g + MK_NAME + MARK_LEN * i) n2)
  by (apply (cm_slot_acstr SEGS _ g gbs MK_NAME i (proj1 HMK)); [unfold MK_NAME; lia | lia
       | rewrite (proj2 HMK); unfold MK_NAME, MARK_LEN, MK_SIZE; lia | exact Hnulg]).
assert (CSy : acstr_at SEGS (rdW W memc) (mp + MD_MARK + MARK_LEN * i) nm)
  by (apply (cm_slot_acstr SEGS _ mp mbs MD_MARK i (proj1 HMD)); [unfold MD_MARK; lia | lia
       | rewrite (proj2 HMD); unfold MD_MARK, MARK_LEN, MD_SIZE; lia | exact Hnulm]).
assert (AFq : cm_argf regs (rdW W memc) (g + MK_NAME + MARK_LEN * i) n2).
{ apply cm_argf_of.
  apply (cm_slot_arg SEGS regs _ g gbs MK_NAME i MK_SIZE (proj1 HMK) (proj2 HMK) MRg RAg HUg PFg Tg);
    [unfold MK_NAME; lia | lia | unfold MK_NAME, MARK_LEN, MK_SIZE; lia | unfold MK_SIZE; lia | exact Hnulg]. }
assert (AFy : cm_argf regs (rdW W memc) (mp + MD_MARK + MARK_LEN * i) nm).
{ apply cm_argf_of.
  apply (cm_slot_arg SEGS regs _ mp mbs MD_MARK i MD_SIZE (proj1 HMD) (proj2 HMD) MRm RAm HUm PFm Tm);
    [unfold MD_MARK; lia | lia | unfold MD_MARK, MARK_LEN, MD_SIZE; lia | unfold MD_SIZE; lia | exact Hnulm]. }
(* the loop head *)
pose proof (cm_seat AF_check_marks G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs regs1 g mp n i
              HJ1 H16 Hwlo Hwhi HINV HSV ltac:(lia) ltac:(lia) ltac:(unfold MARKS_MAX; lia)) as HS.
pose proof (cm_E_img regs regs1 g mp n i) as HEI.
set (E := cm_E regs regs1 g mp n i) in *.
assert (XX33 : ew E 33 = Z_to_bv 64 (g + MK_NAME + MARK_LEN * i)) by exact (cm_E_ext _ _ _ _ _ _ 1%nat ltac:(lia)).
assert (XX34 : ew E 34 = Z_to_bv 64 (mp + MD_MARK + MARK_LEN * i)) by exact (cm_E_ext _ _ _ _ _ _ 2%nat ltac:(lia)).
assert (XX35 : ew E 35 = Z_to_bv 64 (n - i)) by exact (cm_E_ext _ _ _ _ _ _ 3%nat ltac:(lia)).
assert (ER : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> (m < 32)%nat -> ew E m = getr regs r)
  by (intros m r Hmr Hl; apply cm_E_reg; assumption).
assert (EE1 : ew E 1 = getr regs 1) by (apply ER; [reflexivity | lia]).
assert (EE2 : ew E 2 = getr regs 2) by (apply ER; [reflexivity | lia]).
assert (EE3 : ew E 3 = getr regs 3) by (apply ER; [reflexivity | lia]).
assert (EE4 : ew E 4 = getr regs 4) by (apply ER; [reflexivity | lia]).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite EE2; reflexivity).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (rdW W mem1)) by constructor.
(* +0x6c .. +0x74: a0, a1, `jal wrapper_strcmp` *)
paj_run_tok RUN HS HJ1 SHOK Bspan; [cm_awr |].
cm_nokept HFr W UF1. pose proof (cm_grow _ _ _ HG) as GR1. clear HF HFr HG.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msC) => rename msC into msA end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (Hspa : spZ (ms_regs msA) = spZ regs - 32)
  by (unfold spZ at 1; rewrite Q2; rewrite ?ew_ewset_other by lia; rewrite ?Usp; apply unsigned_lit_small; lia).
assert (UNa : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
          aview SEGS (w_H W) (ms_mem msA) a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite (UF1 a Ha ltac:(intros [])); exact (UN a Ha Hw)).
eapply SRr_bind.
{ eapply (cm_call SK B LAWS STRCMP W G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k regs (ms_regs msA) (ms_mem msA)
           (g + MK_NAME + MARK_LEN * i) (mp + MD_MARK + MARK_LEN * i) nm n2 _ HGX HJ1);
  [ exact Hspa | exact H16 | exact Hwlo | exact Hwhi
  | rewrite Q3; rewrite ?ew_ewset_other by lia; rewrite EE3; exact Hgp
  | rewrite Q4; rewrite ?ew_ewset_other by lia; rewrite EE4; exact Htp
  | exact Q1
  | apply ret_ok_codeptr_v; lia
  | rewrite Q10; rewrite ?ew_ewset_other by lia; rewrite XX33; reflexivity
  | rewrite Q11; rewrite ?ew_ewset_other by lia; rewrite XX34; reflexivity
  | apply (cm_cstr_frame_sep W regs memc (ms_mem msA) _ _ CSq);
      [exact (proj2 (proj2 (proj2 (proj2 (proj2 AFq))))) | exact (proj1 (proj2 (proj2 AFq))) | exact UNa]
  | apply (cm_cstr_frame_sep W regs memc (ms_mem msA) _ _ CSy);
      [exact (proj2 (proj2 (proj2 (proj2 (proj2 AFy))))) | exact (proj1 (proj2 (proj2 AFy))) | exact UNa]
  | exact (cm_arg_frame W regs memc (ms_mem msA) _ _ AFq Hceil' UNa)
  | exact (cm_arg_frame W regs memc (ms_mem msA) _ _ AFy Hceil' UNa) ]. }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsm & HP2 & Hiff & Hkeep & Hpres2).
assert (Hz : getr regs2 10 = w64 0) by (apply (proj2 Hiff); exact Heqs).
jafter_call_keep_pi HS 64%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
lazymatch type of HS2 with ?Q -> _ => assert (HKEEP : Q) end.
{ apply Forall_cons; [|apply Forall_nil].
  eapply (region_kept_aview _ (w_H W) (ms_mem msA) mem2 2%nat (spZ regs) (-32) 0 0 0 _);
    [ first [exact Usp | rewrite ?ew_ewset_other by lia; exact Usp]
    | intros a Ha; apply Hkeep; [lia | lia]
    | exact Hpres2 ]. }
specialize (HS2 HKEEP). clear HKEEP.
rewrite <- restrict_mkst_fx in HS2.
lazymatch type of HS2 with st_ok_pi _ _ ?EV _ _ => set (E2 := EV) in * end.
assert (EW2 : forall a, (a < 64)%nat -> ew E2 a = ew E a)
  by (intros a Ha; unfold E2; rewrite ew_havoc_old by lia; rewrite ?ew_ewset_other by lia; reflexivity).
assert (E68 : ew E2 68 = getr regs2 10) by (unfold E2; reflexivity).
assert (HEI2 : img_env VAL A_LIM E2)
  by (unfold E2; apply img_env_havoc; [first [exact HEI | apply img_env_ewset_hi; [exact HEI | cbv; lia]] | cbv; lia]).
assert (SHOK2 : sh_ok SEGS (SOff 32 0) [] E2 (mrestrict (w_H W) mem2)) by constructor.
(* the memory after the call, against the entry's and against the loop head's frame *)
assert (UN2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hw; rewrite (Hkeep a Ha ltac:(lia)); exact (UNa a Ha Hw)).
assert (FR2 : forall a, spZ regs - 32 <= a < spZ regs -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a)
  by (intros a Ha; rewrite (Hkeep a ltac:(lia) ltac:(lia)); exact (UF1 a ltac:(lia) ltac:(intros []))).
(* +0x78 `bnez a0`: the two strings are equal, so a0 = 0 *)
psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
{ exfalso. exact (cm_ne_zero E2 68 _ E68 Hz Hc). }
(* +0x7c .. +0x88: next i, `bnez s2` *)
paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [cm_awr |].
cm_nokept HFr W UF3. pose proof (cm_grow _ _ _ HG) as GR3. clear HF HFr HG.
lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) => rename msF into msC end.
assert (U35 : forall EV, (forall a, (a < 64)%nat -> ew EV a = ew E a) -> U EV (SOff 35 (-1)) = n - i - 1)
  by (intros EV HEV; rewrite U_SOff, HEV by lia; rewrite XX35, unsigned_lit_small by lia;
      apply YP0m.zcanon_small; lia).
psrr_branch_tok RUN BR HS2 SHOK2 Bspan.
- (* BACK: one more mark *)
  lazymatch type of Hc0 with branch_taken BC_NE (sv_denot ?EV _) _ = _ =>
    rewrite branch_ne_U, (U35 EV ltac:(intros a Ha; rewrite ?ew_ewset_other by lia; apply EW2; exact Ha)),
      (U_lit EV 0) in Hc0 by lia end.
  apply negb_true_iff, Z.eqb_neq in Hc0.
  paj_run_to_tok RUNTO HS2 HJ2 SHOK2 Bspan (AF_check_marks + 0x6c); [cm_awr |].
  cm_nokept HFr W UF4. pose proof (cm_grow _ _ _ HG) as GR4. clear HF HFr HG.
  lazymatch type of HS2 with st_ok_pi _ _ ?EV ?ssF (restrict _ ?msF) =>
    rename msF into msB; set (E4 := EV) in HS2; set (ssB := ssF) in HS2 end.
  assert (EW4 : forall a, (a < 64)%nat -> ew E4 a = ew E a)
    by (intros a Ha; unfold E4; rewrite ?ew_ewset_other by lia; apply EW2; exact Ha).
  assert (Y33 : ew E4 33 = Z_to_bv 64 (g + MK_NAME + MARK_LEN * i)) by ((rewrite EW4 by lia); exact XX33).
  assert (Y34 : ew E4 34 = Z_to_bv 64 (mp + MD_MARK + MARK_LEN * i)) by ((rewrite EW4 by lia); exact XX34).
  assert (Y35 : ew E4 35 = Z_to_bv 64 (n - i)) by ((rewrite EW4 by lia); exact XX35).
  assert (Y2 : ew E4 2 = Z_to_bv 64 (spZ regs)) by ((rewrite EW4 by lia); rewrite EE2; symmetry; apply Z_to_bv_bv_unsigned).
  assert (BREG : forall r : bv 5, getr (ms_regs msB) r = sv_denot E4 (sr_get (ss_regs ssB) r))
    by (intros r; exact (st_ok_pi_restrict_reg (w_H W) E4 ssB msB r HS2)).
  assert (HINVB : cm_inv regs (ms_regs msB) g mp n (i + 1)).
  { unfold cm_inv; rewrite !BREG; unfold ssB.
    repeat split;
    lazymatch goal with |- sv_denot _ (sr_get ?LL ?RR) = _ =>
      let v := eval vm_compute in (sr_get LL RR) in change (sr_get LL RR) with v end;
    first
    [ rewrite (cm_soffc E4 2 (-32) (spZ regs) Y2) by lia; reflexivity
    | rewrite cm_soff0; (rewrite EW4 by lia); first [exact EE3 | exact EE4 | apply ER; [reflexivity | lia] ]
    | rewrite (cm_soffc E4 33 16 _ Y33) by (unfold MK_NAME, MARK_LEN, MK_SIZE in *; lia); f_equal; unfold MARK_LEN; lia
    | rewrite (cm_soffc E4 34 16 _ Y34) by (unfold MD_MARK, MARK_LEN, MD_SIZE in *; lia); f_equal; unfold MARK_LEN; lia
    | rewrite (cm_soffc E4 35 (-1) _ Y35) by lia; f_equal; lia
    ]. }
  assert (HSVB : cm_saved W (ms_mem msB) regs).
  { unfold cm_saved in HSV |- *. destruct HSV as (S1 & S8 & S9 & S18).
    repeat split;
    (eapply cm_val_frame; [eassumption | intros x Hx; apply (mbyte_of_aview SEGS);
       rewrite (UF4 x ltac:(lia) ltac:(intros [])), (UF3 x ltac:(lia) ltac:(intros [])); apply FR2; cbn in Hx; lia]). }
  assert (UNB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHECK_MARKS_AK <= a < spZ regs) ->
            aview SEGS (w_H W) (ms_mem msB) a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hw; rewrite (UF4 a Ha ltac:(intros [])), (UF3 a Ha ltac:(intros [])); exact (UN2 a Ha Hw)).
  assert (GRB : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem msB) a)
    by (intros a Ha; apply GR4, GR3, Hpres2, GR1, HGR, Ha).
  pmkst HS2.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?pcl)) _ _) _) _ =>
    replace pcl with (AF_check_marks + 0x6c) by (vm_compute; reflexivity) end.
  apply (IH (i + 1) (ms_mem msB) _ (ms_regs msB));
    [ lia | lia | lia | cm_jour HJ2 | exact UNB | exact GRB
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1
    | exact HINVB | exact HSVB ].
- (* END: the last mark; +0x8c .. +0xa0 restore, pop, ret *)
  paj_run_tok RUN HS2 HJ2 SHOK2 Bspan; [cm_awr |].
  cm_nokept HFr W UF4. pose proof (cm_grow _ _ _ HG) as GR4. clear HF HFr HG.
  lazymatch type of HS2 with st_ok_pi _ _ ?EV _ (restrict _ ?msF) =>
    rename msF into msD;
    assert (HAE4 : env_agree 32 (Ereg regs (cm_extra regs1 g mp n i)) EV)
      by (split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; unfold E2; rewrite ew_havoc_old by lia;
                  rewrite ?ew_ewset_other by lia; unfold E, cm_E; apply Eimg_low; unfold A_TEXT; lia
                 | reflexivity]);
    pose proof (aregs_preserved_of_st_ok SEGS _ EV _ _ regs (cm_extra regs1 g mp n i) HS2 HAE4
                  ltac:(vm_compute; reflexivity)) as HPr
  end.
  prreg HS2 (1%bv : bv 5) P1.
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite P1; rewrite ?ew_ewset_other by lia; unfold E2; rewrite ew_havoc_old by lia;
    rewrite ?ew_ewset_other by lia; rewrite EE1, Hret.
  apply (cm_exit SK B LAWS G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs _ _ _ HJ0).
  + cm_jour HJ2.
  + exact Hwlo.
  + exact Hwhi.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj1 (wvb_fds_fs _ _ _)); exact Hfd1.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)); rewrite (same_but_materialized_wvb _ _ Hsm);
      repeat rewrite (proj2 (wvb_fds_fs _ _ _)); exact Hfs1.
  + exact HPr.
  + intros a Ha Hw. rewrite (UF4 a Ha ltac:(intros [])), (UF3 a Ha ltac:(intros [])). exact (UN2 a Ha Hw).
  + intros a Ha. apply GR4, GR3, Hpres2, GR1, HGR, Ha.
Qed.

Theorem check_marks_aproof : forall rlo rhi, check_marks_acontract SK SEGS rlo rhi B.
Proof.
intros rlo rhi. unfold check_marks_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HA HRd HPre.
destruct HA as (HJ & HGX & HROD & Hret & Hra4 & Hgp & Htp & H16 & Hwlo & Hwhi & Hev & Hside & Hajw & _).
destruct HPre as (gbs & mbs & HMK & HMD & HWF & HMWF & HARE & RAg & HUg & MRg & RAm & HUm & MRm & PFg & PFm & Tg & Tm).
replace (cfg_at SEGS CHECK_MARKS_A regs memc mdc)
  with (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_marks)) memc (seg_rom SEGS)) mdc)
  by (unfold cfg_at, w64, CHECK_MARKS_A, AF_check_marks; rewrite (lv_text LV); reflexivity).
change (SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_check_marks)) memc (seg_rom SEGS)) mdc)
          (cm_Q G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs)).
apply (cm_start G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs mbs HGX HJ Hret H16 Hwlo Hwhi
         HMK HMD HWF HMWF HARE RAg MRg RAm MRm PFg PFm).
intros Hn1 mem1 md1 regs1 HJ1 UN1 GR1 Hfd1 Hfs1 HINV HSV.
exact (cm_loop G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs gbs mbs HGX HJ Hret Hgp Htp H16
         Hwlo Hwhi HMK HMD HWF HMWF HARE RAg HUg MRg RAm HUm MRm PFg PFm Tg Tm
         (Z.to_nat (mk_n gbs - 0)) 0 mem1 md1 regs1 eq_refl ltac:(lia) ltac:(lia) HJ1 UN1 GR1 Hfd1 Hfs1 HINV HSV).
Qed.

End w.

(* LAWS and STRCMP discharged on the image's segments: lib/Reusable/YG0q.v AR_laws_ok and lib/A/Rt/RtStrcmpClosed.v
   link_astrcmp_closed, from the image's asyms record (lib/A/AF0m.v PcapSyms; on the image lib/A/AD2l.v PcapB_syms) *)
Section img. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
Context {PI : PAImg link_listing}.
Theorem check_marks_aproof_img : forall B, PALib B -> LinkVals -> AF0m.PcapSyms B -> pa_segs = AB1v.tfibsegs ->
  forall rlo rhi, check_marks_acontract SK pa_segs rlo rhi B.
Proof.
intros B TL LV TS Hsegs.
assert (LAWS : AR_laws pa_segs B) by (rewrite Hsegs; exact (YG0q.AR_laws_ok AB1v.tfibsegs B)).
apply (check_marks_aproof SK B LAWS TL LV).
rewrite (lv_sigma LV). cbn [link_sigma]. rewrite Hsegs. exact (RtStrcmpClosed.link_astrcmp_closed B TS).
Qed.
End img.

Print Assumptions check_marks_aproof.
Print Assumptions check_marks_aproof_img.
