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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_entry.v, with its module names changed; 1450 of its 1521 lines of code are new or changed and 654 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_kit.v, with its module names changed; 174 of its 249 lines of code are new or changed and 1446 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: the STATEMENT-LEVEL facts of kernel's exit phase (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4). The run itself (+0x2140 -> ret) is kernel_exit.v; this
   file holds what the contract's Post needs of the values the cut carries, with no symbolic run in it:

   - g_nl: `kx_gnl_post` turns the cut invariant `kgnl` (kernel_defs.v) into the eleven g_nl clauses of
     kernel_apost (kernel_c.v).  It is the plain walk's kgnl_post (lib/Prog/kernel.v:37)
     over the image-A field names.  Every field from NK_OPEN (262676) on is read through `kx_slice_skip`, which
     splits the `skipn` of the cut's clause; `Z.to_nat NK_OPEN` is never computed (it is a unary nat: the 31-minute
     trap of link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)), only passed to lia.
   - the byte algebra the transport from the cut's memory to the return memory needs: a value read twice is the
     same value (`kx_val64_unique`), a byte list at an address is unique (`kx_anlk_unique`), bytes move with the
     view (`kx_abytes_moved`), a byte of a value is visible (`kx_view_of_val`), and a visible byte that is not
     read-only is WRITABLE (`kx_writable_of_view`).  The last one is what frame_release_8's contract does not
     give: it keeps presence only above the allocator's ceiling, so the cursor's writability (kernel_apost's
     `awrange m' (aarg regs 0) 16`) has to come from the segments instead -- an absent byte is read from
     `seg_rom`, which reads the same segment `wview` writes, and apre's last conjunct says that segment is not
     read-only.  For g_nl and long_alias the KernImg fields ki_gnl_wseg / ki_la_wseg give it outright
     (`kx_writable_of_wseg`).
   - `kx_akb_out`: a byte of the read set lies in [0, 2 ^ 64) and outside kernel's window, which every transport
     of a read-set byte across the call needs.
   - `kx_aregs`: aregs_preserved from the fifteen callee-saved registers (attr_text.v at_aregs).

   Every lemma of the Section is closed with `Proof using All`, so each takes SK, B and LAWS in that order.
   Proves no function (kind: segment lemma). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK1d PcapImgEnd.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkPi LinkWalkSide LinkWalkShadow BoxBase PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   1. g_nl: the Post of the queue from the cut's kgnl
   ========================================================================== *)

(* A field at or above NK_OPEN is read off the entry's bytes: the cut's clause says the two byte lists agree from
   NK_OPEN on, and a slice there only reads those bytes.  NK_OPEN stays a Z literal throughout. *)
Lemma kx_slice_skip : forall b1 b2 a n,
  skipn (Z.to_nat NK_OPEN) b1 = skipn (Z.to_nat NK_OPEN) b2 -> NK_OPEN <= a ->
  slice b1 a n = slice b2 a n.
Proof.
  intros b1 b2 a n E H. unfold slice.
  replace (Z.to_nat a) with (Z.to_nat (a - NK_OPEN) + Z.to_nat NK_OPEN)%nat by (unfold NK_OPEN in *; lia).
  rewrite <- !skipn_skipn, E. reflexivity.
Qed.

Lemma kx_f32_skip : forall b1 b2 a,
  skipn (Z.to_nat NK_OPEN) b1 = skipn (Z.to_nat NK_OPEN) b2 -> NK_OPEN <= a ->
  fld_u32 b1 a = fld_u32 b2 a.
Proof.
  intros b1 b2 a E H. unfold fld_u32, link_spec.rdn. f_equal. apply kx_slice_skip; assumption.
Qed.

Lemma kx_f64_skip : forall b1 b2 a,
  skipn (Z.to_nat NK_OPEN) b1 = skipn (Z.to_nat NK_OPEN) b2 -> NK_OPEN <= a ->
  fld_u64 b1 a = fld_u64 b2 a.
Proof.
  intros b1 b2 a E H. unfold fld_u64, link_spec.rdn. f_equal. apply kx_slice_skip; assumption.
Qed.

(* nl_errno's six values are int32 (netlink.h's table; link_spec.v nl_errno_tab) *)
Lemma kx_errno_range : forall e, In e nl_errno_tab -> 0 <= e < 2 ^ 31.
Proof.
  intros e H.
  unfold nl_errno_tab, E_NOBUFS, E_INTR, E_AGAIN, E_PERM, E_MFILE, E_CONNREFUSED in H.
  cbn [In] in H. repeat (destruct H as [<- | H]; [lia|]). destruct H.
Qed.

(* THE QUEUE'S POST (the plain walk's kgnl_post at image A's names): from the cut's kgnl and the entry's nlk_wf. *)
Lemma kx_gnl_post : forall kbs0 kbs j, kgnl kbs0 kbs j -> nlk_wf kbs0 -> 0 <= j <= 3 ->
  nlk_wf kbs /\ nk_next kbs = 0 /\ 0 <= nk_n_chunks kbs <= 3
  /\ In (nk_end_errno kbs) nl_errno_tab
  /\ (nk_socket_errno kbs = 0 \/ In (nk_socket_errno kbs) nl_errno_tab)
  /\ (nk_send_errno kbs = 0 \/ In (nk_send_errno kbs) nl_errno_tab)
  /\ nk_open kbs = nk_open kbs0 /\ nk_opened kbs = nk_opened kbs0
  /\ nk_closed kbs = nk_closed kbs0 /\ nk_misuse kbs = nk_misuse kbs0
  /\ nk_n_sent kbs = nk_n_sent kbs0 /\ nk_sent kbs = nk_sent kbs0
  /\ nk_n_if kbs = nk_n_if kbs0.
Proof.
  intros kbs0 kbs j (GL & GS & GJ & GN & GE & GSO & GSE & GC) WF JR.
  assert (EO : nk_open kbs = nk_open kbs0)
    by (unfold nk_open; apply kx_f32_skip; [exact GS | unfold NK_OPEN; lia]).
  assert (EOd : nk_opened kbs = nk_opened kbs0)
    by (unfold nk_opened; apply kx_f32_skip; [exact GS | unfold NK_OPENED, NK_OPEN; lia]).
  assert (EC : nk_closed kbs = nk_closed kbs0)
    by (unfold nk_closed; apply kx_f32_skip; [exact GS | unfold NK_CLOSED, NK_OPEN; lia]).
  assert (EM : nk_misuse kbs = nk_misuse kbs0)
    by (unfold nk_misuse; apply kx_f32_skip; [exact GS | unfold NK_MISUSE, NK_OPEN; lia]).
  assert (ES : nk_n_sent kbs = nk_n_sent kbs0)
    by (unfold nk_n_sent; apply kx_f32_skip; [exact GS | unfold NK_N_SENT, NK_OPEN; lia]).
  assert (EI : nk_n_if kbs = nk_n_if kbs0)
    by (unfold nk_n_if; apply kx_f32_skip; [exact GS | unfold NK_N_IF, NK_OPEN; lia]).
  assert (ESL : forall i, 0 <= i -> fld_u64 kbs (NK_SENT_LEN + 8 * i) = fld_u64 kbs0 (NK_SENT_LEN + 8 * i)).
  { intros i Hi. apply kx_f64_skip; [exact GS | unfold NK_SENT_LEN, NK_OPEN; lia]. }
  assert (ESENT : nk_sent kbs = nk_sent kbs0).
  { unfold nk_sent. rewrite ES. apply map_ext. intros i.
    unfold nk_sent_one. rewrite (ESL (Z.of_nat i) ltac:(lia)).
    apply kx_slice_skip; [exact GS | unfold NK_SENT, NK_OPEN, NL_SENT_LEN; lia]. }
  pose proof WF as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11 & W12 & W13).
  assert (EE : 0 <= nk_end_errno kbs < 2 ^ 31) by (exact (kx_errno_range _ GE)).
  assert (ESO : 0 <= nk_socket_errno kbs < 2 ^ 31)
    by (destruct GSO as [->|GSO]; [lia | exact (kx_errno_range _ GSO)]).
  assert (ESE : 0 <= nk_send_errno kbs < 2 ^ 31)
    by (destruct GSE as [->|GSE]; [lia | exact (kx_errno_range _ GSE)]).
  split.
  - unfold nlk_wf. rewrite EO, EOd, EC, EM, ES, EI, GJ, GN.
    refine (conj _ (conj _ (conj W3 (conj W4 (conj W5 (conj W6 (conj W7 (conj W8 (conj EE (conj ESO (conj ESE
      (conj _ _)))))))))))).
    + unfold NL_CHUNKS. lia.
    + lia.
    + intros i Hi. exact (GC i Hi).
    + intros i Hi. rewrite (ESL i ltac:(lia)). exact (W13 i Hi).
  - split; [exact GN|]. split; [rewrite GJ; lia|].
    split; [exact GE|]. split; [exact GSO|]. split; [exact GSE|].
    exact (conj EO (conj EOd (conj EC (conj EM (conj ES (conj ESENT EI)))))).
Qed.

(* ==========================================================================
   2. aregs_preserved from the fifteen callee-saved registers (attr_text.v at_aregs)
   ========================================================================== *)

Lemma kx_aregs : forall (regs regs' : bvmap 5 word),
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
  getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  aregs_preserved regs regs'.
Proof.
  intros regs regs' Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 r Hr.
  unfold acallee_saved in Hr.
  assert (Hv : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  assert (G : forall (k : Z) (rr : bv 5), r = k -> Z_to_bv 5 k = rr ->
            getr regs' rr = getr regs rr -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros k rr Hrk Hk Hq. subst r. rewrite Hk. exact Hq. }
  repeat match goal with Hq : _ \/ _ |- _ => destruct Hq end;
  first [ exact (G 2 2%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q2)
        | exact (G 3 3%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q3)
        | exact (G 4 4%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q4)
        | exact (G 8 8%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q8)
        | exact (G 9 9%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q9)
        | exact (G 18 18%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q18)
        | exact (G 19 19%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q19)
        | exact (G 20 20%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q20)
        | exact (G 21 21%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q21)
        | exact (G 22 22%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q22)
        | exact (G 23 23%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q23)
        | exact (G 24 24%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q24)
        | exact (G 25 25%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q25)
        | exact (G 26 26%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q26)
        | exact (G 27 27%bv ltac:(assumption) ltac:(vm_compute; reflexivity) Q27) ].
Qed.

(* two byte lists that the same memory holds at the same address are the same list *)
Lemma kx_list_eq_nth : forall (l1 l2 : list byte), (forall i, nth_error l1 i = nth_error l2 i) -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H.
  - reflexivity.
  - pose proof (H 0%nat) as H0. discriminate H0.
  - pose proof (H 0%nat) as H0. discriminate H0.
  - pose proof (H 0%nat) as H0. cbn [nth_error] in H0. injection H0 as ->.
    f_equal. apply IH. intros i. exact (H (S i)).
Qed.

(* ==========================================================================
   3. The byte algebra at the image's segments
   ========================================================================== *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.

(* A byte of a value the memory holds is visible. *)
Lemma kx_view_of_val : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v k,
  val_mem SEGS (mrestrict H m) a n v -> (k < n)%nat -> aview SEGS H m (a + Z.of_nat k) <> None.
Proof using All.
  intros H m a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. discriminate.
Qed.

(* A u64 the memory holds is unique (both readings are the same rdword). *)
Lemma kx_val64_unique : forall (H : word -> bool) (m : word -> option byte) a v v',
  val_mem SEGS (mrestrict H m) a 8 v -> val_mem SEGS (mrestrict H m) a 8 v' ->
  0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof using All.
  intros H m a v v' H1 H2 Hv Hv'.
  pose proof (rdword_of_val_mem SEGS H m a v H1 Hv) as E1.
  pose proof (rdword_of_val_mem SEGS H m a v' H2 Hv') as E2.
  rewrite E1 in E2. injection E2 as E2. exact E2.
Qed.

(* Bytes move with the view. *)
Lemma kx_abytes_moved : forall (H H' : word -> bool) (m m' : word -> option byte) a bs,
  (forall i, (i < length bs)%nat -> aview SEGS H' m' (a + Z.of_nat i) = aview SEGS H m (a + Z.of_nat i)) ->
  abytes SEGS (mrestrict H m) a bs -> abytes SEGS (mrestrict H' m') a bs.
Proof using All.
  intros H H' m m' a bs Hk (B1 & B2 & B3).
  split; [exact B1|]. split; [exact B2|]. intros i Hi.
  rewrite (kn_mbyte_of_aview SEGS H H' m m' (a + Z.of_nat i) (a + Z.of_nat i) (Hk i Hi)). exact (B3 i Hi).
Qed.

(* A byte list the memory holds at an address is unique. *)
Lemma kx_anlk_unique : forall (m : word -> option byte) g bs bs',
  anlk_at SEGS m g bs -> anlk_at SEGS m g bs' -> bs = bs'.
Proof using All.
  intros m g bs bs' (((_ & _ & Hb) & _) & HL) (((_ & _ & Hb') & _) & HL').
  assert (HLn : length bs = length bs') by lia.
  apply kx_list_eq_nth. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi | Hi].
  - rewrite <- (Hb i Hi), <- (Hb' i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None bs' i) ltac:(lia)). reflexivity.
Qed.

(* A VISIBLE byte that is not read-only is WRITABLE, at any memory.  `wview` and `seg_rom` pick the same segment
   (the first one holding the address), so a byte the view reads out of the segments lies in a segment whose
   bytes are there; `~ in_roP` says that segment is writable.  This is the writability frame_release_8's and
   frame_alloc_8's contracts do not keep (they keep presence only above the allocator's ceiling), and apre's last
   conjunct gives `~ in_roP` of every byte kernel writes -- the cursor among them. *)
Lemma kx_writable_of_view : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> aview SEGS H m a <> None -> ~ in_roP SEGS PCAP_RLO PCAP_RHI a ->
  writable_at SEGS (mrestrict H m) a.
Proof using All.
  intros H m a Ha Hv Hro.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; lia).
  unfold writable_at, wview.
  destruct (mrestrict H m (Z_to_bv 64 a)) as [b0|] eqn:Em; [discriminate|].
  unfold aview, mbyte in Hv. rewrite Em in Hv.
  destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b1|] eqn:Er;
    [|cbn [option_map] in Hv; exfalso; exact (Hv eq_refl)].
  clear Hv. unfold seg_rom, memory_read in Er. change (Z.of_N 1) with 1 in Er.
  destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|discriminate Er].
  destruct (seg_readable seg) eqn:Erd; [|discriminate Er].
  (* `destruct ... eqn:Ef` already replaced find_segment in the goal *)
  destruct (find_segment_hit SEGS (bv_unsigned (Z_to_bv 64 a)) 1 seg Ef) as (Hin & Hlo & Hhi).
  rewrite Hu in Hlo, Hhi.
  assert (Hw : seg_writable seg = true).
  { destruct (seg_writable seg) eqn:Ew; [reflexivity|].
    exfalso. apply Hro. left. exists seg. split; [exact Hin | split; [exact Ew | lia]]. }
  rewrite Hw.
  change (N.to_nat 1) with 1%nat in Er. cbn [segment_read_bytes] in Er.
  destruct (segment_byte_at (seg_bytes seg)
              (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base seg)))) as [b2|] eqn:Eb;
    [discriminate | cbn in Er; discriminate Er].
Qed.

(* Every byte of a range of writable segments is writable at any memory (link_ajkit writable_at_of_wseg).
   g_nl and long_alias are such ranges: kernel_defs.v ki_gnl_wseg / ki_la_wseg. *)
Lemma kx_writable_of_wseg : forall (m : word -> option byte) a0 n a,
  0 <= a0 -> a0 + n <= 2 ^ 64 -> wseg_ok SEGS (Z_to_bv 64 a0) (Z.to_nat n) = true ->
  a0 <= a < a0 + n -> writable_at SEGS m a.
Proof using All.
  intros m a0 n a H0 Hn Hw Ha. exact (writable_at_of_wseg SEGS m a0 n H0 Hn Hw a Ha).
Qed.

(* A byte of the read set lies in [0, 2 ^ 64) and OUTSIDE the callee's window: the stack-row clause says so, and
   the three others place the byte in a heap block, in the image or in a side frame, all below the allocator's
   ceiling, which the journal puts below the window. *)
Lemma kx_akb_out : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi a,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  alloc_ceiling <= slo ->
  akb SEGS B lyc Sc slo shi a ->
  0 <= a < 2 ^ 64 /\ ~ (slo <= a < shi).
Proof using All.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi a HJ Hslo Hb.
  destruct (ajournal_gx_row SK SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
    as (R1 & R2 & _ & _).
  pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (H47 : 2 ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
  destruct Hb as [(H1 & H2) | [(b & m & Hin & Hr) | [(Hi & _ & _) | (cid & pos & Hin & Hr)]]].
  - split; [lia | exact H2].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hin) as (_ & H4096 & Hbc & _). lia.
  - pose proof (pa_segs_low a Hi) as Hlow. lia.
  - destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf4 & Hfc & _).
    unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
    pose proof (fs_frame_bytes_nonneg cid) as Hnn. lia.
Qed.

(* a callee-saved register of a preserved pair, at a concrete number *)
Lemma kx_pres_at : forall (regs regs' : bvmap 5 word) (z : Z) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof using All.
  intros regs regs' z r H Hc <-. exact (H z Hc).
Qed.

Hypothesis TB : PcapSyms B.

(* A read-set byte is none of the bytes of a side frame the call does not hold (LinkWalkShadow akb_not_side). *)
Lemma kx_not_side : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos a,
  ajournal_gx SEGS B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  0 <= cid <= 10 -> 0 <= pos < fs_frames cid -> ~ In (cid, pos) (frames Sc) ->
  akb SEGS B lyc Sc slo shi a -> ~ aside_rng lyc cid pos a.
Proof using All.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k slo shi cid pos a HJ Hc Hp Hn Hb.
  exact (akb_not_side SK SEGS B pa_img_range G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
           mdc k slo shi cid pos a HJ Hc Hp Hn Hb).
Qed.

End b.
End a.
