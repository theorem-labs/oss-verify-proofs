(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths, module names and numbers changed; 1307 of its 1499 lines of code are new or changed and 739 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: ported from a Theorem Labs lane's proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v (ge_seat / ge_land) to libreac/fuzz_pcap's pcap_source_next: the region list, the atoms, the spill slots and the frame (class 0, its header and flag word) are this function's; nx_land0 / nx_land, the struct's region, the shadow entry, the first-seat environment and the kept-relation step are new. *)
(* Modified by Theorem Labs, 2026-10: the lib/B (asan-ubsan) twin of lib/A/Prog/PcapSourceNextSeat.v (a Theorem Labs lane): it Require-Exports lib/A/Prog/PcapSourceNextSeatG.v (a Theorem Labs lane's image-free part of the seat, 5dda8acaa6a; never lib/A's PcapSourceNextSeat, whose closure holds lib/A's image: porter) and restates, over lib/B's listing, kit (lib/B/Prog PcapPa, PcapPaLib, PcapFrame, YC1g, YC1h) and phase layer (lib/B/Prog/PcapSourceNextDefs.v), what names lib/B's image: the spill slots of the 0x100 machine frame and their chunks, the region list, the standard symbolic registers (s9 holds the frame's shadow; lib/B's body fixes no s2 / s3), the stack bounds (NX_STK_B, sp1 = sp0 - 256 or - 272), and every lemma of lib/A's PI Section (nx_env .. nx_shent_ts). *)
(* The seat and the landing of a phase of the walk of pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing
   offset AF_pcap_source_next = 0xe30) on the ASan+UBSan build of libreac v1.9.0, stated once for all of its
   phases: lib/A's design (see lib/A/Prog/PcapSourceNextSeat.v's header) at this image.

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; symbols and capstone 5 disassembly from its unstripped twin, same .text);
   the slot table is nxb-handoff.md (sha256 c02dc85fade1; internal record).

   FROM lib/A's SeatG, UNCHANGED (image-free): the atoms NA_SP 2, NA_PS 10, NA_BUF 11, NA_TS 13, NA_SB 32, NA_SP1 60,
   NA_F 516, NA_FL 528, NA_FSH 529, NA_CUR 530; nx_Bx / nx_shx; the chunks of the saved words (lib/B saves ra,
   s0, s1, s2..s11 at the same places, 0x815c0..0x815f0), of the frame's header and of its shadow bytes; the
   regions nx_saved_region, nx_frame_region, nx_shadow_region, nx_ps_region, nx_buf_region, nx_ts_region and
   nx_ps_chunks, nx_SH, nx_facts0; the chunk tests nx_hasb / nx_hasb_sound; the list lemmas; and the lemmas
   over any segs / val: nx_rdword_range, nx_shent_ok, nx_U_Bx, nx_U_shx, nx_img_env_ewset (a Theorem Labs lane 5dda8acaa6a);
   nx_div8_64, nx_bufn_le.

   RESTATED HERE (lib/B's image):
   - THE SPILL SLOTS (lib/B Defs NS_*, offsets from s1): nx_fk_chunk (NS_FK 0x68 = F, written 0x816d0 on both
     readers' paths: the one slot nx_body0 carries) and the twelve slots of nslots (nx_slot_chunks): NS_FK,
     NS_F0 0x40 = F, NS_BUF 0x60 = buf, NS_TS 0x30 = &ts, NS_SB 0x28 = the shadow base (the atom 32 itself, so
     that the reloads 0x819c0, 0x81a10, 0x81a3c, 0x81a88, 0x81b08 give Bx), NS_PS12 0x58 = ps + 12, NS_SH12 0x48 =
     the shadow address of ps + 12 as (x >> 3) + Bx (reloaded 0x817f4), NS_OFF8 0x20 = 3 and NS_OFF12 0x18 = 7
     (ps is 8-aligned), NS_PH4 0x78 / NS_PH8 0x70 / NS_PH12 0x50 = F + 36 / 40 / 44.
   - THE SPILL REGION is [s1, s1 + 152): the slots up to NS_PH4 + 8 = 0x80 and NS_F1 0x90 (`sd s3,0x90(s1)`
     0x81668, never read). s1 = sp0 - 256 or sp0 - 272, so s1 + 152 <= sp0 - 104, the saved words' base.
   - THE SYMBOLIC REGISTERS nx_sr: sp = s1 = the atom 60, s0 = the atom 2, gp, tp, s9 = the atom 529; every
     other x_i is the atom NA_CUR + i. lib/A's s2 = F / s3 = the shadow do not hold here (s3 is F, then ph =
     F + 32 from 0x816f4; s9 = (F >> 3) + Bx from 0x8169c).
   - nx_land_chk / nx_land_chk_split over lib/B's spill chunks, and every lemma of lib/A's PI Section at lib/B
     (nx_env .. nx_seat / nx_land, nx_land0_by / nx_land_by, nx_seat_land_ph, the struct / buffer / timestamp
     regions, nx_keep_out / nx_kept_step). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC88.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
(* The image-free part of the seat (SeatG; its constants are PcapSourceNextSpec's): the names restated
   below are lib/B's. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Export PcapSourceNextSeatG.
(* lib/B's phase layer, LAST (it Require-Exports Spec; lib/B's names shadow the shared ones). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the spill slots (lib/B's), as chunks ---- *)

(* NS_FK (written 0x816d0, before the closed reader's `beqz` 0x816e8: nx_body0) and NS_F0 (0x816f0). *)
Definition nx_fk_chunk : YP09.chunk := YP09.mkChunk NS_FK (CVal 8 (SOff NA_F 0)).
Definition nx_f0_chunk : YP09.chunk := YP09.mkChunk NS_F0 (CVal 8 (SOff NA_F 0)).
(* The twelve slots of the open reader (nslots, in its order): 0x81608 (NS_BUF) and 0x816ec..0x81748. *)
Definition nx_slot_chunks : list YP09.chunk :=
  [ nx_fk_chunk; nx_f0_chunk;
    YP09.mkChunk NS_BUF (CVal 8 (SOff NA_BUF 0));
    YP09.mkChunk NS_TS (CVal 8 (SOff NA_TS 0));
    YP09.mkChunk NS_SB (CVal 8 nx_Bx);
    YP09.mkChunk NS_PS12 (CVal 8 (SOff NA_PS PS_OL_OFF));
    YP09.mkChunk NS_SH12 (CVal 8 (nx_shx (SOff NA_PS PS_OL_OFF)));
    YP09.mkChunk NS_OFF8 (CVal 8 (SLit 3));
    YP09.mkChunk NS_OFF12 (CVal 8 (SLit 7));
    YP09.mkChunk NS_PH4 (CVal 8 (SOff NA_F 36));
    YP09.mkChunk NS_PH8 (CVal 8 (SOff NA_F 40));
    YP09.mkChunk NS_PH12 (CVal 8 (SOff NA_F 44)) ].
(* sf = true: every slot (nx_body); sf = false: NS_FK only (nx_body0, both readers). *)
Definition nx_spill_chunks (sf : bool) : list YP09.chunk :=
  if sf then nx_slot_chunks else [nx_fk_chunk].

(* ---- the regions (lib/B's spill region and region list) ---- *)

(* 1: the spill slots above the realigned stack pointer, [s1, s1 + 152), writable (up to NS_F1 0x90 + 8). *)
Definition NX_SPILL : Z := 152.
Definition nx_spill_region (sf : bool) : YP09.region :=
  YP09.mkRegion (Some NA_SP1) 0 NX_SPILL 0 NX_SPILL (nx_spill_chunks sf).
(* 0 .. 5: the saved words, the spill slots, the class-0 frame, its 8 shadow bytes, the GOT word of the shadow
   base (object 1, 0x996f8) and the shadow-base cell (object 15, 0xa17b8). *)
Definition nx_regions0 (sf : bool) (sh : list Z) (swlo swhi fw : Z) (fcs : list YP09.chunk) : YP09.smem :=
  [ nx_saved_region; nx_spill_region sf; nx_frame_region fw fcs; nx_shadow_region swlo swhi sh;
    got_regionP; bcell_regionP NA_SB ].
Definition nx_regions (sf : bool) (sh : list Z) (swlo swhi fw : Z) (fcs : list YP09.chunk)
  (extra : YP09.smem) : YP09.smem := nx_regions0 sf sh swlo swhi fw fcs ++ extra.
Definition nx_ss (pc : Z) (sr : list sv) (sf : bool) (sh : list Z) (swlo swhi fw : Z)
  (fcs : list YP09.chunk) (extra : YP09.smem) (G : facts) : sstate :=
  mkSS pc sr (nx_regions sf sh swlo swhi fw fcs extra) None G.

(* The symbolic registers of a phase's first seat: the fixed atoms for sp, gp, tp, s0, s1, s9 (x25, the
   frame's shadow), and the atom NA_CUR + i for every other x_i (nx_mkE holds the current value there). *)
Definition nx_sr : list sv :=
  [ SLit 0; SOff 531 0; SOff NA_SP1 0; SOff 3 0; SOff 4 0; SOff 535 0; SOff 536 0; SOff 537 0;
    SOff NA_SP 0; SOff NA_SP1 0; SOff 540 0; SOff 541 0; SOff 542 0; SOff 543 0; SOff 544 0;
    SOff 545 0; SOff 546 0; SOff 547 0; SOff 548 0; SOff 549 0; SOff 550 0; SOff 551 0;
    SOff 552 0; SOff 553 0; SOff 554 0; SOff NA_FSH 0; SOff 556 0; SOff 557 0; SOff 558 0;
    SOff 559 0; SOff 560 0; SOff 561 0 ].

Lemma nx_fk_in : forall sf, In nx_fk_chunk (nx_spill_chunks sf).
Proof. intros [|]; cbn [nx_spill_chunks nx_slot_chunks In]; tauto. Qed.
Lemma nx_f0_in : In nx_f0_chunk (nx_spill_chunks true).
Proof. cbn [nx_spill_chunks nx_slot_chunks In]; tauto. Qed.

(* The chunks nx_land0_by needs (lib/B's spill slots; nx_hasb is lib/A's, image-free): the saved words, the spill slots (sf), the header and the flag
   word, and one shadow chunk per byte with the literals vs. *)
Definition nx_land_chk (sf : bool) (vs : list Z) (rs : YP09.smem) : bool :=
  forallb (nx_hasb rs NA_SP) nx_saved_chunks &&
  forallb (nx_hasb rs NA_SP1) (nx_spill_chunks sf) &&
  forallb (nx_hasb rs NA_F) (nx_hdr_chunks ++ [YP09.mkChunk (NX_FRAME - 8) (CVal 8 (SOff NA_FL 0))]) &&
  forallb (nx_hasb rs NA_FSH) (nx_sh_chunks vs).
Lemma nx_land_chk_split : forall sf vs rs, nx_land_chk sf vs rs = true ->
  (forall c, In c nx_saved_chunks -> nx_hasb rs NA_SP c = true) /\
  (forall c, In c (nx_spill_chunks sf) -> nx_hasb rs NA_SP1 c = true) /\
  (forall c, In c (nx_hdr_chunks ++ [YP09.mkChunk (NX_FRAME - 8) (CVal 8 (SOff NA_FL 0))]) -> nx_hasb rs NA_F c = true) /\
  (forall c, In c (nx_sh_chunks vs) -> nx_hasb rs NA_FSH c = true).
Proof.
  intros sf vs rs H. unfold nx_land_chk in H.
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite forallb_forall in H1, H2, H3, H4. auto.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* ---- the environment a phase runs in ---- *)
(* The entry registers at 0..31, and the six atoms of the fixed part. *)
Definition nx_env (cx : ncx) (fp : Z) (E : env) : Prop :=
  (forall n, (n < 32)%nat -> ew E n = ew (n_E0 cx) n) /\
  ew E NA_SB = w64 SHADOW_OFF /\
  ew E NA_SP1 = w64 (n_sp1 cx) /\
  ew E NA_F = w64 (nF cx fp) /\
  ew E NA_FL = w64 (nFL cx fp) /\
  ew E NA_FSH = w64 (nSH cx fp).

(* The environment of a phase's first seat: nx_env's atoms, the registers `regs` at NA_CUR + i,
   the image. A phase sets its own atoms on top with ewset (nx_env_ewset, nx_img_env_ewset). *)
Definition nx_Ecur (cx : ncx) (regs : bvmap 5 word) : env :=
  mkEnv (fun i => if ((NA_CUR <=? i) && (i <? NA_CUR + 32))%nat
                  then getr regs (Z_to_bv 5 (Z.of_nat (i - NA_CUR))) else ew (n_E0 cx) i)
        (ed (n_E0 cx)).
Definition nx_mkE (cx : ncx) (fp : Z) (regs : bvmap 5 word) : env :=
  Eimg (ewset (ewset (ewset (ewset (ewset (nx_Ecur cx regs) NA_SB (w64 SHADOW_OFF))
    NA_SP1 (w64 (n_sp1 cx))) NA_F (w64 (nF cx fp))) NA_FL (w64 (nFL cx fp))) NA_FSH (w64 (nSH cx fp))).

Lemma nx_mkE_env : forall cx fp regs, nx_env cx fp (nx_mkE cx fp regs).
Proof.
  intros cx fp regs. unfold nx_env, nx_mkE.
  repeat split; [intros n Hn|..];
    rewrite Eimg_low by (unfold A_TEXT, NA_SB, NA_SP1, NA_F, NA_FL, NA_FSH; lia);
    repeat (rewrite ew_ewset_same || (rewrite ew_ewset_other by (unfold NA_SB, NA_SP1, NA_F, NA_FL, NA_FSH; lia)));
    try reflexivity.
  cbn [nx_Ecur ew]. replace ((NA_CUR <=? n) && (n <? NA_CUR + 32))%nat with false; [reflexivity|].
  symmetry. apply andb_false_intro1. apply Nat.leb_gt. unfold NA_CUR. lia.
Qed.

Lemma nx_mkE_img : forall cx fp regs, img_env VAL A_LIM (nx_mkE cx fp regs).
Proof. intros cx fp regs. apply Eimg_env. Qed.

Lemma nx_Eimg_hi : forall E n, (A_LIM <= n)%nat -> ew (Eimg E) n = ew E n.
Proof.
  intros E n Hn. cbn [Eimg ew]. replace ((A_TEXT <=? n) && (n <? A_LIM))%nat with false; [reflexivity|].
  symmetry. apply andb_false_intro2. apply Nat.ltb_ge. exact Hn.
Qed.

Lemma nx_mkE_cur : forall cx fp regs i, (i < 32)%nat ->
  ew (nx_mkE cx fp regs) (NA_CUR + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
Proof.
  intros cx fp regs i Hi. unfold nx_mkE.
  rewrite nx_Eimg_hi by (unfold A_LIM, NA_CUR; lia).
  rewrite !ew_ewset_other by (unfold NA_SB, NA_SP1, NA_F, NA_FL, NA_FSH, NA_CUR; lia).
  cbn [nx_Ecur ew]. replace ((NA_CUR <=? NA_CUR + i) && (NA_CUR + i <? NA_CUR + 32))%nat with true.
  - f_equal. f_equal. f_equal. lia.
  - symmetry. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia.
Qed.

Lemma nx_env_ewset : forall cx fp E n w, nx_env cx fp E ->
  (32 < n)%nat -> n <> NA_SP1 -> n <> NA_F -> n <> NA_FL -> n <> NA_FSH ->
  nx_env cx fp (ewset E n w).
Proof.
  intros cx fp E n w (AG & H32 & H60 & HF & HFL & HFSH) Hn H1 H2 H3 H4.
  unfold nx_env. rewrite !ew_ewset_other by (unfold NA_SB in *; lia || congruence).
  repeat split; try assumption. intros m Hm. rewrite ew_ewset_other by lia. exact (AG m Hm).
Qed.

(* The atoms of the fixed part survive the engine's fresh atoms (extK at K >= 530) and the havoc of
   a call's clobbered registers at k when [k, k + n) misses 0..32 and 60. *)
Lemma nx_env_extK : forall cx fp E K ws, nx_env cx fp E -> (530 <= K)%nat -> nx_env cx fp (extK E K ws).
Proof.
  intros cx fp E K ws HE HK. revert E K HE HK. induction ws as [|w ws IH]; intros E K HE HK;
    cbn [extK]; [exact HE|].
  apply IH; [|lia]. apply nx_env_ewset; [exact HE | unfold NA_SP1, NA_F, NA_FL, NA_FSH; lia ..].
Qed.

Lemma nx_env_havoc : forall cx fp E k ws, nx_env cx fp E ->
  (33 <= k)%nat -> (k + length ws <= 60 \/ 61 <= k)%nat -> (k + length ws <= A_TEXT)%nat ->
  nx_env cx fp (havoc E k ws).
Proof.
  intros cx fp E k ws (AG & H32 & H60 & HF & HFL & HFSH) Hk1 Hk2 Hk3. unfold nx_env.
  assert (Hlo : forall n, (n < k)%nat -> ew (havoc E k ws) n = ew E n)
    by (intros n Hn; apply ew_havoc_old; exact Hn).
  assert (Hhi : forall n, (k + length ws <= n)%nat -> ew (havoc E k ws) n = ew E n)
    by (intros n Hn; apply ew_havoc_above; exact Hn).
  unfold A_TEXT in Hk3.
  split; [intros n Hn; rewrite Hlo by lia; exact (AG n Hn)|].
  split; [rewrite Hlo by (unfold NA_SB; lia); exact H32|].
  split; [destruct Hk2 as [Hk2|Hk2]; [rewrite Hhi by (unfold NA_SP1; lia) | rewrite Hlo by (unfold NA_SP1; lia)]; exact H60|].
  split; [rewrite Hhi by (unfold NA_F; lia); exact HF|].
  split; [rewrite Hhi by (unfold NA_FL; lia); exact HFL|].
  rewrite Hhi by (unfold NA_FSH; lia); exact HFSH.
Qed.

(* nx_rdword_range, nx_shent_ok, nx_img_env_ewset, nx_U_Bx, nx_U_shx: lib/A's (over any segs / val). *)

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.

(* The registers a landing needs, as the values the symbolic registers denote (nx_sr_ok_std gives
   it for the usual file: sp = s1 = the atom 60, s0 = the atom 2, gp, tp, s9 = the atom 529; lib/B's
   body fixes no other register: s3 is F (0x81644) then ph = F + 32 (0x816f4), s2 is per record). *)
Definition nx_sr_ok (cx : ncx) (fp : Z) (E : env) (sr : list sv) : Prop :=
  sv_denot E (sr_get sr 2) = w64 (n_sp1 cx) /\
  sv_denot E (sr_get sr 8) = w64 (spZ (n_regs cx)) /\
  sv_denot E (sr_get sr 9) = w64 (n_sp1 cx) /\
  sv_denot E (sr_get sr 3) = getr (n_regs cx) 3 /\
  sv_denot E (sr_get sr 4) = getr (n_regs cx) 4 /\
  sv_denot E (sr_get sr 25) = w64 (nSH cx fp).

Section d.
Variable cx : ncx.
Variable fp : Z.
Variable k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Hypothesis HB : nx_base SK B KS cx.
Hypothesis HJ : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx)
  (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HFR : frames S3 = (NX_CID, fp) :: frames (n_Sc cx).
#[local] Notation M3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* The facts of nx_base this file uses, by name (robust to the order of nx_base's conjuncts). *)
Lemma nxb_J : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx)
  (n_md0 cx) (n_own cx) (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) (n_k cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.
Lemma nxb_E0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (n_E0 cx) n = getr (n_regs cx) r.
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.
Lemma nxb_E0sp : bv_unsigned (ew (n_E0 cx) 2) = spZ (n_regs cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.
Lemma nxb_sp : spZ (n_regs cx) mod 16 = 0 /\ n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK_B /\
  spZ (n_regs cx) <= n_sp0 cx.
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. auto. Qed.
Lemma nxb_r10 : getr (n_regs cx) 10 = w64 (n_ps cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.
Lemma nxb_r13 : getr (n_regs cx) 13 = w64 (n_ts cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption. Qed.
Lemma nxb_ps : n_ps cx mod 8 = 0 /\ 4096 <= n_ps cx /\ n_ps cx + PS_LEN <= 2 ^ 47 /\
  amem_range (n_ps cx) PS_LEN.
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. auto. Qed.
Lemma nxb_psfr : In (n_cid cx, n_pos cx) (n_own cx) /\ frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) <= n_ps cx /\
  n_ps cx + PS_LEN <= frame_addr (n_lyc cx) (n_cid cx) (n_pos cx) + fs_frame_bytes (n_cid cx).
Proof. pose proof HB as H. unfold nx_base in H. decompose [and] H. auto. Qed.

(* ---- the geometry ---- *)

Lemma nx_fin : In (NX_CID, fp) (frames S3).
Proof. rewrite HFR. left. reflexivity. Qed.

Lemma nx_frame_addr_eq : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p.
Proof.
  intros c p. pose proof HJ as (_ & Hly3 & _). pose proof nxb_J as (_ & Hlyc & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  unfold frame_addr. rewrite EF3, EFc. reflexivity.
Qed.

Lemma nx_flag_addr_eq : flag_addr ly3 NX_CID fp = nFL cx fp.
Proof.
  pose proof HJ as (_ & Hly3 & _). pose proof nxb_J as (_ & Hlyc & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  unfold nFL, flag_addr. rewrite EF3, EFc. reflexivity.
Qed.

Lemma nx_frame_bytes : fs_frame_bytes NX_CID = 64.
Proof. vm_compute. reflexivity. Qed.

Lemma nx_sp_facts :
  spZ (n_regs cx) mod 16 = 0 /\
  alloc_ceiling + 8464 <= spZ (n_regs cx) /\
  spZ (n_regs cx) <= 2 ^ 47 /\
  spZ (n_regs cx) - 272 <= n_sp1 cx <= spZ (n_regs cx) - 256 /\
  n_sp1 cx mod 32 = 0.
Proof.
  pose proof nxb_sp as (Hal & Hlo & Hhi).
  pose proof nxb_J as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  destruct Hstk as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (Hac & _).
  destruct (NX_STK_B_frame (spZ (n_regs cx)) Hal) as ((H1 & H2) & H3).
  unfold n_sp1. unfold NX_MFRAME in H2. unfold NX_STK_B, AFREAD_STK in Hlo.
  split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [lia | exact H3].
Qed.

Lemma nx_F_facts :
  4096 <= nF cx fp /\ nF cx fp + 64 <= alloc_ceiling /\ in_app (nF cx fp) 64 /\
  (nF cx fp + 64 <= 0x10000 \/ pcap_img_end <= nF cx fp) /\ nF cx fp mod 64 = 0 /\
  nSH cx fp = SHADOW_OFF + nF cx fp / 8.
Proof.
  pose proof HJ as (HAR3 & _).
  pose proof (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (HF0 & HFc & HFia).
  pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR3 nx_fin) as HFo.
  pose proof (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR3 nx_fin) as (H64 & _).
  unfold nF. rewrite nx_frame_addr_eq, nx_frame_bytes in *.
  unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFo. unfold pcap_img_end, YImgTop.IMG_TOP.
  split; [exact HF0|]. split; [exact HFc|]. split; [exact HFia|]. split; [exact HFo|].
  split; [exact H64|]. reflexivity.
Qed.

Lemma nx_SH_range : SHADOW_OFF + 512 <= nSH cx fp /\ nSH cx fp + 8 <= SHADOW_OFF + 2 ^ 44 /\
  nSH cx fp mod 8 = 0.
Proof.
  pose proof nx_F_facts as (HF0 & HFc & _ & _ & H64 & HSHeq).
  pose proof asan_consts as (Hac & _).
  assert (Hd0 : 512 <= nF cx fp / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hd1 : nF cx fp / 8 + 8 <= 2 ^ 44)
    by (assert (nF cx fp / 8 <= 0xFFFFFF00000) by (apply Z.div_le_upper_bound; lia); lia).
  pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)) as D. rewrite H64, Z.add_0_r in D.
  assert (E8 : nF cx fp / 8 = 8 * (nF cx fp / 64))
    by (rewrite D at 1; replace (64 * (nF cx fp / 64)) with (8 * (nF cx fp / 64) * 8) by lia;
        rewrite Z.div_mul by lia; reflexivity).
  rewrite HSHeq. split; [lia|]. split; [lia|].
  rewrite E8. unfold SHADOW_OFF. rewrite Z.add_mod, Z.mul_comm, Z_mod_mult by lia. reflexivity.
Qed.

(* A byte range inside one of the caller's frames (`own`) is apart from this call's frame, off the
   image, in the application's memory and under the allocator's ceiling. *)
Lemma nx_own_off : forall cid pos lo n, In (cid, pos) (n_own cx) ->
  frame_addr (n_lyc cx) cid pos <= lo -> lo + n <= frame_addr (n_lyc cx) cid pos + fs_frame_bytes cid ->
  0 <= n ->
  (lo + n <= nF cx fp \/ nF cx fp + 64 <= lo) /\ 4096 <= lo /\ lo + n <= alloc_ceiling /\
  in_app lo n /\ (lo + n <= 0x10000 \/ pcap_img_end <= lo).
Proof.
  intros cid pos lo n Hin Hlo Hhi Hn.
  pose proof nxb_J as (HARc & _ & _ & _ & _ & Hfrc & _).
  pose proof HJ as (HAR3 & _).
  assert (Hinc : In (cid, pos) (frames (n_Sc cx))) by (rewrite Hfrc; apply in_or_app; left; exact Hin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hinc) as (Hf0 & Hfc & Hfia).
  pose proof (frm_off_imgP B _ _ _ _ _ cid pos HARc Hinc) as Hfo. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfo.
  destruct (in_split _ _ Hin) as (l1 & l2 & El).
  assert (Heq : frames S3 = [] ++ (NX_CID, fp) :: l1 ++ (cid, pos) :: (l2 ++ frames (n_S cx))).
  { rewrite HFR, Hfrc, El, <- app_assoc. reflexivity. }
  pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (NX_CID, fp) (cid, pos) [] l1 (l2 ++ frames (n_S cx))
    HAR3 Heq) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !nx_frame_addr_eq, nx_frame_bytes in Hd.
  unfold nF. pose proof (fs_frame_bytes_nonneg cid).
  split; [lia|]. split; [lia|]. split; [lia|]. split; [apply (in_app_sub _ _ _ _ Hfia); lia |].
  unfold pcap_img_end, YImgTop.IMG_TOP. lia.
Qed.

Lemma nx_env_base : forall E n (r : bv 5), nx_env cx fp E -> Z.of_nat n = bv_unsigned r ->
  ew E n = getr (n_regs cx) r.
Proof.
  intros E n r (AG & _) Hn. assert (Hlt : (n < 32)%nat) by (pose proof (bv_unsigned_in_range 5 r) as Hr;
    change (bv_modulus 5) with 32 in Hr; lia).
  rewrite (AG n Hlt). exact (nxb_E0 n r Hn).
Qed.

Lemma nx_base_sp : forall E, nx_env cx fp E -> YP09.base_val E (Some NA_SP) = spZ (n_regs cx).
Proof.
  intros E (AG & _). cbn [YP09.base_val]. rewrite (AG NA_SP ltac:(unfold NA_SP; lia)). exact nxb_E0sp.
Qed.

Lemma nx_ps_atom : forall E, nx_env cx fp E -> ew E NA_PS = w64 (n_ps cx).
Proof. intros E HE. rewrite (nx_env_base E NA_PS (10%bv : bv 5) HE eq_refl). exact nxb_r10. Qed.

Lemma nx_ts_atom : forall E, nx_env cx fp E -> ew E NA_TS = w64 (n_ts cx).
Proof. intros E HE. rewrite (nx_env_base E NA_TS (13%bv : bv 5) HE eq_refl). exact nxb_r13. Qed.

Lemma nx_buf_atom : forall E, nx_env cx fp E -> ew E NA_BUF = w64 (n_buf cx).
Proof.
  intros E HE. rewrite (nx_env_base E NA_BUF (11%bv : bv 5) HE eq_refl).
  pose proof HB as H. unfold nx_base in H. decompose [and] H. assumption.
Qed.

Lemma nx_ps_base : forall E, nx_env cx fp E -> YP09.base_val E (Some NA_PS) = n_ps cx.
Proof.
  intros E HE. pose proof nxb_ps as (_ & H4 & H47 & _). cbn [YP09.base_val].
  rewrite (nx_ps_atom E HE). apply unsigned_lit_small. unfold PS_LEN in *. lia.
Qed.

(* ---- the regions of the fixed part ---- *)

Lemma nx_region_saved : forall E, nx_env cx fp E -> nsaved cx W3 ms3 ->
  YP09.region_ok SEGS E M3 nx_saved_region.
Proof.
  intros E HE Hsv. pose proof (nx_base_sp E HE) as Ub.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & _).
  pose proof asan_consts as (Hac & _).
  assert (HSV : forall (n : nat) (r : bv 5) off,
    Z.of_nat n = bv_unsigned r ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) + off) =
      Some (bv_unsigned (getr (n_regs cx) r)) ->
    YP09.chunk_ok SEGS E M3 (spZ (n_regs cx)) (YP09.mkChunk off (CVal 8 (SOff n 0)))).
  { intros n r off Hn Hrd.
    apply (chunk_ok_val SEGS E M3 (spZ (n_regs cx)) off 8%N (SOff n 0)
             (bv_unsigned (getr (n_regs cx) r))).
    - rewrite nx_sv_SOff0, (nx_env_base E n r HE Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hrd. }
  destruct Hsv as (Hra & Hsj).
  unfold YP09.region_ok, nx_saved_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [unfold NX_STK_B, AFREAD_STK in *; lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold nx_saved_chunks.
  apply Forall_cons;
    [apply (HSV 1%nat (Z_to_bv 5 1) (-8)); [vm_compute; reflexivity |
      replace (spZ (n_regs cx) + -8) with (spZ (n_regs cx) - 8) by lia; exact Hra] | ].
  Local Ltac nx_sj HSV Hsj j n o :=
    apply Forall_cons;
    [apply (HSV n (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) o);
      [vm_compute; reflexivity |
       replace (spZ (n_regs cx) + o) with (spZ (n_regs cx) - 16 - 8 * j) by lia;
       exact (Hsj j ltac:(lia))] | ].
  nx_sj HSV Hsj 0 8%nat (-16). nx_sj HSV Hsj 1 9%nat (-24). nx_sj HSV Hsj 2 18%nat (-32).
  nx_sj HSV Hsj 3 19%nat (-40). nx_sj HSV Hsj 4 20%nat (-48). nx_sj HSV Hsj 5 21%nat (-56).
  nx_sj HSV Hsj 6 22%nat (-64). nx_sj HSV Hsj 7 23%nat (-72). nx_sj HSV Hsj 8 24%nat (-80).
  nx_sj HSV Hsj 9 25%nat (-88). nx_sj HSV Hsj 10 26%nat (-96). nx_sj HSV Hsj 11 27%nat (-104).
  apply Forall_nil.
Qed.

Lemma nx_slot_chunk_ok : forall E off e v,
  nslot cx W3 ms3 off v -> sv_denot E e = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E M3 (n_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
  intros E off e v Hv He.
  apply (chunk_ok_val SEGS E M3 (n_sp1 cx) off 8%N e v He).
  - cbn [Z.of_N]. change (8 * 8) with 64. exact (nx_rdword_range _ _ _ _ Hv).
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hv.
Qed.

Lemma nx_region_spill : forall E sf, nx_env cx fp E ->
  nslot cx W3 ms3 NS_FK (nF cx fp) -> (sf = true -> nslots cx fp W3 ms3) ->
  YP09.region_ok SEGS E M3 (nx_spill_region sf).
Proof.
  intros E sf HE HFK Hsl.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nxb_sp as (_ & Hwin & Htop).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  pose proof nx_F_facts as (HF0 & HFc & _).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  pose proof (nx_ps_atom E HE) as HPS. pose proof (nx_ts_atom E HE) as HTS.
  pose proof (nx_buf_atom E HE) as HBUF.
  assert (Ub : YP09.base_val E (Some NA_SP1) = n_sp1 cx).
  { cbn [YP09.base_val]. rewrite Hsp1E. apply unsigned_lit_small. lia. }
  assert (Hpsr : 0 <= n_ps cx < 2 ^ 64) by (unfold PS_LEN in *; lia).
  assert (CFK : YP09.chunk_ok SEGS E M3 (n_sp1 cx) nx_fk_chunk).
  { apply (nx_slot_chunk_ok E _ _ _ HFK). rewrite nx_sv_SOff0, HFE. reflexivity. }
  assert (PH : forall c, sv_denot E (SOff NA_F c) = Z_to_bv 64 (nF cx fp + c)).
  { intros c. cbn [sv_denot]. rewrite HFE, unsigned_lit_small by lia. reflexivity. }
  unfold YP09.region_ok, nx_spill_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. unfold NX_SPILL. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply HJpres. unfold NX_STK_B, AFREAD_STK in *. lia. }
  destruct sf; cbn [nx_spill_chunks]; [|apply Forall_cons; [exact CFK | apply Forall_nil]].
  destruct (Hsl eq_refl) as (S_FK & S_F0 & S_BUF & S_TS & S_SB & S_PS12 & S_SH12 & S_OFF8 & S_OFF12 &
    S_PH4 & S_PH8 & S_PH12).
  unfold nx_slot_chunks.
  apply Forall_cons; [exact CFK|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_F0); rewrite nx_sv_SOff0, HFE; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_BUF); rewrite nx_sv_SOff0, HBUF; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_TS); rewrite nx_sv_SOff0, HTS; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_SB); unfold nx_Bx; rewrite nx_sv_SOff0, Hsb; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_PS12); cbn [sv_denot]; rewrite HPS;
    rewrite unsigned_lit_small by exact Hpsr; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_SH12);
    apply (nx_U_shx E NA_PS (n_ps cx) PS_OL_OFF Hsb HPS Hpsr); unfold PS_OL_OFF, PS_LEN in *; lia|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_OFF8); unfold PS_SW_OFF; cbn [sv_denot];
    f_equal; rewrite Z.add_mod, Hps8 by lia; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_OFF12); unfold PS_OL_OFF; cbn [sv_denot];
    f_equal; rewrite Z.add_mod, Hps8 by lia; reflexivity|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_PH4); rewrite PH; unfold NO_PH; f_equal; lia|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_PH8); rewrite PH; unfold NO_PH; f_equal; lia|].
  apply Forall_cons; [apply (nx_slot_chunk_ok E _ _ _ S_PH12); rewrite PH; unfold NO_PH; f_equal; lia|].
  apply Forall_nil.
Qed.

Lemma nx_region_frame : forall E fw fcs, nx_env cx fp E -> img_env VAL A_LIM E ->
  nheader cx fp W3 ms3 -> nflagw cx fp W3 ms3 ->
  0 <= fw <= NX_FRAME ->
  Forall (YP09.chunk_ok SEGS E M3 (nF cx fp)) fcs ->
  YP09.region_ok SEGS E M3 (nx_frame_region fw fcs).
Proof.
  intros E fw fcs HE HEI (Hm & H13 & H14) Hfl Hfw Hcs. unfold nflagw in Hfl.
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & HFpres & _).
  rewrite nx_frame_addr_eq, nx_frame_bytes in HFpres. fold (nF cx fp) in HFpres.
  destruct (al_flag _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & Hfia & Hflt).
  rewrite nx_flag_addr_eq in Hfia, Hflt.
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (Ub : YP09.base_val E (Some NA_F) = nF cx fp).
  { cbn [YP09.base_val]. rewrite HFE. apply unsigned_lit_small. lia. }
  assert (HflZ : 0 <= nFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  assert (CK : forall off (e : sv) v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + off) = Some v ->
    YP09.chunk_ok SEGS E M3 (nF cx fp) (YP09.mkChunk off (CVal 8 e))).
  { intros off e v He Hv Hr. apply (chunk_ok_val SEGS E M3 (nF cx fp) off 8%N e v He).
    - cbn [Z.of_N]. change (8 * 8) with 64. exact Hv.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Hr. }
  unfold YP09.region_ok, nx_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. unfold NX_FRAME in *. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (nF cx fp + o) ltac:(lia))). }
  apply Forall_app. split.
  { unfold nx_hdr_chunks. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    - apply (CK 0 (SLit NX_MAGIC) NX_MAGIC eq_refl); [unfold NX_MAGIC; lia | rewrite Z.add_0_r; exact Hm].
    - apply (CK 8 (SOff (A_OBJ 13) 0) (VAL (A_OBJ 13))).
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 13) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 13)). lia.
      + exact H13.
    - apply (CK 16 (SOff (A_OBJ 14) 0) (VAL (A_OBJ 14))).
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 14) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 14)). lia.
      + exact H14. }
  apply Forall_app. split; [exact Hcs|]. apply Forall_cons; [|apply Forall_nil].
  apply (CK (64 - 8) (SOff NA_FL 0) (nFL cx fp)); [rewrite nx_sv_SOff0, HFLE; reflexivity | exact HflZ |].
  replace (nF cx fp + (64 - 8)) with (nF cx fp + NX_FLAGPTR) by (unfold NX_FLAGPTR; lia). exact Hfl.
Qed.

Lemma nx_sh_chunks_from_ok : forall (E : env) sh i,
  (forall j, (j < length sh)%nat ->
     aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + (i + Z.of_nat j)) = Some (nth j sh 0)) ->
  Forall (YP09.chunk_ok SEGS E M3 (nSH cx fp)) (nx_sh_chunks_from i sh).
Proof.
  intros E sh. induction sh as [|v t IH]; intros i H; cbn [nx_sh_chunks_from]; [constructor|].
  constructor.
  - pose proof (H 0%nat ltac:(cbn [length]; lia)) as H0. cbn [nth] in H0.
    rewrite Z.add_0_r in H0.
    destruct (val_mem1_of_aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + i) v H0) as [Hm Hb].
    apply (chunk_ok_val SEGS E M3 (nSH cx fp) i 1%N (SLit v) v).
    + reflexivity.
    + cbn [Z.of_N]. change (8 * 1) with 8. exact Hb.
    + cbn [Z.of_N]. lia.
    + cbn [N.to_nat]. exact Hm.
  - apply IH. intros j Hj. pose proof (H (S j) ltac:(cbn [length]; lia)) as Hs. cbn [nth] in Hs.
    replace (nSH cx fp + (i + 1 + Z.of_nat j)) with (nSH cx fp + (i + Z.of_nat (S j))) by lia.
    exact Hs.
Qed.

Lemma nx_region_shadow : forall E sh swlo swhi, nx_env cx fp E ->
  0 <= swlo -> swhi <= 8 -> nshadow cx fp W3 ms3 sh ->
  YP09.region_ok SEGS E M3 (nx_shadow_region swlo swhi sh).
Proof.
  intros E sh swlo swhi HE Hwlo Hwhi Hsh.
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof nx_F_facts as (_ & _ & _ & _ & _ & HSHeq).
  pose proof HJ as (HAR3 & _).
  destruct (al_frames _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & _ & HFSpres).
  rewrite nx_frame_addr_eq, nx_frame_bytes in HFSpres. change (64 / 8) with 8 in HFSpres.
  assert (Hsa : shadow_addr (frame_addr (n_lyc cx) NX_CID fp) = nSH cx fp)
    by (unfold shadow_addr; rewrite HSHeq; reflexivity).
  rewrite Hsa in HFSpres.
  assert (Hcs : Forall (YP09.chunk_ok SEGS E M3 (nSH cx fp)) (nx_sh_chunks sh)).
  { apply nx_sh_chunks_from_ok. intros j Hj.
    replace (nSH cx fp + (0 + Z.of_nat j)) with (nSH cx fp + Z.of_nat j) by lia. exact (Hsh j Hj). }
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (Ub : YP09.base_val E (Some NA_FSH) = nSH cx fp).
  { cbn [YP09.base_val]. rewrite HFSE. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia. }
  unfold YP09.region_ok, nx_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
Qed.

Lemma nx_region_objs : forall E, nx_env cx fp E -> img_env VAL A_LIM E ->
  Forall (YP09.region_ok SEGS E M3) [got_regionP; bcell_regionP NA_SB].
Proof.
  intros E HE HEI.
  pose proof HJ as (HAR3 & _).
  destruct (al_const _ _ LAWS _ _ _ _ _ HAR3) as (Kcell & _ & Kgot & _).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot.
  rewrite (pal_cell B TL) in Kcell.
  pose proof HE as (AG & Hsb & _).
  pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
  unfold pcap_img_end, YImgTop.IMG_TOP in Ho1, Ho15.
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  unfold got_regionP, bcell_regionP.
  apply Forall_cons.
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 1) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 1)) 0 8%N (SOff (A_OBJ 15) 0) (VAL (A_OBJ 15))).
    - rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 15) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
    - cbn [Z.of_N]. change (8 * 8) with 64. pose proof (pa_val_range (A_OBJ 15)). lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kgot. }
  apply Forall_cons; [|apply Forall_nil].
  { unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite (EA (A_OBJ 15) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E M3 (VAL (A_OBJ 15)) 0 8%N (SOff NA_SB 0) SHADOW_OFF).
    - rewrite nx_sv_SOff0. exact Hsb.
    - cbn [Z.of_N]. change (8 * 8) with 64. unfold SHADOW_OFF. lia.
    - cbn [Z.of_N]. lia.
    - cbn [N.to_nat]. rewrite Z.add_0_r.
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact Kcell. }
Qed.

(* The base values of the fixed part's regions. *)
Lemma nx_bases : forall E, nx_env cx fp E -> img_env VAL A_LIM E ->
  YP09.base_val E (Some NA_SP) = spZ (n_regs cx) /\
  YP09.base_val E (Some NA_SP1) = n_sp1 cx /\
  YP09.base_val E (Some NA_F) = nF cx fp /\
  YP09.base_val E (Some NA_FSH) = nSH cx fp /\
  YP09.base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1) /\
  YP09.base_val E (Some (A_OBJ 15)) = VAL (A_OBJ 15).
Proof.
  intros E HE HEI.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (EA : forall n, (A_TEXT <= n < A_LIM)%nat -> YP09.base_val E (Some n) = VAL n).
  { intros n Hn. cbn [YP09.base_val]. rewrite (img_env_atomP E n HEI Hn).
    apply unsigned_lit_small. apply pa_val_range. }
  split; [exact (nx_base_sp E HE)|].
  split; [cbn [YP09.base_val]; rewrite Hsp1E; apply unsigned_lit_small; lia|].
  split; [cbn [YP09.base_val]; rewrite HFE; apply unsigned_lit_small; lia|].
  split; [cbn [YP09.base_val]; rewrite HFSE; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia|].
  split; apply EA; unfold A_OBJ, A_TEXT, A_LIM; lia.
Qed.

Lemma nx_disj : forall E sf sh swlo swhi fw fcs, nx_env cx fp E -> img_env VAL A_LIM E ->
  YP09.pairwise_disjoint E (nx_regions0 sf sh swlo swhi fw fcs).
Proof.
  intros E sf sh swlo swhi fw fcs HE HEI.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
  pose proof (pal_got_cell B TL) as Hgc.
  pose proof (nx_bases E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  apply pairwise_disjoint_of_extents.
  unfold nx_regions0, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region,
    got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U2, U60, U516, U529, U242, U256.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, NX_SPILL, NX_FRAME, NX_STK_B,
    AFREAD_STK, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
  repeat split; lia.
Qed.

(* ---- the seat: a phase's machine state as the engine's symbolic state ---- *)
Lemma nx_seat_gen : forall E pc sr sf sh swlo swhi fw fcs extra G,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  nx_body0 cx fp pc W3 ms3 sh -> (sf = true -> nslots cx fp W3 ms3) ->
  regs_ok E sr (ms_regs ms3) ->
  0 <= fw <= NX_FRAME -> Forall (YP09.chunk_ok SEGS E M3 (nF cx fp)) fcs ->
  0 <= swlo -> swhi <= 8 ->
  YP09.regions_wf (nx_regions sf sh swlo swhi fw fcs extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (nx_regions0 sf sh swlo swhi fw fcs) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (nx_ss pc sr sf sh swlo swhi fw fcs extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sf sh swlo swhi fw fcs extra G HE HEI HBD Hsl HR Hfw HFC Hwlo Hwhi Hwf Hex Hexp Hexd HG.
  pose proof HBD as HBD'. unfold nx_body0 in HBD'.
  assert (Hpc : ms_pc_val ms3 = w64 (BASE + pc)) by (decompose [and] HBD'; assumption).
  assert (Hresv : ms_resv ms3 = None) by (decompose [and] HBD'; assumption).
  assert (Hpend : ms_svc_pending ms3 = None) by (decompose [and] HBD'; assumption).
  assert (Hrom : ms_rom ms3 = seg_rom SEGS) by (decompose [and] HBD'; assumption).
  assert (Hfregs : ms_fregs ms3 = fp_regs) by (decompose [and] HBD'; assumption).
  assert (Hfcsr : ms_fcsr ms3 = fp_csr) by (decompose [and] HBD'; assumption).
  assert (Hsaved : nsaved cx W3 ms3) by (decompose [and] HBD'; assumption).
  assert (Hhdr : nheader cx fp W3 ms3) by (decompose [and] HBD'; assumption).
  assert (Hflag : nflagw cx fp W3 ms3) by (decompose [and] HBD'; assumption).
  assert (Hshadow : nshadow cx fp W3 ms3 sh) by (decompose [and] HBD'; assumption).
  assert (HFK : nslot cx W3 ms3 NS_FK (nF cx fp)) by (decompose [and] HBD'; assumption).
  clear HBD'.
  assert (Hms : restrict (w_H W3) ms3 =
                mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W3) (ms_mem ms3))
                     (seg_rom SEGS)).
  { destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
      in Hpc, Hresv, Hpend, Hrom, Hfregs, Hfcsr.
    subst. reflexivity. }
  rewrite Hms. unfold nx_ss, nx_regions.
  apply pa_entry_st_ok_full; [exact HR | exact Hwf | | | exact HG].
  - apply Forall_app. split; [|exact Hex].
    unfold nx_regions0. apply Forall_cons; [exact (nx_region_saved E HE Hsaved)|].
    apply Forall_cons; [exact (nx_region_spill E sf HE HFK Hsl)|].
    apply Forall_cons; [exact (nx_region_frame E fw fcs HE HEI Hhdr Hflag Hfw HFC)|].
    apply Forall_cons; [exact (nx_region_shadow E sh swlo swhi HE Hwlo Hwhi Hshadow)|].
    exact (nx_region_objs E HE HEI).
  - apply nx_pwd_app; [exact (nx_disj E sf sh swlo swhi fw fcs HE HEI) | exact Hexp | exact Hexd].
Qed.

(* The open reader's cuts (every slot written): nx_body. *)
Theorem nx_seat : forall E pc sr sh swlo swhi fw fcs extra G,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  nx_body cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  0 <= fw <= NX_FRAME -> Forall (YP09.chunk_ok SEGS E M3 (nF cx fp)) fcs ->
  0 <= swlo -> swhi <= 8 ->
  YP09.regions_wf (nx_regions true sh swlo swhi fw fcs extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (nx_regions0 true sh swlo swhi fw fcs) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (nx_ss pc sr true sh swlo swhi fw fcs extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh swlo swhi fw fcs extra G HE HEI [HB0 Hsl]. 
  apply (nx_seat_gen E pc sr true sh swlo swhi fw fcs extra G HE HEI HB0 (fun _ => Hsl)).
Qed.

(* Every cut from the FK spill on, both readers (NS_FK only): nx_body0. *)
Theorem nx_seat0 : forall E pc sr sh swlo swhi fw fcs extra G,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  nx_body0 cx fp pc W3 ms3 sh ->
  regs_ok E sr (ms_regs ms3) ->
  0 <= fw <= NX_FRAME -> Forall (YP09.chunk_ok SEGS E M3 (nF cx fp)) fcs ->
  0 <= swlo -> swhi <= 8 ->
  YP09.regions_wf (nx_regions false sh swlo swhi fw fcs extra) = true ->
  Forall (YP09.region_ok SEGS E M3) extra ->
  YP09.pairwise_disjoint E extra ->
  Forall (fun r => YP09.all_disjoint E r extra) (nx_regions0 false sh swlo swhi fw fcs) ->
  facts_ok E G ->
  st_ok_pi SEGS VAL E (nx_ss pc sr false sh swlo swhi fw fcs extra G) (restrict (w_H W3) ms3).
Proof.
  intros E pc sr sh swlo swhi fw fcs extra G HE HEI HB0.
  apply (nx_seat_gen E pc sr false sh swlo swhi fw fcs extra G HE HEI HB0 (fun H => ltac:(discriminate H))).
Qed.

(* ---- the registers of a phase's first seat ---- *)
Lemma nx_sr_ok_std : forall E sr, nx_env cx fp E ->
  sr_get sr 2 = SOff NA_SP1 0 -> sr_get sr 8 = SOff NA_SP 0 -> sr_get sr 9 = SOff NA_SP1 0 ->
  sr_get sr 3 = SOff 3 0 -> sr_get sr 4 = SOff 4 0 -> sr_get sr 25 = SOff NA_FSH 0 ->
  nx_sr_ok cx fp E sr.
Proof.
  intros E sr HE H2 H8 H9 H3 H4 H25. pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  unfold nx_sr_ok. rewrite H2, H8, H9, H3, H4, H25, !nx_sv_SOff0.
  split; [exact Hsp1E|]. split.
  { rewrite (nx_env_base E NA_SP (2%bv : bv 5) HE eq_refl). unfold w64, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
  split; [exact Hsp1E|].
  split; [exact (nx_env_base E 3%nat (3%bv : bv 5) HE eq_refl)|].
  split; [exact (nx_env_base E 4%nat (4%bv : bv 5) HE eq_refl)|].
  exact HFSE.
Qed.

(* The standard symbolic registers nx_sr in the environment nx_mkE, from the body's registers. *)
Lemma nx_regs_ok : nregs cx ms3 -> getr (ms_regs ms3) 25 = w64 (nSH cx fp) ->
  regs_ok (nx_mkE cx fp (ms_regs ms3)) nx_sr (ms_regs ms3).
Proof.
  intros (R2 & R8 & R9 & R3 & R4) R25.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE.
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  set (E := nx_mkE cx fp (ms_regs ms3)) in *.
  assert (E2 : ew E NA_SP = getr (n_regs cx) 2) by exact (nx_env_base E NA_SP (2%bv : bv 5) HE eq_refl).
  assert (E3 : ew E 3%nat = getr (n_regs cx) 3) by exact (nx_env_base E 3%nat (3%bv : bv 5) HE eq_refl).
  assert (E4 : ew E 4%nat = getr (n_regs cx) 4) by exact (nx_env_base E 4%nat (4%bv : bv 5) HE eq_refl).
  assert (CUR : forall i, (i < 32)%nat -> ew E (NA_CUR + i) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat i)))
    by (intros i Hi; exact (nx_mkE_cur cx fp (ms_regs ms3) i Hi)).
  unfold NA_SP, NA_SB, NA_SP1, NA_F, NA_FL, NA_FSH, NA_CUR in *.
  apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  Local Ltac nx_rcase CUR R2 R8 R9 R3 R4 R25 E2 E3 E4 Hsp1E HFSE :=
    match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
      let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
    first
    [ rewrite getr_zero; reflexivity
    | rewrite nx_sv_SOff0;
      match goal with |- getr ?rg ?r = ew ?E ?k =>
        first
        [ lazymatch eval vm_compute in (530 <=? k)%nat with true =>
            let i := eval vm_compute in (k - 530)%nat in
            let Hk := fresh "Hk" in
            assert (Hk : ew E k = getr rg (Z_to_bv 5 (Z.of_nat i))) by (exact (CUR i ltac:(lia)));
            rewrite Hk; f_equal; apply bv_eq; reflexivity end
        | transitivity (getr rg 2); [f_equal; apply bv_eq; reflexivity|]; rewrite R2; symmetry; exact Hsp1E
        | transitivity (getr rg 9); [f_equal; apply bv_eq; reflexivity|]; rewrite R9; symmetry; exact Hsp1E
        | transitivity (getr rg 8); [f_equal; apply bv_eq; reflexivity|]; rewrite R8, E2; unfold w64, spZ;
          rewrite Z_to_bv_bv_unsigned; f_equal; apply bv_eq; reflexivity
        | transitivity (getr rg 3); [f_equal; apply bv_eq; reflexivity|]; rewrite R3, E3;
          f_equal; apply bv_eq; reflexivity
        | transitivity (getr rg 4); [f_equal; apply bv_eq; reflexivity|]; rewrite R4, E4;
          f_equal; apply bv_eq; reflexivity
        | transitivity (getr rg 25); [f_equal; apply bv_eq; reflexivity|]; rewrite R25; symmetry; exact HFSE ]
      end ].
  repeat (destruct Hr as [<- | Hr]; [nx_rcase CUR R2 R8 R9 R3 R4 R25 E2 E3 E4 Hsp1E HFSE|]).
  destruct Hr.
Qed.

(* ---- the facts of the fixed part ---- *)
Lemma nx_facts0_ok : forall E, nx_env cx fp E -> facts_ok E nx_facts0.
Proof.
  intros E HE.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & Hs8).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & Hfia & Hflt).
  rewrite nx_flag_addr_eq in Hfia, Hflt.
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (U2 : bv_unsigned (ew E NA_SP) = spZ (n_regs cx)) by exact (nx_base_sp E HE).
  assert (U10 : bv_unsigned (ew E NA_PS) = n_ps cx) by exact (nx_ps_base E HE).
  split; [|split; exact I].
  cbn [nx_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U10, Hsb, Hsp1E, HFE, HFLE, HFSE.
  rewrite !unsigned_lit_small by (unfold in_app, SHADOW_OFF in *; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 5) with 32. change (2 ^ 6) with 64.
  rewrite Z.pow_0_r, !Z.mod_1_r.
  unfold in_app, SHADOW_OFF, NX_STK_B, AFREAD_STK, PS_LEN in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* ---- the shadow entries ---- *)
Lemma nx_shok : forall E SHx, nx_env cx fp E ->
  range_addressable (aview SEGS (w_H W3) (ms_mem ms3)) SHADOW_OFF (n_ps cx) PS_LEN ->
  sh_ok SEGS nx_Bx SHx E M3 -> sh_ok SEGS nx_Bx (nx_SH ++ SHx) E M3.
Proof.
  intros E SHx HE HR HX. unfold sh_ok in *. unfold nx_SH. cbn [app]. constructor; [|exact HX].
  pose proof nxb_ps as (_ & H4 & H47 & Ham). pose proof HE as (_ & Hsb & _).
  apply (nx_shent_ok E M3 NA_PS (n_ps cx) 0 PS_LEN Hsb (nx_ps_atom E HE));
    [unfold PS_LEN in *; lia | unfold PS_LEN; lia | |].
  - rewrite Z.add_0_r, Z.sub_0_r. exact Ham.
  - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact HR.
Qed.

(* ---- the landing: the engine's symbolic state back as a phase's machine state ---- *)
Local Ltac nx_in := cbn [nx_spill_chunks nx_slot_chunks nx_fk_chunk nx_f0_chunk nx_hdr_chunks In app];
  repeat (first [left; reflexivity | right]).

Lemma nxb_buf : n_h cx <> 0 ->
  In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B (n_lyc cx) (n_Sc cx)) /\
  4096 <= n_buf cx /\ n_buf cx + nx_bufn (n_cap cx) < 2 ^ 63 /\ 0 <= n_cap cx <= NX_CAP_MAX /\
  (n_buf cx + nx_bufn (n_cap cx) <= n_ps cx \/ n_ps cx + PS_LEN <= n_buf cx).
Proof.
  intros Hh. pose proof HB as H. unfold nx_base in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbf & _).
  destruct (Hbf Hh) as (Hin & H4 & H63 & _ & _ & Hcap & _ & Hsep). auto.
Qed.

Lemma nxb_ts_rng : n_h cx <> 0 -> 0 <= n_ts cx < 2 ^ 64.
Proof.
  intros Hh. destruct (Z.eq_dec (n_ts cx) 0) as [E0|Hn]; [lia|].
  pose proof HB as H. unfold nx_base in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hts & _).
  destruct (Hts Hh Hn) as (_ & _ & H4 & H47 & _). lia.
Qed.

Theorem nx_land0 : forall E pc sr sf sh swlo swhi fw fcs extra G,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E (nx_ss pc sr sf sh swlo swhi fw fcs extra G) (restrict (w_H W3) ms3) ->
  nx_sr_ok cx fp E sr ->
  length sh = NX_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  nx_body0 cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sf sh swlo swhi fw fcs extra G HE HEI HS (R2 & R8 & R9 & R3 & R4 & R25) Hlen Hsh256.
  pose proof (nx_base_sp E HE) as Ub2.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof nx_F_facts as (HF0 & HFc & HFia & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & Hfia & Hflt).
  rewrite nx_flag_addr_eq in Hfia, Hflt.
  assert (HflZ : 0 <= nFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  cbn [YP09.base_val] in Ub2.
  assert (Rsaved : YP09.region_ok SEGS E M3 nx_saved_region)
    by exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 0%nat _ HS eq_refl).
  assert (Rspill : YP09.region_ok SEGS E M3 (nx_spill_region sf))
    by exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 1%nat _ HS eq_refl).
  assert (Rframe : YP09.region_ok SEGS E M3 (nx_frame_region fw fcs))
    by exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 2%nat _ HS eq_refl).
  assert (Rshadow : YP09.region_ok SEGS E M3 (nx_shadow_region swlo swhi sh))
    by exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 3%nat _ HS eq_refl).
  assert (SAV : forall (n : nat) (r : bv 5) od,
    Z.of_nat n = bv_unsigned r ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) nx_saved_chunks ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) + od) =
      Some (bv_unsigned (getr (n_regs cx) r))).
  { intros n r od Hn Hin.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|apply u64_range].
    apply (field_of_region E M3 NA_SP (spZ (n_regs cx)) nx_saved_chunks (-104) 0 0 0 od 8%N
             (SOff n 0) (bv_unsigned (getr (n_regs cx) r)) Rsaved Ub2 Hin).
    - rewrite nx_sv_SOff0, (nx_env_base E n r HE Hn). symmetry. apply Z_to_bv_bv_unsigned.
    - cbn [Z.of_N]. change (8 * 8) with 64. apply u64_range.
    - cbn [Z.of_N]. lia. }
  assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (nx_spill_chunks sf) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> nslot cx W3 ms3 od v).
  { intros od e v Hin He Hv. unfold nslot.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
    apply (field_of_region E M3 NA_SP1 (n_sp1 cx) (nx_spill_chunks sf) 0 NX_SPILL 0 NX_SPILL od 8%N e v Rspill);
      [ rewrite Hsp1E; apply unsigned_lit_small; lia | exact Hin | exact He | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (FR : forall od e v,
    In (YP09.mkChunk od (CVal 8 e)) (nx_hdr_chunks ++ fcs ++ [YP09.mkChunk (NX_FRAME - 8) (CVal 8 (SOff NA_FL 0))]) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + od) = Some v).
  { intros od e v Hin He Hv.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
    apply (field_of_region E M3 NA_F (nF cx fp) _ 0 NX_FRAME 0 fw od 8%N e v Rframe);
      [ rewrite HFE; apply unsigned_lit_small; lia | exact Hin | exact He | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (SHW : nshadow cx fp W3 ms3 sh).
  { intros i Hi.
    assert (Hb : 0 <= nth i sh 0 < 256).
    { rewrite Forall_forall in Hsh256. apply Hsh256. apply nth_In. exact Hi. }
    apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [|exact Hb].
    apply (field_of_region E M3 NA_FSH (nSH cx fp) (nx_sh_chunks sh) 0 8 swlo swhi (Z.of_nat i) 1%N
             (SLit (nth i sh 0)) (nth i sh 0) Rshadow).
    - rewrite HFSE. apply unsigned_lit_small. unfold SHADOW_OFF in *. lia.
    - apply nx_sh_chunks_In. exact Hi.
    - reflexivity.
    - cbn [Z.of_N]. lia.
    - cbn [Z.of_N]. lia. }
  assert (HDR : nheader cx fp W3 ms3).
  { split; [|split].
    - pose proof (FR 0 (SLit NX_MAGIC) NX_MAGIC ltac:(apply in_or_app; left; nx_in) eq_refl
        ltac:(unfold NX_MAGIC; lia)) as X. rewrite Z.add_0_r in X. exact X.
    - apply (FR 8 (SOff (A_OBJ 13) 0) (VAL (A_OBJ 13))).
      + apply in_or_app. left. nx_in.
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 13) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 13)). lia.
    - apply (FR 16 (SOff (A_OBJ 14) 0) (VAL (A_OBJ 14))).
      + apply in_or_app. left. nx_in.
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 14) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 14)). lia. }
  assert (FLG : nflagw cx fp W3 ms3).
  { unfold nflagw. replace (nF cx fp + NX_FLAGPTR) with (nF cx fp + (NX_FRAME - 8)) by (unfold NX_FLAGPTR, NX_FRAME; lia).
    apply (FR (NX_FRAME - 8) (SOff NA_FL 0) (nFL cx fp)); [| rewrite nx_sv_SOff0, HFLE; reflexivity | exact HflZ].
    apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
  assert (SFK : nslot cx W3 ms3 NS_FK (nF cx fp)).
  { apply (SL NS_FK (SOff NA_F 0) (nF cx fp) (nx_fk_in sf)); [rewrite nx_sv_SOff0, HFE; reflexivity | lia]. }
  pose proof HS as (Hfr & Hpcv & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
  unfold nx_ss, abs_ss, setpc in Hpcv, Hresv, Hregs.
  cbn [ss_pc ss_regs ss_resv resv_denot restrict
       ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs]
    in Hfr, Hpcv, Hpend, Hresv, Hfcsr, Hrom, Hregs.
  assert (Hpc' : ms_pc_val ms3 = w64 (BASE + pc)) by exact Hpcv.
  assert (NR : nregs cx ms3).
  { unfold nregs. rewrite !Hregs. exact (conj R2 (conj R8 (conj R9 (conj R3 R4)))). }
  assert (NSV : nsaved cx W3 ms3).
  { split.
    - replace (spZ (n_regs cx) - 8) with (spZ (n_regs cx) + -8) by lia.
      exact (SAV 1%nat (1%bv : bv 5) (-8) ltac:(vm_compute; reflexivity)
               ltac:(unfold nx_saved_chunks; cbn [In]; tauto)).
    - assert (SJ : forall (j : Z) (n : nat) (od : Z),
        Z.of_nat n = bv_unsigned (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) ->
        In (YP09.mkChunk od (CVal 8 (SOff n 0))) nx_saved_chunks ->
        od = -16 - 8 * j ->
        rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 16 - 8 * j) =
          Some (bv_unsigned (getr (n_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
      { intros j n od Hn Hin Hod.
        replace (spZ (n_regs cx) - 16 - 8 * j) with (spZ (n_regs cx) + od) by lia.
        exact (SAV n (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) od Hn Hin). }
      intros j Hj.
      assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                      j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
      Local Ltac nx_sjc SJ v n o :=
        apply (SJ v n o);
        [vm_compute; reflexivity | unfold nx_saved_chunks; cbn [In]; tauto | lia].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 0 8%nat (-16)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 1 9%nat (-24)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 2 18%nat (-32)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 3 19%nat (-40)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 4 20%nat (-48)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 5 21%nat (-56)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 6 22%nat (-64)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 7 23%nat (-72)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 8 24%nat (-80)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 9 25%nat (-88)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjc SJ 10 26%nat (-96)|].
      subst j; nx_sjc SJ 11 27%nat (-104). }
  assert (G25 : getr (ms_regs ms3) 25 = w64 (nSH cx fp)) by (rewrite Hregs; exact R25).
  unfold nx_body0. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* The open reader's cuts: every slot as the seat left it (the spill region with sf = true). *)
Theorem nx_land : forall E pc sr sh swlo swhi fw fcs extra G,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E (nx_ss pc sr true sh swlo swhi fw fcs extra G) (restrict (w_H W3) ms3) ->
  nx_sr_ok cx fp E sr ->
  length sh = NX_NSH -> Forall (fun v => 0 <= v < 256) sh ->
  n_h cx <> 0 ->
  nx_body cx fp pc W3 ms3 sh.
Proof.
  intros E pc sr sh swlo swhi fw fcs extra G HE HEI HS HR Hlen Hsh Hh.
  split; [exact (nx_land0 E pc sr true sh swlo swhi fw fcs extra G HE HEI HS HR Hlen Hsh)|].
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & _).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  pose proof (nxb_ts_rng Hh) as Hts.
  pose proof asan_consts as (Hac & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  pose proof (nx_ps_atom E HE) as HPS. pose proof (nx_ts_atom E HE) as HTS.
  assert (Hpsr : 0 <= n_ps cx < 2 ^ 64) by (unfold PS_LEN in *; lia).
  assert (Rspill : YP09.region_ok SEGS E M3 (nx_spill_region true))
    by exact (st_ok_pi_region_nth E _ (restrict (w_H W3) ms3) 1%nat _ HS eq_refl).
  assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (nx_spill_chunks true) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> nslot cx W3 ms3 od v).
  { intros od e v Hin He Hv. unfold nslot.
    apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
    apply (field_of_region E M3 NA_SP1 (n_sp1 cx) (nx_spill_chunks true) 0 NX_SPILL 0 NX_SPILL od 8%N e v Rspill);
      [ rewrite Hsp1E; apply unsigned_lit_small; lia | exact Hin | exact He | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (SHR : forall c, 0 <= c <= 16 -> 0 <= shadow_of_addr SHADOW_OFF (n_ps cx + c) < 2 ^ 64).
  { intros c Hc. unfold shadow_of_addr, SHADOW_OFF.
    assert (0 <= (n_ps cx + c) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold PS_LEN in *; lia).
    lia. }
  destruct (nxb_buf Hh) as (_ & Hb4 & Hb63 & _).
  pose proof (nx_buf_atom E HE) as HBUF.
  assert (E8 : (n_ps cx + PS_SW_OFF) mod 8 + 3 = 3) by (unfold PS_SW_OFF; rewrite Z.add_mod, Hps8 by lia; reflexivity).
  assert (E12 : (n_ps cx + PS_OL_OFF) mod 8 + 3 = 7) by (unfold PS_OL_OFF; rewrite Z.add_mod, Hps8 by lia; reflexivity).
  assert (PH : forall c, sv_denot E (SOff NA_F c) = Z_to_bv 64 (nF cx fp + c)).
  { intros c. cbn [sv_denot]. rewrite HFE, unsigned_lit_small by lia. reflexivity. }
  unfold nslots.
  split; [apply (SL NS_FK (SOff NA_F 0)); [nx_in | rewrite nx_sv_SOff0, HFE; reflexivity | lia]|].
  split; [apply (SL NS_F0 (SOff NA_F 0)); [nx_in | rewrite nx_sv_SOff0, HFE; reflexivity | lia]|].
  split; [apply (SL NS_BUF (SOff NA_BUF 0)); [nx_in | rewrite nx_sv_SOff0, HBUF; reflexivity | unfold nx_bufn in *; lia]|].
  split; [apply (SL NS_TS (SOff NA_TS 0)); [nx_in | rewrite nx_sv_SOff0, HTS; reflexivity | exact Hts]|].
  split; [apply (SL NS_SB nx_Bx); [nx_in | unfold nx_Bx; rewrite nx_sv_SOff0, Hsb; reflexivity | unfold SHADOW_OFF; lia]|].
  split; [apply (SL NS_PS12 (SOff NA_PS PS_OL_OFF)); [nx_in | cbn [sv_denot]; rewrite HPS, unsigned_lit_small by exact Hpsr; reflexivity | unfold PS_OL_OFF, PS_LEN in *; lia]|].
  split; [apply (SL NS_SH12 (nx_shx (SOff NA_PS PS_OL_OFF))); [nx_in | apply (nx_U_shx E NA_PS (n_ps cx) PS_OL_OFF Hsb HPS Hpsr); unfold PS_OL_OFF, PS_LEN in *; lia | apply SHR; unfold PS_OL_OFF; lia]|].
  split; [rewrite E8; apply (SL NS_OFF8 (SLit 3)); [nx_in | reflexivity | lia]|].
  split; [rewrite E12; apply (SL NS_OFF12 (SLit 7)); [nx_in | reflexivity | lia]|].
  split; [apply (SL NS_PH4 (SOff NA_F 36)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia]|].
  split; [apply (SL NS_PH8 (SOff NA_F 40)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia]|].
  apply (SL NS_PH12 (SOff NA_F 44)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia].
Qed.

(* ---- landing from any region list that still holds the fixed part's chunks ---- *)
Lemma nx_st_ok_regions : forall E ss, st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  Forall (YP09.region_ok SEGS E M3) (ss_mem ss).
Proof.
  intros E ss HS. destruct ss as [p0 r0 f0 m0 v0 g0].
  pose proof (st_ok_mem_ok SEGS E _ _ HS) as (_ & Hrs & _). exact Hrs.
Qed.

Lemma nx_has_val : forall E ss n b od (w : N) e, st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  bv_unsigned (ew E n) = b -> nx_hasb (ss_mem ss) n (YP09.mkChunk od (CVal w e)) = true -> (Z.of_N w <= 8) ->
  val_mem SEGS M3 (b + od) (N.to_nat w) (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E ss n b od w e HS Hb Hh Hw.
  destruct (nx_hasb_sound _ _ _ Hh) as (lo & hi & wlo & whi & cs & Hin & Hc).
  pose proof (proj1 (Forall_forall _ _) (nx_st_ok_regions E ss HS) _ Hin) as HR.
  exact (field_of_region_any E M3 n b cs lo hi wlo whi od w e HR Hb Hc Hw).
Qed.

Lemma nx_has_word : forall E ss n b od e v, st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) ->
  bv_unsigned (ew E n) = b -> nx_hasb (ss_mem ss) n (YP09.mkChunk od (CVal 8 e)) = true ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (b + od) = Some v.
Proof.
  intros E ss n b od e v HS Hb Hh He Hv.
  apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms3)); [|exact Hv].
  pose proof (nx_has_val E ss n b od 8%N e HS Hb Hh ltac:(cbn; lia)) as X.
  rewrite He, unsigned_lit_small in X by exact Hv. rewrite Z.mod_small in X by (cbn; lia). exact X.
Qed.

Theorem nx_land0_by : forall E ss sf vs sh,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) -> ss_resv ss = None ->
  nx_sr_ok cx fp E (ss_regs ss) ->
  nx_land_chk sf vs (ss_mem ss) = true ->
  map (fun v => v mod 256) vs = sh -> length sh = NX_NSH ->
  nx_body0 cx fp (ss_pc ss) W3 ms3 sh.
Proof.
  intros E ss sf vs sh HE HEI HS Hrv (R2 & R8 & R9 & R3 & R4 & R25) Hchk Hsh Hlen.
  destruct (nx_land_chk_split _ _ _ Hchk) as (CS & CL & CF & CH).
  pose proof (nx_base_sp E HE) as Ub2. cbn [YP09.base_val] in Ub2.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof nx_F_facts as (HF0 & HFc & HFia & _ & _ & HSHeq).
  pose proof asan_consts as (Hac & _).
  pose proof HJ as (HAR3 & _).
  destruct (al_flag _ _ LAWS _ _ _ _ _ NX_CID fp HAR3 nx_fin) as (_ & _ & Hfia & Hflt).
  rewrite nx_flag_addr_eq in Hfia, Hflt.
  assert (HflZ : 0 <= nFL cx fp < 2 ^ 64) by (unfold in_app in Hfia; lia).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  assert (U60 : bv_unsigned (ew E NA_SP1) = n_sp1 cx) by (rewrite Hsp1E; apply unsigned_lit_small; lia).
  assert (U516 : bv_unsigned (ew E NA_F) = nF cx fp) by (rewrite HFE; apply unsigned_lit_small; lia).
  assert (U529 : bv_unsigned (ew E NA_FSH) = nSH cx fp)
    by (rewrite HFSE; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (nx_spill_chunks sf) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> nslot cx W3 ms3 od v).
  { intros od e v Hin He Hv. exact (nx_has_word E ss NA_SP1 _ od e v HS U60 (CL _ Hin) He Hv). }
  assert (FR : forall od e v,
    In (YP09.mkChunk od (CVal 8 e)) (nx_hdr_chunks ++ [YP09.mkChunk (NX_FRAME - 8) (CVal 8 (SOff NA_FL 0))]) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (nF cx fp + od) = Some v).
  { intros od e v Hin He Hv. exact (nx_has_word E ss NA_F _ od e v HS U516 (CF _ Hin) He Hv). }
  assert (SAV : forall (n : nat) (r : bv 5) od,
    Z.of_nat n = bv_unsigned r ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0))) nx_saved_chunks ->
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) + od) =
      Some (bv_unsigned (getr (n_regs cx) r))).
  { intros n r od Hn Hin. apply (nx_has_word E ss NA_SP _ od (SOff n 0) _ HS Ub2 (CS _ Hin)); [|apply u64_range].
    rewrite nx_sv_SOff0, (nx_env_base E n r HE Hn). symmetry. apply Z_to_bv_bv_unsigned. }
  assert (SHW : nshadow cx fp W3 ms3 sh).
  { intros i Hi. subst sh. rewrite length_map in Hi.
    pose proof (nx_sh_chunks_In vs i Hi) as Hin.
    pose proof (nx_has_val E ss NA_FSH _ (Z.of_nat i) 1%N (SLit (nth i vs 0)) HS U529 (CH _ Hin) ltac:(cbn; lia)) as X.
    cbn [sv_denot] in X. rewrite Z_to_bv_unsigned in X. unfold bv_wrap in X.
    change (bv_modulus 64) with (2 ^ 64) in X. change (2 ^ (8 * Z.of_N 1)) with 256 in X.
    replace (nth i vs 0 mod 2 ^ 64 mod 256) with (nth i vs 0 mod 256) in X
      by (symmetry; apply Z.mod_mod_divide; exists (2 ^ 56); reflexivity).
    pose proof (map_nth (fun v : Z => v mod 256) vs 0 i) as M. cbn beta in M.
    change (0 mod 256) with 0 in M. rewrite M.
    apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [exact X | apply Z.mod_pos_bound; lia]. }
  assert (HDR : nheader cx fp W3 ms3).
  { split; [|split].
    - pose proof (FR 0 (SLit NX_MAGIC) NX_MAGIC ltac:(apply in_or_app; left; nx_in) eq_refl
        ltac:(unfold NX_MAGIC; lia)) as X. rewrite Z.add_0_r in X. exact X.
    - apply (FR 8 (SOff (A_OBJ 13) 0) (VAL (A_OBJ 13))).
      + apply in_or_app. left. nx_in.
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 13) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 13)). lia.
    - apply (FR 16 (SOff (A_OBJ 14) 0) (VAL (A_OBJ 14))).
      + apply in_or_app. left. nx_in.
      + rewrite nx_sv_SOff0. apply (img_env_atomP E (A_OBJ 14) HEI). unfold A_OBJ, A_TEXT, A_LIM. lia.
      + pose proof (pa_val_range (A_OBJ 14)). lia. }
  assert (FLG : nflagw cx fp W3 ms3).
  { unfold nflagw. replace (nF cx fp + NX_FLAGPTR) with (nF cx fp + (NX_FRAME - 8)) by (unfold NX_FLAGPTR, NX_FRAME; lia).
    apply (FR (NX_FRAME - 8) (SOff NA_FL 0) (nFL cx fp)); [| rewrite nx_sv_SOff0, HFLE; reflexivity | exact HflZ].
    apply in_or_app. right. left. reflexivity. }
  assert (SFK : nslot cx W3 ms3 NS_FK (nF cx fp)).
  { apply (SL NS_FK (SOff NA_F 0) (nF cx fp) (nx_fk_in sf)); [rewrite nx_sv_SOff0, HFE; reflexivity | lia]. }
  pose proof HS as (Hfr & Hpcv & Hpend & Hresv & Hfcsr & Hrom & Hregs & _).
  unfold abs_ss, setpc in Hpcv, Hresv, Hregs.
  destruct ss as [pc0 r0 f0 m0 v0 g0]. cbn [ss_pc ss_regs ss_resv ss_mem] in *. subst v0.
  cbn [ss_pc ss_regs ss_resv resv_denot restrict
       ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs]
    in Hfr, Hpcv, Hpend, Hresv, Hfcsr, Hrom, Hregs.
  assert (Hpc' : ms_pc_val ms3 = w64 (BASE + pc0)) by exact Hpcv.
  assert (NR : nregs cx ms3).
  { unfold nregs. rewrite !Hregs. exact (conj R2 (conj R8 (conj R9 (conj R3 R4)))). }
  assert (NSV : nsaved cx W3 ms3).
  { split.
    - replace (spZ (n_regs cx) - 8) with (spZ (n_regs cx) + -8) by lia.
      exact (SAV 1%nat (1%bv : bv 5) (-8) ltac:(vm_compute; reflexivity)
               ltac:(unfold nx_saved_chunks; cbn [In]; tauto)).
    - assert (SJ : forall (j : Z) (n : nat) (od : Z),
        Z.of_nat n = bv_unsigned (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) ->
        In (YP09.mkChunk od (CVal 8 (SOff n 0))) nx_saved_chunks ->
        od = -16 - 8 * j ->
        rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - 16 - 8 * j) =
          Some (bv_unsigned (getr (n_regs cx) (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j))))).
      { intros j n od Hn Hin Hod.
        replace (spZ (n_regs cx) - 16 - 8 * j) with (spZ (n_regs cx) + od) by lia.
        exact (SAV n (Z_to_bv 5 (if j <? 2 then 8 + j else 16 + j)) od Hn Hin). }
      intros j Hj.
      assert (Hcase : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/
                      j = 8 \/ j = 9 \/ j = 10 \/ j = 11) by lia.
      Local Ltac nx_sjb SJ v n o :=
        apply (SJ v n o); [vm_compute; reflexivity | unfold nx_saved_chunks; cbn [In]; tauto | lia].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 0 8%nat (-16)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 1 9%nat (-24)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 2 18%nat (-32)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 3 19%nat (-40)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 4 20%nat (-48)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 5 21%nat (-56)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 6 22%nat (-64)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 7 23%nat (-72)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 8 24%nat (-80)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 9 25%nat (-88)|].
      destruct Hcase as [Hc|Hcase]; [subst j; nx_sjb SJ 10 26%nat (-96)|].
      subst j; nx_sjb SJ 11 27%nat (-104). }
  assert (G25 : getr (ms_regs ms3) 25 = w64 (nSH cx fp)) by (rewrite Hregs; exact R25).
  unfold nx_body0. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Theorem nx_land_by : forall E ss vs sh,
  nx_env cx fp E -> img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms3) -> ss_resv ss = None ->
  nx_sr_ok cx fp E (ss_regs ss) ->
  nx_land_chk true vs (ss_mem ss) = true ->
  map (fun v => v mod 256) vs = sh -> length sh = NX_NSH ->
  n_h cx <> 0 ->
  nx_body cx fp (ss_pc ss) W3 ms3 sh.
Proof.
  intros E ss vs sh HE HEI HS Hrv HR Hchk Hsh Hlen Hh.
  split; [exact (nx_land0_by E ss true vs sh HE HEI HS Hrv HR Hchk Hsh Hlen)|].
  destruct (nx_land_chk_split _ _ _ Hchk) as (_ & CL & _).
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & _).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  pose proof (nxb_ts_rng Hh) as Hts.
  pose proof asan_consts as (Hac & _).
  pose proof HE as (AG & Hsb & Hsp1E & HFE & HFLE & HFSE).
  pose proof (nx_ps_atom E HE) as HPS. pose proof (nx_ts_atom E HE) as HTS.
  assert (Hpsr : 0 <= n_ps cx < 2 ^ 64) by (unfold PS_LEN in *; lia).
  assert (U60 : bv_unsigned (ew E NA_SP1) = n_sp1 cx) by (rewrite Hsp1E; apply unsigned_lit_small; lia).
  assert (SL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (nx_spill_chunks true) ->
    sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> nslot cx W3 ms3 od v).
  { intros od e v Hin He Hv. exact (nx_has_word E ss NA_SP1 _ od e v HS U60 (CL _ Hin) He Hv). }
  assert (SHR : forall c, 0 <= c <= 16 -> 0 <= shadow_of_addr SHADOW_OFF (n_ps cx + c) < 2 ^ 64).
  { intros c Hc. unfold shadow_of_addr, SHADOW_OFF.
    assert (0 <= (n_ps cx + c) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; unfold PS_LEN in *; lia).
    lia. }
  destruct (nxb_buf Hh) as (_ & Hb4 & Hb63 & _).
  pose proof (nx_buf_atom E HE) as HBUF.
  assert (E8 : (n_ps cx + PS_SW_OFF) mod 8 + 3 = 3) by (unfold PS_SW_OFF; rewrite Z.add_mod, Hps8 by lia; reflexivity).
  assert (E12 : (n_ps cx + PS_OL_OFF) mod 8 + 3 = 7) by (unfold PS_OL_OFF; rewrite Z.add_mod, Hps8 by lia; reflexivity).
  assert (PH : forall c, sv_denot E (SOff NA_F c) = Z_to_bv 64 (nF cx fp + c)).
  { intros c. cbn [sv_denot]. rewrite HFE, unsigned_lit_small by lia. reflexivity. }
  unfold nslots.
  split; [apply (SL NS_FK (SOff NA_F 0)); [nx_in | rewrite nx_sv_SOff0, HFE; reflexivity | lia]|].
  split; [apply (SL NS_F0 (SOff NA_F 0)); [nx_in | rewrite nx_sv_SOff0, HFE; reflexivity | lia]|].
  split; [apply (SL NS_BUF (SOff NA_BUF 0)); [nx_in | rewrite nx_sv_SOff0, HBUF; reflexivity | unfold nx_bufn in *; lia]|].
  split; [apply (SL NS_TS (SOff NA_TS 0)); [nx_in | rewrite nx_sv_SOff0, HTS; reflexivity | exact Hts]|].
  split; [apply (SL NS_SB nx_Bx); [nx_in | unfold nx_Bx; rewrite nx_sv_SOff0, Hsb; reflexivity | unfold SHADOW_OFF; lia]|].
  split; [apply (SL NS_PS12 (SOff NA_PS PS_OL_OFF)); [nx_in | cbn [sv_denot]; rewrite HPS, unsigned_lit_small by exact Hpsr; reflexivity | unfold PS_OL_OFF, PS_LEN in *; lia]|].
  split; [apply (SL NS_SH12 (nx_shx (SOff NA_PS PS_OL_OFF))); [nx_in | apply (nx_U_shx E NA_PS (n_ps cx) PS_OL_OFF Hsb HPS Hpsr); unfold PS_OL_OFF, PS_LEN in *; lia | apply SHR; unfold PS_OL_OFF; lia]|].
  split; [rewrite E8; apply (SL NS_OFF8 (SLit 3)); [nx_in | reflexivity | lia]|].
  split; [rewrite E12; apply (SL NS_OFF12 (SLit 7)); [nx_in | reflexivity | lia]|].
  split; [apply (SL NS_PH4 (SOff NA_F 36)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia]|].
  split; [apply (SL NS_PH8 (SOff NA_F 40)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia]|].
  apply (SL NS_PH12 (SOff NA_F 44)); [nx_in | rewrite PH; unfold NO_PH; f_equal; lia | unfold NO_PH; lia].
Qed.

(* The seat and the landing compose: a cut of the open reader with `ph` in scope, seated in the
   first-seat environment with the standard registers, lands back where it was. *)
Lemma nx_seat_land_ph : forall pc, nx_body cx fp pc W3 ms3 NSH_ph -> n_h cx <> 0 ->
  st_ok_pi SEGS VAL (nx_mkE cx fp (ms_regs ms3)) (nx_ss pc nx_sr true NSH_ph 0 0 0 [] [] nx_facts0)
    (restrict (w_H W3) ms3) /\
  nx_body cx fp pc W3 ms3 NSH_ph.
Proof.
  intros pc HBD Hh.
  pose proof (nx_mkE_env cx fp (ms_regs ms3)) as HE. pose proof (nx_mkE_img cx fp (ms_regs ms3)) as HEI.
  pose proof HBD as [HB0 _]. pose proof HB0 as HB0'. unfold nx_body0 in HB0'.
  assert (NR : nregs cx ms3) by (decompose [and] HB0'; assumption).
  assert (G25 : getr (ms_regs ms3) 25 = w64 (nSH cx fp)) by (decompose [and] HB0'; assumption).
  assert (HS : st_ok_pi SEGS VAL (nx_mkE cx fp (ms_regs ms3)) (nx_ss pc nx_sr true NSH_ph 0 0 0 [] [] nx_facts0)
    (restrict (w_H W3) ms3)).
  { apply (nx_seat _ pc nx_sr NSH_ph 0 0 0 [] [] nx_facts0 HE HEI HBD (nx_regs_ok NR G25));
      [unfold NX_FRAME; lia | constructor | lia | lia | vm_compute; reflexivity | constructor | exact I
      | unfold nx_regions0; repeat constructor | exact (nx_facts0_ok _ HE)]. }
  split; [exact HS|].
  apply (nx_land _ pc nx_sr NSH_ph 0 0 0 [] [] nx_facts0 HE HEI HS); [| reflexivity | | exact Hh].
  - apply (nx_sr_ok_std _ nx_sr HE); vm_compute; reflexivity.
  - unfold NSH_ph, nsh_set, NSH_entry. cbn. repeat constructor; lia.
Qed.

(* ---- the caller's struct as a region ---- *)
Lemma nx_ps_region_ok : forall E pw pcs, nx_env cx fp E -> 0 <= pw <= PS_LEN ->
  Forall (YP09.chunk_ok SEGS E M3 (n_ps cx)) pcs -> YP09.region_ok SEGS E M3 (nx_ps_region pw pcs).
Proof.
  intros E pw pcs HE Hpw Hcs.
  pose proof nxb_psfr as (Hin & Hlo & Hhi).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  pose proof nxb_J as (_ & _ & _ & _ & _ & Hfrc & _).
  pose proof HJ as (HAR3 & _).
  assert (Hin3 : In (n_cid cx, n_pos cx) (frames S3))
    by (rewrite HFR, Hfrc; right; apply in_or_app; left; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hpres & _).
  rewrite nx_frame_addr_eq in Hpres.
  unfold YP09.region_ok, nx_ps_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite (nx_ps_base E HE). unfold PS_LEN in *. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (n_ps cx + o) ltac:(lia))).
Qed.

(* The struct's fields as nx_ps_chunks: from nx_ps_at to the chunks (seat) and back (land). *)
Lemma nx_ps_chunks_ok : forall E m eh esw eol evt evid h sw ol vt vid pad pd0 pd1,
  nx_ps_at SEGS m (n_ps cx) h sw ol vt vid pad -> pad = [pd0; pd1] ->
  sv_denot E eh = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 ->
  sv_denot E esw = Z_to_bv 64 sw -> 0 <= sw < 2 ^ 32 ->
  sv_denot E eol = Z_to_bv 64 ol -> 0 <= ol < 2 ^ 32 ->
  sv_denot E evt = Z_to_bv 64 vt -> 0 <= vt < 2 ^ 32 ->
  sv_denot E evid = Z_to_bv 64 vid -> 0 <= vid < 2 ^ 16 ->
  Forall (YP09.chunk_ok SEGS E m (n_ps cx)) (nx_ps_chunks eh esw eol evt evid pd0 pd1).
Proof.
  intros E m eh esw eol evt evid h sw ol vt vid pad pd0 pd1 (Vf & Vs & Vo & Vt & Vi & Vp & Hl) -> Eh Rh Es Rs Eo Ro Et Rt Ei Ri.
  unfold nx_ps_chunks.
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E m (n_ps cx) PS_F_OFF 8%N eh h Eh); [cbn; lia | cbn; lia | exact Vf].
  - apply (chunk_ok_val SEGS E m (n_ps cx) PS_SW_OFF 4%N esw sw Es); [cbn; lia | cbn; lia | exact Vs].
  - apply (chunk_ok_val SEGS E m (n_ps cx) PS_OL_OFF 4%N eol ol Eo); [cbn; lia | cbn; lia | exact Vo].
  - apply (chunk_ok_val SEGS E m (n_ps cx) PS_VT_OFF 4%N evt vt Et); [cbn; lia | cbn; lia | exact Vt].
  - apply (chunk_ok_val SEGS E m (n_ps cx) PS_VID_OFF 2%N evid vid Ei); [cbn; lia | cbn; lia | exact Vi].
  - destruct (Vp 0%nat ltac:(cbn; lia)) as [V0 B0]. cbn [nth] in V0, B0.
    apply (chunk_ok_val SEGS E m (n_ps cx) 22 1%N (SLit pd0) pd0 eq_refl); [cbn; lia | cbn; lia |].
    cbn [N.to_nat]. rewrite Z.add_0_r in V0. exact V0.
  - destruct (Vp 1%nat ltac:(cbn; lia)) as [V1 B1]. cbn [nth] in V1, B1.
    apply (chunk_ok_val SEGS E m (n_ps cx) 23 1%N (SLit pd1) pd1 eq_refl); [cbn; lia | cbn; lia |].
    cbn [N.to_nat]. replace (n_ps cx + 23) with (n_ps cx + 22 + Z.of_nat 1) by lia. exact V1.
Qed.

Lemma nx_ps_at_of_region : forall E m pw eh esw eol evt evid h sw ol vt vid pd0 pd1,
  nx_env cx fp E ->
  YP09.region_ok SEGS E m (nx_ps_region pw (nx_ps_chunks eh esw eol evt evid pd0 pd1)) ->
  sv_denot E eh = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 ->
  sv_denot E esw = Z_to_bv 64 sw -> 0 <= sw < 2 ^ 32 ->
  sv_denot E eol = Z_to_bv 64 ol -> 0 <= ol < 2 ^ 32 ->
  sv_denot E evt = Z_to_bv 64 vt -> 0 <= vt < 2 ^ 32 ->
  sv_denot E evid = Z_to_bv 64 vid -> 0 <= vid < 2 ^ 16 ->
  0 <= pd0 < 256 -> 0 <= pd1 < 256 ->
  nx_ps_at SEGS m (n_ps cx) h sw ol vt vid [pd0; pd1].
Proof.
  intros E m pw eh esw eol evt evid h sw ol vt vid pd0 pd1 HE HR Eh Rh Es Rs Eo Ro Et Rt Ei Ri R0 R1.
  pose proof (nx_ps_base E HE) as U10. cbn [YP09.base_val] in U10.
  Local Ltac nx_fld HR U10 o w e v :=
    apply (field_of_region _ _ NA_PS _ _ 0 PS_LEN 0 _ o w e v HR U10);
    [ unfold nx_ps_chunks; cbn [In]; repeat (first [left; reflexivity | right]) | assumption | cbn; lia | cbn; lia ].
  split; [nx_fld HR U10 PS_F_OFF 8%N eh h|].
  split; [nx_fld HR U10 PS_SW_OFF 4%N esw sw|].
  split; [nx_fld HR U10 PS_OL_OFF 4%N eol ol|].
  split; [nx_fld HR U10 PS_VT_OFF 4%N evt vt|].
  split; [nx_fld HR U10 PS_VID_OFF 2%N evid vid|].
  split; [|reflexivity].
  intros j Hj. cbn [length] in Hj.
  destruct j as [|[|j]]; [| |lia]; cbn [nth Z.of_nat]; (split; [|lia]).
  - rewrite Z.add_0_r. apply (field_of_region E _ NA_PS _ _ 0 PS_LEN 0 _ 22 1%N (SLit pd0) pd0 HR U10);
      [ unfold nx_ps_chunks; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia ].
  - replace (n_ps cx + 22 + Z.of_nat 1) with (n_ps cx + 23) by lia.
    apply (field_of_region E _ NA_PS _ _ 0 PS_LEN 0 _ 23 1%N (SLit pd1) pd1 HR U10);
      [ unfold nx_ps_chunks; cbn [In]; repeat (first [left; reflexivity | right]) | reflexivity | cbn; lia | cbn; lia ].
Qed.

Lemma nx_ps_disj : forall E sf sh swlo swhi fw fcs pw pcs, nx_env cx fp E -> img_env VAL A_LIM E ->
  0 <= fw <= NX_FRAME -> 0 <= swlo -> swhi <= 8 ->
  Forall (fun r => YP09.all_disjoint E r [nx_ps_region pw pcs]) (nx_regions0 sf sh swlo swhi fw fcs).
Proof.
  intros E sf sh swlo swhi fw fcs pw pcs HE HEI Hfw Hwlo Hwhi.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
  pose proof nxb_psfr as (Hin & Hplo & Hphi).
  pose proof nxb_ps as (Hps8 & Hps4 & Hps47 & _).
  destruct (nx_own_off _ _ (n_ps cx) PS_LEN Hin Hplo Hphi ltac:(unfold PS_LEN; lia)) as (DF & D4 & Dc & Dapp & Dimg).
  pose proof (nx_bases E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  pose proof (nx_ps_base E HE) as U10.
  unfold nx_regions0.
  repeat apply Forall_cons; try apply Forall_nil; apply all_disjoint_of_extents;
    unfold nx_ps_region, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region,
      got_regionP, bcell_regionP, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint];
    rewrite ?U2, ?U60, ?U516, ?U529, ?U242, ?U256, ?U10;
    unfold zdisj; cbn [fst snd];
    unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, NX_SPILL, NX_FRAME, NX_STK_B,
      AFREAD_STK, PS_LEN, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *;
    repeat split; lia.
Qed.

(* ---- what a run keeps ---- *)

(* A run from a seated state writes only the windows of its regions. *)
Lemma nx_keep_out : forall E sf sh swlo swhi fw fcs extra (m m' : word -> option byte),
  nx_env cx fp E -> img_env VAL A_LIM E ->
  frame_of E (nx_regions sf sh swlo swhi fw fcs extra) (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  forall a, 0 <= a < 2 ^ 64 ->
  ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) -> ~ (nF cx fp <= a < nF cx fp + fw) ->
  ~ (nSH cx fp + swlo <= a < nSH cx fp + swhi) -> ~ in_wrange E extra a ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof.
  intros E sf sh swlo swhi fw fcs extra m m' HE HEI HF a Ha N1 N2 N3 N4.
  pose proof (nx_bases E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  apply (kept_of_frame E _ (w_H W3) m m'
    (fun x => (n_sp1 cx <= x < n_sp1 cx + NX_SPILL) \/ (nF cx fp <= x < nF cx fp + fw) \/
              (nSH cx fp + swlo <= x < nSH cx fp + swhi) \/ in_wrange E extra x) HF); [| exact Ha | tauto].
  intros b wlo whi x Hin Hr. unfold nx_regions, windows in Hin. rewrite map_app in Hin.
  apply in_app_or in Hin as [Hin|Hin].
  - unfold nx_regions0, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region,
      got_regionP, bcell_regionP in Hin.
    cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
    repeat (destruct Hin as [Hq|Hin];
      [injection Hq as <- <- <-; rewrite ?U2, ?U60, ?U516, ?U529, ?U242, ?U256 in Hr;
       first [exfalso; lia | left; lia | right; left; lia | right; right; left; lia] |]).
    destruct Hin.
  - right. right. right. apply in_map_iff in Hin as (r & Hq & Hr0). exists r. split; [exact Hr0|].
    injection Hq as <- <- <-. exact Hr.
Qed.

(* nx_mid's kept relation across a run from a seated state: the bytes the run wrote are its
   windows, which are this call's own (the spill slots in its stack window, its frame and the
   frame's shadow) or the extra regions' (Ew': the phase names them, and they are off the image). *)
Lemma nx_kept_step : forall E sf sh swlo swhi fw fcs extra (m m' : word -> option byte) (Ew Ew' : Z -> Prop),
  nx_env cx fp E -> img_env VAL A_LIM E ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 <= fw <= NX_FRAME -> 0 <= swlo -> swhi <= 8 ->
  frame_of E (nx_regions sf sh swlo swhi fw fcs extra) (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  mem_grows (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  (forall a, in_wrange E extra a -> Ew' a /\ ~ in_img SEGS a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W3) m' a) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m (spZ (n_regs cx)) Ew ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m' (spZ (n_regs cx))
    (fun a => Ew a \/ Ew' a).
Proof.
  intros E sf sh swlo swhi fw fcs extra m m' Ew Ew' HE HEI HBL Hfw Hwlo Hwhi HF HG HX Hpres
    (K1 & K2 & K3 & K4 & K5 & K6).
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & _).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof nxb_J as (HARc & _ & _ & _ & _ & Hfrc & _).
  pose proof HJ as (HAR3 & _).
  pose proof (nx_keep_out E sf sh swlo swhi fw fcs extra m m' HE HEI HF) as KO.
  assert (NX : forall a, ~ (Ew a \/ Ew' a) -> ~ in_wrange E extra a)
    by (intros a Hn Hw; apply Hn; right; exact (proj1 (HX a Hw))).
  unfold NX_FRAME in Hfw.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hn HnE.
    assert (D0 : 0 <= a < 2 ^ 64) by lia.
    assert (D1 : ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL)) by (unfold NX_SPILL, NX_STK_B, AFREAD_STK in *; lia).
    assert (D2 : ~ (nF cx fp <= a < nF cx fp + fw)) by lia.
    assert (D3 : ~ (nSH cx fp + swlo <= a < nSH cx fp + swhi)) by (unfold SHADOW_OFF in *; lia).
    rewrite (KO a D0 D1 D2 D3 (NX a HnE)).
    apply K1; [exact Ha | exact Hn | intros X; apply HnE; left; exact X].
  - intros b mm i Hin Hi HnE.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HARc Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
    assert (Hin3 : In (b, mm) (ablocks B ly3 S3)) by (rewrite HBL; exact Hin).
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ b mm NX_CID fp HAR3 Hin3 nx_fin) as Dbf.
    unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite nx_frame_addr_eq, nx_frame_bytes in Dbf.
    fold (nF cx fp) in Dbf.
    assert (D0 : 0 <= b + i < 2 ^ 64) by lia.
    assert (D1 : ~ (n_sp1 cx <= b + i < n_sp1 cx + NX_SPILL)) by (unfold NX_SPILL in *; lia).
    assert (D2 : ~ (nF cx fp <= b + i < nF cx fp + fw)) by lia.
    assert (D3 : ~ (nSH cx fp + swlo <= b + i < nSH cx fp + swhi))
      by (unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia).
    rewrite (KO (b + i) D0 D1 D2 D3 (NX _ HnE)).
    apply (K2 b mm i Hin Hi). intros X. apply HnE. left. exact X.
  - intros a Hi Hno Herr. pose proof (pa_img_range a Hi) as Hr. pose proof (pa_segs_low a Hi) as Hr2.
    assert (D0 : 0 <= a < 2 ^ 64) by (unfold kLowMemEnd in *; lia).
    assert (D1 : ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL)) by (unfold NX_SPILL, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
    assert (D2 : ~ (nF cx fp <= a < nF cx fp + fw)) by (unfold pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
    assert (D3 : ~ (nSH cx fp + swlo <= a < nSH cx fp + swhi)) by (unfold SHADOW_OFF, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia).
    rewrite (KO a D0 D1 D2 D3 (fun Hw => proj2 (HX a Hw) Hi)).
    exact (K3 a Hi Hno Herr).
  - intros cid pos a Hin Hr HnE.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hin) as (Hg0 & Hgc & Hgapp).
    pose proof (frame_al64 SEGS B _ _ _ _ _ cid pos HARc Hin) as (Hga64 & Hgb64 & Hgb).
    destruct (in_split _ _ Hin) as (l1 & l2 & El).
    assert (Heq : frames S3 = [] ++ (NX_CID, fp) :: l1 ++ (cid, pos) :: l2) by (rewrite HFR, El; reflexivity).
    pose proof (sep_frames_pos SEGS B LAWS _ _ _ _ _ (NX_CID, fp) (cid, pos) [] l1 l2 HAR3 Heq) as Dff.
    unfold zdisjoint, frame_rng in Dff. cbn [fst snd] in Dff. rewrite !nx_frame_addr_eq, nx_frame_bytes in Dff.
    fold (nF cx fp) in Dff.
    destruct (nx_div8_64 _ Hga64) as (Ga8 & Ga64). destruct (nx_div8_64 _ Hgb64) as (Gb8 & Gb64).
    destruct (nx_div8_64 _ H64) as (F8 & F64).
    set (fa := frame_addr (n_lyc cx) cid pos) in *. set (fb := fs_frame_bytes cid) in *.
    assert (Hdisj : ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) /\ ~ (nF cx fp <= a < nF cx fp + fw) /\
                    ~ (nSH cx fp + swlo <= a < nSH cx fp + swhi) /\ 0 <= a < 2 ^ 64).
    { unfold in_zr, frame_rng, shadow_addr in Hr. cbn [fst snd] in Hr. fold fa fb in Hr.
      rewrite HSHeq. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, NX_SPILL, NX_STK_B, AFREAD_STK in *.
      destruct Hr as [Hr|Hr]; repeat split; lia. }
    destruct Hdisj as (D1 & D2 & D3 & D4).
    rewrite (KO a D4 D1 D2 D3 (NX a HnE)).
    apply (K4 cid pos a Hin Hr). intros X. apply HnE. left. exact X.
  - intros a Ha Hn Hp. eapply apresent_grows; [exact HG | exact (K5 a Ha Hn Hp)].
  - exact Hpres.
Qed.


(* ---- the record buffer and the timestamp cell as regions (the open reader) ---- *)

Lemma nxb_ts : n_h cx <> 0 -> n_ts cx <> 0 ->
  n_ts cx mod 8 = 0 /\ 4096 <= n_ts cx /\ n_ts cx + 8 <= 2 ^ 47 /\ amem_range (n_ts cx) 8 /\
  (exists tcid tpos, In (tcid, tpos) (n_own cx) /\ frame_addr (n_lyc cx) tcid tpos <= n_ts cx /\
     n_ts cx + 8 <= frame_addr (n_lyc cx) tcid tpos + fs_frame_bytes tcid) /\
  (n_ts cx + 8 <= n_ps cx \/ n_ps cx + PS_LEN <= n_ts cx) /\
  (n_buf cx + nx_bufn (n_cap cx) <= n_ts cx \/ n_ts cx + 8 <= n_buf cx).
Proof.
  intros Hh Hn. pose proof HB as H. unfold nx_base in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hts & _).
  destruct (Hts Hh Hn) as (_ & H8 & H4 & H47 & Ham & Hfr & _ & _ & Hps & Hbuf). auto 8.
Qed.

Lemma nx_buf_region_ok : forall E n bw bcs, nx_env cx fp E -> n_h cx <> 0 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 <= bw <= n -> n <= nx_bufn (n_cap cx) ->
  Forall (YP09.chunk_ok SEGS E M3 (n_buf cx)) bcs -> YP09.region_ok SEGS E M3 (nx_buf_region n bw bcs).
Proof.
  intros E n bw bcs HE Hh HBL Hbw Hn Hcs.
  destruct (nxb_buf Hh) as (Hin & H4 & H63 & Hcap & _).
  assert (Hin3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite HBL; exact Hin).
  pose proof HJ as (HAR3 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & _ & _ & Hpres & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  assert (Ub : YP09.base_val E (Some NA_BUF) = n_buf cx).
  { cbn [YP09.base_val]. rewrite (nx_buf_atom E HE). apply unsigned_lit_small. unfold nx_bufn in *. lia. }
  unfold YP09.region_ok, nx_buf_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. unfold nx_bufn in *. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (n_buf cx + o) ltac:(lia))).
Qed.

Lemma nx_ts_region_ok : forall E tw tcs, nx_env cx fp E -> n_h cx <> 0 -> n_ts cx <> 0 ->
  0 <= tw <= 8 ->
  Forall (YP09.chunk_ok SEGS E M3 (n_ts cx)) tcs -> YP09.region_ok SEGS E M3 (nx_ts_region tw tcs).
Proof.
  intros E tw tcs HE Hh Hn Htw Hcs.
  destruct (nxb_ts Hh Hn) as (H8 & H4 & H47 & _ & (tcid & tpos & Hin & Hlo & Hhi) & _).
  pose proof nxb_J as (_ & _ & _ & _ & _ & Hfrc & _).
  pose proof HJ as (HAR3 & _).
  assert (Hin3 : In (tcid, tpos) (frames S3)) by (rewrite HFR, Hfrc; right; apply in_or_app; left; exact Hin).
  destruct (al_frames _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & _ & Hpres & _).
  rewrite nx_frame_addr_eq in Hpres.
  assert (Ub : YP09.base_val E (Some NA_TS) = n_ts cx).
  { cbn [YP09.base_val]. rewrite (nx_ts_atom E HE). apply unsigned_lit_small. lia. }
  unfold YP09.region_ok, nx_ts_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite Ub. split; [lia|]. split; [lia|]. split; [|exact Hcs].
  intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hpres (n_ts cx + o) ltac:(lia))).
Qed.

Local Ltac nx_disj_fin :=
  unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, SHADOW_OFF, NX_SPILL, NX_FRAME, NX_STK_B,
    AFREAD_STK, PS_LEN, pcap_img_end, YImgTop.IMG_LO, YImgTop.IMG_TOP, nx_bufn in *;
  repeat split; lia.

Lemma nx_buf_disj : forall E sf sh swlo swhi fw fcs n bw bcs, nx_env cx fp E -> img_env VAL A_LIM E ->
  n_h cx <> 0 -> ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  0 <= fw <= NX_FRAME -> 0 <= swlo -> swhi <= 8 -> 0 <= n <= nx_bufn (n_cap cx) ->
  Forall (fun r => YP09.all_disjoint E r [nx_buf_region n bw bcs]) (nx_regions0 sf sh swlo swhi fw fcs).
Proof.
  intros E sf sh swlo swhi fw fcs n bw bcs HE HEI Hh HBL Hfw Hwlo Hwhi Hn.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
  destruct (nxb_buf Hh) as (Hin & H4 & H63 & Hcap & _).
  pose proof nxb_J as (HARc & _).
  pose proof HJ as (HAR3 & _).
  assert (Hin3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite HBL; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hb4096 & Hbceil & Hbapp & _).
  pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hbo.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ NX_CID fp HAR3 Hin3 nx_fin) as Dbf.
  unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite nx_frame_addr_eq, nx_frame_bytes in Dbf.
  fold (nF cx fp) in Dbf.
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  pose proof (nx_bases E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  assert (U11 : YP09.base_val E (Some NA_BUF) = n_buf cx).
  { cbn [YP09.base_val]. rewrite (nx_buf_atom E HE). apply unsigned_lit_small. unfold nx_bufn in *. lia. }
  unfold nx_regions0.
  repeat apply Forall_cons; try apply Forall_nil; apply all_disjoint_of_extents;
    unfold nx_buf_region, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region,
      got_regionP, bcell_regionP, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint];
    rewrite ?U2, ?U60, ?U516, ?U529, ?U242, ?U256, ?U11;
    unfold zdisj; cbn [fst snd]; nx_disj_fin.
Qed.

Lemma nx_ts_disj : forall E sf sh swlo swhi fw fcs tw tcs, nx_env cx fp E -> img_env VAL A_LIM E ->
  n_h cx <> 0 -> n_ts cx <> 0 ->
  0 <= fw <= NX_FRAME -> 0 <= swlo -> swhi <= 8 ->
  Forall (fun r => YP09.all_disjoint E r [nx_ts_region tw tcs]) (nx_regions0 sf sh swlo swhi fw fcs).
Proof.
  intros E sf sh swlo swhi fw fcs tw tcs HE HEI Hh Hn Hfw Hwlo Hwhi.
  pose proof nx_sp_facts as (Hal & Hlo & Hhi & Hsp1 & Hsp32).
  pose proof nx_F_facts as (HF0 & HFc & HFia & HFo & H64 & HSHeq).
  pose proof nx_SH_range as (Hs0 & Hs1 & _).
  pose proof asan_consts as (Hac & Hhs & Hhb & Hhe & Hlm).
  pose proof (pa_obj_img 1 ltac:(lia)) as Ho1. pose proof (pa_obj_img 15 ltac:(lia)) as Ho15.
  destruct (nxb_ts Hh Hn) as (H8 & H4 & H47 & _ & (tcid & tpos & Hin & Htlo & Hthi) & _).
  destruct (nx_own_off _ _ (n_ts cx) 8 Hin Htlo Hthi ltac:(lia)) as (DF & D4 & Dc & Dapp & Dimg).
  pose proof (nx_bases E HE HEI) as (U2 & U60 & U516 & U529 & U242 & U256).
  assert (U13 : YP09.base_val E (Some NA_TS) = n_ts cx).
  { cbn [YP09.base_val]. rewrite (nx_ts_atom E HE). apply unsigned_lit_small. lia. }
  unfold nx_regions0.
  repeat apply Forall_cons; try apply Forall_nil; apply all_disjoint_of_extents;
    unfold nx_ts_region, nx_saved_region, nx_spill_region, nx_frame_region, nx_shadow_region,
      got_regionP, bcell_regionP, extent_of_region;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint];
    rewrite ?U2, ?U60, ?U516, ?U529, ?U242, ?U256, ?U13;
    unfold zdisj; cbn [fst snd]; nx_disj_fin.
Qed.

(* The three regions among themselves. *)
Lemma nx_ps_buf_disj : forall E pw pcs n bw bcs, nx_env cx fp E -> n_h cx <> 0 -> 0 <= n <= nx_bufn (n_cap cx) ->
  YP09.all_disjoint E (nx_ps_region pw pcs) [nx_buf_region n bw bcs].
Proof.
  intros E pw pcs n bw bcs HE Hh Hn.
  destruct (nxb_buf Hh) as (_ & H4 & H63 & _ & Hsep).
  pose proof nxb_ps as (_ & Hp4 & Hp47 & _).
  assert (U11 : YP09.base_val E (Some NA_BUF) = n_buf cx).
  { cbn [YP09.base_val]. rewrite (nx_buf_atom E HE). apply unsigned_lit_small. unfold nx_bufn in *. lia. }
  apply all_disjoint_of_extents. unfold nx_ps_region, nx_buf_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint]. rewrite (nx_ps_base E HE), U11.
  unfold zdisj. cbn [fst snd]. nx_disj_fin.
Qed.

Lemma nx_ps_ts_disj : forall E pw pcs tw tcs, nx_env cx fp E -> n_h cx <> 0 -> n_ts cx <> 0 ->
  YP09.all_disjoint E (nx_ps_region pw pcs) [nx_ts_region tw tcs].
Proof.
  intros E pw pcs tw tcs HE Hh Hn.
  destruct (nxb_ts Hh Hn) as (_ & H4 & H47 & _ & _ & Hps & _).
  pose proof nxb_ps as (_ & Hp4 & Hp47 & _).
  assert (U13 : YP09.base_val E (Some NA_TS) = n_ts cx).
  { cbn [YP09.base_val]. rewrite (nx_ts_atom E HE). apply unsigned_lit_small. lia. }
  apply all_disjoint_of_extents. unfold nx_ps_region, nx_ts_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint]. rewrite (nx_ps_base E HE), U13.
  unfold zdisj. cbn [fst snd]. nx_disj_fin.
Qed.

Lemma nx_buf_ts_disj : forall E n bw bcs tw tcs, nx_env cx fp E -> n_h cx <> 0 -> n_ts cx <> 0 ->
  0 <= n <= nx_bufn (n_cap cx) ->
  YP09.all_disjoint E (nx_buf_region n bw bcs) [nx_ts_region tw tcs].
Proof.
  intros E n bw bcs tw tcs HE Hh Hn Hnb.
  destruct (nxb_ts Hh Hn) as (_ & H4 & H47 & _ & _ & _ & Hbs).
  destruct (nxb_buf Hh) as (_ & Hb4 & H63 & _ & _).
  assert (U11 : YP09.base_val E (Some NA_BUF) = n_buf cx).
  { cbn [YP09.base_val]. rewrite (nx_buf_atom E HE). apply unsigned_lit_small. unfold nx_bufn in *. lia. }
  assert (U13 : YP09.base_val E (Some NA_TS) = n_ts cx).
  { cbn [YP09.base_val]. rewrite (nx_ts_atom E HE). apply unsigned_lit_small. lia. }
  apply all_disjoint_of_extents. unfold nx_buf_region, nx_ts_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zall_disjoint]. rewrite U11, U13.
  unfold zdisj. cbn [fst snd]. nx_disj_fin.
Qed.

(* The shadow entry of the timestamp cell (its 8 bytes are addressable when the caller asked for
   one). *)
Lemma nx_shent_ts : forall E m, nx_env cx fp E -> n_h cx <> 0 -> n_ts cx <> 0 ->
  range_addressable (rd_of SEGS m) SHADOW_OFF (n_ts cx) 8 ->
  shent_ok SEGS nx_Bx E m (mkSHE NA_TS 0 8).
Proof.
  intros E m HE Hh Hn HR. destruct (nxb_ts Hh Hn) as (_ & H4 & H47 & Ham & _).
  pose proof HE as (_ & Hsb & _).
  apply (nx_shent_ok E m NA_TS (n_ts cx) 0 8 Hsb (nx_ts_atom E HE)); [lia | lia | |].
  - rewrite Z.add_0_r, Z.sub_0_r. exact Ham.
  - rewrite Z.add_0_r, Z.sub_0_r. exact HR.
Qed.

End d.
End c.
End b.
End a.
