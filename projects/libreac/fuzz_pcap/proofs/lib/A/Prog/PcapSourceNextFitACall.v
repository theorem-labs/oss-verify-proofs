(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedSetupC), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/AD27.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedSetupC.v, with its module paths and module names changed; 1421 of its 1480 lines of code are new or changed and 596 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNextSkip.v, with its module paths and module names changed; 362 of its 407 lines of code are new or changed and 1435 lines of the source are left out. *)
(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the call transport of the fit-A
   phase across its __asan_memmove call.

   THE CALL (0x81cc0 .. 0x81ce4, rows NP_fit_ra -> NP_mm_ra -> NP_ts of PcapSourceNextDefs.v):
     a0 = buf + 12   `mv a0,a1` 0x81cd4 (a1 = buf + 12 from `addi a1,s4,0xc` 0x81c1c)
     a1 = buf + 16   `addi s4,s4,0x10` 0x81cb4; `mv a1,s4` 0x81cd8
     a2 = incl - 16  `addi a4,s9,-0x10` 0x81cc0; `slli a4,a4,0x20` 0x81cc4; `srli a2,a4,0x20` 0x81cd0
     `jal __asan_memmove` 0x81cdc (0x51bf0, 880 B, symtab of the unstripped twin; the runtime's own
     function, called directly: no interceptor trampoline and no real-function slot), ra = 0x81ce0;
     then `addi s9,s9,-4` 0x81ce0 and NP_ts 0x81ce4 (`beqz s5`).
   The callee writes the caller's buffer [buf + 12, buf + incl - 4) (the two ranges overlap) and its
   own ESTACK window below sp = s1 (YG0d.v:19); its contract is MemmoveDef.v's amemmove_realizes,
   applied inside the caller's journal by PcapSourceNextFitAHelp.v's aj_memmove_atS.

   - fa_mm_pre: what aj_memmove_atS asks of the destination and the source (both in the caller's
     record buffer, a heap block below the allocator's ceiling, so off the callee's stack window).
   - fa_mm_buf: the buffer after the call as a byte list, from the callee's post; its first incl
     bytes are the list PcapSourceNextFitABits.v's fa_mm_list states.
   - fa_mmr_run: the one slot NP_mm_ra -> NP_ts (`addi s9,s9,-4`), at the machine level.
   - fa_mm_call: the call, the slot, and the landing (PcapSourceNextFitALand.v's fa_land_ts), so
     that a state at the call reaches the post from nx_ts_inv at NP_ts. THE STATEMENT is a Theorem Labs lane's
     (text of 2026-10-29 05:56Z), stated here word for word.

   TAKEN FROM.
   - __asan_memmove: MemmoveDef.v amemmove_realizes (a Theorem Labs lane), applied by
     PcapSourceNextFitAHelp.v aj_memmove_atS (a Theorem Labs lane, a2aabd0a676), Required, not copied.
   - fa_mm_pre: the destination half follows lib/A's fa_call (PcapSourceNextFitA.v:504-545 on
     a2aabd0a676) and a Theorem Labs lane's nx_fread_buf_pre (PcapSourceNextSkipDefs.v:233-299 on a5de09c4afc):
     awr_byte_weaken of nx_base's nx_wr_ok, amem_range_sub_app, range_addressable_of_block,
     shadow_hull_vis_of_block; the source half (src_ok) is new: al_blocks' presence clause with
     aview_some_of_apresent.
   - fa_mm_buf: new; its list is PcapSourceNextFitABits.v fa_mm_list (b756f7b51d4), Required; the byte
     moves use YC88.garr8_aview (a Theorem Labs lane's YC88 family), as lib/B's fa_mm_bytes does
     (lib/B/Prog/PcapSourceNextFitAKit.v on a working branch 18f2df02f64).
   - fa_mmr_run: a Theorem Labs lane's ts_run (PcapSourceNextFitB.v:209-377 on a2aabd0a676): an all-atom seat with
     no region (pa_entry_st_ok_full), paj_run_to_tok, regs_kept_of_st_ok_pi, kept_of_frame.
   - fa_mm_call: lib/A's fa_call (the SRr_bind of a callee's contract, then the continuation
     NEXT), lib/B's sk_body_call / sk_fread_buf_post (PcapSourceNextSkipCall.v on
     a working branch 0aac3a54d6d) for the kept-bytes reasoning across the call, and
     PcapSourceNextFitALand.v fa_land_ts (540230b0f44), PcapSourceNextFitAModel.v fa_rec_tagged
     (d3292ab2561), PcapSourceNextFitAHelp.v fa_pres / fa_vm_kept / fa_garr8_kept, PaJournalFs.v
     same_but_materialized_fs, all Required.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017df0462bf382b3211837851bf801e792673b1cee0797cdca2a; symbols from its
   unstripped twin, capstone 5 disassembly next.dis (sha256 06286410ee55; internal record)). *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaJournalFs PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitAModel PcapSourceNextFitAHelp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC4b YC81 YC1g YC1h YC85 YC88 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitBDefs PcapSourceNextFitALand.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceNextFitABits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the symbolic state of the slot NP_mm_ra (0x81ce0): every register an atom, no region ---- *)
Definition mm_Bx : sv := SOff 32 0.
Definition mm_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition mm_facts : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ss_mmr : sstate := mkSS NP_mm_ra sr_atoms [] None mm_facts.
Definition mm_extra : list word := [Z_to_bv 64 SHADOW_OFF].
(* The registers the slot does not write: all but zero and s9. *)
Definition NX_MMR_KEEP : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24;
   26; 27; 28; 29; 30; 31]%bv.

Section w.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

(* ---------------------------------------------------------------------------------------------- *)
(* The buffer after the move                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

(* One byte read through two memories at two addresses that view the same byte. *)
Lemma fa_vm1_at : forall (W : world SEGS) (m m' : word -> option byte) a a' v,
  aview SEGS (w_H W) m' a' = aview SEGS (w_H W) m a ->
  val_mem SEGS (rdW W m) a 1 v -> 0 <= v < 256 -> val_mem SEGS (rdW W m') a' 1 v.
Proof.
  intros W m m' a a' v Ha Hv Hr.
  assert (G : garr8 SEGS (rdW W m) a [v]).
  { intros j Hj. cbn [length] in Hj. replace j with 0%nat by lia. cbn [nth]. rewrite Z.add_0_r.
    split; [exact Hv | exact Hr]. }
  assert (G' : garr8 SEGS (rdW W m') a' [v]).
  { apply (garr8_aview SEGS (w_H W) (w_H W) m m' a a' [v]); [|exact G].
    intros i Hi. cbn [length] in Hi. replace i with 0 by lia. rewrite !Z.add_0_r. exact Ha. }
  destruct (G' 0%nat ltac:(cbn; lia)) as [Hv' _]. cbn [nth] in Hv'. rewrite Z.add_0_r in Hv'. exact Hv'.
Qed.

(* The callee's post on the buffer: [buf + 12, buf + n - 4) reads what stood 4 bytes higher, every
   other byte of the buffer is kept. The list after the call has fa_mm_list's first n bytes. *)
Lemma fa_mm_buf : forall (W : world SEGS) (m m' : word -> option byte) buf (bj : list Z) (n : nat),
  (18 <= n)%nat -> (n <= length bj)%nat ->
  garr8 SEGS (rdW W m) buf bj ->
  (forall i, 0 <= i < Z.of_nat n - 16 ->
     aview SEGS (w_H W) m' (buf + 12 + i) = aview SEGS (w_H W) m (buf + 16 + i)) ->
  (forall a, buf <= a < buf + Z.of_nat (length bj) -> ~ (buf + 12 <= a < buf + 12 + (Z.of_nat n - 16)) ->
     aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
  exists bj', garr8 SEGS (rdW W m') buf bj' /\ length bj' = length bj /\
    firstn n bj' = firstn 12 (firstn n bj) ++ firstn (n - 16) (skipn 16 (firstn n bj))
                   ++ skipn (n - 4) (firstn n bj).
Proof.
  intros W m m' buf bj n Hn Hnl HG HMV HKP.
  set (f := fun i : nat => if ((12 <=? i) && (i <? n - 4))%nat then nth (i + 4) bj 0 else nth i bj 0).
  set (bj' := map f (seq 0 (length bj))).
  assert (Hl : length bj' = length bj) by (unfold bj'; rewrite length_map, length_seq; reflexivity).
  assert (Hnth : forall i, (i < length bj')%nat -> nth i bj' 0 = f i).
  { intros i Hi. rewrite Hl in Hi. unfold bj'.
    rewrite (nth_indep _ _ (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. reflexivity. }
  exists bj'. split; [|split; [exact Hl|]].
  - intros j Hj. rewrite (Hnth j Hj). pose proof Hj as Hj'. rewrite Hl in Hj'. unfold f.
    destruct (Nat.leb_spec 12 j) as [H12|H12]; destruct (Nat.ltb_spec j (n - 4)) as [H4|H4]; cbn [andb].
    + destruct (HG (j + 4)%nat ltac:(lia)) as [Hv Hr]. split; [|exact Hr].
      apply (fa_vm1_at W m m' (buf + Z.of_nat (j + 4))); [|exact Hv | exact Hr].
      replace (buf + Z.of_nat j) with (buf + 12 + (Z.of_nat j - 12)) by lia.
      replace (buf + Z.of_nat (j + 4)) with (buf + 16 + (Z.of_nat j - 12)) by lia.
      apply HMV. lia.
    + destruct (HG j Hj') as [Hv Hr]. split; [|exact Hr].
      apply (fa_vm1_at W m m' (buf + Z.of_nat j)); [|exact Hv | exact Hr].
      apply HKP; lia.
    + destruct (HG j Hj') as [Hv Hr]. split; [|exact Hr].
      apply (fa_vm1_at W m m' (buf + Z.of_nat j)); [|exact Hv | exact Hr].
      apply HKP; lia.
    + destruct (HG j Hj') as [Hv Hr]. split; [|exact Hr].
      apply (fa_vm1_at W m m' (buf + Z.of_nat j)); [|exact Hv | exact Hr].
      apply HKP; lia.
  - apply (PcapSourceNextFitABits.fa_mm_list bj bj' n Hn Hnl Hl).
    intros i Hi. rewrite (Hnth i Hi). reflexivity.
Qed.

Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AMM : MemmoveDef.amemmove_realizes SEGS B (SIGMA PS___asan_memmove).
Let RUNTO := paj_run_to B LAWS.

(* ---------------------------------------------------------------------------------------------- *)
(* What the callee asks of the destination and the source                                           *)
(* ---------------------------------------------------------------------------------------------- *)

(* Both ranges lie in the caller's record buffer: a live heap block (so the bytes are present,
   addressable, writable by the caller and not owned by anybody else) below the allocator's
   ceiling, while the callee's window [sp1 - ESTACK, sp1) lies above it (sp1 >= sp - 256 and
   alloc_ceiling + NX_STK <= sp, NX_STK = 8496). *)
Lemma fa_mm_pre : forall cx fp k2 ly3 S3 W3 memT mdT n,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 memT mdT k2 ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  16 <= n <= n_cap cx ->
  (forall a, n_buf cx + 12 <= a < n_buf cx + 12 + (n - 16) ->
     awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B ly3 S3) ly3
       ((NX_CID, fp) :: n_own cx) a /\ ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx)) /\
  amem_range (n_buf cx + 12) (n - 16) /\
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (n_buf cx + 12) (n - 16) /\
  (0 < n - 16 -> shadow_hull_vis (aview SEGS (w_H W3) memT) (n_buf cx + 12) (n - 16)) /\
  (forall a, n_buf cx + 16 <= a < n_buf cx + 16 + (n - 16) ->
     aview SEGS (w_H W3) memT a <> None /\ ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx)) /\
  amem_range (n_buf cx + 16) (n - 16) /\
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF (n_buf cx + 16) (n - 16) /\
  (0 < n - 16 -> shadow_hull_vis (aview SEGS (w_H W3) memT) (n_buf cx + 16) (n - 16)) /\
  0 <= n_buf cx + 12 /\ n_buf cx + 12 + (n - 16) <= 2 ^ 63 /\
  0 <= n_buf cx + 16 /\ n_buf cx + 16 + (n - 16) <= 2 ^ 63.
Proof.
  intros cx fp k2 ly3 S3 W3 memT mdT n HB Hh HJ Hab Hn.
  pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBUFB & _ & _ & _ & _ & _).
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : alloc_ceiling + NX_STK <= spZ (n_regs cx) <= 2 ^ 47)
    by (clear - Hceil Hslo Hshi H47 Hwlo Hwhi; lia).
  assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224)
    by (unfold n_sp1; apply fl_sp1_range).
  destruct (HBUFB Hh) as (Hbin & Hb4096 & Hb63 & _ & _ & Hcap & HWRbuf & _).
  assert (Hbin3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab; exact Hbin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & _ & Hbceil & Hbapp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hbin3) as (_ & _ & _ & _ & Hbpres & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & Hrq).
  assert (Hbn : n <= nx_bufn (n_cap cx)) by (unfold nx_bufn; lia).
  assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
  { intros c p. rewrite (frame_addr_layout_le _ _ _ Hly3 c p). symmetry. exact (frame_addr_layout_le _ _ _ Hly0 c p). }
  assert (Hblc : forall x, In x (ablocks B (n_lyc cx) (n_Sc cx)) -> In x (ablocks B ly3 S3))
    by (intros x Hx; rewrite Hab; exact Hx).
  assert (Hown : forall x, In x (n_own cx) -> In x ((NX_CID, fp) :: n_own cx)) by (intros x Hx; right; exact Hx).
  assert (Hwin : forall a, n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx) -> ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx)).
  { intros a Ha. clear - Ha Hbceil Hrq Hsp Hsp1 HNX HES. lia. }
  split.
  { intros a Ha. split; [|apply Hwin; lia].
    apply (awr_byte_weaken _ _ _ _ _ _ _ _ _ _ a Hblc Hown EFA). apply (proj1 (HWRbuf a ltac:(lia))). }
  split.
  { apply (amem_range_sub_app (n_buf cx) (req_size (nx_bufn (n_cap cx)))); [exact Hbapp | lia | lia | lia | lia]. }
  split.
  { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 memT mdT (n_buf cx) (nx_bufn (n_cap cx)));
      [exact HAR3 | exact Hbin3 | lia | lia]. }
  split.
  { intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 memT mdT (n_buf cx) (nx_bufn (n_cap cx)));
      [exact HAR3 | exact Hbin3 | lia | lia | exact Hn0]. }
  split.
  { intros a Ha. split; [|apply Hwin; lia].
    apply (aview_some_of_apresent SEGS). apply (proj1 (Hbpres a ltac:(lia))). }
  split.
  { apply (amem_range_sub_app (n_buf cx) (req_size (nx_bufn (n_cap cx)))); [exact Hbapp | lia | lia | lia | lia]. }
  split.
  { apply (range_addressable_of_block SEGS B LAWS ly3 S3 W3 memT mdT (n_buf cx) (nx_bufn (n_cap cx)));
      [exact HAR3 | exact Hbin3 | lia | lia]. }
  split.
  { intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 memT mdT (n_buf cx) (nx_bufn (n_cap cx)));
      [exact HAR3 | exact Hbin3 | lia | lia | exact Hn0]. }
  clear - Hb4096 Hb63 Hbn Hn. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The slot NP_mm_ra -> NP_ts                                                                       *)
(* ---------------------------------------------------------------------------------------------- *)

(* `addi s9,s9,-4` (0x81ce0): the record lost its 4-byte tag, so its length in the buffer is
   incl - 4. No other register and no byte changes. *)
Lemma fa_mmr_run : forall (W3 : world SEGS) (ms : machine_state) (md : Model)
  STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms) md k2 ->
  ms = mkst (ms_regs ms) (w64 (BASE + NP_mm_ra)) (ms_mem ms) (seg_rom SEGS) ->
  (forall ms' md',
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms') md' k2 ->
     ms' = mkst (ms_regs ms') (w64 (BASE + NP_ts)) (ms_mem ms') (seg_rom SEGS) ->
     (forall r, In r NX_MMR_KEEP -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
     getr (ms_regs ms') 25 = Z_to_bv 64 (bv_unsigned (getr (ms_regs ms) 25) - 4) ->
     (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
     mem_grows (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
     m_fds md' = m_fds md -> m_fs md' = m_fs md ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms md) Q.
Proof.
  intros W3 ms md STK sp0 FP ly S W0 mem0 md0 own ly3 S3 k2 Q HJ Hms HK.
  assert (Hrs : restrict (w_H W3) ms =
                mkst (ms_regs ms) (Z_to_bv 64 (BASE + NP_mm_ra)) (rdW W3 (ms_mem ms)) (seg_rom SEGS)).
  { rewrite Hms at 1. reflexivity. }
  set (E := Eimg (Ereg (ms_regs ms) mm_extra)).
  assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms) mm_extra) n)
    by (intros n Hn; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms) mm_extra) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | reflexivity]).
  assert (E25 : ew E 25 = getr (ms_regs ms) 25)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  (* the landing, for the state the run leaves at NP_ts *)
  assert (LAND : forall ss (ms' : machine_state) mat,
    st_ok_pi SEGS VAL E ss (restrict (w_H W3) ms') -> ss_resv ss = None -> ss_pc ss = NP_ts ->
    forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) NX_MMR_KEEP = true ->
    sr_get (ss_regs ss) 25 = SOff 25 (-4) ->
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly3 S3 W3 (ms_mem ms') (with_vm_backing (m_vm_lazy md) mat md) k2 ->
    (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
    mem_grows (rdW W3 (ms_mem ms)) (rdW W3 (ms_mem ms')) ->
    SRr SEGS W3 (mkCfg ms' (with_vm_backing (m_vm_lazy md) mat md)) Q).
  { intros ss ms' mat HS' Hrv Hpc' Hkeep H25 HJ' HUN HG'.
    apply (HK ms' _ HJ').
    - pose proof (st_ok_pi_restrict_mkst (w_H W3) E ss ms' HS' Hrv) as Hsh. rewrite Hpc' in Hsh. exact Hsh.
    - intros r Hr. pose proof (regs_kept_of_st_ok_pi E ss _ (ms_regs ms) mm_extra NX_MMR_KEEP HS' HAE Hkeep r Hr) as Hk.
      cbn [restrict ms_regs] in Hk. exact Hk.
    - pose proof (st_ok_pi_restrict_reg (w_H W3) E ss ms' 25%bv HS') as R. rewrite H25 in R.
      cbn [sv_denot] in R. rewrite E25 in R. rewrite R. f_equal; lia.
    - exact HUN.
    - exact HG'.
    - destruct md. reflexivity.
    - destruct md. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL E ss_mmr (restrict (w_H W3) ms)).
  { rewrite Hrs. unfold ss_mmr. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - apply pairwise_disjoint_of_extents. cbn. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [mm_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32. unfold SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia]. }
  assert (SHOK : sh_ok SEGS mm_Bx [] E (rdW W3 (ms_mem ms))) by (unfold sh_ok; apply Forall_nil).
  clearbody E.
  paj_run_to_tok RUNTO HS HJ SHOK mm_span NP_ts.
  - lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_nil.
  - eapply LAND; [exact HS | reflexivity | reflexivity | vm_compute; reflexivity | reflexivity | exact HJ | | exact HG].
    intros a Ha. apply (kept_of_frame E _ (w_H W3) _ _ (fun _ => False) HFr); [| exact Ha | intros []].
    intros bb wlo whi aa Hin Hrr. vm_compute in Hin. destruct Hin.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The call, the slot and the landing                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Ltac mm_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end;
  clear; lia.
Ltac mm_keep := unfold NX_MMR_KEEP; cbn [In]; repeat (first [left; reflexivity | right]).

(* THE STATEMENT is a Theorem Labs lane's (the consumer; text of 05:56Z): from the state AT `jal __asan_memmove`
   (0x81cdc), reached from the cut at NP_fit_ra (ms3, md3) by the stores to ps->vtag / ps->vid only
   ([ps + 16, ps + 22)), the call (aj_memmove_atS), the slot NP_mm_ra -> NP_ts (fa_mmr_run) and the
   landing (fa_land_ts) reach the post through NP_ts (NEXT). *)
Lemma fa_mm_call : forall cx fp k2 ly3 S3 W3 ms3 md3 q bj' (rg : bvmap 5 word) (mem : word -> option byte) (mdq : Model),
  let sw := n_sw cx =? 1 in let F := nxF (n_C cx) in let incl := PSN.incl sw F q in
  nx_from SK B KS (nx_post SK B MT KS) (nx_ts_inv B MT KS) ->
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem mdq k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw F q) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q -> nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q -> n_p cx <= q ->
  0 < incl <= n_cap cx -> q + 16 + incl <= Z.of_nat (length (n_C cx)) -> PSN.tagged sw F q = true ->
  garr8 SEGS (rdW W3 (ms_mem ms3)) (n_buf cx) bj' -> length bj' = length (n_bj cx) ->
  firstn (Z.to_nat incl) bj' = firstn (Z.to_nat incl) (skipn (Z.to_nat (q + 16)) (n_C cx)) ->
  getr rg 1 = Z_to_bv 64 (BASE + NP_mm_ra) -> getr rg 10 = w64 (n_buf cx + 12) -> getr rg 11 = w64 (n_buf cx + 16) -> getr rg 12 = w64 (incl - 16) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 24]%bv -> getr rg r = getr (ms_regs ms3) r) ->
  getr rg 21 = w64 (n_ts cx) -> getr rg 25 = w64 incl ->
  bv_unsigned (getr rg 26) mod 2 ^ 32 = PSN.hw sw F q 0 -> bv_unsigned (getr rg 23) mod 2 ^ 32 = PSN.hw sw F q 4 ->
  m_fds mdq = m_fds md3 -> m_fs mdq = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + 16 <= a < n_ps cx + 22) -> aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) mem a) ->
  val_mem SEGS (rdW W3 mem) (n_ps cx + 16) 4 1 -> val_mem SEGS (rdW W3 mem) (n_ps cx + 20) 2 (PSN.rec_vid F q) ->
  SRr SEGS W3 (mkCfg (mkst rg (Z_to_bv 64 (SIGMA PS___asan_memmove)) mem (seg_rom SEGS)) mdq) (nx_post SK B MT KS cx).
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 q bj3 rg memT mdT. cbv zeta.
  intros NEXT HB HJ HFR HM Hq Hlh Hpq Hincl Hfit Ht Hg3 Hl3 Hp3
    R1 R10 R11 R12 RK R21 R25 R26 R23 HfdT HfsT HUT HPT Vvt Vvid.
  (* ---- the cut at NP_fit_ra ---- *)
  pose proof HM as (HBD & _ & HJBK & _ & _ & Hh & _ & _ & HSRC & _ & _ & _).
  pose proof HJBK as (_ & Hab & _ & _ & _).
  pose proof HBD as ((_ & _ & _ & _ & _ & _ & (G2 & _ & _ & G3 & G4) & _) & _).
  (* ---- nx_base ---- *)
  pose proof HB as (HJ0 & _ & _ & _ & Hgp & Htp & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _
    & _ & _ & _ & _ & Hps4 & Hps47 & _ & Hpsown & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & _ & HSTR & _ & _ & _).
  pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _ & Hstk0 & _).
  pose proof Hstk0 as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK = 8496) by reflexivity.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (Hsp : alloc_ceiling + NX_STK <= spZ (n_regs cx) <= 2 ^ 47)
    by (clear - Hceil Hslo Hshi H47 Hwlo Hwhi; lia).
  assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224)
    by (unfold n_sp1; apply fl_sp1_range).
  destruct (HBUFB Hh) as (Hbin & Hb4096 & Hb63 & _ & Hlbj0 & Hcap & _ & Hbps).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hbin) as (_ & _ & Hbceil & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; clear; lia)) as (_ & Hrq).
  destruct (HSTR Hh) as (_ & _ & _ & _ & Hp0 & _).
  assert (Hpsin : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
    by (rewrite Hfrs0; apply in_or_app; left; exact Hpsown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hpsin) as (_ & Hpfceil & _).
  assert (Hpsceil : n_ps cx + PS_LEN <= alloc_ceiling) by (clear - Hpsf2 Hpfceil; lia).
  (* ---- the model ---- *)
  assert (HC : bytes_ok (n_C cx)).
  { destruct HSRC as (Wn & cpos & fl & mdd & HSR). cbv zeta in HSR.
    destruct HSR as (_ & _ & _ & _ & _ & _ & _ & HC & _). exact HC. }
  assert (Hq0 : 0 <= q) by (clear - Hpq Hp0; lia).
  assert (Hroom : q + 16 <= Z.of_nat (length (n_C cx))) by (clear - Hfit Hincl; lia).
  assert (Hrec : nx_rec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) =
    firstn 12 (fa_raw (n_sw cx =? 1) (n_C cx) q)
    ++ firstn (Z.to_nat (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q - 16)) (skipn 16 (fa_raw (n_sw cx =? 1) (n_C cx) q))
    ++ skipn (Z.to_nat (PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q - 4)) (fa_raw (n_sw cx =? 1) (n_C cx) q))
    by (eapply fa_rec_tagged; eassumption).
  assert (H18 : 18 <= PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q).
  { pose proof Ht as Ht'. unfold PSN.tagged in Ht'. apply andb_prop in Ht' as [Ht1 _].
    apply andb_prop in Ht1 as [Ht1 _]. apply Z.leb_le in Ht1. exact Ht1. }
  assert (Hrl : PSN.rec_len (n_sw cx =? 1) (nxF (n_C cx)) q = PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q - 4)
    by (unfold PSN.rec_len; rewrite Ht; reflexivity).
  unfold fa_raw in Hrec. rewrite <- Hp3 in Hrec.
  set (incl := PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q) in *.
  assert (Hbn : incl <= nx_bufn (n_cap cx)) by (clear - Hincl; unfold nx_bufn; lia).
  assert (Hcap' : n_cap cx <= 2040) by (clear - Hcap; unfold NX_CAP_MAX in Hcap; lia).
  (* ---- the registers at the call ---- *)
  assert (Hspc : spZ rg = n_sp1 cx).
  { unfold spZ. rewrite (RK 2%bv ltac:(cbn; tauto)), G2. apply unsigned_lit_small. clear - Hsp Hsp1 C1 HNX. lia. }
  assert (Hal : (n_sp1 cx - n_sp0 cx) mod 16 = 0).
  { unfold n_sp1, nx_sp1. pose proof (Z.div_mod (n_sp0 cx) 16 ltac:(clear; lia)) as D.
    rewrite Hsp0al, Z.add_0_r in D. rewrite D.
    replace (32 * ((spZ (n_regs cx) - NX_MFRAME) / 32) - 16 * (n_sp0 cx / 16))
      with ((2 * ((spZ (n_regs cx) - NX_MFRAME) / 32) - n_sp0 cx / 16) * 16) by ring.
    apply Z_mod_mult. }
  (* ---- the callee's premises ---- *)
  destruct (fa_mm_pre cx fp k2 ly3 S3 W3 memT mdT incl HB Hh HJ Hab ltac:(clear - H18 Hincl; lia))
    as (Pd & Pamd & Prad & Phd & Ps & Pamx & Prax & Phx & Pd0 & Pdn & Px0 & Pxn).
  eapply SRr_bind.
  { refine (aj_memmove_atS SEGS B LAWS pa_segs_low (SIGMA PS___asan_memmove) AMM W3 rg memT
      (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 mdT k2 (n_buf cx + 12) (n_buf cx + 16) (incl - 16)
      (n_sp1 cx - n_sp0 cx) (getr rg 1) HJ R10 R11 R12 ltac:(clear - H18 Hincl Hcap'; lia) Pd0 Pdn
      ltac:(rewrite Hspc; clear; lia) Hal
      ltac:(clear - Hsp1 Hwhi; lia) ltac:(clear - HES Hwlo HNX Hsp1; lia)
      _ _ eq_refl _ _ Pamd Prad Phd Px0 Pxn _ Pamx Prax Phx).
    - rewrite (RK 3%bv ltac:(cbn; tauto)), G3. exact Hgp.
    - rewrite (RK 4%bv ltac:(cbn; tauto)), G4. exact Htp.
    - rewrite R1. apply ret_ok_codeptr_v; [unfold NP_mm_ra; clear; lia | reflexivity].
    - intros a Ha. destruct (Pd a Ha) as [Pw Pn]. split; [exact Pw|].
      replace (n_sp0 cx + (n_sp1 cx - n_sp0 cx)) with (n_sp1 cx) by ring. exact Pn.
    - intros a Ha. rewrite Hspc. exact (Ps a Ha). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hmv & Hkp & Hpr & Hsame).
  rewrite R1.
  apply (fa_mmr_run W3 (mkst regs2 (Z_to_bv 64 (BASE + NP_mm_ra)) mem2 (seg_rom SEGS)) md2
    (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 k2 _ HJ2 eq_refl).
  cbn [ms_regs ms_mem mkst].
  intros ms' md' HJ' Hms' Hkeep H25 Hmem HG' Hfd' Hfs'.
  (* ---- what the call and the slot kept ---- *)
  assert (P : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr rg r)
    by (apply fa_pres; exact HP).
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx)) ->
    ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx) ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) memT a).
  { intros a Ha Hna Hnw. rewrite (Hmem a Ha). apply Hkp; [exact Ha | clear - Hna Hbn H18; lia | clear - Hnw; lia]. }
  assert (KP : forall x, n_ps cx + 16 <= x < n_ps cx + 22 ->
    aview SEGS (w_H W3) (ms_mem ms') x = aview SEGS (w_H W3) memT x).
  { intros x Hx. rewrite (Hmem x ltac:(clear - Hx Hps4 Hps47; unfold PS_LEN in *; lia)). apply Hkp.
    - clear - Hx Hps4 Hps47. unfold PS_LEN in *. lia.
    - clear - Hx Hbps Hbn H18. unfold PS_LEN, nx_bufn in *. lia.
    - clear - Hx Hpsceil Hsp Hsp1 HNX HES. unfold PS_LEN in *. lia. }
  assert (Hg4 : garr8 SEGS (rdW W3 memT) (n_buf cx) bj3).
  { apply (fa_garr8_kept W3 W3 (ms_mem ms3) memT); [|exact Hg3].
    intros x Hx. rewrite Hl3 in Hx. apply HUT.
    - clear - Hx Hlbj0 Hb4096 Hb63. lia.
    - clear - Hx Hlbj0 Hbps. unfold PS_LEN, nx_bufn in *. lia. }
  assert (HMV4 : forall i, 0 <= i < Z.of_nat (Z.to_nat incl) - 16 ->
    aview SEGS (w_H W3) (ms_mem ms') (n_buf cx + 12 + i) = aview SEGS (w_H W3) memT (n_buf cx + 16 + i)).
  { intros i Hi. rewrite Z2Nat.id in Hi by (clear - H18; lia).
    rewrite (Hmem (n_buf cx + 12 + i) ltac:(clear - Hi Hb4096 Hb63 Hbn; lia)).
    exact (Hmv i ltac:(clear - Hi; lia)). }
  assert (HKP4 : forall a, n_buf cx <= a < n_buf cx + Z.of_nat (length bj3) ->
    ~ (n_buf cx + 12 <= a < n_buf cx + 12 + (Z.of_nat (Z.to_nat incl) - 16)) ->
    aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) memT a).
  { intros a Ha Hna. rewrite Z2Nat.id in Hna by (clear - H18; lia). rewrite Hl3 in Ha.
    rewrite (Hmem a ltac:(clear - Ha Hlbj0 Hb4096 Hb63; lia)).
    apply Hkp; [clear - Ha Hlbj0 Hb4096 Hb63; lia | exact Hna |].
    clear - Ha Hlbj0 Hbceil Hrq Hsp Hsp1 HNX HES. lia. }
  destruct (fa_mm_buf W3 memT (ms_mem ms') (n_buf cx) bj3 (Z.to_nat incl) ltac:(clear - H18; lia)
    ltac:(clear - Hl3 Hlbj0 Hbn; lia) Hg4 HMV4 HKP4) as (bj4 & Hg4' & Hl4 & Hf4).
  replace (Z.to_nat (incl - 16)) with (Z.to_nat incl - 16)%nat in Hrec by (clear - H18; lia).
  replace (Z.to_nat (incl - 4)) with (Z.to_nat incl - 4)%nat in Hrec by (clear - H18; lia).
  rewrite <- Hf4 in Hrec.
  (* ---- the landing ---- *)
  apply (NEXT cx fp k2 ly3 S3 W3 ms' md' HB HJ' HFR).
  apply (fa_land_ts B MT KS LAWS ASIL cx fp k2 ly3 S3 W3 ms3 md3 ms' md' q bj4 HB HJ' HFR HM Hq Hlh Hpq
    Hincl Hfit).
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - rewrite Hms'. reflexivity.
  - intros r Hr. rewrite (Hkeep r ltac:(repeat (destruct Hr as [<- | Hr]; [mm_keep |]); destruct Hr)).
    rewrite (P r ltac:(repeat (destruct Hr as [<- | Hr]; [mm_cs |]); destruct Hr)). exact (RK r Hr).
  - rewrite (Hkeep 21%bv ltac:(mm_keep)), (P 21%bv ltac:(mm_cs)). exact R21.
  - rewrite H25, (P 25%bv ltac:(mm_cs)), R25, Hrl. unfold w64.
    rewrite (unsigned_lit_small incl) by (clear - Hincl Hcap'; lia).
    rewrite unsigned_lit_small by (clear - H18 Hincl Hcap'; lia).
    apply Z.mod_small. clear - H18 Hincl Hcap'. lia.
  - rewrite (Hkeep 26%bv ltac:(mm_keep)), (P 26%bv ltac:(mm_cs)). exact R26.
  - rewrite (Hkeep 23%bv ltac:(mm_keep)), (P 23%bv ltac:(mm_cs)). exact R23.
  - rewrite Hfd', (proj1 (same_but_materialized_fs mdT md2 Hsame)). exact HfdT.
  - rewrite Hfs', (proj2 (same_but_materialized_fs mdT md2 Hsame)). exact HfsT.
  - intros a Ha H1 H2 H3. rewrite (KM a Ha H2 H3). exact (HUT a Ha H1).
  - intros a Hp. apply (apresent_grows _ _ _ _ HG'). apply Hpr. apply HPT. exact Hp.
  - rewrite Ht. apply (fa_vm_kept W3 W3 memT (ms_mem ms') _ 4 _); [|exact Vvt].
    intros x Hx. change (Z.of_nat 4) with 4 in Hx. apply KP. clear - Hx. lia.
  - rewrite Ht. apply (fa_vm_kept W3 W3 memT (ms_mem ms') _ 2 _); [|exact Vvid].
    intros x Hx. change (Z.of_nat 2) with 2 in Hx. apply KP. clear - Hx. lia.
  - exact Hg4'.
  - rewrite Hl4. exact Hl3.
  - rewrite Hrec. rewrite length_firstn, Nat.min_l by (clear - Hl4 Hl3 Hlbj0 Hbn; lia). reflexivity.
Qed.

End w.
