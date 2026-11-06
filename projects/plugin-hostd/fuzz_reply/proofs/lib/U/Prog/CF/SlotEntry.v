(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v, with its addresses and numbers changed; 1611 of its 1721 lines of code are new or changed and 561 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass1w.v, with its module paths and module names changed; 712 of its 801 lines of code are new or changed and 1632 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO0x YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Spec Require StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack AllocPackRoom AllocPack3 SlotPack3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept SlotInv SlotSteps SlotRes SlotRI3 SlotNcWt ListFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRunT RelayRunF.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessTr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_add_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessFrame SlotEntryRun SlotMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma entry_errno_image : forall B, ms_segs B = rsegs -> ms_tp B = 0x31b70 -> ms_errno_off B = -164 ->
  forall a, errno_addr B <= a < errno_addr B + 4 ->
  in_img B a /\ wview rsegs (fun _ => None) (wa a) <> None /\ seg_rom rsegs (wa a) <> None.
Proof.
  intros B SEG TP OFF a HA. unfold errno_addr in HA. rewrite TP, OFF in HA.
  split.
  - assert (C : existsb (fun s : word * word => (bv_unsigned (fst s) <=? 0x31acc) &&
        (0x31ad0 <=? bv_unsigned (fst s) + bv_unsigned (snd s))) (segments_reserved rsegs) = true)
      by (vm_compute; reflexivity).
    apply existsb_exists in C as (s & HS & HB). apply andb_prop in HB as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    unfold in_img. rewrite SEG. split; [intros EQ; rewrite EQ in HS; destruct HS|].
    exists s. split; [exact HS|lia].
  - assert (C : forallb (fun i =>
        match wview rsegs (fun _ => None) (wa (0x31acc + i)), seg_rom rsegs (wa (0x31acc + i)) with
        | Some _, Some _ => true | _, _ => false end) (map Z.of_nat (seq 0 4)) = true)
      by (vm_compute; reflexivity).
    pose proof (zseq_forall _ _ C (a - 0x31acc) ltac:(cbn; lia)) as H.
    change (match wview rsegs (fun _ => None) (wa (0x31acc + (a - 0x31acc))),
                  seg_rom rsegs (wa (0x31acc + (a - 0x31acc))) with
            | Some _, Some _ => true | _, _ => false end = true) in H.
    replace (0x31acc + (a - 0x31acc)) with a in H by lia.
    destruct (wview rsegs (fun _ => None) (wa a)) as [v|] eqn:W;
      destruct (seg_rom rsegs (wa a)) as [u|] eqn:R; cbn in H; try congruence.
    split; congruence.
Qed.

Lemma entry_errno_access : forall B, ms_segs B = rsegs -> ms_tp B = 0x31b70 -> ms_errno_off B = -164 ->
  forall m a, errno_addr B <= a < errno_addr B + 4 ->
  writable_at rsegs m a /\ exists v, mbyte rsegs m a = Some v.
Proof.
  intros B SEG TP OFF m a HA. destruct (entry_errno_image B SEG TP OFF a HA) as (_ & W & R).
  unfold writable_at, wview, mbyte, wa in *. destruct (m (Z_to_bv 64 a)) as [v|] eqn:M.
  - split; [discriminate|exists v; reflexivity].
  - split; [exact W|]. change (exists v, seg_rom rsegs (Z_to_bv 64 a) = Some v).
    destruct (seg_rom rsegs (Z_to_bv 64 a)) as [v|]; [exists v; reflexivity|contradiction].
Qed.

Lemma entry_errno_cells : forall B, ms_segs B = rsegs -> ms_tp B = 0x31b70 -> ms_errno_off B = -164 ->
  forall m, exists ev, rw_cells rsegs m (errno_addr B) [C4 ev].
Proof.
  intros B SEG TP OFF m.
  assert (EA : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite TP, OFF; reflexivity).
  destruct (entry_errno_access B SEG TP OFF m (errno_addr B) ltac:(lia)) as (_ & b0 & B0).
  destruct (entry_errno_access B SEG TP OFF m (errno_addr B + 1) ltac:(lia)) as (_ & b1 & B1).
  destruct (entry_errno_access B SEG TP OFF m (errno_addr B + 2) ltac:(lia)) as (_ & b2 & B2).
  destruct (entry_errno_access B SEG TP OFF m (errno_addr B + 3) ltac:(lia)) as (_ & b3 & B3).
  pose proof (bytes_le_to_Z_bound [b0; b1; b2; b3]) as N1. pose proof (bytes_le_to_Z_nonneg [b0; b1; b2; b3]) as N0.
  cbn [length Z.of_nat] in N1.
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split; [split|].
  - cbn. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold le4. rewrite unsigned_lit by lia.
    change 4%nat with (length [b0; b1; b2; b3]). rewrite StrFun.Z_to_le_bytes_to_Z.
    apply bytes_at_of_mbyte; [lia|cbn; lia|].
    intros i HI. destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat].
    + rewrite Z.add_0_r. exact B0.
    + exact B1.
    + exact B2.
    + exact B3.
    + cbn in HI. lia.
  - cbn [cells_size csize]. split; [lia|]. split; [lia|]. intros i HI.
    exact (proj1 (entry_errno_access B SEG TP OFF m (errno_addr B + i) ltac:(lia))).
Qed.

Lemma entry_blocks_apart : forall rc B (API : AllocAPI B) L A mem md p n q k,
  aa_MR (rc := rc) API L A mem md -> In (p, n) (blocks L A) -> In (q, k) (blocks L A) -> (p, n) <> (q, k) ->
  p + n <= q \/ q + k <= p.
Proof.
  intros rc B API L A mem md p n q k HM Hp Hq Hne.
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L A mem md HM) as HD.
  destruct (YI04.pairwise_in2 _ _ _ _ HD Hp Hq Hne) as [H|H]; unfold ranges_disjoint in H; simpl in H; lia.
Qed.

Lemma entry_output_rmid : forall rc B (API : AllocAPI B), blocks_writable B API ->
  forall K sp E L A mem md L' A' mem' md' nout cap out,
  rmid (rc := rc) B API K sp E (fun _ => False) L A mem md L' A' mem' md' ->
  output_at (rc := rc) B L A mem nout cap out ->
  (0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L A) ->
     forall i, 0 <= i < bv_unsigned cap -> ~ E (bv_unsigned out + i)) ->
  output_at (rc := rc) B L' A' mem' nout cap out.
Proof.
  intros rc B API BW K sp E L A mem md L' A' mem' md' nout cap out R OA HD.
  unfold output_at in *. cbv zeta in *. destruct OA as ((O & junk & HO) & HC).
  split; [|exact HC]. exists O, junk.
  destruct HO as [Z0|(CP & NO & IB & FB & BY & LO & LJ)]; [left; exact Z0|right].
  pose proof (HD CP IB) as NE.
  split; [exact CP|]. split; [exact NO|].
  split.
  { exact (proj1 (rmid_block B API BW K sp E (fun _ => False) L A mem md L' A' mem' md' _ _ 0 R IB CP
      (fun X => X) ltac:(lia) (NE 0 ltac:(lia)))). }
  split; [exact FB|].
  split.
  { eapply (rmid_bytes_block B API BW K sp E (fun _ => False)); [exact R|exact IB|exact CP|intros X; exact X|exact BY|lia| |].
    - rewrite length_app. lia.
    - intros i HI. rewrite length_app in HI. apply NE. lia. }
  split; assumption.
Qed.

Lemma entry_frame_keep : forall (m m' : word -> option byte) lo hi a cs,
  munch [(lo, hi)] m m' -> wmono rsegs m m' -> rw_cells rsegs m a cs ->
  a + Z.of_nat (cells_size cs) <= lo \/ hi <= a -> rw_cells rsegs m' a cs.
Proof.
  intros m m' lo hi a cs MU WM RW HD.
  eapply rw_cells_transport; [exact RW|exact MU|exact WM|]. cbn. split; [exact HD|exact I].
Qed.

Lemma entry_init_cells : forall CS B API LS SH SK ra empty rc fx j E mem,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (in_globals G_reply) (fun _ => False)
    (ss_L E) (ss_A E) (ss_mem E) (ss_md E) (ss_L E) (ss_A E) mem (ss_md E) ->
  munch (entry_frame_writes (spZ (ss_regs E))) (ss_mem E) mem -> wmono (ms_segs B) (ss_mem E) mem ->
  rw_cells (ms_segs B) mem 0x21624 [C4 (Z_to_bv 64 3)] ->
  rw_cells (ms_segs B) mem 0x318d8 [C8 (Z_to_bv 64 0)] ->
  entry_fixed_cells mem /\
  rw_cells rsegs mem 0x21620 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 3)] /\
  exists C G NO CAP OUT tail,
    ss_T E = kept_blocks C G CAP OUT /\
    rw_cells rsegs mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 C)] /\
    rw_cells rsegs mem G_SRC [C8 (Z_to_bv 64 G)] /\
    rw_cells rsegs mem G_OUTV [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 NO); C8 (Z_to_bv 64 CAP); C8 (Z_to_bv 64 OUT)] /\
    0 <= NO <= CAP /\ CAP <= TBBYTES /\ 0 <= OUT < 2 ^ 64 /\
    ((C = 0 /\ G = 0 /\ tail = []) \/
     (C = 16 /\ In (G, SRC_TABLE) (blocks (ss_L E) (ss_A E)) /\ fresh_block (rc := rc) B G SRC_TABLE /\
      Z.of_nat (length tail) = SRC_TABLE /\ rw_cells rsegs mem G [CB (Z.to_nat SRC_TABLE) tail])) /\
    output_at (rc := rc) B (ss_L E) (ss_A E) mem (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT).
Proof.
  intros CS B API LS SH SK ra empty rc fx j E mem (FF & HJ & HP & HCS) RM MU WM WC WMX.
  destruct HP as (PRE & (RES & _) & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by
    (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  pose proof (@alloc_ceiling_value rc) as AC. pose proof (@alloc_ceiling_lt rc) as ACL.
  assert (HS : 0x100000 <= spZ (ss_regs E) - 192) by (unfold SLOT_STACK in *; lia).
  rewrite SEG in WM, WC, WMX.
  assert (UT : forall a cs, rw_cells rsegs (ss_mem E) a cs -> 0 < Z.of_nat (cells_size cs) ->
     (forall i, 0 <= i < Z.of_nat (cells_size cs) -> entry_untouched (a + i)) -> rw_cells rsegs mem a cs)
    by (intros a cs H1 H2 H3; exact (entry_untouched_rw _ _ _ a cs HS MU WM H1 H2 H3)).
  assert (GL : forall a, 0x318a0 <= a < 0x31aa0 -> in_globals G_reply a) by (intros a Ha; apply in_G_bss; lia).
  pose proof GI as (GR & _).
  assert (FIX : entry_fixed_cells mem) by exact (entry_fixed_preserved _ _ _ HS MU WM (entry_fixed_of_GI j _ GR)).
  split; [exact FIX|].
  split.
  { apply hg_join with (B := 0x21624) (cs1 := [C4 (Z_to_bv 64 (-1))]); [|exact WC|reflexivity].
    apply UT; [|cbn; lia|intros k HK; cbn in HK; unfold entry_untouched; lia].
    eapply rw_cells_retype with (cs := [CB 4 (repeat (Z_to_bv 8 255) 4)]).
    - apply entry_byte_cells; [lia|cbn; lia| |].
      + intros i HI. exists 0x21620, 16. split; [left; reflexivity|cbn in HI; lia].
      + intros i HI. replace (0x21620 + i) with (G_DATA + i) by reflexivity. apply (proj1 GR). cbn in HI. lia.
    - cbn; tauto.
    - vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. }
  destruct (entry_gi_blocks rc B (API rc) AX BW (ss_L E) (ss_A E) (ss_mem E) (ss_md E) j (ss_T E) HM GI LIVE)
    as (C & G & NO & CAP & OUT & tail & WCS & WG & WNO & WCP & WO & HNO & HCAP & HOUT & HT & TAB & OA).
  assert (GB : 0 <= G < 2 ^ 64 /\ (C = 0 \/ C = 16)).
  { destruct TAB as [(-> & -> & _)|(-> & _ & (F1 & F2 & _) & _)]; unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  destruct GB as [G64 C016].
  assert (W4 : rw_cells rsegs mem 0x318bc [C4 (Z_to_bv 64 C)]).
  { apply UT; [|cbn; lia|intros k HK; cbn in HK; unfold entry_untouched; lia].
    apply entry_word4; [lia|lia|lia|intros i HI; apply GL; lia|exact WCS]. }
  assert (W8 : forall a v, 0x318c4 <= a -> a + 8 <= 0x31aa0 -> 0 <= v < 2 ^ 64 ->
      (forall i, 0 <= i < 8 -> entry_untouched (a + i)) ->
      wN_at (ss_mem E) a v 8 -> rw_cells rsegs mem a [C8 (Z_to_bv 64 v)]).
  { intros a v H1 H2 H3 H4 H5. apply UT; [|cbn; lia|intros k HK; cbn in HK; apply H4; lia].
    apply entry_word8; [lia|lia|exact H3|intros i HI; apply GL; lia|exact H5]. }
  exists C, G, NO, CAP, OUT, tail.
  split; [exact HT|].
  split.
  { apply hg_join with (B := 0x318bc) (cs1 := [C4 (Z_to_bv 64 0)]); [exact (proj1 (proj2 (proj2 FIX)))|exact W4|reflexivity]. }
  split.
  { apply W8; [unfold G_SRC; lia|unfold G_SRC; lia|lia|intros i HI; unfold entry_untouched, G_SRC; lia|exact WG]. }
  split.
  { apply hg_join with (B := 0x318e0) (cs1 := [C8 (Z_to_bv 64 0)]); [exact WMX| |reflexivity].
    apply hg_join with (B := 0x318e8) (cs1 := [C8 (Z_to_bv 64 NO)]); [| |reflexivity].
    { apply W8; [lia|lia|unfold TBBYTES in *; lia|intros i HI; unfold entry_untouched; lia|exact WNO]. }
    apply hg_join with (B := 0x318f0) (cs1 := [C8 (Z_to_bv 64 CAP)]); [| |reflexivity].
    { apply W8; [lia|lia|unfold TBBYTES in *; lia|intros i HI; unfold entry_untouched; lia|exact WCP]. }
    apply W8; [lia|lia|lia|intros i HI; unfold entry_untouched; lia|exact WO]. }
  split; [lia|]. split; [exact HCAP|]. split; [exact HOUT|].
  split.
  { destruct TAB as [T0|(T16 & GBL & GF & TL & TRW)]; [left; exact T0|right].
    do 4 (split; [assumption|]). rewrite <- SEG.
    eapply (rmid_rw_block B (API rc) BW); [exact RM|exact GBL|unfold SRC_TABLE, SRC_ENTRY; lia|intros X; exact X|exact TRW|lia| |].
    - change (cells_size [CB (Z.to_nat SRC_TABLE) tail]) with 896%nat. unfold SRC_TABLE, SRC_ENTRY. lia.
    - intros i HI HG. change (cells_size [CB (Z.to_nat SRC_TABLE) tail]) with 896%nat in HI.
      destruct GF as (_ & _ & NX). apply (NX i ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)). exact (proj1 (PL _ HG)). }
  eapply entry_output_rmid; [exact BW|exact RM|exact OA|].
  intros CP IB i HI HG. destruct (entry_block_data rc B (API rc) AX BW _ _ _ _ _ _ HM IB CP) as ((_ & _ & NX) & _).
  exact (NX i HI (proj1 (PL _ HG))).
Qed.

Lemma entry_ub_nonneg : forall s p n, WF s -> In (p, n) (user_blocks s) -> 0 <= n.
Proof.
  intros s p n HW Hin.
  destruct (YO0x.user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & En & Ep).
  pose proof (YO10.block_in_slot s g am idx fr HW Hu Hi Hfr) as (_ & _ & H). lia.
Qed.

Lemma entry_blk_nn : forall rc B (API : AllocAPI B) L A mem md x k,
  aa_MR (rc := rc) API L A mem md -> In (x, k) (blocks L A) -> 0 <= k.
Proof.
  intros rc B API L A mem md x k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-.
  exact (entry_ub_nonneg A p k' (mr_wf _ _ (aa_laws API) L A mem md HM) Hp).
Qed.

Lemma entry_blk_lo : forall rc B (API : AllocAPI B) L A mem md x k,
  aa_MR (rc := rc) API L A mem md -> In (x, k) (blocks L A) -> 4096 <= x.
Proof.
  intros rc B API L A mem md x k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & EQ & Hp).
  cbn [fst snd] in EQ. injection EQ as <- <-.
  exact (proj1 (mr_blocks_range _ _ (aa_laws API) L A mem md p k' HM Hp)).
Qed.

Lemma entry_blk_nd : forall B API LS SH SK ra empty rc fx j E CS L A mem md,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> aa_MR (rc := rc) (API rc) L A mem md ->
  List.NoDup (map fst (blocks L A)).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem md (FF & _) HM.
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (ND : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
  exact (proj1 (NoDup_ListNoDup _) (ND L A mem md HM)).
Qed.

Lemma entry_in_mid : forall (d1 d2 : list (Z * Z)) a x, In x (d1 ++ a :: d2) <-> a = x \/ In x (d1 ++ d2).
Proof. intros d1 d2 a x. rewrite !in_app_iff. cbn [In]. tauto. Qed.

(* nc_move for a call that frees nothing and adds the blocks adds: the view keeps R and drops the addresses gone
   (they have no block), and the new view adds the addresses of adds. *)
Lemma entry_mv_ins : forall (V V' : rview) L A L' A' (R gone : list Z) (adds : list (Z * Z)),
  List.NoDup (map fst (blocks L A)) -> List.NoDup (map fst (blocks L' A')) ->
  Permutation (rv_nc V) (R ++ gone) -> Permutation (rv_nc V') (R ++ map fst adds) ->
  (forall x m, In (x, m) (blocks L' A') -> In (x, m) (blocks L A) \/ In (x, m) adds) ->
  (forall x m, In (x, m) (blocks L A) -> In (x, m) (blocks L' A')) ->
  incl adds (blocks L' A') -> List.NoDup adds -> (forall u, In u adds -> ~ In u (blocks L A)) ->
  (forall x m, In (x, m) (blocks L' A') -> 0 <= m) ->
  (forall g, In g gone -> forall m, ~ In (g, m) (blocks L A)) ->
  nc_move V L A V' L' A' [] adds.
Proof.
  intros V V' L A L' A' R gone adds ND0 ND1 PV PV' H1 H2 Inc NDa Na Pos Gn.
  refine (mv_build V V' L A L' A' [] adds [] R gone (fun _ => true) ND0 ND1 PV PV' _ _ _ _ _ _ _ _ _ Pos _ Gn).
  - intros u [].
  - constructor.
  - intros u [].
  - intros x m _ K. cbv beta in K. discriminate K.
  - intros x m Hx. destruct (H1 x m Hx) as [Ho|Ha]; [left; split; [exact Ho|reflexivity]|].
    right. rewrite app_nil_r. exact Ha.
  - intros x m Hx _. exact (H2 x m Hx).
  - rewrite app_nil_r. exact Inc.
  - rewrite app_nil_r. exact NDa.
  - intros u Hu. right. rewrite app_nil_r in Hu. exact (Na u Hu).
  - intros u [].
Qed.

Lemma entry_driver_kept : forall CS B API LS SH SK ra empty rc fx j E C G TA L A mem md,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (entry_modified C G) (fun _ => False)
    (ss_L E) (ss_A E) (ss_mem E) (ss_md E) L A mem md ->
  (C = 16 -> In (G, SRC_TABLE) (ss_T E)) ->
  (forall d m, In (d, m) (blocks (ss_L E) (ss_A E)) -> ~ In (d, m) (ss_T E) -> 0 < m -> ~ In d TA) ->
  (forall b m, In (b, m) (blocks L A) ->
     (In (b, m) (blocks (ss_L E) (ss_A E)) /\ ~ In (b, m) (ss_T E)) \/ In b TA) ->
  driver_kept B E TA L A mem.
Proof.
  intros CS B API LS SH SK ra empty rc fx j E C G TA L A mem md (FF & HJ & HP & HCS) R GT HTA HBL.
  destruct HP as (PRE & (RES & _) & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by
    (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  pose proof R as (M1 & W1 & B1 & LY1 & LN1 & PA1 & SV1 & Z01 & OW1 & MD1 & BY1 & BK1 & SC1).
  assert (NE : forall d m i, In (d, m) (blocks (ss_L E) (ss_A E)) -> ~ In (d, m) (ss_T E) -> 0 <= i < m ->
      ~ entry_modified C G (d + i)).
  { intros d m i HD HNT HI [HG|(HC & HG)].
    - destruct (entry_block_data rc B (API rc) AX BW _ _ _ _ d m HM HD ltac:(lia)) as ((_ & _ & NX) & _).
      exact (NX i HI (proj1 (PL _ HG))).
    - pose proof (GT HC) as GIN. pose proof (proj2 LIVE _ GIN) as GBL.
      assert (NEQ : (d, m) <> (G, SRC_TABLE)) by (intros EQ; rewrite EQ in HNT; exact (HNT GIN)).
      destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ HM HD GBL NEQ);
        unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (UB : forall q m, In (q, m) (user_blocks (ss_A E)) ->
      In (ptr_addr (ss_L E) q, m) (blocks (ss_L E) (ss_A E)))
    by (intros q m HQ; exact (in_map (fun b => (ptr_addr (ss_L E) (fst b), snd b)) _ (q, m) HQ)).
  unfold driver_kept. split; [|split; [|split]].
  - intros q m HQ HNT. split; [intros Hm; exact (HTA _ m (UB q m HQ) HNT Hm)|].
    exists q. pose proof (entry_ub_nonneg _ _ _ HW HQ) as HN.
    destruct (Z.eq_dec m 0) as [->|Hm].
    + exact (Z01 q HQ).
    + assert (HQ' : In (q, m) (user_blocks A)) by (apply SV1; [exact HQ|lia|intros X; exact X]).
      split; [exact HQ'|exact (PA1 q m HQ HQ' (fun X => X))].
  - intros q m i HQ HNT HP' HI.
    assert (HQ' : In (q, m) (user_blocks A)) by (apply SV1; [exact HQ|lia|intros X; exact X]).
    exact (BK1 q m i HQ HQ' (fun X => X) HI (NE _ m i (UB q m HQ) HNT HI)).
  - intros i HI. destruct INPUT as [(HN0 & _)|(HN & qp & HQP & HPP)]; [lia|].
    rewrite <- HPP.
    assert (HNT : ~ In (ptr_addr (ss_L E) qp, ss_n E) (ss_T E)) by (rewrite HPP; exact (NI HN)).
    assert (HQ' : In (qp, ss_n E) (user_blocks A)) by (apply SV1; [exact HQP|lia|intros X; exact X]).
    exact (BK1 qp (ss_n E) i HQP HQ' (fun X => X) HI (NE _ _ i (UB qp _ HQP) HNT HI)).
  - exact HBL.
Qed.

Definition entry_add_mod (C G a : Z) : Prop :=
  G_S + SRC_SIZE * Z.of_nat 0 <= a < G_S + SRC_SIZE * Z.of_nat 0 + SRC_SIZE \/ G_NFD <= a < G_NFD + 4 \/
  G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 8 \/ G_SRC <= a < G_SRC + 8 \/
  (0 < C /\ G + SRC_ENTRY * 0 <= a < G + SRC_ENTRY * (0 + 1)).

Lemma entry_after_init : forall CS RI F B API LS SH SK ra empty rc fx j E c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> ss_n E < INPUT_MAX ->
  (forall C G CAP OUT, ss_T E = kept_blocks C G CAP OUT -> (C = 0 /\ G = 0) \/ C = 16 -> 0 <= CAP <= TBBYTES ->
     (CAP = 0 -> OUT = 0) -> RI E 0 (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E)) ->
  entry_add_resources_s F RI ->
  @op_add_contract fx rc B (API rc) F ->
  entry_initialized (fx := fx) (rc := rc) B (API rc) E c ->
  SR (ms_segs B) c (LI (rc := rc) B (API rc) E RI 0 0).
Proof.
  intros CS RI F B API LS SH SK ra empty rc fx j E c HF Hs HRI HAR HOA
    (regs & mem & junk & -> & RM1 & RO1 & MU1 & WM1 & CR & SLOT & WC & WN & WMX & WB & WG & WD & WE).
  pose proof HF as (FF & HJ & HP & HCS).
  destruct HP as (PRE & (RES & _) & PACK & MIS & GI & LIVE & NI & IMG & RO & TASK & FZ).
  destruct PRE as (PRE & LEN & DATA & SINK & FD & FS & FDC & SP47).
  destruct PRE as (HM & HW & HB & INIT & RA & ALIGN & SPLO & SPHI & WST & TP & WERR & RP & RN & INPUT & ROD).
  assert (SEG : ms_segs B = rsegs) by (unfold frame_facts in FF; tauto).
  assert (PL : forall a, in_globals G_reply a -> img_plain B a) by
    (unfold frame_facts, G_reply, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (EA : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  pose proof (@alloc_ceiling_value rc) as AC. pose proof (@alloc_ceiling_lt rc) as ACL.
  destruct (entry_init_cells CS B API LS SH SK ra empty rc fx j E mem HF RM1 MU1 WM1 WC WMX)
    as (FIX & LST & C & G & NO & CAP & OUT & tail & HT & NSRC & GSRC & OUTV & HNO & HCAP & HOUT & TAB & OA).
  pose proof FIX as (THREAD & WAKE & NSRC0 & LOCK & SOURCES).
  rewrite SEG in WB, WG, WD, WE, SLOT.
  assert (C016 : C = 0 \/ C = 16) by (destruct TAB as [(H & _)|(H & _)]; [left|right]; exact H).
  assert (GFR : C = 16 -> fresh_block (rc := rc) B G SRC_TABLE).
  { intros HC. destruct TAB as [(H0 & _)|(_ & _ & H & _)]; [lia|exact H]. }
  assert (GBC : C = 16 -> In (G, SRC_TABLE) (blocks (ss_L E) (ss_A E))).
  { intros HC. destruct TAB as [(H0 & _)|(_ & H & _)]; [lia|exact H]. }
  assert (GTIN : C = 16 -> In (G, SRC_TABLE) (ss_T E)).
  { intros HC. rewrite HT, HC. unfold kept_blocks. cbn. left. reflexivity. }
  assert (TIN : forall b m, In (b, m) (ss_T E) -> (C = 16 /\ b = G) \/ (0 < CAP /\ b = OUT /\ m = CAP)).
  { intros b m HIN. rewrite HT in HIN. unfold kept_blocks in HIN. apply in_app_or in HIN as [HIN|HIN].
    - revert HIN. destruct (Z.eqb_spec C 16) as [HC|HC]; intros HIN; [|destruct HIN].
      destruct HIN as [EQ|[]]. injection EQ as <- <-. left. split; [exact HC|reflexivity].
    - revert HIN. destruct (Z.eqb_spec CAP 0) as [HC|HC]; intros HIN; [destruct HIN|].
      destruct HIN as [EQ|[]]. injection EQ as <- <-. right. split; [lia|split; reflexivity]. }
  assert (TDIS : C = 16 -> 0 < CAP -> (G, SRC_TABLE) <> (OUT, CAP)).
  { intros HC HCP EQ. destruct LIVE as [ND _]. rewrite HT, HC in ND. unfold kept_blocks in ND.
    replace (CAP =? 0) with false in ND by (symmetry; apply Z.eqb_neq; lia). cbn in ND.
    apply NoDup_ListNoDup in ND. apply List.NoDup_cons_iff in ND as [NIN _].
    apply NIN. left. rewrite <- EQ. reflexivity. }
  assert (OCASE : (CAP = 0 /\ OUT = 0) \/ (0 < CAP /\ In (OUT, CAP) (blocks (ss_L E) (ss_A E)))).
  { unfold output_at in OA. cbv zeta in OA. rewrite !unsigned_lit in OA by (unfold TBBYTES in *; lia).
    destruct OA as ((O & jk & [(H1 & H2 & _)|(H1 & _ & H3 & _)]) & _); [left|right]; split; assumption. }
  assert (HCG : (C = 0 /\ G = 0) \/ C = 16).
  { destruct TAB as [(H0 & H1 & _)|(H0 & _)]; [left; split; assumption|right; exact H0]. }
  assert (HCO : CAP = 0 -> OUT = 0) by (intros H0; destruct OCASE as [(_ & H1)|(H1 & _)]; [exact H1|lia]).
  destruct (HAR E (ss_L E) (ss_A E) C G OUT (HRI C G CAP OUT HT HCG ltac:(lia) HCO) C016) as (bnd & ROK & ROOM & RIK).
  pose proof RM1 as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  pose proof CR as (R1 & R2 & R3 & R4 & R9 & R18 & R20).
  assert (REGSP : spZ regs = slot_sp E).
  { unfold spZ. rewrite R2. apply unsigned_lit. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (NAM : forall a, in_globals G_reply a -> ~ (0 < C /\ G + SRC_ENTRY * 0 <= a < G + SRC_ENTRY * (0 + 1))).
  { intros a HG (HC & X). assert (C16 : C = 16) by (destruct C016; lia).
    destruct (GFR C16) as (_ & _ & NX).
    apply (NX (a - G) ltac:(unfold SRC_TABLE, SRC_ENTRY in *; lia)). replace (G + (a - G)) with a by lia.
    exact (proj1 (PL _ HG)). }
  assert (EMS : forall a, @YM05.alloc_ceiling rc <= a -> ~ entry_add_mod C G a).
  { intros a Ha HE. unfold entry_add_mod in HE.
    destruct HE as [X|[X|[X|[X|[X|(HC & X)]]]]];
      try (unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC in X; lia).
    assert (C16 : C = 16) by (destruct C016; lia). destruct (GFR C16) as (_ & GH & _).
    unfold SRC_TABLE, SRC_ENTRY in *. lia. }
  assert (CUTS : forall i, (i < 4)%nat ->
      rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i + 4) [C4 (Z_to_bv 64 0)]).
  { intros i Hi. rewrite SEG.
    assert (S' : rw_cells rsegs mem (G_S + SRC_SIZE * Z.of_nat i)
        [CB 4 (nulbytes 4); C4 (Z_to_bv 64 0); CB 88 (nulbytes 88)])
      by (eapply rw_cells_retype; [exact (SOURCES i Hi)|cbn; tauto|reflexivity]).
    destruct (hg_cut rsegs mem _ [CB 4 (nulbytes 4)] [C4 (Z_to_bv 64 0); CB 88 (nulbytes 88)] S') as [_ S2].
    exact (proj1 (hg_cut rsegs mem _ [C4 (Z_to_bv 64 0)] [CB 88 (nulbytes 88)] S2)). }
  assert (LOCK3 : rw_cells rsegs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
    by exact (proj1 (hg_cut rsegs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
      [CB 28 (nulbytes 28)] LOCK)).
  assert (LOCK28 : rw_cells rsegs mem (G_LOCK + 12) [CB 28 (nulbytes 28)])
    by exact (proj2 (hg_cut rsegs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
      [CB 28 (nulbytes 28)] LOCK)).
  assert (WAKEB : bytes_at (ms_segs B) mem G_WAKE1 (le4 (Z_to_bv 64 (-1)))).
  { rewrite SEG.
    pose proof (proj2 (hg_cut rsegs mem G_WAKE0 [C4 (Z_to_bv 64 (-1))] [C4 (Z_to_bv 64 (-1))] WAKE)) as W1'.
    destruct W1' as [[_ HBY] _]. cbn [cells_bytes cbytes] in HBY. rewrite app_nil_r in HBY. exact HBY. }
  destruct (hg_cut rsegs mem (slot_sp E) [C8 (Z_to_bv 64 CLIENT_BASE); CB 80 junk] (saved_cells (ss_regs E)) SLOT)
    as [SL01 SAVED].
  destruct (hg_cut rsegs mem (slot_sp E) [C8 (Z_to_bv 64 CLIENT_BASE)] [CB 80 junk] SL01) as [CLB S80].
  assert (JL : length junk = 80%nat) by exact (proj1 (proj1 (proj1 S80))).
  assert (S8 : rw_cells rsegs mem (slot_sp E + 8) [CB 8 (firstn 8 junk)]).
  { assert (S3 : rw_cells rsegs mem (slot_sp E + 8) [CB 8 (firstn 8 junk); CB 72 (skipn 8 junk)]).
    { eapply rw_cells_retype; [exact S80| |].
      - cbn [cells_wf cell_wf]. rewrite length_firstn, length_skipn, JL. cbn. tauto.
      - cbn [cells_bytes cbytes]. now rewrite !app_nil_r, firstn_skipn. }
    exact (proj1 (hg_cut rsegs mem _ [CB 8 (firstn 8 junk)] [CB 72 (skipn 8 junk)] S3)). }
  eapply SR_bind.
  { apply (HOA (ss_L E) (ss_A E) regs mem (ss_md E) bnd [0; 0; 0; 0] 0 0 C G [] tail).
    - exact SEG.
    - exact (entry_call_pre CS B API LS SH SK ra empty rc fx j E regs mem HF RM1 CR).
    - exact INIT.
    - exact RO1.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - intros a Ha. apply PL. apply in_G_bss. unfold G_S, SRC_SIZE, SOURCES_MAX, G_RELAY_LO in *. lia.
    - intros a Ha. apply PL. exists 0x21620, 16. split; [left; reflexivity|unfold G_WAKE1 in *; lia].
    - reflexivity.
    - intros i Hi. split; [destruct i as [|[|[|[|i]]]]; cbn; lia|].
      destruct i as [|[|[|[|i]]]]; [exact (CUTS 0%nat Hi)|exact (CUTS 1%nat Hi)|exact (CUTS 2%nat Hi)|
        exact (CUTS 3%nat Hi)|lia].
    - intros i Hi _. rewrite SEG. exact (SOURCES i Hi).
    - exact WN.
    - lia.
    - rewrite SEG. exact LOCK3.
    - exact WAKEB.
    - rewrite SEG. exact NSRC.
    - rewrite SEG. exact GSRC.
    - destruct TAB as [(-> & -> & ->)|(-> & GBL & GF & TL & TRW)].
      + left. repeat split.
      + right. split; [reflexivity|]. split; [exact GBL|]. split; [exact GF|].
        split; [reflexivity|]. split; [rewrite TL; reflexivity|]. rewrite SEG. exact TRW.
    - exact ROK.
    - intros _. lia.
    - exact ROOM. }
  intros c' (L' & A' & regs' & mem' & md' & -> & INIT' & RO' & _ & POST).
  destruct (POST 0%nat eq_refl) as (q & G' & pj & rest & RP' & (qs & QLEN & ROK' & LQ & LG) & HA0 & SRC0 & NFD1 &
    LOCK1 & WAKE1' & NSRC1 & GSRC1 & GBL' & GF' & RL & GTAB & QB & QF & QNEW & CASES').
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP') as [RM2 RPR].
  rewrite REGSP in RM2.
  assert (RM2' : rmid B (API rc) OP_ADD_K (slot_sp E) (entry_add_mod C G) (fun _ => False)
      (ss_L E) (ss_A E) mem (ss_md E) L' A' mem' md') by exact RM2.
  clear RM2.
  pose proof RM2' as (M2 & W2 & B2 & LY2 & LN2 & PA2 & SV2 & Z02 & OW2 & MD2 & BY2 & BK2 & SC2).
  rewrite SEG in RO', NFD1, LOCK1, NSRC1, GSRC1, GTAB.
  assert (RM2W : rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (entry_add_mod C G) (fun _ => False)
      (ss_L E) (ss_A E) mem (ss_md E) L' A' mem' md').
  { apply (rmid_widen B (API rc) OP_ADD_K (slot_sp E)); [exact M1| | | | | | |exact RM2'].
    - change OP_ADD_K with 8352. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - unfold slot_sp, SLOT_FRAME. lia.
    - unfold SLOT_STACK in *. lia.
    - lia.
    - intros a Ha. apply SC1. left. exact Ha.
    - intros a Ha. apply EMS. unfold SLOT_STACK in *. lia. }
  pose proof RM2W as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SCW).
  assert (KS1 : forall a cs, rw_cells rsegs mem a cs -> slot_sp E <= a ->
      a + Z.of_nat (cells_size cs) <= spZ (ss_regs E) -> rw_cells rsegs mem' a cs).
  { intros a cs H1 H2 H3. rewrite <- SEG.
    eapply (rmid_rw_hi B (API rc)); [| |exact M1|exact RM2'|rewrite SEG; exact H1|exact H2| |].
    - unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - rewrite EA. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia.
    - lia.
    - intros i Hi. apply EMS. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (S8' : rw_cells (ms_segs B) mem' (slot_sp E + 8) [CB 8 (firstn 8 junk)]).
  { rewrite SEG. apply KS1; [exact S8|lia|cbn; unfold slot_sp, SLOT_FRAME; lia]. }
  assert (P2 : YK11.getr regs' 2 = Z_to_bv 64 (slot_sp E))
    by exact (eq_trans (RPR 2 ltac:(unfold callee_saved; lia)) R2).
  assert (P3 : YK11.getr regs' 3 = YK11.getr (ss_regs E) 3)
    by exact (eq_trans (RPR 3 ltac:(unfold callee_saved; lia)) R3).
  assert (P4 : YK11.getr regs' 4 = YK11.getr (ss_regs E) 4)
    by exact (eq_trans (RPR 4 ltac:(unfold callee_saved; lia)) R4).
  assert (P9 : YK11.getr regs' 9 = Z_to_bv 64 (ss_n E))
    by exact (eq_trans (RPR 9 ltac:(unfold callee_saved; lia)) R9).
  assert (P18 : YK11.getr regs' 18 = Z_to_bv 64 (ss_p E))
    by exact (eq_trans (RPR 18 ltac:(unfold callee_saved; lia)) R18).
  assert (P20 : YK11.getr regs' 20 = Z_to_bv 64 G_RELAY_LO)
    by exact (eq_trans (RPR 20 ltac:(unfold callee_saved; lia)) R20).
  assert (PC : getr regs 1 = Z_to_bv 64 0x14118) by exact R1.
  rewrite PC.
  eapply SR_bind.
  { exact (entry_head_step CS B API LS SH SK ra empty rc fx j E L' A' regs' mem' md' (firstn 8 junk)
      HF ltac:(lia) M2 W2 B2 ltac:(rewrite SEG; exact RO') SCW P2 P3 P4 P9 P18 P20 S8'). }
  intros c'' (regs'' & mem'' & -> & RM3 & RO3 & HR3 & MU3 & WM3 & S8G).
  apply SR_ret.
  rewrite SEG in WM3, S8G.
  pose proof RM3 as (M3 & W3 & B3 & _).
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW RM1 RM2W) as R12.
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HW R12 RM3) as R123.
  assert (RMA : rmid B (API rc) SLOT_STACK (spZ (ss_regs E)) (entry_modified C G) (fun _ => False)
      (ss_L E) (ss_A E) (ss_mem E) (ss_md E) L' A' mem'' md').
  { apply (rmid_EF B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ R123).
    - intros a [[HG|HE]|[]]; [left; exact HG|].
      unfold entry_add_mod in HE. destruct HE as [X|[X|[X|[X|[X|(HC & X)]]]]];
        try (left; apply in_G_bss; unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC in X; lia).
      right. split; [destruct C016; lia|unfold SRC_ENTRY in *; lia].
    - intros q0 [[X|X]|X]; exact X. }
  assert (KH : forall a cs, rw_cells rsegs mem' a cs -> a + Z.of_nat (cells_size cs) <= 0x31aa0 ->
      rw_cells rsegs mem'' a cs).
  { intros a cs H1 H2. eapply entry_frame_keep; [exact MU3|exact WM3|exact H1|].
    left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
  assert (KG : forall a cs, rw_cells rsegs mem a cs -> a + Z.of_nat (cells_size cs) <= 0x31aa0 ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) -> in_globals G_reply (a + i)) ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
         ~ (G_S <= a + i < G_S + SRC_SIZE) /\ ~ (G_NFD <= a + i < G_NFD + 4) /\
         ~ (G_LOCK + 4 <= a + i < G_LOCK + 8) /\ ~ (G_NSRC <= a + i < G_NSRC + 8) /\
         ~ (G_SRC <= a + i < G_SRC + 8)) ->
      rw_cells rsegs mem'' a cs).
  { intros a cs H1 H0 HGl HNum. apply KH; [|exact H0].
    rewrite <- SEG.
    eapply (rmid_rw_img B (API rc) AX); [exact (hg_img_low B SEG)| |exact M1|exact RM2W|rewrite SEG; exact H1|].
    - unfold SLOT_STACK in *. lia.
    - intros i Hi. split; [exact (PL _ (HGl i Hi))|].
      intros HE. unfold entry_add_mod in HE. destruct (HNum i Hi) as (N1 & N2 & N3 & N4 & N5).
      destruct HE as [X|[X|[X|[X|[X|X]]]]]; [lia|exact (N2 X)|exact (N3 X)|exact (N4 X)|exact (N5 X)|].
      exact (NAM (a + i) (HGl i Hi) X). }
  assert (KS : forall a cs, rw_cells rsegs mem a cs -> slot_sp E <= a ->
      a + Z.of_nat (cells_size cs) <= spZ (ss_regs E) ->
      (a + Z.of_nat (cells_size cs) <= slot_sp E + 8 \/ slot_sp E + 16 <= a) -> rw_cells rsegs mem'' a cs)
    by (intros a cs H1 H2 H3 H4; exact (entry_frame_keep _ _ _ _ a cs MU3 WM3 (KS1 a cs H1 H2 H3) H4)).
  assert (OA2 : output_at (rc := rc) B L' A' mem' (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT)).
  { eapply entry_output_rmid; [exact BW|exact RM2'|exact OA|].
    rewrite !unsigned_lit by (unfold TBBYTES in *; lia).
    intros CP IB i Hi HE.
    destruct (entry_block_data rc B (API rc) AX BW _ _ _ _ _ _ HM IB CP) as ((F1 & F2 & NX) & _).
    unfold entry_add_mod in HE.
    destruct HE as [X|[X|[X|[X|[X|(HC & X)]]]]];
      try (apply (NX i Hi); apply (proj1 (PL (OUT + i)
        (in_G_bss (OUT + i) ltac:(unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC in X; lia))))).
    assert (C16 : C = 16) by (destruct C016; lia).
    destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ HM (GBC C16) IB (TDIS C16 CP));
      unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (OA3 : output_at (rc := rc) B L' A' mem'' (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT)).
  { eapply entry_output_rmid; [exact BW|exact RM3|exact OA2|]. intros _ _ i _ X. exact X. }
  assert (QLO : 4096 <= q) by (destruct QF as (H & _); exact H).
  assert (GLO : 4096 <= G') by (destruct GF' as (H & _); exact H).
  assert (GQ : G' <> q).
  { intros EQ. assert (NE : (G', SRC_TABLE) <> (q, PARTIAL_BYTES))
      by (intros X; injection X as _ X; unfold SRC_TABLE, SRC_ENTRY, PARTIAL_BYTES in X; lia).
    destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ M2 GBL' QB NE);
      unfold SRC_TABLE, SRC_ENTRY, PARTIAL_BYTES in *; lia. }
  assert (OQ : OUT <> q).
  { destruct OCASE as [(_ & ->)|(CP & IB)]; [lia|]. exact (QNEW OUT CAP IB CP). }
  assert (GO : G' <> OUT).
  { destruct OCASE as [(_ & ->)|(CP & IB)]; [lia|].
    destruct CASES' as [(HC0 & GNEW & _)|(HC16 & HGG & _)].
    - intros EQ. exact (GNEW OUT CAP IB CP (eq_sym EQ)).
    - subst G'. intros EQ.
      destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ HM (GBC HC16) IB (TDIS HC16 CP));
        unfold SRC_TABLE, SRC_ENTRY in *; lia. }
  assert (TAD : forall d m, In (d, m) (blocks (ss_L E) (ss_A E)) -> ~ In (d, m) (ss_T E) -> 0 < m ->
      ~ In d [G'; OUT; q]).
  { intros d m HD HNT Hm [EQ|[EQ|[EQ|[]]]]; subst d.
    - destruct CASES' as [(HC0 & GNEW & _)|(HC16 & HGG & _)].
      + exact (GNEW G' m HD Hm eq_refl).
      + subst G'. assert (NE : (G, m) <> (G, SRC_TABLE)) by (intros X; apply HNT; rewrite X; exact (GTIN HC16)).
        destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ HM HD (GBC HC16) NE);
          unfold SRC_TABLE, SRC_ENTRY in *; lia.
    - destruct OCASE as [(_ & ->)|(CP & IB)].
      + destruct (entry_block_data rc B (API rc) AX BW _ _ _ _ _ _ HM HD Hm) as ((F1 & _) & _). lia.
      + assert (OT : In (OUT, CAP) (ss_T E)).
        { rewrite HT. unfold kept_blocks. apply in_or_app. right.
          replace (CAP =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
        assert (NE : (OUT, m) <> (OUT, CAP)) by (intros X; apply HNT; rewrite X; exact OT).
        destruct (entry_blocks_apart rc B (API rc) _ _ _ _ _ _ _ _ HM HD IB NE); lia.
    - exact (QNEW q m HD Hm eq_refl). }
  assert (TBL : forall b m, In (b, m) (blocks L' A') ->
      (In (b, m) (blocks (ss_L E) (ss_A E)) /\ ~ In (b, m) (ss_T E)) \/ In b [G'; OUT; q]).
  { assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
    assert (OLD : forall b m, In (b, m) (blocks (ss_L E) (ss_A E)) ->
        (In (b, m) (blocks (ss_L E) (ss_A E)) /\ ~ In (b, m) (ss_T E)) \/ In b [G'; OUT; q]).
    { intros b m HBm. destruct (in_dec DEC (b, m) (ss_T E)) as [IT|NT]; [right|left; split; assumption].
      destruct (TIN b m IT) as [(HC & ->)|(_ & -> & _)].
      - left. destruct CASES' as [(HC0 & _)|(_ & HGG & _)]; [lia|exact HGG].
      - right. left. reflexivity. }
    intros b m HBm.
    destruct CASES' as [(HC0 & GNEW & c1 & c2 & d1 & d2 & EB & EC & ED)|(HC16 & HGG & HR & d1 & d2 & EB & ED)].
    - rewrite EB in HBm. apply in_app_or in HBm as [HBm|[EQ|HBm]].
      + assert (H1 : In (b, m) (c1 ++ c2)) by (apply in_or_app; left; exact HBm).
        rewrite EC in H1. apply in_app_or in H1 as [H1|[EQ|H1]].
        * apply OLD. rewrite <- ED. apply in_or_app. left. exact H1.
        * injection EQ as <- <-. right. right. right. left. reflexivity.
        * apply OLD. rewrite <- ED. apply in_or_app. right. exact H1.
      + injection EQ as <- <-. right. left. reflexivity.
      + assert (H1 : In (b, m) (c1 ++ c2)) by (apply in_or_app; right; exact HBm).
        rewrite EC in H1. apply in_app_or in H1 as [H1|[EQ|H1]].
        * apply OLD. rewrite <- ED. apply in_or_app. left. exact H1.
        * injection EQ as <- <-. right. right. right. left. reflexivity.
        * apply OLD. rewrite <- ED. apply in_or_app. right. exact H1.
    - rewrite EB in HBm. apply in_app_or in HBm as [HBm|[EQ|HBm]].
      + apply OLD. rewrite <- ED. apply in_or_app. left. exact HBm.
      + injection EQ as <- <-. right. right. right. left. reflexivity.
      + apply OLD. rewrite <- ED. apply in_or_app. right. exact HBm. }
  assert (GA : globals_at B mem'' 3 0 0 0 0 (Z.of_nat (length [entry_relay])) G' 1
                 (Z_to_bv 64 0) (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT)).
  { unfold globals_at, CF.relay_finish_b_c.G_LISTEN, CF.relay_finish_b_c.G_THREAD_UP, G_WAKE0, G_BROKEN, G_GONE,
      G_DEAD, G_EINTR, G_OUTV. rewrite ?SEG.
    split.
    { apply KG; [exact LST|cbn; lia|intros k Hk; cbn in Hk; exists 0x21620, 16; split; [left; reflexivity|lia]|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact WAKE|cbn; lia|intros k Hk; cbn in Hk; exists 0x21620, 16; split; [left; reflexivity|lia]|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact THREAD|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact WB|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact WG|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact WD|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split.
    { apply KG; [exact WE|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split; [apply KH; [exact NSRC1|cbn; unfold G_NSRC; lia]|].
    split; [apply KH; [exact NFD1|cbn; unfold G_NFD; lia]|].
    split; [apply KH; [exact GSRC1|cbn; unfold G_SRC; lia]|].
    split.
    { apply KG; [exact OUTV|cbn; lia|intros k Hk; cbn in Hk; apply in_G_bss; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split; [apply KH; [exact LOCK1|cbn; unfold G_LOCK; lia]|].
    split.
    { apply KG; [exact LOCK28|cbn; unfold G_LOCK; lia|intros k Hk; cbn in Hk; apply in_G_bss; unfold G_LOCK; lia|].
      intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    split; [exact (entry_errno_cells B SEG ETP EOFF mem'')|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [split; [intros _; repeat split|intros X; discriminate X]|].
    rewrite unsigned_lit by lia. lia. }
  assert (RLA : relay_at (rc := rc) B L' A' mem'' 0 1 G' OUT [entry_relay] [(new_src FIRST_FD q pj, 0%nat)]).
  { unfold relay_at. rewrite ?SEG.
    split.
    { exists rest. unfold table_at. rewrite ?SEG. split; [rewrite RL; reflexivity|].
      cbn [concat map]. rewrite app_nil_r, entry_relay_bytes.
      eapply entry_frame_keep; [exact MU3|exact WM3|exact GTAB|].
      left. change (cells_size [CB 896 (new_entry FIRST_FD ++ rest)]) with 896%nat.
      destruct GF' as (_ & GHI & _). unfold SRC_TABLE, SRC_ENTRY, slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    split; [exact GBL'|].
    split; [exact GF'|].
    split; [constructor; [apply entry_relay_ok|constructor]|].
    split; [apply NoDup_ListNoDup; constructor; [intros []|constructor]|].
    split; [constructor; [cbn; unfold FIRST_FD; lia|constructor]|].
    split.
    { constructor; [|constructor]. apply entry_pair_ok.
      eapply (entry_src_rmid rc B (API rc) AX BW); [exact SEG| |exact M2|exact RM3| |exact SRC0].
      - unfold SLOT_STACK in *. lia.
      - intros i Hi. apply PL. apply in_G_bss. unfold G_S in *. lia. }
    split; [apply NoDup_ListNoDup; constructor; [intros []|constructor]|].
    split.
    { intros i Hi Hso. destruct i as [|i]; [discriminate Hso|].
      apply KG; [exact (SOURCES (S i) Hi)|cbn; unfold G_S, SRC_SIZE; lia| |].
      - intros k Hk. apply in_G_bss. cbn in Hk. unfold G_S, SRC_SIZE. lia.
      - intros k Hk. cbn in Hk. unfold G_S, SRC_SIZE, G_NFD, G_LOCK, G_NSRC, G_SRC. lia. }
    rewrite entry_target_addrs. apply NoDup_ListNoDup.
    constructor; [intros [EQ|[EQ|[]]]; [exact (GO (eq_sym EQ))|exact (GQ (eq_sym EQ))]|].
    constructor; [intros [EQ|[]]; exact (OQ (eq_sym EQ))|].
    constructor; [intros []|constructor]. }
  assert (MV : nc_move (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E)
      (view_of G' OUT [entry_relay] [(new_src FIRST_FD q pj, 0%nat)]) L' A' [] (entry_adds q G' C)).
  { assert (NV' : rv_nc (view_of G' OUT [entry_relay] [(new_src FIRST_FD q pj, 0%nat)]) = [G'; OUT; q])
      by reflexivity.
    pose proof (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF HM) as ND0.
    pose proof (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M2) as ND1.
    destruct CASES' as [(HC0 & GNEW & c1 & c2 & d1 & d2 & EB & EC & ED)|(HC16 & HGG & _ & d1 & d2 & EB & ED)].
    - (* The first add makes the table at G'; the start view's G is 0 and has no block. *)
      assert (G0 : G = 0) by (destruct TAB as [(_ & H & _)|(H & _)]; [exact H|lia]).
      rewrite HC0. change (entry_adds q G' 0) with [(q, PARTIAL_BYTES); (G', SRC_TABLE)].
      apply (entry_mv_ins _ _ _ _ _ _ [OUT] [G]); [exact ND0|exact ND1| | | | | | | | |].
      + cbn [rv_nc app]. apply perm_swap.
      + rewrite NV'. cbn [map fst app]. eapply perm_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
      + intros x m Hx. rewrite EB in Hx. apply entry_in_mid in Hx as [Ex|Hx].
        * right. rewrite <- Ex. right. left. reflexivity.
        * rewrite EC in Hx. apply entry_in_mid in Hx as [Ex|Hx].
          -- right. rewrite <- Ex. left. reflexivity.
          -- left. rewrite <- ED. exact Hx.
      + intros x m Hx. rewrite EB. apply entry_in_mid. right. rewrite EC. apply entry_in_mid. right.
        rewrite ED. exact Hx.
      + intros u [<-|[<-|[]]]; [exact QB|exact GBL'].
      + constructor; [intros [E1|[]]; apply GQ; congruence|constructor; [intros []|constructor]].
      + intros u [<-|[<-|[]]] Hin.
        * exact (QNEW q PARTIAL_BYTES Hin ltac:(unfold PARTIAL_BYTES; lia) eq_refl).
        * exact (GNEW G' SRC_TABLE Hin ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) eq_refl).
      + intros x m Hx. exact (entry_blk_nn rc B (API rc) _ _ _ _ x m M2 Hx).
      + intros g [<-|[]] m Hin. pose proof (entry_blk_lo rc B (API rc) _ _ _ _ _ _ HM Hin) as X. lia.
    - (* A later add keeps the table G. *)
      rewrite HC16, HGG. change (entry_adds q G 16) with [(q, PARTIAL_BYTES)].
      rewrite HGG in NV'.
      apply (entry_mv_ins _ _ _ _ _ _ [G; OUT] []); [exact ND0|exact ND1| | | | | | | | |].
      + cbn [rv_nc app]. apply Permutation_refl.
      + rewrite NV'. cbn [map fst app]. apply Permutation_refl.
      + intros x m Hx. rewrite EB in Hx. apply entry_in_mid in Hx as [Ex|Hx].
        * right. rewrite <- Ex. left. reflexivity.
        * left. rewrite <- ED. exact Hx.
      + intros x m Hx. rewrite EB. apply entry_in_mid. right. rewrite ED. exact Hx.
      + intros u [<-|[]]. exact QB.
      + constructor; [intros []|constructor].
      + intros u [<-|[]] Hin. exact (QNEW q PARTIAL_BYTES Hin ltac:(unfold PARTIAL_BYTES; lia) eq_refl).
      + intros x m Hx. exact (entry_blk_nn rc B (API rc) _ _ _ _ x m M2 Hx).
      + intros g []. }
  unfold LI.
  exists fx, L', A', regs'', mem'', md', 3, 0, 0, 0, 0, G', 1,
    (Z_to_bv 64 0), (Z_to_bv 64 NO), (Z_to_bv 64 CAP), (Z_to_bv 64 OUT),
    [entry_relay], [(new_src FIRST_FD q pj, 0%nat)].
  rewrite (unsigned_lit OUT HOUT), entry_target_addrs.
  split; [reflexivity|].
  split; [exact FZ|].
  split; [unfold OPS_MAX; lia|].
  split; [lia|]. split; [exact (walk_start (ss_pl E))|].
  split; [exact Hs|].
  split; [exact HR3|].
  split; [exact M3|]. split; [exact W3|]. split; [exact B3|]. split; [exact INIT'|].
  split; [exact MD2|].
  split; [exact RO3|].
  split; [exact (entry_image_kept CS B API LS SH SK ra empty rc fx j E C G L' A' mem'' md' HF GFR RMA)|].
  split.
  { unfold stack_at. rewrite ?SEG. split; [|split].
    - apply KS; [exact SAVED|unfold slot_sp, SLOT_FRAME; lia|unfold saved_cells; cbn; unfold slot_sp, SLOT_FRAME; lia|right; lia].
    - apply KS; [exact CLB|lia|cbn; unfold slot_sp, SLOT_FRAME; lia|left; cbn; lia].
    - intros HB0. apply S8G. unfold head_body in HB0. apply andb_prop in HB0 as [_ HB0].
      apply Z.ltb_lt in HB0. exact HB0. }
  pose proof (entry_driver_kept CS B API LS SH SK ra empty rc fx j E C G [G'; OUT; q] L' A' mem'' md'
    HF RMA GTIN TAD TBL) as DK.
  split; [exact DK|].
  split; [exact GA|].
  split; [lia|].
  split; [exact OA3|].
  split; [exact RLA|].
  split; [cbn; lia|].
  split; [rewrite entry_cost; lia|].
  pose proof (entry_blk_nd B API LS SH SK ra empty rc fx j E CS _ _ _ _ HF M2) as ND2.
  apply (RIK L' A' qs QLEN ROK' q G' LQ LG); [| reflexivity | reflexivity | cbn [length]; lia | exact MV | exact ND2 | | |].
  - intros qq mm HQ. destruct DK as (_ & _ & _ & DK4). rewrite entry_target_addrs.
    destruct (DK4 qq mm HQ) as [(X & _)|X]; [left; exact X|right; exact X].
  - intros p n n' Hp _ Hin _.
    rewrite (lf_addr (ss_A E) (ss_L E) L' p n HW LY2 Hp).
    change (rv_nc (view_of G' OUT [entry_relay] [(new_src FIRST_FD q pj, 0%nat)])) with [G'; OUT; q].
    change (rv_nc (RV [] [G; OUT] NC_FIX [])) with [G; OUT] in Hin.
    assert (LO : 4096 <= ptr_addr (ss_L E) p)
      by exact (entry_blk_lo rc B (API rc) _ _ _ _ _ _ HM
        (in_map (fun b => (ptr_addr (ss_L E) (fst b), snd b)) _ (p, n) Hp)).
    destruct Hin as [EG|[EO|[]]].
    + destruct HCG as [(_ & G0)|HC16]; [lia|]. left.
      destruct CASES' as [(HC0 & _)|(_ & HGG & _)]; [lia|]. rewrite HGG. exact EG.
    + right. left. exact EO.
  - pose proof (ncs_le_wt B (API rc) L' A' mem'' md' 0 1 G' (Z_to_bv 64 NO) (Z_to_bv 64 CAP) (Z_to_bv 64 OUT)
      [entry_relay] [(new_src FIRST_FD q pj, 0%nat)] M3 OA3 ltac:(rewrite (unsigned_lit OUT HOUT); exact RLA)
      ltac:(cbn [length]; lia) ND2) as NW3.
    rewrite (unsigned_lit OUT HOUT) in NW3. exact NW3.
  - apply Z.eq_le_incl. vm_compute. reflexivity.
Qed.

Lemma entry_small : forall CS RI F B API LS SH SK ra empty rc fx j E,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> ss_n E < INPUT_MAX ->
  (forall C G CAP OUT, ss_T E = kept_blocks C G CAP OUT -> (C = 0 /\ G = 0) \/ C = 16 -> 0 <= CAP <= TBBYTES ->
     (CAP = 0 -> OUT = 0) -> RI E 0 (RV [] [G; OUT] NC_FIX []) (ss_L E) (ss_A E)) ->
  entry_add_resources_s F RI ->
  @op_add_contract fx rc B (API rc) F ->
  SR (ms_segs B) (slot_cfg (fx := fx) B E) (LI (rc := rc) B (API rc) E RI 0 0).
Proof.
  intros CS RI F B API LS SH SK ra empty rc fx j E HF Hs HRI HAR HOA.
  eapply SR_bind; [exact (entry_initialize CS B API LS SH SK ra empty rc fx j E HF Hs)|].
  intros c HC. exact (entry_after_init CS RI F B API LS SH SK ra empty rc fx j E c HF Hs HRI HAR HOA HC).
Qed.

Theorem entry_holds : forall CS RI (F : ResFormT),
  RI_start RI CS ->
  entry_add_resources_s F RI ->
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @op_add_contract fx rc B (API rc) F) ->
  CF.SlotSteps.entry_ok CS RI.
Proof.
  intros CS RI F HRS HAR HOA B API LS SH SK ra empty rc fx j E HF.
  destruct (Z_lt_le_dec (ss_n E) INPUT_MAX) as [Hs|Hl].
  - eapply SR_mono.
    + exact (entry_small CS RI F B API LS SH SK ra empty rc fx j E HF Hs
        (HRS B API LS SH SK ra empty rc fx j E HF) HAR (HOA B API LS SH SK ra empty rc fx (proj1 HF))).
    + intros c Hc. right. exact Hc.
  - eapply SR_mono; [exact (entry_large_holds CS B API LS SH SK ra empty rc fx j E HF Hl)|].
    intros c Hc. left. exact Hc.
Qed.
