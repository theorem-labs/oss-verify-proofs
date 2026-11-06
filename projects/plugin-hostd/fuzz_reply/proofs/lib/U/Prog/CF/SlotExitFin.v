(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its numbers changed; 1527 of its 1633 lines of code are new or changed and 558 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass1w.v, with its module paths and module names changed; 1947 of its 2108 lines of code are new or changed and 1472 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass5L2.v, with its module paths, module names and addresses changed; 1158 of its 1291 lines of code are new or changed and 1975 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotExitScan.v; 553 of its 666 lines of code are new or changed and 1178 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09 YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09 YL01 YL00 YL0g YI06 YI16 YI14 YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import
  PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import
  Img0 Contract ContractT FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require SlotNcWt SlotRI3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotMove SlotExitMove.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c check_shape_ends_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_shape_done_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c op_add_c SlotInv SlotSteps SlotRes SlotReads.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import HarnessGlue HarnessFrame SlotHead SlotHeadQ.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import SlotExitRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotExitWip SlotEntry RelayCap SlotExitFinAux.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import source_reset_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition exit_fin_E (live : bool) (OUT CAP G : Z) (a : Z) : Prop :=
  G_OUTV + 8 <= a < G_OUTV + 16 \/ send_writes live OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/
  G_NSRC <= a < G_NSRC + 4 \/ G_LISTEN <= a < G_CLIENT + 4 \/ G <= a < G + SRC_TABLE.

Definition exit_fin_F (live : bool) (OUT : Z) (es : list rentry) (q : Z) : Prop :=
  (live = true /\ q = OUT) \/ In q (concat (map entry_blocks es)).

Section Mid.
Context {rc : RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable E : sstart.
Variable RI : res_inv.
Variables t k : Z.
Let segs := ms_segs B.

Definition exit_state (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat)) : Prop :=
  0 <= t <= OPS_MAX /\ 0 <= k <= ss_n E /\ ss_n E < INPUT_MAX /\ (t = OPS_MAX \/ k = ss_n E) /\
  head_regs E t k regs /\
  aa_MR API L A mem md /\ WF A /\ bounded A /\ st_init_done A = true /\
  (exists vm, md = with_vmmaps vm (ss_md E)) /\
  ro_agree segs mem /\ image_kept (rc := rc) B E mem /\ stack_at B E t k mem /\
  driver_kept B E (target_addrs G (bv_unsigned out) es hj) L A mem /\
  globals_at B mem cl br gn dd ei (Z.of_nat (length es)) G nfd mx nout cap out /\
  0 <= nfd <= t + 1 /\ output_at (rc := rc) B L A mem nout cap out /\
  relay_at (rc := rc) B L A mem t nfd G (bv_unsigned out) es hj /\
  (length es <= 4)%nat /\ slot_cost es hj <= k /\ RI E k (view_of G (bv_unsigned out) es hj) L A.

Definition exit_mid1 (c : config) : Prop :=
  exists (fx' : FPState) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (m0 : word -> option byte) (md0 : Model)
         (cl br gn dd ei G nfd : Z) (mx nout cap out : word) (es : list rentry) (hj : list (hsrc * nat))
         (tail : list byte) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (OUT' CAP' : Z) (junk' : list byte),
    let N := Z.of_nat (length es) in
    let TOT := entries_total es in
    let CAP := bv_unsigned cap in
    let OUT := bv_unsigned out in
    let live := send_live cl br dd TOT in
    let off := send_off cl br TOT in
    let b := slot_sp E in
    c = mkCfg (@YK11.mkst fx' regs (Z_to_bv 64 (if N =? 0 then 0x14740 else 0x146d4)) mem (seg_rom segs)) md /\
    frm_zero (@fp_csr fx') /\
    exit_state L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out es hj /\
    table_at B m0 G es tail /\
    rmid B API SLOT_STACK (spZ (ss_regs E)) (exit_fin_E live OUT CAP G) (exit_fin_F live OUT es)
      L0 A0 m0 md0 L A mem md /\
    st_init_done A = true /\ ro_agree segs mem /\
    (forall r, callee_saved r -> r <> 8 -> YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)) /\
    (0 < N -> YK11.getr regs (Z_to_bv 5 8) = Z_to_bv 64 N) /\
    rw_cells segs mem (b + 88) (saved_cells (ss_regs E)) /\
    rw_cells segs mem b [C8 (Z_to_bv 64 CLIENT_BASE)] /\
    rw_cells segs mem (b + 16) [C8 (Z_to_bv 64 0)] /\
    (forall i, (i < length es)%nat ->
       rw_cells segs mem (b + 40 + 4 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]) /\
    rw_cells segs mem G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
    rw_cells segs mem G_GONE [C1 (Z_to_bv 8 gn)] /\
    rw_cells segs mem G_NFD [C4 (Z_to_bv 64 nfd)] /\
    rw_cells segs mem (G_LOCK + 12) [CB 28 (nulbytes 28)] /\
    rw_cells segs mem G_THREAD_UP [C1 (Z_to_bv 8 0)] /\
    rw_cells segs mem G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    rw_cells segs mem G_NSRC [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16)] /\
    rw_cells segs mem G_SRC [C8 (Z_to_bv 64 G)] /\
    rw_cells segs mem G_LISTEN [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))] /\
    rw_cells segs mem G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
    rw_cells segs mem G_DEAD [C1 (Z_to_bv 8 dd)] /\
    rw_cells segs mem G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
    (exists ev, rw_cells segs mem (errno_addr B) [C4 ev]) /\
    Forall2 (pair_ok (rc := rc) B L A mem t) es hj /\
    (forall i, (i < 4)%nat -> slot_open hj i = false ->
       rw_cells segs mem (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]) /\
    table_at B mem G (map entry_cleared es) tail /\ In (G, SRC_TABLE) (blocks L A) /\
    (forall q m, In (q, m) (blocks L A) <->
       ((In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (concat (map entry_blocks es))) \/
        (live = true /\ q = OUT' /\ m = CAP') \/ (live = false /\ 0 < CAP /\ q = OUT /\ m = CAP))) /\
    (live = false -> rw_cells segs mem G_OUTV [C8 mx; C8 (Z_to_bv 64 0); C8 cap; C8 out]) /\
    (live = true ->
       TOT <= CAP' /\ CAP' = relay_finish_cap live (bv_unsigned mx) 0 CAP es /\ CAP' <= Z.max CAP (2 * TOT) /\
       fresh_block B OUT' CAP' /\
       (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q (concat (map entry_blocks es)) -> 0 < m ->
          q <> OUT') /\
       bytes_at segs mem OUT' (entries_out es ++ junk') /\ Z.of_nat (length junk') = CAP' - TOT /\
       rw_cells segs mem G_OUTV [C8 mx; C8 (Z_to_bv 64 TOT); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')]) /\
    RI E k (view_of G (if live then OUT' else OUT) [] hj) L A.

End Mid.

Lemma fin_E_hi : forall (rc : RunCeil) B live OUT CAP G a,
  (0 < CAP -> fresh_block (rc := rc) B OUT CAP) -> G + SRC_TABLE <= @YM05.alloc_ceiling rc ->
  @YM05.alloc_ceiling rc <= a -> ~ exit_fin_E live OUT CAP G a.
Proof.
  intros rc B live OUT CAP G a HO HG Ha X. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  unfold exit_fin_E, send_writes in X.
  destruct X as [X|[[X|[X|[X|(_ & X)]]]|[X|[X|[X|X]]]]];
    unfold G_OUTV, G_BROKEN, G_EINTR, G_LOCK, G_NSRC, G_LISTEN, G_CLIENT in *; try lia.
  assert (HC : 0 < CAP) by lia. destruct (HO HC) as (_ & F1 & _). lia.
Qed.

Lemma fin_E_img : forall (rc : RunCeil) B live OUT CAP G a,
  (0 < CAP -> fresh_block (rc := rc) B OUT CAP) -> fresh_block (rc := rc) B G SRC_TABLE -> in_img B a ->
  (a < 0x21620 \/ 0x21628 <= a < 0x318a4 \/ 0x318a5 <= a < 0x318b0 \/ 0x318b1 <= a < 0x318b8 \/
   0x318bc <= a < 0x318e0 \/ 0x318f8 <= a < 0x318fc \/ 0x31900 <= a) ->
  ~ exit_fin_E live OUT CAP G a.
Proof.
  intros rc B live OUT CAP G a HO (G0 & G1 & GN) HI HR X.
  unfold exit_fin_E, send_writes in X.
  destruct X as [X|[[X|[X|[X|(_ & X)]]]|[X|[X|[X|X]]]]];
    unfold G_OUTV, G_BROKEN, G_EINTR, G_LOCK, G_NSRC, G_LISTEN, G_CLIENT in *; try lia.
  - assert (HC : 0 < CAP) by lia. destruct (HO HC) as (_ & _ & ON).
    apply (ON (a - OUT) ltac:(lia)). replace (OUT + (a - OUT)) with a by lia. exact HI.
  - apply (GN (a - G) ltac:(lia)). replace (G + (a - G)) with a by lia. exact HI.
Qed.

Lemma fin_U : forall (rc : RunCeil) B live OUT CAP G a,
  (forall x, 0x318a0 <= x < 0x31aa0 \/ 0x21620 <= x < 0x21630 -> img_plain B x) ->
  (0 < CAP -> fresh_block (rc := rc) B OUT CAP) -> fresh_block (rc := rc) B G SRC_TABLE ->
  (0x21628 <= a < 0x21630 \/ 0x318a0 <= a < 0x318a4 \/ 0x318a5 <= a < 0x318b0 \/ 0x318b1 <= a < 0x318b8 \/
   0x318bc <= a < 0x318e0 \/ 0x318f8 <= a < 0x318fc \/ 0x31900 <= a < 0x31aa0) ->
  img_plain B a /\ ~ exit_fin_E live OUT CAP G a.
Proof.
  intros rc B live OUT CAP G a PL HO HG HR.
  assert (P : img_plain B a) by (apply PL; lia).
  split; [exact P|]. apply (fin_E_img rc B live OUT CAP G a HO HG (proj1 P)). lia.
Qed.

Lemma fin_kept : forall (rc : RunCeil) B (API : AllocAPI B) L A mem md live OUT CAP G es q,
  AllocExtra B (aa_MR API) -> aa_MR API L A mem md ->
  (forall x, 0x21620 <= x < 0x21630 \/ 0x318a0 <= x < 0x31aa0 -> in_img B x) ->
  In (G, SRC_TABLE) (blocks L A) -> (0 < CAP -> In (OUT, CAP) (blocks L A)) ->
  q <> G -> q <> OUT -> ~ In q (concat (map entry_blocks es)) ->
  kept_block (exit_fin_E live OUT CAP G) (exit_fin_F live OUT es) L A q.
Proof.
  intros rc B API L A mem md live OUT CAP G es q AX HM IMG HG HO NG NO NE.
  split; [intros [(_ & X)|X]; [exact (NO X)|exact (NE X)]|].
  intros k i Hq Hi X.
  pose proof (hf_blk_img B API AX L A mem md q k i HM Hq Hi) as NI.
  unfold exit_fin_E, send_writes in X.
  destruct X as [X|[[X|[X|[X|(_ & X)]]]|[X|[X|[X|X]]]]];
    try (apply NI, IMG; unfold G_OUTV, G_BROKEN, G_EINTR, G_LOCK, G_NSRC, G_LISTEN, G_CLIENT in *; lia).
  - assert (HC : 0 < CAP) by lia.
    destruct (blocks_disjoint B API L A mem md q k OUT CAP HM Hq (HO HC) NO); lia.
  - destruct (blocks_disjoint B API L A mem md q k G SRC_TABLE HM Hq HG NG); lia.
Qed.

Lemma fin_src : forall (rc : RunCeil) B (API : AllocAPI B) K sp Ee Ff L A mem md L' A' mem' md' HA h,
  AllocExtra B (aa_MR API) -> blocks_writable B API -> ms_segs B = rsegs -> @YM05.alloc_ceiling rc <= sp - K ->
  aa_MR API L A mem md -> rmid B API K sp Ee Ff L A mem md L' A' mem' md' ->
  (forall i, 0 <= i < 96 -> img_plain B (HA + i) /\ ~ Ee (HA + i)) ->
  (forall q, In q (hs_blocks h) -> kept_block Ee Ff L A q) ->
  src_at (rc := rc) B L A mem HA h -> src_at (rc := rc) B L' A' mem' HA h.
Proof.
  intros rc B API K sp Ee Ff L A mem md L' A' mem' md' HA h AX BW SEG HK HM RM PL KB HS.
  apply src_at_iff in HS. destruct HS as (HS & HE & HH & ND). apply src_at_iff.
  split.
  - eapply (src_base_rmid B API AX BW K sp Ee Ff); [exact SEG|exact HK|exact HM|exact RM|exact HS| |].
    + intros i HI. apply PL. lia.
    + intros q [Hq|Hq]; apply KB; unfold hs_blocks; rewrite !in_app_iff;
        [left; exact Hq|right; left; left; symmetry; exact Hq].
  - split.
    + eapply (list_at_rmid B API AX BW K sp Ee Ff); [exact SEG|exact HK|exact HM|exact RM|exact HE| |].
      * intros i HI. replace (HA + 64 + i) with (HA + (64 + i)) by lia. apply PL. lia.
      * intros q Hq. apply KB. unfold hs_blocks. rewrite !in_app_iff. right; right; left; exact Hq.
    + split; [|exact ND].
      eapply (list_at_rmid B API AX BW K sp Ee Ff); [exact SEG|exact HK|exact HM|exact RM|exact HH| |].
      * intros i HI. replace (HA + 80 + i) with (HA + (80 + i)) by lia. apply PL. lia.
      * intros q Hq. apply KB. unfold hs_blocks. rewrite !in_app_iff. right; right; right; exact Hq.
Qed.

Ltac fin_num := cbn [cells_size csize]; unfold G_OUTV, G_THREAD_UP, G_LOCK, G_NSRC, G_SRC, G_LISTEN, G_BROKEN,
  G_DEAD, G_EINTR, G_WAKE0, G_GONE, G_NFD, G_CLIENT, G_RELAY_LO, G_LOCK_HI, G_S, SRC_SIZE in *; lia.

Theorem exit_fin : forall CS RI (F : ResFormT),
  (forall B API LS SH SK ra empty rc fx, frame_facts B API LS SH SK ra empty ->
     @relay_finish_contract fx rc B (API rc) F) ->
  exit_res_fin_d F RI CS ->
  forall B API LS SH SK ra empty rc fx j E,
    slot_frame B API LS SH SK ra empty rc fx j E CS ->
    forall t k c,
      LI (rc := rc) B (API rc) E RI t k c -> t = OPS_MAX \/ k = ss_n E ->
      SR (ms_segs B) c (exit_mid1 (rc := rc) B (API rc) E RI t k).
Proof.
  intros CS RI F HRF HRES B API LS SH SK ra empty rc fx j E HF t k c HL HX.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (FG : forall a, in_globals frame_G a -> img_plain B a)
    by (unfold frame_facts, img_plain in *; tauto).
  assert (FA : @frame_allocator rc fx B (API rc)).
  { assert (ALL : forall fx, @frame_allocator rc fx B (API rc)) by (unfold frame_facts in FF; tauto).
    exact (ALL fx). }
  assert (AX : AllocExtra B (aa_MR (API rc))) by (unfold frame_allocator in FA; tauto).
  assert (BW : blocks_writable B (API rc)) by (unfold frame_allocator in FA; tauto).
  assert (UNG : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_G a -> ~ owned B L A a)
    by (unfold frame_allocator in FA; tauto).
  assert (ETP : ms_tp B = 0x31b70) by (unfold frame_facts in FF; tauto).
  assert (EOFF : ms_errno_off B = -164) by (unfold frame_facts in FF; tauto).
  assert (EA : errno_addr B = 0x31acc) by (unfold errno_addr; rewrite ETP, EOFF; reflexivity).
  assert (PLG : forall a, 0x318a0 <= a < 0x31aa0 \/ 0x21620 <= a < 0x21630 -> img_plain B a).
  { intros a [Ha|Ha]; apply FG.
    - apply in_G_bss. lia.
    - exists 0x21620, 16. split; [left; reflexivity|lia]. }
  assert (IMG : forall a, 0x21620 <= a < 0x21630 \/ 0x318a0 <= a < 0x31aa0 -> in_img B a).
  { intros a Ha. destruct (PLG a ltac:(lia)) as [X _]. exact X. }
  assert (IMG' : forall a, 0x318a0 <= a < 0x31aa0 -> in_img B a) by (intros a Ha; apply IMG; lia).
  destruct (proj1 (proj1 PRE)) as (MRE & _ & _ & _ & _ & ALIGN & SPLO & SPHI & _ & TPE & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (HB1 : @YM05.alloc_ceiling rc + 65000 <= slot_sp E) by (unfold slot_sp, SLOT_FRAME, SLOT_STACK in *; lia).
  assert (HB2 : slot_sp E + 192 < 2 ^ 63) by (unfold slot_sp, SLOT_FRAME in *; lia).
  assert (HB3 : slot_sp E mod 16 = 0) by (unfold slot_sp, SLOT_FRAME; Z.div_mod_to_equations; lia).
  assert (HB4 : spZ (ss_regs E) = slot_sp E + 192) by (unfold slot_sp, SLOT_FRAME; lia).
  assert (HSL : @YM05.alloc_ceiling rc <= spZ (ss_regs E) - SLOT_STACK) by lia.
  assert (KV : 0 <= RELAY_FINISH_K <= 20000) by (split; apply Z.leb_le; vm_compute; reflexivity).
  destruct HL as (fx' & L0 & A0 & regs0 & m0 & md0 & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & HW & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  assert (EXS : exit_state (rc := rc) B (API rc) E RI t k L0 A0 regs0 m0 md0 cl br gn dd ei G nfd mx nout cap out es hj).
  { exact (conj Ht (conj Hk (conj Hn (conj HX (conj HR (conj HMR (conj HWF (conj HBD (conj HINIT (conj HVM
      (conj HRO (conj HIK (conj HST (conj HDK (conj HGL (conj Hnfd (conj HOUT (conj HREL (conj Hes
      (conj Hcost HRI)))))))))))))))))))). }
  pose proof HREL as (_ & _ & _ & HES0 & _ & _ & HPA0 & _).
  assert (HFE : Forall (fun e => 0 <= re_cap e /\ (re_hp e <> 0 -> 0 <= re_kh e)) es).
  { eapply Forall_impl; [|exact HES0]. intros e He. exact (mv_eok_nn B L0 A0 m0 e He). }
  assert (HTOT : entries_total es < INPUT_MAX).
  { assert (X : entries_total es <= k).
    { eapply Z.le_trans; [|exact Hcost]. apply exit_entries_cost; [exact (Forall2_length HPA0)|].
      eapply Forall_impl; [|exact HES0]. intros e (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia. }
    lia. }
  assert (ND0 : List.NoDup (map fst (blocks L0 A0))).
  { assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    pose proof (NDB L0 A0 m0 md0 HMR) as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X]. }
  destruct (HRES B API LS SH SK ra empty rc fx j E HF k L0 A0 cl br dd G mx cap out es hj HRI ND0 HFE HTOT)
    as (bnd & ROK & ROOM & RIK).
  destruct (exit_head E t k Ht Hk HX) as [HB0 HPC]. rewrite HPC.
  pose proof HR as (B2 & B3 & B4 & B20 & _).
  pose proof HST as (ST1 & ST2 & _).
  pose proof HREL as ((tail & HT & TC) & GIN & GFR & HES & HND & HFD & HPA & NDH & ZH & NDA).
  pose proof HGL as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & ER & RCL & RBR & RGN & RDD &
    REI & _).
  pose proof HOUT as ((O0 & junk0 & HO) & HCAPB).
  destruct (fin_target G (bv_unsigned out) es hj NDA) as (TGO & TGE & TOE & NDE & TPH).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (HROr : ro_agree rsegs m0) by (rewrite <- SEG; exact HRO).
  assert (GLOW : 4096 <= G /\ G + 896 <= @YM05.alloc_ceiling rc).
  { destruct GFR as (X0 & X1 & _). unfold SRC_TABLE, SRC_ENTRY in X1. lia. }
  assert (GTB : G + SRC_TABLE <= @YM05.alloc_ceiling rc) by (unfold SRC_TABLE, SRC_ENTRY; lia).
  assert (GAL : G mod 8 = 0).
  { pose proof GIN as GIN0. unfold blocks in GIN0. apply in_map_iff in GIN0 as ([p k'] & EG & Hp). cbn [fst snd] in EG.
    injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws (API rc)) L0 A0 m0 md0 p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  assert (GIMG : G + 896 <= 0x318a0 \/ 0x31aa0 <= G).
  { pose proof GFR as (_ & _ & NI). destruct (Z_le_gt_dec (G + 896) 0x318a0) as [X|X]; [left; exact X|right].
    destruct (Z_le_gt_dec 0x31aa0 G) as [Y|Y]; [exact Y|exfalso].
    apply (NI (Z.max G 0x318a0 - G) ltac:(unfold SRC_TABLE, SRC_ENTRY; lia)), IMG'. lia. }
  assert (OFR' : 0 < bv_unsigned cap -> fresh_block (rc := rc) B (bv_unsigned out) (bv_unsigned cap)).
  { intros HC. destruct HO as [(X & _)|(_ & _ & _ & FRo & _)]; [lia|exact FRo]. }
  assert (OIN : 0 < bv_unsigned cap -> In (bv_unsigned out, bv_unsigned cap) (blocks L0 A0)).
  { intros HC. destruct HO as [(X & _)|(_ & _ & IN & _)]; [lia|exact IN]. }
  assert (FDB : Forall (fun e => 0 <= re_fd e < 2 ^ 31) es).
  { eapply Forall_impl; [|exact HES]. intros e (_ & _ & _ & _ & X & _). exact X. }
  assert (LEN : length es = length hj) by exact (Forall2_length HPA).
  assert (TOTB : 0 <= entries_total es <= k).
  { split; [apply exit_entries_nonneg|]. eapply Z.le_trans; [|exact Hcost].
    apply exit_entries_cost; [exact LEN|]. eapply Forall_impl; [|exact HES].
    intros e (_ & _ & _ & _ & _ & _ & U & _). rewrite <- U. lia. }
  assert (SCX : forall a n, slot_sp E <= a -> a + Z.of_nat n <= slot_sp E + 192 ->
      exists bs, rw_cells rsegs (normalize rsegs m0) a [CB n bs]).
  { intros a n H1 H2. apply present_rw_cells; [lia|lia|]. intros i Hi.
    assert (W : writable_at rsegs m0 (a + i)).
    { rewrite <- SEG. apply (proj2 (proj2 (proj2 HIK))). left. unfold slot_sp, SLOT_FRAME, SLOT_STACK in *. lia. }
    destruct (writable_hi_present m0 (a + i) ltac:(lia) W) as [v HV]. unfold present. exists v.
    unfold normalize. cbv beta. rewrite (ro_addr_hi (a + i)) by lia. exact HV. }
  destruct (SCX (slot_sp E + 16) 8%nat ltac:(lia) ltac:(lia)) as [j16 J16].
  destruct (SCX (slot_sp E + 40) 4%nat ltac:(lia) ltac:(lia)) as [j40 J40].
  destruct (SCX (slot_sp E + 44) 4%nat ltac:(lia) ltac:(lia)) as [j44 J44].
  destruct (SCX (slot_sp E + 48) 4%nat ltac:(lia) ltac:(lia)) as [j48 J48].
  destruct (SCX (slot_sp E + 52) 4%nat ltac:(lia) ltac:(lia)) as [j52 J52].
  assert (NC : forall a cs, rw_cells (ms_segs B) m0 a cs -> 0x318a0 <= a -> a + Z.of_nat (cells_size cs) <= 0x31aa0 ->
      rw_cells rsegs (normalize rsegs m0) a cs).
  { intros a cs H H1 H2. rewrite SEG in H. apply rw_cells_normalize; [exact HROr|exact H|].
    intros i Hi. apply hf_ro_glob. lia. }
  assert (NSRCn : rw_cells rsegs (normalize rsegs m0) 0x318b8 [C4 (Z_to_bv 64 (Z.of_nat (length es)))]).
  { apply NC; [exact (proj1 (hg_cut _ _ _ [C4 (Z_to_bv 64 (Z.of_nat (length es)))] [C4 (Z_to_bv 64 16)] Q8))|lia|cbn; lia]. }
  assert (GSRCn : rw_cells rsegs (normalize rsegs m0) 0x318d0 [C8 (Z_to_bv 64 G)]).
  { apply NC; [exact Q10|lia|cbn; lia]. }
  assert (NOUTn : rw_cells rsegs (normalize rsegs m0) 0x318e0 [C8 nout]).
  { apply NC; [|lia|cbn; lia]. exact (proj1 (hg_cut _ _ _ [C8 nout] [C8 cap; C8 out]
      (proj2 (hg_cut _ _ _ [C8 mx] [C8 nout; C8 cap; C8 out] Q11)))). }
  assert (FDN : forall i, (i < length es)%nat ->
      rw_cells rsegs (normalize rsegs m0) (G + 56 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]).
  { intros i Hi. pose proof (fin_fd_cell rc B L0 A0 m0 G es tail i HES (conj HT TC) Hi) as H. rewrite SEG in H.
    apply rw_cells_normalize; [exact HROr|exact H|]. intros x Hx. cbn [cells_size csize] in Hx.
    assert (Hi' : 56 * Z.of_nat i + 4 <= 896) by lia.
    pose proof GFR as (_ & _ & NI).
    apply (ro_addr_out B SEG); [lia|].
    replace (G + 56 * Z.of_nat i + x) with (G + (56 * Z.of_nat i + x)) by lia. apply NI. unfold SRC_TABLE, SRC_ENTRY. lia. }
  rewrite SEG.
  eapply kseg; [exact wx_apart_rsegs|exact HROr|exact Hh|exact Hl| | |].
  { unfold Regs6ss.mkR_of, LOOP_EXIT.
    eapply exit_pre_run with (b := slot_sp E) (G := G) (N := Z.of_nat (length es))
      (f0 := nth 0 (map re_fd es) 0) (f1 := nth 1 (map re_fd es) 0) (f2 := nth 2 (map re_fd es) 0)
      (f3 := nth 3 (map re_fd es) 0) (nw := nout) (j16 := j16) (j40 := j40) (j44 := j44) (j48 := j48) (j52 := j52).
    - exact B2.
    - exact B20.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact GAL.
    - apply mem_inv_normalize.
    - lia.
    - apply fin_fd_bound; exact FDB.
    - apply fin_fd_bound; exact FDB.
    - apply fin_fd_bound; exact FDB.
    - apply fin_fd_bound; exact FDB.
    - exact GIMG.
    - exact NSRCn.
    - exact GSRCn.
    - exact NOUTn.
    - exact J16.
    - exact J40.
    - exact J44.
    - exact J48.
    - exact J52.
    - intros HN. pose proof (FDN 0%nat ltac:(lia)) as H. replace (G + 56 * Z.of_nat 0) with G in H by lia. exact H.
    - intros HN. pose proof (FDN 1%nat ltac:(lia)) as H. replace (G + 56 * Z.of_nat 1) with (G + 56) in H by lia. exact H.
    - intros HN. pose proof (FDN 2%nat ltac:(lia)) as H. replace (G + 56 * Z.of_nat 2) with (G + 112) in H by lia. exact H.
    - intros HN. pose proof (FDN 3%nat ltac:(lia)) as H. replace (G + 56 * Z.of_nat 3) with (G + 168) in H by lia. exact H. }
  { intros s0 (x8 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m' & -> & _). do 3 eexists. reflexivity. }
  intros R pc' mn regs1 m1 HQ GR MREL ROS.
  destruct HQ as (x8 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & mn' & EQ & MU0 & WM0 & MIN & X8 & Z16 & Z31 &
    F0 & F1 & F2 & F3).
  injection EQ as ER0 EP EM. subst R pc' mn.
  assert (R1E : YK11.getr regs1 1 = Z_to_bv 64 (if Z.of_nat (length es) =? 0 then 0x14740 else 0x146d4))
    by (rewrite GR; reflexivity).
  assert (R2E : YK11.getr regs1 2 = Z_to_bv 64 (slot_sp E)) by (rewrite GR; exact B2).
  assert (R4E : YK11.getr regs1 4 = YK11.getr (ss_regs E) 4) by (rewrite GR; exact B4).
  assert (SP1 : spZ regs1 = slot_sp E) by (unfold spZ; rewrite R2E; apply unsigned_lit; lia).
  assert (KEEP : forall r, callee_saved r -> r <> 8 ->
      YK11.getr regs1 (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).
  { intros r Hr H8. rewrite GR. unfold callee_saved in Hr.
    assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
  assert (R8 : 0 < Z.of_nat (length es) ->
      YK11.getr regs1 (Z_to_bv 5 8) = Z_to_bv 64 (Z.of_nat (length es))).
  { intros HN. rewrite GR. exact X8. }
  destruct (rmid_norm B (API rc) SLOT_STACK (spZ (ss_regs E))
              (exit_fin_E (send_live cl br dd (entries_total es)) (bv_unsigned out) (bv_unsigned cap) G)
              (exit_fin_F (send_live cl br dd (entries_total es)) (bv_unsigned out) es)
              L0 A0 m0 md0 mn' m1 (exit_pre_writes (slot_sp E)) SEG HROr MREL ROS MU0 WM0 HMR HWF HBD)
    as (RM0 & MU & WM).
  { exact HSL. }
  { intros a Ha. apply (proj2 (proj2 (proj2 HIK))). exact Ha. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & HIN & Hlh). unfold exit_pre_writes in HIN.
    destruct HIN as [EQ|[EQ|[EQ|[]]]]; injection EQ as <- <-.
    - left. unfold SLOT_STACK. lia.
    - left. unfold SLOT_STACK. lia.
    - right. left. unfold G_OUTV. lia. }
  { intros a HOW. pose proof (mr_owned_low _ _ (aa_laws (API rc)) _ _ _ _ a HMR HOW) as HA. apply hg_out.
    intros lo hi HIN. unfold exit_pre_writes in HIN.
    destruct HIN as [EQ|[EQ|[EQ|[]]]]; injection EQ as <- <-; [left; lia|left; lia|].
    destruct (Z_lt_ge_dec a 0x318e0) as [X|X]; [left; lia|].
    destruct (Z_lt_ge_dec a 0x318e8) as [Y|Y]; [|right; lia].
    exfalso. apply (UNG L0 A0 m0 md0 a HMR); [apply in_G_bss; lia|exact HOW]. }
  { intros p n i Hp Hi O. exfalso.
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p n i HMR Hp Hi) as (_ & BB0 & BB1 & _).
    pose proof (ax_blocks_img AX L0 A0 m0 md0 p n i HMR Hp Hi) as NI.
    destruct (hg_not_out _ _ O) as (lo & hi & HIN & Hlh). unfold exit_pre_writes in HIN.
    destruct HIN as [EQ|[EQ|[EQ|[]]]]; injection EQ as <- <-; [lia|lia|]. apply NI, IMG'. lia. }
  pose proof RM0 as (MR1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  assert (RO1 : ro_agree rsegs m1) by exact (ro_agree_same rsegs m0 m1 HROr ROS).
  assert (WM' : wmono (ms_segs B) m0 m1) by (rewrite SEG; exact WM).
  assert (KM : forall a cs, rw_cells (ms_segs B) m0 a cs -> 0 <= a ->
      a + Z.of_nat (cells_size cs) <= @YM05.alloc_ceiling rc ->
      (a + Z.of_nat (cells_size cs) <= 0x318e0 \/ 0x318e8 <= a) -> rw_cells (ms_segs B) m1 a cs).
  { intros a cs H H0 H1 H2. eapply rw_cells_transport; [exact H|exact MU|exact WM'|].
    unfold exit_pre_writes. cbn [disjoint_from]. split; [left; lia|]. split; [left; lia|]. split; [exact H2|exact I]. }
  assert (KS : forall a cs, rw_cells (ms_segs B) m0 a cs -> slot_sp E <= a ->
      (a + Z.of_nat (cells_size cs) <= slot_sp E + 16 \/ slot_sp E + 56 <= a) -> rw_cells (ms_segs B) m1 a cs).
  { intros a cs H H0 H1. eapply rw_cells_transport; [exact H|exact MU|exact WM'|].
    unfold exit_pre_writes. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [right; lia|exact I]. }
  assert (AFW : forall a n kk, fresh_block (rc := rc) B a n -> 0 < n -> 0 <= kk <= n + 7 ->
      disjoint_from (exit_pre_writes (slot_sp E)) a kk).
  { intros a n kk H1 H2 H3. exact (fin_apart rc B (slot_sp E) a n kk IMG' ltac:(lia) H1 H2 H3). }
  assert (REL : forall a cs, rw_cells rsegs mn' a cs -> rw_cells (ms_segs B) m1 a cs).
  { intros a cs H. rewrite SEG. exact (rw_cells_of_rel rsegs m1 mn' a cs MREL H). }
  assert (OUTV1 : rw_cells (ms_segs B) m1 G_OUTV [C8 mx; C8 (Z_to_bv 64 0); C8 cap; C8 out]).
  { pose proof (hg_cut _ _ _ [C8 mx] [C8 nout; C8 cap; C8 out] Q11) as [O1 O2].
    pose proof (hg_cut _ _ _ [C8 nout] [C8 cap; C8 out] O2) as [_ O3].
    apply (hg_join _ _ G_OUTV 0x318e0 [C8 mx] [C8 (Z_to_bv 64 0); C8 cap; C8 out]).
    - apply KM; [exact O1|fin_num..].
    - apply (hg_join _ _ 0x318e0 0x318e8 [C8 (Z_to_bv 64 0)] [C8 cap; C8 out]).
      + exact (REL _ _ Z31).
      + apply KM; [exact O3|fin_num..].
      + reflexivity.
    - reflexivity. }
  pose proof (HRF B API LS SH SK ra empty rc fx' FF) as HC. unfold relay_finish_contract in HC.
  rewrite <- SEG.
  eapply SR_bind.
  { apply (HC L0 A0 regs1 m1 md0 bnd (map short_entry es) 16 G tail [] (O0 ++ junk0) (-1) cl br dd ei mx
             (Z_to_bv 64 0) cap out).
    - exact SEG.
    - eapply (cpk_of_rmid B (API rc)); [exact RM0|exact HINIT| | | | | | | |].
      + rewrite R1E. apply ret_ok_even. destruct (Z.of_nat (length es) =? 0); vm_compute; reflexivity.
      + rewrite R4E. exact TPE.
      + rewrite SP1. exact HB3.
      + rewrite SP1. unfold SLOT_STACK. lia.
      + rewrite SP1. lia.
      + lia.
      + rewrite SP1. lia.
      + rewrite SP1. lia.
    - exact HINIT.
    - unfold errno_addr, ERRNO_OFF. rewrite EOFF. reflexivity.
    - rewrite EA. reflexivity.
    - rewrite EA. unfold G_LOCK_HI. lia.
    - rewrite SEG. exact RO1.
    - intros a Ha. apply PLG. unfold G_RELAY_LO, G_LOCK_HI in Ha. lia.
    - intros a Ha. apply PLG. unfold G_LISTEN, G_CLIENT in Ha. lia.
    - intros a Ha. exact (proj1 (entry_errno_image B SEG ETP EOFF a Ha)).
    - exact (fin_end5 B API LS SH SK ra empty FF).
    - apply KM; [exact Q3|fin_num..].
    - apply KM; [exact Q12|fin_num..].
    - rewrite length_map. apply KM; [exact Q8|fin_num..].
    - apply KM; [exact Q10|fin_num..].
    - apply KM; [exact Q1|fin_num..].
    - rewrite length_map. lia.
    - right. split; [reflexivity|]. split; [exact GIN|]. split; [exact GFR|]. split; [exact TGO|].
      split; [rewrite fin_blocks; exact TGE|].
      split; [rewrite length_map; exact HT|].
      assert (EB : map entry_bytes (map short_entry es) = map entry_bytes es).
      { rewrite map_map. apply map_ext. apply short_entry_bytes. }
      rewrite EB. apply (pre_fresh_cells B m0 m1 _ MU WM' AFW G SRC_TABLE);
        [exact GFR|unfold SRC_TABLE, SRC_ENTRY; lia|cbn; unfold SRC_TABLE, SRC_ENTRY; lia|exact TC].
    - apply Forall_map. eapply Forall_impl; [|exact HES]. intros e He. exact (pre_entry B m0 m1 _ MU WM' AFW L0 A0 e He).
    - unfold entries_disjoint. rewrite fin_blocks. split; [exact NDE|exact TOE].
    - exact RCL.
    - exact RBR.
    - exact RDD.
    - exact REI.
    - apply KM; [exact Q4|fin_num..].
    - apply KM; [exact Q6|fin_num..].
    - apply KM; [exact Q7|fin_num..].
    - exact OUTV1.
    - destruct ER as [ev ER]. exists ev. rewrite EA in ER |- *. apply KM; [exact ER|fin_num..].
    - rewrite (unsigned_lit 0) by lia.
      destruct HO as [(HC0 & HO0 & HN0 & HOE)|(HC0 & HN0 & IN0 & FR0 & BY0 & LO0 & LJ0)].
      + left. repeat split; first [assumption|reflexivity].
      + right. split; [exact HC0|]. split; [lia|]. split; [exact IN0|]. split; [exact FR0|].
        split; [cbn [app]; exact (pre_fresh_bytes B m0 m1 _ MU AFW (bv_unsigned out) (bv_unsigned cap) (O0 ++ junk0)
                                    FR0 HC0 ltac:(rewrite length_app; lia) BY0)|].
        split; [reflexivity|]. rewrite length_app. lia.
    - rewrite (unsigned_lit 0) by lia. rewrite fin_total. unfold INPUT_MAX in *. lia.
    - exact ROK.
    - rewrite fin_total, fin_tr. rewrite (unsigned_lit 0) by lia. exact ROOM. }
  intros c2 (L2 & A2 & regs2 & m2 & md2 & OUT' & CAP' & junk' & -> & RP & INIT2 & RF2 & RO2 & THR2 & LOCK2 & NSRC2 &
    GSRC2 & LIST2 & TAB2 & BRK2 & DEAD2 & EINTR2 & ERR2 & BLK2 & NLIVE & YLIVE).
  rewrite !fin_total in *. rewrite !fin_blocks in *. rewrite !fin_tr in *. rewrite !fin_cleared in *.
  rewrite !fin_out in *. rewrite !fin_rout in *. rewrite !fin_cap in *. rewrite (unsigned_lit 0) in * by lia.
  destruct RF2 as (qs & QLEN & QOK & QLK).
  destruct (rp_split B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as [RM1 PR].
  rewrite SP1 in RM1.
  assert (RM1' : rmid B (API rc) RELAY_FINISH_K (slot_sp E)
      (exit_fin_E (send_live cl br dd (entries_total es)) (bv_unsigned out) (bv_unsigned cap) G)
      (exit_fin_F (send_live cl br dd (entries_total es)) (bv_unsigned out) es) L0 A0 m1 md0 L2 A2 m2 md2).
  { eapply rmid_EF; [exact RM1| |].
    - intros a X. cbv beta in X. unfold exit_fin_E. destruct X as [X|[X|[X|[X|(_ & X)]]]]; tauto.
    - intros q X. exact X. }
  assert (RM1w : rmid B (API rc) SLOT_STACK (spZ (ss_regs E))
      (exit_fin_E (send_live cl br dd (entries_total es)) (bv_unsigned out) (bv_unsigned cap) G)
      (exit_fin_F (send_live cl br dd (entries_total es)) (bv_unsigned out) es) L0 A0 m1 md0 L2 A2 m2 md2).
  { apply (rmid_widen B (API rc) RELAY_FINISH_K (slot_sp E)); [exact MR1| | | | | | |exact RM1'].
    - unfold SLOT_STACK. lia.
    - lia.
    - exact HSL.
    - lia.
    - intros a Ha. apply SC1. left. exact Ha.
    - intros a Ha. apply (fin_E_hi rc B _ _ _ G a OFR' GTB). lia. }
  pose proof (rmid_seq B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0 RM1w) as RM01.
  assert (RMF : rmid B (API rc) SLOT_STACK (spZ (ss_regs E))
      (exit_fin_E (send_live cl br dd (entries_total es)) (bv_unsigned out) (bv_unsigned cap) G)
      (exit_fin_F (send_live cl br dd (entries_total es)) (bv_unsigned out) es) L0 A0 m0 md0 L2 A2 m2 md2).
  { eapply rmid_EF; [exact RM01|intros a [X|X]; exact X|intros q [X|X]; exact X]. }
  assert (KH : forall a cs, rw_cells (ms_segs B) m1 a cs -> slot_sp E <= a ->
      a + Z.of_nat (cells_size cs) <= slot_sp E + 192 -> rw_cells (ms_segs B) m2 a cs).
  { intros a cs H H1 H2. eapply (rmid_rw_hi B (API rc)); [| |exact MR1|exact RM1'|exact H|exact H1| |].
    - lia.
    - rewrite EA. lia.
    - lia.
    - intros i Hi. apply (fin_E_hi rc B _ _ _ G _ OFR' GTB). lia. }
  assert (KG2 : forall a cs, rw_cells (ms_segs B) m0 a cs ->
      (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
         0x21628 <= a + i < 0x21630 \/ 0x318a0 <= a + i < 0x318a4 \/ 0x318a5 <= a + i < 0x318b0 \/
         0x318b1 <= a + i < 0x318b8 \/ 0x318bc <= a + i < 0x318e0 \/ 0x318f8 <= a + i < 0x318fc \/
         0x31900 <= a + i < 0x31aa0) ->
      rw_cells (ms_segs B) m2 a cs).
  { intros a cs H D. apply (rmid_rw_img B (API rc) AX SLOT_STACK (spZ (ss_regs E)) _ _ L0 A0 m0 md0 L2 A2 m2 md2 a cs
      (hg_img_low B SEG) HSL HMR RMF H).
    intros i Hi. exact (fin_U rc B _ _ _ G (a + i) PLG OFR' GFR (D i Hi)). }
  assert (PA2 : Forall2 (pair_ok (rc := rc) B L2 A2 m2 t) es hj).
  { apply (fin_forall2 _ _ _ _ _ _ HPA). intros e p He Hp HP. unfold pair_ok in HP |- *. cbv zeta in HP |- *.
    destruct HP as (SRC & HI4 & REST). split; [|split; [exact HI4|exact REST]].
    apply (fin_src rc B (API rc) SLOT_STACK (spZ (ss_regs E)) _ _ L0 A0 m0 md0 L2 A2 m2 md2 _ _ AX BW SEG HSL HMR RMF);
      [|intros q Hq; destruct (TPH p q Hp Hq) as (T1 & T2 & T3);
        exact (fin_kept rc B (API rc) L0 A0 m0 md0 _ _ _ G es q AX HMR IMG GIN OIN T1 T2 T3)|exact SRC].
    intros i Hi. apply (fin_U rc B _ _ _ G _ PLG OFR' GFR). unfold G_S, SRC_SIZE. lia. }
  assert (ZH2 : forall i, (i < 4)%nat -> slot_open hj i = false ->
      rw_cells (ms_segs B) m2 (G_S + SRC_SIZE * Z.of_nat i) [CB 96%nat (nulbytes 96)]).
  { intros i Hi HZ. apply KG2; [exact (ZH i Hi HZ)|]. intros x Hx. cbn [cells_size csize] in Hx.
    unfold G_S, SRC_SIZE. lia. }
  assert (WAKE2 : rw_cells (ms_segs B) m2 G_WAKE0 [C4 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (-1))]).
  { apply KG2; [exact Q2|]. intros x Hx. cbn [cells_size csize] in Hx. unfold G_WAKE0. lia. }
  assert (GONE2 : rw_cells (ms_segs B) m2 G_GONE [C1 (Z_to_bv 8 gn)]).
  { apply KG2; [exact Q5|]. intros x Hx. cbn [cells_size csize] in Hx. unfold G_GONE. lia. }
  assert (NFD2 : rw_cells (ms_segs B) m2 G_NFD [C4 (Z_to_bv 64 nfd)]).
  { apply KG2; [exact Q9|]. intros x Hx. cbn [cells_size csize] in Hx. unfold G_NFD. lia. }
  assert (LCK2 : rw_cells (ms_segs B) m2 (G_LOCK + 12) [CB 28 (nulbytes 28)]).
  { apply KG2; [exact Q13|]. intros x Hx. cbn [cells_size csize] in Hx. unfold G_LOCK. lia. }
  assert (SAV2 : rw_cells (ms_segs B) m2 (slot_sp E + 88) (saved_cells (ss_regs E))).
  { apply KH; [apply KS; [exact ST1|lia|right; lia]|lia|unfold saved_cells; cbn [cells_size csize]; lia]. }
  assert (CLB2 : rw_cells (ms_segs B) m2 (slot_sp E) [C8 (Z_to_bv 64 CLIENT_BASE)]).
  { apply KH; [apply KS; [exact ST2|lia|left; cbn; lia]|lia|cbn; lia]. }
  assert (Z162 : rw_cells (ms_segs B) m2 (slot_sp E + 16) [C8 (Z_to_bv 64 0)]).
  { apply KH; [exact (REL _ _ Z16)|lia|cbn; lia]. }
  assert (FD2 : forall i, (i < length es)%nat ->
      rw_cells (ms_segs B) m2 (slot_sp E + 40 + 4 * Z.of_nat i) [C4 (Z_to_bv 64 (nth i (map re_fd es) 0))]).
  { intros i Hi. destruct i as [|[|[|[|i]]]]; [| | | |lia].
    - replace (slot_sp E + 40 + 4 * Z.of_nat 0) with (slot_sp E + 40) by lia.
      apply KH; [exact (REL _ _ (F0 ltac:(lia)))|lia|cbn; lia].
    - replace (slot_sp E + 40 + 4 * Z.of_nat 1) with (slot_sp E + 44) by lia.
      apply KH; [exact (REL _ _ (F1 ltac:(lia)))|lia|cbn; lia].
    - replace (slot_sp E + 40 + 4 * Z.of_nat 2) with (slot_sp E + 48) by lia.
      apply KH; [exact (REL _ _ (F2 ltac:(lia)))|lia|cbn; lia].
    - replace (slot_sp E + 40 + 4 * Z.of_nat 3) with (slot_sp E + 52) by lia.
      apply KH; [exact (REL _ _ (F3 ltac:(lia)))|lia|cbn; lia]. }
  assert (KEEP2 : forall r, callee_saved r -> r <> 8 ->
      YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).
  { intros r Hr H8. rewrite (PR r Hr). exact (KEEP r Hr H8). }
  assert (R82 : 0 < Z.of_nat (length es) ->
      YK11.getr regs2 (Z_to_bv 5 8) = Z_to_bv 64 (Z.of_nat (length es))).
  { intros HN. rewrite (PR 8 ltac:(unfold callee_saved; lia)). exact (R8 HN). }
  assert (MOVE : nc_move (view_of G (bv_unsigned out) es hj) L0 A0
      (view_of G (if send_live cl br dd (entries_total es) then OUT' else bv_unsigned out) [] hj) L2 A2
      (out_move_dels (bv_unsigned out) (bv_unsigned cap)
         (if send_live cl br dd (entries_total es) then OUT' else bv_unsigned out)
         (relay_finish_cap (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es) ++
       ent_dels es)
      (out_move_adds (bv_unsigned out) (bv_unsigned cap)
         (if send_live cl br dd (entries_total es) then OUT' else bv_unsigned out)
         (relay_finish_cap (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es))).
  { assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    pose proof RMF as (HM2 & _).
    apply (mv_fin L0 A0 L2 A2 G (bv_unsigned out) (bv_unsigned cap) es hj (send_live cl br dd (entries_total es))
             OUT' CAP' (relay_finish_cap (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es)).
    - pose proof (NDB L0 A0 m0 md0 HMR) as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X].
    - pose proof (NDB L2 A2 m2 md2 HM2) as X. first [exact (proj1 (NoDup_ListNoDup _) X)|exact X].
    - intros q m Hq. exact (mv_blk B (API rc) L0 A0 m0 md0 q m HMR Hq).
    - first [exact (proj1 (NoDup_ListNoDup _) NDA)|exact NDA].
    - eapply Forall_impl; [|exact HES0]. intros e He. exact (mv_eok B L0 A0 m0 e He).
    - exact (proj1 (bv_unsigned_in_range _ cap)).
    - intros C0. destruct HO as [(_ & X & _)|(X & _)]; [exact X|lia].
    - exact OIN.
    - intros HLV. rewrite HLV. apply mv_fin_cap_off.
    - intros HLV. destruct (YLIVE HLV) as (Y1 & Y2 & _ & Y4 & _).
      assert (TP : 0 < entries_total es).
      { pose proof (exit_entries_nonneg es) as N0. unfold send_live, send_off in HLV.
        destruct (Z.eqb_spec (entries_total es) 0) as [Z0|Z0]; [|lia].
        try rewrite Z0 in HLV. try rewrite Z.eqb_refl in HLV. rewrite ?orb_true_r in HLV. cbn in HLV. discriminate HLV. }
      split; [exact Y2|]. split; [|exact Y4].
      rewrite <- Y2. lia.
    - exact BLK2. }
  apply SR_ret. unfold exit_mid1.
  exists fx', L0, A0, regs0, m0, md0, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, es, hj, tail, L2, A2, regs2, m2,
    md2, OUT', CAP', junk'.
  cbv zeta.
  split; [rewrite <- R1E; reflexivity|].
  split; [exact FZ|].
  split; [exact EXS|].
  split; [exact (conj HT TC)|].
  split; [exact RMF|].
  split; [exact INIT2|].
  split; [exact RO2|].
  split; [exact KEEP2|].
  split; [exact R82|].
  split; [exact SAV2|].
  split; [exact CLB2|].
  split; [exact Z162|].
  split; [exact FD2|].
  split; [exact WAKE2|].
  split; [exact GONE2|].
  split; [exact NFD2|].
  split; [exact LCK2|].
  split; [exact THR2|].
  split; [exact LOCK2|].
  split; [exact NSRC2|].
  split; [exact GSRC2|].
  split; [exact LIST2|].
  split; [exact BRK2|].
  split; [exact DEAD2|].
  split; [exact EINTR2|].
  split; [exact ERR2|].
  split; [exact PA2|].
  split; [exact ZH2|].
  split; [exact (proj1 (TAB2 eq_refl))|].
  split; [exact (proj2 (TAB2 eq_refl))|].
  split; [exact BLK2|].
  split; [exact NLIVE|].
  assert (ND2 : List.NoDup (map fst (blocks L2 A2))).
  { assert (NDB : blocks_nodup B (API rc)) by (unfold frame_allocator in FA; tauto).
    pose proof RMF as (HM2 & _). pose proof (NDB L2 A2 m2 md2 HM2) as X.
    first [exact (proj1 (NoDup_ListNoDup _) X)|exact X]. }
  pose proof RMF as (_ & _ & _ & LY2 & _).
  split; [|refine (RIK L2 A2 qs QLEN QOK G (if send_live cl br dd (entries_total es) then OUT' else bv_unsigned out)
                      [] hj _ eq_refl eq_refl (Nat.le_0_l 4) _
                      (if send_live cl br dd (entries_total es) then OUT' else bv_unsigned out) _ _ MOVE ND2 _ _ _)].
  8: { apply fin_wt_clear. eapply Forall_impl; [|exact HES]. intros e (_ & _ & _ & _ & _ & _ & U & _).
       rewrite <- U. lia. }
  7: { apply fin_ncs_view; [exact ND2|exact (proj2 (TAB2 eq_refl))| |exact (fin_src_wt rc B L2 A2 m2 t es hj ND2 PA2)|
         rewrite <- LEN; exact Hes].
       pose proof (relay_finish_cap_le (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0 (bv_unsigned cap) es)
         as CL.
       destruct (send_live cl br dd (entries_total es)) eqn:HLV.
       - change (CF.SlotRI3.nc_sz L2 A2 OUT' <= TBBYTES). destruct (YLIVE eq_refl) as (_ & Y2 & _).
         rewrite (CF.SlotNcWt.nw_sz_at L2 A2 OUT' CAP' ND2
                    (proj2 (BLK2 OUT' CAP') (or_intror (or_introl (conj eq_refl (conj eq_refl eq_refl)))))).
         unfold TBBYTES, INPUT_MAX in *. lia.
       - change (CF.SlotRI3.nc_sz L2 A2 (bv_unsigned out) <= TBBYTES).
         apply Z.le_trans with (bv_unsigned cap); [|exact HCAPB].
         apply fin_sz_le; [exact ND2|exact (proj1 (bv_unsigned_in_range _ cap))|].
         intros m Hm. apply BLK2 in Hm as [(_ & NO & _)|[(X & _)|(_ & _ & _ & ->)]];
           [exfalso; exact (NO eq_refl)| |lia].
         discriminate X. }
  6: { intros p n n' H1 H2 H3 _.
       exact (fin_keep_addr A0 L0 L2 A2 _ _ HWF LY2
                (fin_view_keep G (bv_unsigned out) es hj _ OUT' L0 A0 L2 A2 CAP' (bv_unsigned cap)
                   (fun q m X => proj1 (BLK2 q m) X)) p n n' H1 H2 H3). }
  5: { intros HLV. destruct (YLIVE HLV) as (_ & Y2 & _). rewrite <- Y2. pose proof (QLK HLV) as X.
       rewrite HLV in X |- *. exact X. }
  4: { intros HLV. rewrite HLV. reflexivity. }
  3: { rewrite <- LEN. exact Hes. }
  2: { intros q m X. apply BLK2 in X.
       destruct X as [(X & _)|[(HLV & -> & _)|(HLV & _ & -> & _)]]; [left; exact X| |];
         right; right; left; rewrite HLV; reflexivity. }
  intros HLV. destruct (YLIVE HLV) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
  split; [lia|]. split; [exact Y2|].
  split; [rewrite Y2; pose proof (relay_finish_cap_le (send_live cl br dd (entries_total es)) (bv_unsigned mx) 0
    (bv_unsigned cap) es) as CL; rewrite Z.add_0_l in CL; exact CL|].
  split; [exact Y3|]. split; [exact Y4|].
  split; [exact Y5|]. split; [lia|].
  rewrite Z.add_0_l in Y7. exact Y7.
Qed.
