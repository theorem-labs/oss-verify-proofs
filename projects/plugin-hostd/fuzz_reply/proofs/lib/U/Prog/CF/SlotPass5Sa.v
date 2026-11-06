(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 625 of its 671 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/CF/SlotPass9G.v, with its module names and numbers changed; 354 of its 436 lines of code are new or changed and 589 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import Statement.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import StatementKept.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import send_line_c gesture_end_c relay_event_c RelayFrame RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import drain_b_c source_reset_c op_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import check_bounded_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotInv SlotSteps SlotHead SlotHeadP SlotRes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotHeadQD SlotPass1 SlotPass9G.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_remove_b_c relay_instance_gone_b_c SlotPass5Run SlotPass5A.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RG0u (E : sstart) (t k id : Z) :
    list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop :=
  fun _ _ no regs => no = 0 /\ base_regs E regs /\
    getr regs 23 = Z_to_bv 64 (slot_sp E + 32) /\ getr regs 25 = Z_to_bv 64 DIV10 /\
    getr regs 21 = Z_to_bv 64 10 /\ getr regs 27 = Z_to_bv 64 (G_S + 4) /\ getr regs 24 = Z_to_bv 64 1 /\
    getr regs 8 = Z_to_bv 64 (ss_p E + k) /\ getr regs 26 = Z_to_bv 64 (ss_n E - k) /\
    getr regs 22 = Z_to_bv 64 t /\ 0 <= id < 256 /\ getr regs 9 = Z_to_bv 64 id /\
    getr regs 18 = Z_to_bv 64 G_S /\ getr regs 19 = Z_to_bv 64 (slot_sp E + 16).

Definition J0u_stack (B : malloc_syms) (E : sstart) (id : Z) (fs os : list Z) (junk : list byte)
    (mem : word -> option byte) : Prop :=
  (forall i, (i < 4)%nat -> rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i)
      [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) /\
  (forall i, (i < 4)%nat -> (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31) /\
  wr_at (ms_segs B) mem (slot_sp E + 16) 16 /\
  rw_cells (ms_segs B) mem (slot_sp E + 32) [C8 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem (slot_sp E + 40)
    [CB 48 (pf_bytes (instance_prefix id ++ [0]) ++ skipn (length (instance_prefix id) + 1) junk)].

Definition J0u {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (RI : res_inv) (t k : Z)
    (c : config) : Prop :=
  exists (id : Z) (fs os : list Z) (junk : list byte),
    MI (rc := rc) B API E RI t k 0x144a0 (RG0u E t k id) c /\
    J0u_stack B E id fs os junk (ms_mem (cfg_ms c)).

Lemma s5u_out : forall SP x, x < SP - SNPRINTF_K \/ SP <= x < SP + 16 \/ SP + 88 <= x -> outside (g5_W SP) x.
Proof. intros SP x H. unfold g5_W, SNPRINTF_K in *. cbn [outside]. split; [lia|split; [lia|exact I]]. Qed.

Lemma s5u_dj : forall SP a n,
  a + n <= SP - SNPRINTF_K \/ (SP <= a /\ a + n <= SP + 16) \/ SP + 88 <= a -> disjoint_from (g5_W SP) a n.
Proof. intros SP a n H. unfold g5_W, SNPRINTF_K in *. cbn [disjoint_from]. split; [lia|split; [lia|exact I]]. Qed.

Lemma s5u_low : forall SP a n, a + n <= 2 ^ 21 -> 2 ^ 21 + SNPRINTF_K <= SP -> disjoint_from (g5_W SP) a n.
Proof. intros SP a n H1 H2. apply s5u_dj. left. lia. Qed.

Lemma s5u_eq : forall segs W (m m' : word -> option byte) x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mbyte segs m' x = mbyte segs m x /\ (writable_at segs m' x <-> writable_at segs m x) /\
  (present m' x <-> present m x).
Proof.
  intros segs W m m' x MU Hx HO.
  assert (E : m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
  { apply MU. rewrite unsigned_lit by lia. exact HO. }
  unfold mbyte, writable_at, wview, present. rewrite E. split; [reflexivity|split; reflexivity].
Qed.

Lemma s5u_null8 : forall segs m A, rw_cells segs m A [CB 96 (nulbytes 96)] ->
  rw_cells segs m A [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Proof.
  intros segs m A ((_ & BY) & (W0 & W1 & W2)).
  cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
  change (nulbytes 96) with (nulbytes 8 ++ nulbytes 88) in BY.
  apply bytes_at_app in BY. destruct BY as (BY & _).
  split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. change (le4 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ []) with (nulbytes 8). exact BY.
  - cbn [cells_size csize] in *. split; [exact W0|]. split; [lia|]. intros i Hi. apply W2. lia.
Qed.

Lemma s5u_slot : forall rc B L A mem t nfd G OUT es hj i,
  ms_segs B = rsegs -> relay_at (rc := rc) B L A mem t nfd G OUT es hj -> (i < 4)%nat ->
  exists f o, rw_cells rsegs mem (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 f); C4 (Z_to_bv 64 o)] /\
    (o = 0 \/ o = 1) /\ 0 <= f < 2 ^ 31.
Proof.
  intros rc B L A mem t nfd G OUT es hj i SEG HR Hi.
  destruct HR as (_ & _ & _ & _ & _ & _ & HP & _ & HC & _).
  destruct (slot_open hj i) eqn:SO.
  - unfold slot_open in SO. apply existsb_exists in SO. destruct SO as (x & Hx & Hq).
    apply Nat.eqb_eq in Hq. subst x. apply in_map_iff in Hx. destruct Hx as (p & Hp2 & Hp).
    destruct (pair_find _ _ _ _ _ _ HP Hp) as (e & HPO).
    destruct HPO as (HS & _). destruct HS as (HS & _ & _ & Hopen & Hfd & _).
    rewrite Hp2, SEG in HS.
    pose proof (g9_cut mem _ [C4 (Z_to_bv 64 (hs_fd (fst p))); C4 (Z_to_bv 64 (hs_open (fst p)))]
      [C4 (Z_to_bv 64 (hs_closed (fst p))); C4 (Z_to_bv 64 (hs_eintr (fst p)))] HS) as (HS1 & _).
    exists (hs_fd (fst p)), (hs_open (fst p)). split; [exact HS1|]. split; [right; exact Hopen|exact Hfd].
  - specialize (HC i Hi SO). rewrite SEG in HC. exists 0, 0. split; [apply s5u_null8; exact HC|].
    split; [left; reflexivity|lia].
Qed.

Lemma s5u_slots : forall rc B L A mem t nfd G OUT es hj,
  ms_segs B = rsegs -> relay_at (rc := rc) B L A mem t nfd G OUT es hj ->
  exists fs os : list Z, forall i, (i < 4)%nat ->
    rw_cells rsegs mem (G_S + SRC_SIZE * Z.of_nat i) [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))] /\
    (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31.
Proof.
  intros rc B L A mem t nfd G OUT es hj SEG HR.
  destruct (s5u_slot rc B L A mem t nfd G OUT es hj 0 SEG HR ltac:(lia)) as (f0 & o0 & S0).
  destruct (s5u_slot rc B L A mem t nfd G OUT es hj 1 SEG HR ltac:(lia)) as (f1 & o1 & S1).
  destruct (s5u_slot rc B L A mem t nfd G OUT es hj 2 SEG HR ltac:(lia)) as (f2 & o2 & S2).
  destruct (s5u_slot rc B L A mem t nfd G OUT es hj 3 SEG HR ltac:(lia)) as (f3 & o3 & S3).
  exists [f0; f1; f2; f3], [o0; o1; o2; o3].
  intros i Hi. destruct i as [|[|[|[|i]]]]; [exact S0|exact S1|exact S2|exact S3|lia].
Qed.

Definition p5u_post (P N K SP : Z) (junk : list byte) (x3 x4 x21 x22 x23 x25 x27 : word)
    (m : word -> option byte) (ms : machine_state) : Prop :=
  exists (id K' : Z) (x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word) (Ft : bvmap 5 word) (fc' : bv 32)
         (m3 : word -> option byte),
    ms = MS (mkR (Z_to_bv 64 0x14498) (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K')) (Z_to_bv 64 id)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 G_S) (Z_to_bv 64 (SP + 16)) (Z_to_bv 64 0x318a0) x21 x22 x23
               (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K')) x27 x28 x29 x30 x31) Ft (Z_to_bv 64 0x144a0) fc' None
            m3 (seg_rom rsegs) /\
    0 <= id < 256 /\ (K < N /\ K' = K + 1 \/ K = N /\ K' = K) /\ frm0 fc' /\
    munch (g5_W SP) m m3 /\ wmono rsegs m m3 /\ wr_at rsegs m3 (SP + 16) 16 /\
    rw_cells rsegs m3 (SP + 32) [C8 (Z_to_bv 64 0)] /\
    rw_cells rsegs m3 (SP + 40)
      [CB 48 (pf_bytes (instance_prefix id ++ [0]) ++ skipn (length (instance_prefix id) + 1) junk)].

Lemma p5u_run : snprintf_contract -> forall (P N K SP g : Z) (junk : list byte)
    (x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27 x28 x29 x30 x31 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b : byte),
  0 <= K <= N -> N < 2 ^ 26 -> 0 < P -> P + N < 2 ^ 64 ->
  (K < N -> ov_read_bytes rsegs m (Z_to_bv 64 (P + K)) 1 = Some [b]) ->
  IMG_END + SNPRINTF_K <= SP -> 2 ^ 21 + SNPRINTF_K <= SP -> SP + 88 <= TASK_SIZE ->
  (forall a, SP - SNPRINTF_K <= a < SP + 88 -> writable_at rsegs m a) ->
  bytes_at rsegs m (SP + 40) junk -> length junk = 48%nat ->
  ro_agree rsegs m -> frm0 fc ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 (Z_to_bv 64 g)) ->
  evt rsegs (p5u_post P N K SP junk x3 x4 x21 x22 x23 x25 x27 m)
    (MS (mkR x1 (Z_to_bv 64 SP) x3 x4 x5 x6 x7 (Z_to_bv 64 (P + K)) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
      (Z_to_bv 64 0x318a0) x21 x22 x23 (Z_to_bv 64 1) x25 (Z_to_bv 64 (N - K)) x27 x28 x29 x30 x31) F
      (Z_to_bv 64 0x143d8) fc None m (seg_rom rsegs)).
Proof.
  intros SNP P N K SP g junk x1 x3 x4 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x25 x27
    x28 x29 x30 x31 F fc m b HK HN HP HPN RB HI1 HI2 HTS WS JB JL RO FZ GW GU.
  assert (KV : SNPRINTF_K = 5936) by reflexivity.
  assert (TV : TASK_SIZE = 2 ^ 47) by reflexivity.
  assert (WR : forall a n, SP - SNPRINTF_K <= a -> a + n <= SP + 88 -> 0 <= n -> wr_at rsegs m a n).
  { intros a n H1 H2 H3. split; [lia|]. split; [lia|]. intros i Hi. exact (WS (a + i) ltac:(lia)). }
  pose (m1 := write_to_mem m (Z_to_bv 64 (SP + 32)) (le8 (Z_to_bv 64 0))).
  assert (MU1 : munch (g5_W SP) m m1).
  { unfold m1. apply munch_write; [intros x _; reflexivity|lia|rewrite length_le8; lia|].
    unfold g5_W. cbn [inside]. right. left. rewrite length_le8. lia. }
  assert (WM1 : wmono rsegs m m1) by (unfold m1; apply wmono_write; intros x H; exact H).
  eapply evt_cut.
  { eapply (op5_seg_a P N K SP); [exact HK|exact HN|exact HP|exact HPN|exact RB|].
    exact (wr_at_store_ok rsegs m SP 88 32 8 (WR SP 88 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)). }
  intros ms1 (s0 & s1 & s10 & K' & -> & Hs0 & Hs10 & HC). subst s0 s10.
  assert (IDX : exists id, 0 <= id < 256 /\ s1 = Z_to_bv 64 id /\ (K < N /\ K' = K + 1 \/ K = N /\ K' = K)).
  { destruct HC as [(HKN & HK' & Hs1) | (HKN & HK' & Hs1)].
    - exists (bv_unsigned b).
      assert (BR : 0 <= bv_unsigned b < 256) by exact (bv_unsigned_in_range _ b).
      split; [lia|]. split; [exact Hs1|left; lia].
    - exists 0. split; [lia|]. split; [exact Hs1|right; lia]. }
  destruct IDX as (id & Hid & -> & HKK). clear HC.
  eapply evt_cut.
  { eapply (g5a_snp SNP) with (SP := SP) (id := id) (junk := junk) (canary := Z_to_bv 64 g).
    - exact Hid.
    - exact HI1.
    - exact HI2.
    - exact HTS.
    - intros a Ha. exact (WM1 _ (WS a ltac:(lia))).
    - split; [split|].
      + cbn [cells_wf cell_wf]. split; [exact JL|exact I].
      + cbn [cells_bytes cbytes]. rewrite app_nil_r.
        apply bytes_at_write_other; [exact JB|lia|rewrite length_le8; lia|rewrite length_le8, JL; lia].
      + cbn [cells_size csize]. eapply wr_at_transport; [exact (WR (SP + 40) 48 ltac:(lia) ltac:(lia) ltac:(lia))|].
        exact WM1.
    - apply (g5a_ro_hi (g5_W SP) m m1 MU1); [|exact RO]. intros x Hx. apply s5u_out. lia.
    - exact FZ.
    - apply bytes_at_write_other; [exact GW|lia|rewrite length_le8; lia|rewrite !length_le8; unfold GOT_GUARD; lia].
    - apply bytes_at_write_other; [exact GU|lia|rewrite length_le8; lia|rewrite !length_le8; unfold GUARD; lia]. }
  intros ms2 HP2.
  destruct HP2 as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & Ft & fc' & m2 &
    -> & FR & MU2 & WM2 & RO2 & CB2).
  rewrite ret_pc_even by lia.
  assert (MU12 : munch (g5_W SP) m1 m2).
  { eapply munch_weaken; [|exact MU2]. intros x Hx. unfold g5_W in Hx. cbn [outside] in Hx |- *.
    destruct Hx as (H1 & H2 & _). split; [exact H1|split; [lia|exact I]]. }
  assert (MU02 : munch (g5_W SP) m m2) by exact (munch_trans _ _ _ _ MU1 MU12).
  assert (WM02 : wmono rsegs m m2) by exact (wmono_trans _ _ _ _ WM1 WM2).
  eapply evt_mono; [apply op5_seg_b|].
  intros ms3 ->.
  unfold p5u_post.
  exists id, K', t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, Ft, fc', m2.
  split; [replace (SP + 16 + 4 * Z.of_nat 0) with (SP + 16) by lia; reflexivity|].
  split; [exact Hid|]. split; [exact HKK|]. split; [exact FR|].
  split; [exact MU02|]. split; [exact WM02|].
  split; [eapply wr_at_transport; [exact (WR (SP + 16) 16 ltac:(lia) ltac:(lia) ltac:(lia))|exact WM02]|].
  split.
  { split; [split|].
    - cbn [cells_wf cell_wf]. tauto.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r.
      eapply bytes_at_transport; [|exact MU2|cbn [disjoint_from]; rewrite length_le8; split; [lia|split; [lia|exact I]]].
      apply bytes_at_write_same; [lia|rewrite length_le8; lia].
    - cbn [cells_size csize]. eapply wr_at_transport; [exact (WR (SP + 32) 8 ltac:(lia) ltac:(lia) ltac:(lia))|].
      exact WM02. }
  exact CB2.
Qed.

Lemma s5u_keep : forall B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA,
  slot_frame B API LS SH SK ra empty rc fx j E CS ->
  munch (g5_W (slot_sp E)) mem mem' -> wmono (ms_segs B) mem mem' ->
  aa_MR (API rc) L A mem md -> ro_agree (ms_segs B) mem -> image_kept (rc := rc) B E mem ->
  stack_mid B E mem -> driver_kept B E TA L A mem ->
  aa_MR (API rc) L A mem' md /\ ro_agree (ms_segs B) mem' /\ image_kept (rc := rc) B E mem' /\
  stack_mid B E mem' /\ driver_kept B E TA L A mem'.
Proof.
  intros B API LS SH SK ra empty rc fx j E CS L A mem mem' md TA HF MU WM HMR HRO HIK HST HDK.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFG. do 27 (destruct FFG as [_ FFG]). destruct FFG as [FG _].
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _ & _ & _ & _ & _ & HIN & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC.
  pose proof (aa_laws (API rc)) as LW.
  assert (EQ : forall x, 0 <= x < slot_sp E - SNPRINTF_K \/ slot_sp E <= x < slot_sp E + 16 \/
      slot_sp E + 88 <= x < 2 ^ 64 ->
    mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
    (writable_at (ms_segs B) mem' x <-> writable_at (ms_segs B) mem x) /\ (present mem' x <-> present mem x)).
  { intros x Hx. apply (s5u_eq _ _ _ _ _ MU).
    - clear - Hx SPHI SPLO AC. unfold slot_sp, SLOT_FRAME, SLOT_STACK, SNPRINTF_K in *. lia.
    - apply s5u_out. lia. }
  assert (LO : forall x, 0 <= x < YM05.alloc_ceiling + 59000 ->
    mbyte (ms_segs B) mem' x = mbyte (ms_segs B) mem x /\
    (writable_at (ms_segs B) mem' x <-> writable_at (ms_segs B) mem x) /\ (present mem' x <-> present mem x)).
  { intros x Hx. apply EQ. left. unfold slot_sp, SLOT_FRAME, SLOT_STACK, SNPRINTF_K in *. lia. }
  assert (MR' : aa_MR (API rc) L A mem' md).
  { destruct (mr_model _ _ LW _ _ _ _ HMR) as (Hh & Hl & Hm).
    apply (mr_frame B (aa_MR (API rc)) LW L A mem mem' md md HMR).
    - intros a Ha. pose proof (owned_low B (aa_MR (API rc)) LW L A mem md a HMR Ha) as Hlo.
      exact (proj1 (LO a ltac:(lia))).
    - intros a Ha HP. pose proof (owned_low B (aa_MR (API rc)) LW L A mem md a HMR Ha) as Hlo.
      exact (proj2 (proj2 (proj2 (LO a ltac:(lia)))) HP).
    - intros p n i Hp Hi.
      destruct (mr_blocks B (aa_MR (API rc)) LW L A mem md p n i HMR Hp Hi) as (HP & H1 & H2 & _).
      exact (proj2 (proj2 (proj2 (LO (ptr_addr L p + i) ltac:(lia)))) HP).
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hm. }
  assert (RO' : ro_agree (ms_segs B) mem').
  { rewrite SEG. rewrite SEG in HRO. apply (g5a_ro_hi _ mem mem' MU); [|exact HRO]. intros x Hx. apply s5u_out.
    unfold slot_sp, SLOT_FRAME, SLOT_STACK, SNPRINTF_K in *. lia. }
  assert (IK' : image_kept (rc := rc) B E mem').
  { destruct HIK as (IK1 & IK2 & IK3 & IK4).
    split; [|split; [|split]].
    - intros a Ha H1 H2 H3 H4. pose proof (in_img_low B SEG a Ha) as Hlo.
      destruct (IK1 a Ha H1 H2 H3 H4) as (Q1 & Q2).
      destruct (LO a ltac:(lia)) as (E1 & E2 & _). rewrite E1, E2. split; assumption.
    - intros a Ha. destruct (FG a Ha) as (Hi & _). pose proof (in_img_low B SEG a Hi) as Hlo.
      destruct (LO a ltac:(lia)) as (_ & E2 & _). rewrite E2. exact (IK2 a Ha).
    - intros a Ha Hn. destruct (IK3 a Ha Hn) as (Q1 & Q2).
      assert (Ho : 0 <= a < slot_sp E - SNPRINTF_K \/ slot_sp E <= a < slot_sp E + 16 \/
        slot_sp E + 88 <= a < 2 ^ 64).
      { unfold lib_scratch in Hn. unfold slot_sp, SLOT_FRAME, SNPRINTF_K. unfold SLOT_STACK in Hn. lia. }
      destruct (EQ a Ho) as (E1 & E2 & _). rewrite E1, E2. split; assumption.
    - intros a Ha. exact (WM _ (IK4 a Ha)). }
  assert (ST' : stack_mid B E mem').
  { destruct HST as (S1 & S2 & S3). split; [|split].
    - eapply rw_cells_transport; [exact S1|exact MU|exact WM|]. apply s5u_dj. right. right. lia.
    - eapply rw_cells_transport; [exact S2|exact MU|exact WM|]. apply s5u_dj. right. left.
      cbn [cells_size csize]. lia.
    - eapply rw_cells_transport; [exact S3|exact MU|exact WM|]. apply s5u_dj. right. left.
      cbn [cells_size csize]. lia. }
  assert (DK' : driver_kept B E TA L A mem').
  { destruct HDK as (D1 & D2 & D3 & D4). split; [exact D1|]. split; [|split; [|exact D4]].
    - intros q n i Hq HT Hp Hi. rewrite <- (D2 q n i Hq HT Hp Hi).
      destruct (mr_blocks B (aa_MR (API rc)) LW (ss_L E) (ss_A E) (ss_mem E) (ss_md E) q n i MR0 Hq Hi)
        as (_ & H1 & H2 & _).
      exact (proj1 (LO (ptr_addr (ss_L E) q + i) ltac:(lia))).
    - intros i Hi. rewrite <- (D3 i Hi).
      destruct HIN as [(Hn0 & _) | (_ & q & Hq & Hp)]; [lia|].
      destruct (mr_blocks B (aa_MR (API rc)) LW (ss_L E) (ss_A E) (ss_mem E) (ss_md E) q (ss_n E) i MR0 Hq Hi)
        as (_ & H1 & H2 & _).
      rewrite Hp in H1, H2. exact (proj1 (LO (ss_p E + i) ltac:(lia))). }
  exact (conj MR' (conj RO' (conj IK' (conj ST' DK')))).
Qed.

Lemma s5u_globals : forall B SP (m m' : word -> option byte) cl br gn dd ei N G nfd mx no cap out,
  munch (g5_W SP) m m' -> wmono (ms_segs B) m m' -> errno_addr B = 0x31acc -> 2 ^ 21 + SNPRINTF_K <= SP ->
  globals_at B m cl br gn dd ei N G nfd mx no cap out -> globals_at B m' cl br gn dd ei N G nfd mx no cap out.
Proof.
  intros B SP m m' cl br gn dd ei N G nfd mx no cap out MU WM ERR HSP H.
  assert (T : forall a cs, rw_cells (ms_segs B) m a cs -> a + Z.of_nat (cells_size cs) <= 2 ^ 21 ->
    rw_cells (ms_segs B) m' a cs).
  { intros a cs Hc Ha. eapply rw_cells_transport; [exact Hc|exact MU|exact WM|]. apply s5u_low; lia. }
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & (ev & H14) & HR).
  split; [apply T; [exact H1|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H2|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H3|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H4|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H5|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H6|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H7|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H8|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H9|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H10|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H11|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H12|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [apply T; [exact H13|cbn [cells_size csize]; apply Z.leb_le; vm_compute; reflexivity]|].
  split; [exists ev; apply T; [exact H14|cbn [cells_size csize]; rewrite ERR; lia]|].
  exact HR.
Qed.

Lemma p5_start_a : forall B API LS SH SK ra empty rc fx j E CS RI t K s c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> snprintf_contract -> RI_mono RI ->
  MI (rc := rc) B (API rc) E RI t K 0x143d8
    (fun _ hj no regs => no = 0 /\ disp_src 5 s hj /\ disp_regs E t K s regs) c ->
  SR (ms_segs B) c (fun c' => exists k', (K < ss_n E /\ k' = K + 1 \/ K = ss_n E /\ k' = K) /\
    J0u (rc := rc) B (API rc) E RI t k' c').
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t K s c HF SNP RIM HM.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  pose proof FF as FFT. do 7 (destruct FFT as [_ FFT]). destruct FFT as (GD & GG & _).
  pose proof FF as FFA. do 31 (destruct FFA as [_ FFA]). specialize (FFA fx).
  do 12 (destruct FFA as [_ FFA]). destruct FFA as (AX & _).
  assert (ERR : errno_addr B = 0x31acc).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  assert (EMP : empty = 0x31880) by (unfold frame_facts in FF; tauto).
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _ & _ & _ & _ & _ & PIN & _).
  pose proof PRE as PT. do 9 (destruct PT as [_ PT]). destruct PT as (TS & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (PB : 0 < ss_p E /\ ss_p E + ss_n E < 2 ^ 64).
  { destruct PIN as [(HN0 & HPE)|(HN0 & p & HPp & EP)]; [lia|].
    destruct (mr_blocks _ _ (aa_laws (API rc)) _ _ _ _ p (ss_n E) 0 MR0 HPp ltac:(lia)) as (_ & P0 & P1 & _).
    rewrite EP in P0, P1. lia. }
  destruct PB as (HP0 & HPN).
  assert (SPB : YM05.alloc_ceiling + 59000 <= slot_sp E - SNPRINTF_K /\ slot_sp E + 88 <= TASK_SIZE /\
    IMG_END + SNPRINTF_K <= slot_sp E /\ 2 ^ 21 + SNPRINTF_K <= slot_sp E).
  { unfold slot_sp, SLOT_FRAME, SNPRINTF_K, IMG_END, TASK_SIZE in *. unfold SLOT_STACK in SPLO. lia. }
  destruct SPB as (SB1 & SB2 & SB3 & SB4).
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  replace (t + (if (0x143d8 =? TAIL_CHECK) || (0x143d8 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (Hno & _ & (B2 & B3 & B4 & B20) & (F23 & F25 & F21 & F19 & F27 & F24) & R8 & R26 & R22 & _).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HIK as (_ & _ & _ & IK4).
  assert (KV : SNPRINTF_K = 5936) by reflexivity.
  assert (TV : TASK_SIZE = 2 ^ 47) by reflexivity.
  assert (WS : forall a, slot_sp E - SNPRINTF_K <= a < slot_sp E + 88 -> writable_at rsegs mem a).
  { intros a Ha. rewrite <- SEG. apply IK4. unfold lib_scratch. left.
    unfold slot_sp, SLOT_FRAME, SLOT_STACK, SNPRINTF_K in *. lia. }
  assert (STK : stk rsegs mem (slot_sp E + 40) (slot_sp E + 88)).
  { split; [lia|]. split; [unfold TASK_SIZE in SB2; lia|]. intros a Ha.
    assert (HW : writable_at rsegs mem a) by (apply WS; lia).
    split; [exact HW|].
    assert (NI : ~ in_img B a) by (intro HI; pose proof (in_img_low B SEG a HI); lia).
    destruct (present_of_writable_out B SEG mem a ltac:(unfold TASK_SIZE in SB2; lia) NI HW) as (b & Hb).
    exists b. unfold mrd, wa. rewrite Hb. reflexivity. }
  destruct (stk_bytes _ _ _ _ STK ltac:(lia)) as (junk & HJL & HJB).
  destruct (ax_statics AX L A mem md HMR) as (GW & (g & Hg & GU) & _).
  rewrite GG, GD in GW. rewrite GD in GU.
  destruct (s5u_slots rc B L A mem t nfd G (bv_unsigned out) es hj SEG HREL) as (fs & os & SL).
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + K)) by exact R8.
  assert (E20 : reg_get regs 20 = Z_to_bv 64 0x318a0) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - K)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEG. eapply (evt_SR_canon rsegs); [|exact Hh|exact Hl|].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (p5u_run SNP (ss_p E) (ss_n E) K (slot_sp E) g junk).
    - lia.
    - unfold INPUT_MAX in Hn. lia.
    - exact HP0.
    - exact HPN.
    - intros HK. rewrite <- SEG. eapply input_read with (fx := fx); [exact HF|exact HDK|lia].
    - exact SB3.
    - exact SB4.
    - exact SB2.
    - exact WS.
    - exact HJB.
    - rewrite HJL. replace (slot_sp E + 88 - (slot_sp E + 40)) with 48 by lia. reflexivity.
    - rewrite <- SEG. exact HRO.
    - exact FZ.
    - rewrite <- SEG. apply g5a_word_le8; [exact GW|unfold GUARD; lia|unfold GOT_GUARD; lia|unfold GOT_GUARD; lia].
    - rewrite <- SEG. apply g5a_word_le8; [exact GU|lia|unfold GUARD; lia|unfold GUARD; lia]. }
  intros ms1 (can1 & HQ & EQ1).
  destruct HQ as (id & K' & y5 & y6 & y7 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & y28 & y29 & y30 & y31 & Ft & fc' &
    m3 & -> & Hid & HKK & FR & MU3 & WM3 & WR3 & Z32 & C40).
  destruct (eqv_mkst (fx := mkFP Ft fc') _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  intros T HT. apply HT.
  exists K'. split; [exact HKK|].
  assert (WM3' : wmono (ms_segs B) mem m3) by (rewrite SEG; exact WM3).
  destruct (s5u_keep B API LS SH SK ra empty rc fx j E CS L A mem m3 md (target_addrs G (bv_unsigned out) es hj)
    HF MU3 WM3' HMR HRO HIK HST HDK) as (MR3 & RO3 & IK3 & ST3 & DK3).
  assert (FRB : forall a n, fresh_block B a n -> 0 < n -> disjoint_from (g5_W (slot_sp E)) a (n + 7)).
  { intros a n (H1 & H2 & _) Hn0. apply s5u_dj. left. lia. }
  unfold J0u.
  exists id, fs, os, junk.
  split.
  - exists (mkFP Ft fc'), L, A, R1, m3, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
    split; [rewrite SEG; reflexivity|].
    split; [exact FR|]. split; [exact Ht|]. split; [lia|]. split; [exact Hn|].
    split.
    { split; [exact Hno|]. split; [unfold base_regs; repeat split; geq X1|].
      do 8 (split; [geq X1|]). split; [exact Hid|]. split; [geq X1|]. split; geq X1. }
    split; [exact MR3|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
    split; [exact RO3|]. split; [exact IK3|]. split; [exact ST3|].
    split; [rewrite short_target; exact DK3|].
    split; [rewrite length_map; eapply s5u_globals; [exact MU3|exact WM3'|exact ERR|exact SB4|exact HGL]|].
    split; [revert Hnfd; unfold TAIL_CHECK, TAIL_STEP; cbn; lia|].
    split; [eapply g9_output; [exact MU3|exact FRB|exact HOUT]|].
    split.
    { replace (t + (if (0x144a0 =? TAIL_CHECK) || (0x144a0 =? TAIL_STEP) then 1 else 0)) with t
        by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
      eapply g9_relay; [exact MU3|exact WM3'|exact FRB| |exact HREL].
      apply s5u_low; [apply Z.leb_le; vm_compute; reflexivity|exact SB4]. }
    split; [rewrite length_map; exact Hes|].
    split; [rewrite short_cost; lia|].
    rewrite short_view. eapply RIM; [exact HRI|lia].
  - cbn [cfg_ms ms_mem YK11.mkst]. unfold J0u_stack.
    split; [|split; [|split; [|split]]].
    + intros i Hi. destruct (SL i Hi) as (C & _ & _). rewrite SEG.
      eapply rw_cells_transport; [exact C|exact MU3|exact WM3|].
      apply s5u_low; [|exact SB4]. cbn [cells_size csize]. unfold G_S, SRC_SIZE. lia.
    + intros i Hi. destruct (SL i Hi) as (_ & Ho & Hf). split; [exact Ho|exact Hf].
    + rewrite SEG. exact WR3.
    + rewrite SEG. exact Z32.
    + rewrite SEG. exact C40.
Qed.
