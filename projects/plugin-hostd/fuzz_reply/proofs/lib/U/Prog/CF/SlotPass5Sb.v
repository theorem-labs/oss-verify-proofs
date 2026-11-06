(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths and module names changed; 618 of its 664 lines of code are new or changed and 1183 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/SlotPass9G.v, with its module paths and addresses changed; 283 of its 335 lines of code are new or changed and 612 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotHeadRun SlotHeadPick SlotHeadQ SlotPass1.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import printf_facts_c snprintf_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_remove_b_c relay_instance_gone_b_c SlotPass5Run HarnessGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SlotPass9G SlotPass5A SlotPass5Sa SlotPass5Sl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require relay_source_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import relay_reads_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Definition RG1u (E : sstart) (t k id : Z) (fs os rs : list Z) :
    list rentry -> list (hsrc * nat) -> Z -> bvmap 5 word -> Prop :=
  fun es _ no regs => no = 0 /\ base_regs E regs /\
    getr regs 23 = Z_to_bv 64 (slot_sp E + 32) /\ getr regs 25 = Z_to_bv 64 DIV10 /\
    getr regs 21 = Z_to_bv 64 10 /\ getr regs 27 = Z_to_bv 64 (G_S + 4) /\ getr regs 24 = Z_to_bv 64 1 /\
    getr regs 8 = Z_to_bv 64 (ss_p E + k) /\ getr regs 26 = Z_to_bv 64 (ss_n E - k) /\
    getr regs 22 = Z_to_bv 64 t /\ getr regs 1 = Z_to_bv 64 0x144c8 /\
    getr regs 18 = Z_to_bv 64 (G_S + 384) /\ getr regs 19 = Z_to_bv 64 (slot_sp E + 32) /\
    0 <= id < 256 /\ getr regs 9 = Z_to_bv 64 id /\ getr regs 10 = Z_to_bv 64 id /\
    (forall i, (i < 4)%nat -> nth i rs 0 = op5_rec es (nth i fs 0) (nth i os 0)).

Definition J1u_stack (B : malloc_syms) (E : sstart) (id : Z) (fs os rs : list Z) (junk : list byte)
    (mem : word -> option byte) : Prop :=
  (forall i, (i < 4)%nat -> rw_cells (ms_segs B) mem (G_S + SRC_SIZE * Z.of_nat i)
      [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]) /\
  (forall i, (i < 4)%nat -> (nth i os 0 = 0 \/ nth i os 0 = 1) /\ 0 <= nth i fs 0 < 2 ^ 31) /\
  rw_cells (ms_segs B) mem (slot_sp E + 16) [C4 (Z_to_bv 64 (nth 0 rs 0)); C4 (Z_to_bv 64 (nth 1 rs 0));
    C4 (Z_to_bv 64 (nth 2 rs 0)); C4 (Z_to_bv 64 (nth 3 rs 0))] /\
  rw_cells (ms_segs B) mem (slot_sp E + 32) [C8 (Z_to_bv 64 0)] /\
  rw_cells (ms_segs B) mem (slot_sp E + 40)
    [CB 48 (pf_bytes (instance_prefix id ++ [0]) ++ skipn (length (instance_prefix id) + 1) junk)].

Definition J1u {rc : YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (E : sstart) (RI : res_inv) (t k : Z)
    (c : config) : Prop :=
  exists (id : Z) (fs os rs : list Z) (junk : list byte),
    MI (rc := rc) B API E RI t k 0x13664 (RG1u E t k id fs os rs) c /\
    J1u_stack B E id fs os rs junk (ms_mem (cfg_ms c)).

Lemma p5b_hit_short : forall fd es, op5_hit fd (map short_entry es) = op5_hit fd es.
Proof. intros fd es. induction es as [|e es IH]; cbn [map op5_hit]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma p5b_rec_short : forall es fd op, op5_rec (map short_entry es) fd op = op5_rec es fd op.
Proof. intros es fd op. unfold op5_rec. rewrite p5b_hit_short. reflexivity. Qed.

Lemma p5b_eb_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof. intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity. Qed.

Lemma p5b_concat_len : forall l, Forall (fun e => length (entry_bytes e) = 56%nat) l ->
  length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof. induction 1 as [|x l Hx _ IH]; cbn [map concat length]; [reflexivity|]. rewrite length_app, Hx, IH. lia. Qed.

Lemma p5b_bss_not_ro : forall a, 0x318a0 <= a < 0x31aa0 -> Mem.ro_addr rsegs (wa a) = false.
Proof. intros a Ha. unfold wa. apply g9_glob_not_ro. exists 0x318a0, 512. split; [right; left; reflexivity|lia]. Qed.

Lemma p5b_mem : forall (SP lo : Z) (es : list rentry) (fd op : nat -> Z) (n : nat) (m m1 : word -> option byte),
  0 <= SP -> SP + 32 <= 2 ^ 64 -> (n <= 4)%nat ->
  mem_inv rsegs m -> stk rsegs m lo SP -> wr_at rsegs m (SP + 16) 16 -> p5sl_mem SP lo es fd op n m m1 ->
  munch [(SP - RELAY_READS_K, SP); (SP + 16, SP + 32)] m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\
  stk rsegs m1 lo SP /\
  (forall q, (q < n)%nat ->
     bytes_at rsegs m1 (SP + 16 + 4 * Z.of_nat q) (le4 (Z_to_bv 64 (op5_rec es (fd q) (op q))))).
Proof.
  intros SP lo es fd op n m m1 H0 H1 Hn MI0 ST0 WR0. revert m1. revert Hn.
  induction n as [|n IH]; intros Hn m1 HM.
  - cbn [p5sl_mem] in HM. subst m1.
    split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI0|]. split; [exact ST0|].
    intros q Hq. lia.
  - cbn [p5sl_mem] in HM. destruct HM as (ma & mb & HA & HC & ->).
    destruct (IH ltac:(lia) ma HA) as (MUa & WMa & MIa & STa & BYa).
    assert (CB : munch [(SP - RELAY_READS_K, SP)] ma mb /\ wmono rsegs ma mb /\ mem_inv rsegs mb /\
      stk rsegs mb lo SP).
    { destruct HC as [(_ & ->)|(_ & MU & WM & MIc & ST)].
      - exact (conj (munch_refl _ _) (conj (wmono_refl _ _) (conj MIa STa))).
      - exact (conj MU (conj WM (conj MIc ST))). }
    destruct CB as (MUb & WMb & MIb & STb).
    assert (WMab : wmono rsegs m mb) by exact (wmono_trans rsegs _ _ _ WMa WMb).
    assert (WRb : wr_at rsegs mb (SP + 16) 16) by (eapply wr_at_transport; [exact WR0|exact WMab]).
    assert (SO : store_ok rsegs mb (wa (SP + 16 + 4 * Z.of_nat n)) 4 = true).
    { apply (wr_at_store_ok rsegs mb (SP + 16) 16 (4 * Z.of_nat n) 4); [exact WRb|lia|lia]. }
    change (Z_to_bv 64 (SP + 16 + 4 * Z.of_nat n)) with (wa (SP + 16 + 4 * Z.of_nat n)).
    assert (RK : RELAY_READS_K = 16) by reflexivity.
    split.
    { eapply munch_write; [|lia|rewrite length_le4; lia|].
      - eapply munch_trans; [exact MUa|]. eapply munch_weaken; [|exact MUb].
        intros x Hx. cbn [outside] in Hx |- *. destruct Hx as (X1 & _ & _). split; [exact X1|exact I].
      - cbn [inside]. right. left. rewrite length_le4. lia. }
    split; [apply wmono_write; exact WMab|].
    split; [apply mem_inv_store; [exact MIb|rewrite length_le4; exact SO]|].
    split; [apply stk_write; [exact STb|lia|rewrite length_le4; lia]|].
    intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne].
    + apply bytes_at_write_same; [lia|rewrite length_le4; lia].
    + apply bytes_at_write_other; [|lia|rewrite length_le4; lia|rewrite !length_le4; lia].
      eapply bytes_at_transport; [exact (BYa q ltac:(lia))|exact MUb|].
      cbn [disjoint_from]. rewrite length_le4. split; [lia|exact I].
Qed.

Lemma p5b_recs : forall segs m SP (r : nat -> Z),
  (forall q, (q < 4)%nat -> bytes_at segs m (SP + 16 + 4 * Z.of_nat q) (le4 (Z_to_bv 64 (r q)))) ->
  wr_at segs m (SP + 16) 16 ->
  rw_cells segs m (SP + 16) [C4 (Z_to_bv 64 (r 0%nat)); C4 (Z_to_bv 64 (r 1%nat)); C4 (Z_to_bv 64 (r 2%nat));
    C4 (Z_to_bv 64 (r 3%nat))].
Proof.
  intros segs m SP r HB HW.
  pose proof (HB 0%nat ltac:(lia)) as B0. pose proof (HB 1%nat ltac:(lia)) as B1.
  pose proof (HB 2%nat ltac:(lia)) as B2. pose proof (HB 3%nat ltac:(lia)) as B3.
  split; [split|].
  - cbn [cells_wf cell_wf]. tauto.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    apply bytes_at_app. split; [replace (SP + 16) with (SP + 16 + 4 * Z.of_nat 0) by lia; exact B0|].
    rewrite length_le4. apply bytes_at_app.
    split; [replace (SP + 16 + Z.of_nat 4) with (SP + 16 + 4 * Z.of_nat 1) by lia; exact B1|].
    rewrite length_le4. apply bytes_at_app.
    split; [replace (SP + 16 + Z.of_nat 4 + Z.of_nat 4) with (SP + 16 + 4 * Z.of_nat 2) by lia; exact B2|].
    rewrite length_le4.
    replace (SP + 16 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) with (SP + 16 + 4 * Z.of_nat 3) by lia. exact B3.
  - cbn [cells_size csize]. exact HW.
Qed.

Lemma p5_scan : forall B API LS SH SK ra empty rc fx j E CS RI t k c,
  slot_frame B API LS SH SK ra empty rc fx j E CS -> relay_reads_contract ->
  J0u (rc := rc) B (API rc) E RI t k c ->
  SR (ms_segs B) c (J1u (rc := rc) B (API rc) E RI t k).
Proof.
  intros B API LS SH SK ra empty rc fx j E CS RI t k c HF RRC HJ.
  pose proof HF as (FF & _ & PRE & _). pose proof (proj1 FF) as SEG.
  assert (ERR : errno_addr B = 0x31acc).
  { pose proof FF as FTP. do 16 (destruct FTP as [_ FTP]). destruct FTP as (TP & EO & _).
    unfold errno_addr. rewrite TP, EO. reflexivity. }
  pose proof (proj1 (proj1 PRE)) as LP.
  destruct LP as (MR0 & _ & _ & _ & _ & _ & SPLO & SPHI & _).
  pose proof PRE as PT. do 9 (destruct PT as [_ PT]). destruct PT as (TS & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  assert (SPB : YM05.alloc_ceiling + 59000 <= slot_sp E - SNPRINTF_K /\ slot_sp E + 88 <= TASK_SIZE /\
    2 ^ 21 + SNPRINTF_K <= slot_sp E).
  { unfold slot_sp, SLOT_FRAME, SNPRINTF_K, TASK_SIZE in *. unfold SLOT_STACK in SPLO. lia. }
  destruct SPB as (SB1 & SB2 & SB4).
  assert (KV : SNPRINTF_K = 5936) by reflexivity.
  assert (TV : TASK_SIZE = 2 ^ 47) by reflexivity.
  assert (RK : RELAY_READS_K = 16) by reflexivity.
  assert (GSH : HarnessRep.G_S = 0x31920) by reflexivity.
  assert (GSM : G_S = 0x31920) by reflexivity.
  assert (SSV : SRC_SIZE = 96) by reflexivity.
  assert (NSV : CF.relay_source_c.G_NSRC = 0x318b8) by reflexivity.
  assert (SRV : CF.relay_source_c.G_SRC = 0x318d0) by reflexivity.
  destruct HJ as (id & fs & os & junk & HM & HS).
  destruct HM as (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
    -> & FZ & Ht & Hk & Hn & HR & HMR & HWF & HBD & HINIT & HVM & HRO & HIK & HST & HDK & HGL & Hnfd & HOUT & HREL &
    Hes & Hcost & HRI).
  cbn [cfg_ms ms_mem YK11.mkst] in HS.
  destruct HS as (SL & SV & WR16 & Z32 & C40).
  replace (t + (if (0x144a0 =? TAIL_CHECK) || (0x144a0 =? TAIL_STEP) then 1 else 0)) with t in HREL
    by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
  destruct HR as (Hno & (B2 & B3 & B4 & B20) & F23 & F25 & F21 & F27 & F24 & R8 & R26 & R22 & Hid & R9 & R18 & R19).
  destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HMR) as (Hh & Hl & _).
  pose proof HIK as (_ & _ & _ & IK4).
  pose proof HREL as ((tail & TL & TC) & GIN & GFR & HES & _).
  destruct GFR as (GF0 & GF1 & _). unfold SRC_TABLE, SRC_ENTRY in GF1.
  assert (GAL : G mod 8 = 0).
  { pose proof GIN as GIN'. unfold blocks in GIN'. apply in_map_iff in GIN' as ([p k'] & EG & Hp).
    cbn [fst snd] in EG. injection EG as EG _. rewrite <- EG.
    pose proof (mr_blocks_aligned _ _ (aa_laws (API rc)) L A mem md p k' HMR Hp) as H16.
    Z.div_mod_to_equations. lia. }
  assert (UG : bv_unsigned (Z_to_bv 64 G) = G) by (apply unsigned_lit; lia).
  assert (RO : MemNorm.ro_agree rsegs mem) by (rewrite <- SEG; exact HRO).
  pose proof (MemNorm.mem_rel_normalize rsegs mem RO) as HR0.
  pose proof (MemNorm.mem_inv_normalize rsegs mem) as MIN.
  assert (WS : forall a, slot_sp E - SNPRINTF_K <= a < slot_sp E + 88 -> writable_at rsegs mem a).
  { intros a Ha. rewrite <- SEG. apply IK4. unfold lib_scratch. left.
    unfold slot_sp, SLOT_FRAME, SLOT_STACK, SNPRINTF_K in *. lia. }
  assert (ST0 : stk rsegs mem (slot_sp E - RELAY_READS_K) (slot_sp E)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (WA : writable_at rsegs mem a) by (apply WS; lia).
    split; [exact WA|]. destruct (writable_hi_present mem a ltac:(lia) WA) as [b HB].
    exists b. unfold mrd, wa. rewrite HB. reflexivity. }
  assert (STN : stk rsegs (MemNorm.normalize rsegs mem) (slot_sp E - RELAY_READS_K) (slot_sp E)).
  { apply stk_normalize; [exact ST0|lia]. }
  assert (WRN : wr_at rsegs (MemNorm.normalize rsegs mem) (slot_sp E + 16) 16).
  { apply (RoAdapt.wr_at_norm' rsegs mem); [exact RO|rewrite <- SEG; exact WR16|].
    unfold RoAdapt.not_ro. intros q Hq. unfold wa. apply ro_addr_hi. lia. }
  assert (SLN : forall i, (i < 4)%nat -> rw_cells rsegs (MemNorm.normalize rsegs mem) (G_S + SRC_SIZE * Z.of_nat i)
      [C4 (Z_to_bv 64 (nth i fs 0)); C4 (Z_to_bv 64 (nth i os 0))]).
  { intros i Hi. apply (RoAdapt.rw_cells_norm rsegs mem); [exact RO|rewrite <- SEG; exact (SL i Hi)|].
    unfold RoAdapt.not_ro. intros q Hq. cbn [cells_size csize] in Hq. apply p5b_bss_not_ro. rewrite GSM, SSV. lia. }
  assert (BN : bytes_at rsegs mem CF.relay_source_c.G_NSRC (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & G8 & _).
    destruct G8 as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r, bytes_at_app in BY.
    rewrite SEG in BY. exact (proj1 BY). }
  assert (BG : bytes_at rsegs mem CF.relay_source_c.G_SRC (le8 (Z_to_bv 64 G))).
  { pose proof HGL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & G10 & _).
    destruct G10 as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY.
    rewrite SEG in BY. exact BY. }
  assert (BT : bytes_at rsegs mem G (concat (map entry_bytes es))).
  { destruct TC as ((_ & BY) & _). cbn [cells_bytes cbytes] in BY.
    rewrite app_nil_r, bytes_at_app in BY. rewrite SEG in BY. exact (proj1 BY). }
  assert (EL : Forall (fun x => length (entry_bytes x) = 56%nat) es).
  { eapply Forall_impl; [|exact HES]. intros x (_ & _ & X3 & X4 & _). exact (p5b_eb_len x X3 X4). }
  assert (CL : Z.of_nat (length (concat (map entry_bytes es))) = 56 * Z.of_nat (length es)).
  { rewrite (p5b_concat_len es EL). lia. }
  assert (SRCF : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\
      -2^31 <= re_fd e < 2^31) es).
  { eapply Forall_impl; [|exact HES]. intros x (_ & _ & X3 & X4 & X5 & _).
    split; [exact X3|]. split; [exact X4|]. lia. }
  pose proof (MemNorm.bytes_at_normalize rsegs mem _ _ RO BN) as BNn.
  pose proof (MemNorm.bytes_at_normalize rsegs mem _ _ RO BG) as BGn.
  pose proof (MemNorm.bytes_at_normalize rsegs mem _ _ RO BT) as BTn.
  assert (E2 : reg_get regs 2 = Z_to_bv 64 (slot_sp E)) by exact B2.
  assert (E3 : reg_get regs 3 = getr (ss_regs E) 3) by exact B3.
  assert (E4 : reg_get regs 4 = getr (ss_regs E) 4) by exact B4.
  assert (E8 : reg_get regs 8 = Z_to_bv 64 (ss_p E + k)) by exact R8.
  assert (E9 : reg_get regs 9 = Z_to_bv 64 id) by exact R9.
  assert (E18 : reg_get regs 18 = Z_to_bv 64 (HarnessRep.G_S + 96 * Z.of_nat 0)).
  { transitivity (Z_to_bv 64 G_S); [exact R18|f_equal; lia]. }
  assert (E19 : reg_get regs 19 = Z_to_bv 64 (slot_sp E + 16 + 4 * Z.of_nat 0)).
  { transitivity (Z_to_bv 64 (slot_sp E + 16)); [exact R19|f_equal; lia]. }
  assert (E20 : reg_get regs 20 = Z_to_bv 64 G_RELAY_LO) by exact B20.
  assert (E21 : reg_get regs 21 = Z_to_bv 64 10) by exact F21.
  assert (E22 : reg_get regs 22 = Z_to_bv 64 t) by exact R22.
  assert (E23 : reg_get regs 23 = Z_to_bv 64 (slot_sp E + 32)) by exact F23.
  assert (E24 : reg_get regs 24 = Z_to_bv 64 1) by exact F24.
  assert (E25 : reg_get regs 25 = Z_to_bv 64 DIV10) by exact F25.
  assert (E26 : reg_get regs 26 = Z_to_bv 64 (ss_n E - k)) by exact R26.
  assert (E27 : reg_get regs 27 = Z_to_bv 64 (G_S + 4)) by exact F27.
  rewrite SEG.
  eapply (kseg regs (Z_to_bv 64 0x144a0) mem md); [exact wx_apart_rsegs|exact RO|exact Hh|exact Hl| | |].
  - unfold Regs6ss.mkR_of.
    rewrite E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
    eapply (p5_rloop RRC (slot_sp E) (slot_sp E - RELAY_READS_K) es (Z_to_bv 64 G)
      (fun i => nth i fs 0) (fun i => nth i os 0)).
    + lia.
    + lia.
    + lia.
    + intros i Hi. cbv beta. destruct (SV i Hi) as (Ho & Hf). split; [destruct Ho as [Ho|Ho]; lia|intros _; lia].
    + lia.
    + eapply Forall_impl; [|exact HES]. intros x (X1 & _). lia.
    + intros _. rewrite UG. split; [lia|exact GAL].
    + left. lia.
    + left. lia.
    + left. lia.
    + intros _. left. rewrite UG. lia.
    + intros i m1 Hi Hm.
      destruct (p5b_mem (slot_sp E) (slot_sp E - RELAY_READS_K) es (fun i => nth i fs 0) (fun i => nth i os 0)
        i (MemNorm.normalize rsegs mem) m1 ltac:(lia) ltac:(lia) ltac:(lia) MIN STN WRN Hm)
        as (MU1 & WM1 & MI1 & ST1 & _).
      assert (WR1 : wr_at rsegs m1 (slot_sp E + 16) 16) by (eapply wr_at_transport; [exact WRN|exact WM1]).
      split.
      { eapply rw_cells_transport; [exact (SLN i Hi)|exact MU1|exact WM1|].
        cbn [disjoint_from cells_size csize]. split; [lia|split; [lia|exact I]]. }
      split; [exact WR1|]. intros _.
      split.
      { eapply bytes_at_transport; [exact BNn|exact MU1|].
        cbn [disjoint_from]. rewrite length_le4. split; [lia|split; [lia|exact I]]. }
      split.
      { eapply bytes_at_transport; [exact BGn|exact MU1|].
        cbn [disjoint_from]. rewrite length_le8. split; [lia|split; [lia|exact I]]. }
      split.
      { rewrite UG. unfold CF.relay_source_c.src_table. split; [exact SRCF|].
        eapply bytes_at_transport; [exact BTn|exact MU1|].
        cbn [disjoint_from]. rewrite CL. split; [lia|split; [lia|exact I]]. }
      split; [exact MI1|]. split; [exact ST1|].
      intros m2 _ WM2. eapply wr_at_transport; [exact WR1|exact WM2].
  - intros s0 (y11 & y12 & y13 & y14 & y15 & y16 & y17 & m' & _ & ->). do 3 eexists. reflexivity.
  - intros R pc' m0 regs1 m1 (y11 & y12 & y13 & y14 & y15 & y16 & y17 & m' & HPM & EQ) GR MREL ROS.
    injection EQ as ER EP EM. subst R pc' m0.
    destruct (p5b_mem (slot_sp E) (slot_sp E - RELAY_READS_K) es (fun i => nth i fs 0) (fun i => nth i os 0)
      4 (MemNorm.normalize rsegs mem) m' ltac:(lia) ltac:(lia) ltac:(lia) MIN STN WRN HPM)
      as (MUf & WMf & _ & _ & BYf).
    assert (MU1 : munch [(slot_sp E - RELAY_READS_K, slot_sp E); (slot_sp E + 16, slot_sp E + 32)] mem m1)
      by exact (MemNorm.munch_rel rsegs _ mem _ m1 m' HR0 MREL ROS MUf).
    assert (WM1 : wmono rsegs mem m1) by exact (MemNorm.wmono_rel rsegs mem _ m1 m' HR0 MREL ROS WMf).
    assert (BY1 : forall q, (q < 4)%nat -> bytes_at rsegs m1 (slot_sp E + 16 + 4 * Z.of_nat q)
        (le4 (Z_to_bv 64 (op5_rec es (nth q fs 0) (nth q os 0))))).
    { intros q Hq. exact (proj2 (MemNorm.bytes_at_rel rsegs m1 m' _ _ MREL) (BYf q Hq)). }
    assert (MU : munch (g5_W (slot_sp E)) mem m1).
    { eapply munch_weaken; [|exact MU1]. intros x Hx. unfold g5_W in Hx. cbn [outside] in Hx |- *.
      destruct Hx as (X1 & X2 & _). split; [lia|split; [lia|exact I]]. }
    assert (WM' : wmono (ms_segs B) mem m1) by (rewrite SEG; exact WM1).
    assert (WR1 : wr_at rsegs m1 (slot_sp E + 16) 16).
    { rewrite <- SEG. eapply wr_at_transport; [exact WR16|exact WM']. }
    destruct (s5u_keep B API LS SH SK ra empty rc fx j E CS L A mem m1 md (target_addrs G (bv_unsigned out) es hj)
      HF MU WM' HMR HRO HIK HST HDK) as (MR1 & RO1 & IK1 & ST1 & DK1).
    assert (FRB : forall a n, fresh_block B a n -> 0 < n -> disjoint_from (g5_W (slot_sp E)) a (n + 7)).
    { intros a n (H1 & H2 & _) Hn0. apply s5u_dj. left. lia. }
    apply SR_ret. unfold J1u.
    exists id, fs, os, [op5_rec es (nth 0 fs 0) (nth 0 os 0); op5_rec es (nth 1 fs 0) (nth 1 os 0);
      op5_rec es (nth 2 fs 0) (nth 2 os 0); op5_rec es (nth 3 fs 0) (nth 3 os 0)], junk.
    split.
    + exists fx', L, A, regs1, m1, md, cl, br, gn, dd, ei, G, nfd, mx, nout, cap, out, (map short_entry es), hj.
      split; [rewrite SEG; reflexivity|].
      split; [exact FZ|]. split; [exact Ht|]. split; [exact Hk|]. split; [exact Hn|].
      split.
      { split; [exact Hno|].
        split; [unfold base_regs; split; [|split; [|split]]; rewrite GR; reflexivity|].
        do 11 (split; [rewrite GR; reflexivity|]).
        split; [exact Hid|].
        split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
        intros i Hi. destruct i as [|[|[|[|i]]]]; [| | | |lia]; cbn [nth]; symmetry; apply p5b_rec_short. }
      split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HINIT|]. split; [exact HVM|].
      split; [exact RO1|]. split; [exact IK1|]. split; [exact ST1|].
      split; [rewrite short_target; exact DK1|].
      split; [rewrite length_map; eapply s5u_globals; [exact MU|exact WM'|exact ERR|exact SB4|exact HGL]|].
      split; [revert Hnfd; unfold TAIL_CHECK, TAIL_STEP; cbn; lia|].
      split; [eapply g9_output; [exact MU|exact FRB|exact HOUT]|].
      split.
      { replace (t + (if (0x13664 =? TAIL_CHECK) || (0x13664 =? TAIL_STEP) then 1 else 0)) with t
          by (unfold TAIL_CHECK, TAIL_STEP; cbn; lia).
        eapply g9_relay; [exact MU|exact WM'|exact FRB| |exact HREL].
        apply s5u_low; [apply Z.leb_le; vm_compute; reflexivity|exact SB4]. }
      split; [rewrite length_map; exact Hes|].
      split; [rewrite short_cost; exact Hcost|].
      rewrite short_view. exact HRI.
    + cbn [cfg_ms ms_mem YK11.mkst]. unfold J1u_stack.
      split; [|split; [|split; [|split]]].
      * intros i Hi. eapply rw_cells_transport; [exact (SL i Hi)|exact MU|exact WM'|].
        apply s5u_low; [|exact SB4]. cbn [cells_size csize]. rewrite GSM, SSV. lia.
      * exact SV.
      * rewrite SEG. apply (p5b_recs rsegs m1 (slot_sp E) (fun q => op5_rec es (nth q fs 0) (nth q os 0)));
          [exact BY1|exact WR1].
      * eapply rw_cells_transport; [exact Z32|exact MU1|exact WM'|].
        cbn [disjoint_from cells_size csize]. split; [lia|split; [lia|exact I]].
      * eapply rw_cells_transport; [exact C40|exact MU1|exact WM'|].
        cbn [disjoint_from cells_size csize]. split; [lia|split; [lia|exact I]].
Qed.
