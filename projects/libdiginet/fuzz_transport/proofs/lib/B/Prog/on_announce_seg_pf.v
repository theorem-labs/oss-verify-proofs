(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 697 of its 763 lines of code are new or changed and 1858 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/on_announce_seg_tail.v, with its module names changed; 957 of its 1044 lines of code are new or changed and 676 lines of the source are left out. *)
(* on_announce_seg_pf: Lemma onann_pf_piece : onann_pf_stmt (lib/B/Prog/OnannCutB.v), the personality piece of
   on_announce's image-B walk, offsets +0x1e0 .. +0x24c and +0x270 .. +0x274 of the listing
   lib/B/Prog/DgnTransportBList.v (fuzz_transport.asan-ubsan 0x87ea8 .. 0x87f14, 0x87f38 .. 0x87f3c), from the
   personality cut onann_pf_at to the find_mac cut onann_fm_at (+0x250, cmd = 0xe1) or the desk notice cut onann_dn_at
   (+0x300, any other cmd), which it is given.

   What the code does (diginet_session.c:191-194).
     +0x1e0 `addi a0, s10, 10` (a0 = a.name), +0x1e4 `jal diginet_personality_from_name`: a donor-form callee
       (diginet_personality_from_name_cg.v transport_diginet_personality_from_name_cg through TransportGCg.v gx_call_cg),
       called with the name bytes tb = TSess.v ann_field of the body from 24, which diginet_announce_parse left at
       a + 10 (OnannCutB.v onann_a_ok); its X: a0 = trans_pfrom_res tb = onann_pv timg_B b (on_announce_seg_kit.v
       onann_pv_res).
     +0x1e8 `mv a6, a0`, +0x1ec `beq a0, zero, +0x210`. p = 0 goes to +0x210; the model's onann_w1 is then the world
       (opf_w1_none). Else +0x1f0 `andi a0, s4, 7` and `bnez a0` to the trap word (s = 0x5df640: the engine folds it to
       0 by the fact of s4, so the trap is not reached), the check of the 8-byte store at s + 128 (its shadow byte is 0:
       on_announce_cg.v trans_onann_cells), `sd a6, 0(a0)` (:193; the world is set_S_personality Bw p = onann_w1).
     +0x210 `andi a0, s6, 7` and `bnez a0` to the trap word (fp mod 8 = 0, folded by the fact of s6); the check of the
       1-byte load at f + 30 (a3 = its shadow address, the shadow byte 0: on_announce_seg_kit.v onann_f30); the spills
       of a3 at s1 + 48 and f + 30 at s1 + 56, a1 = cmd (the 1-byte load at f + 30), a0 = s & 7 = 0, a2 = 225,
       a5 = -1, the spills of now (s7) at s1 + 24 and a (s10) at s1 + 16; +0x24c `bne a1, a2, +0x270`.
     cmd = 0xe1: the find_mac cut +0x250 (a0 = 0, a6 = p). Else +0x270 `sltiu a1, a0, 1` (a1 = 1), +0x274 `j +0x300`:
       the desk notice cut (a5 = -1 = onann_off at a cmd other than 0xe1: opf_off_dn).

   The runs are the token engine's over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x): run 0 (+0x1e0 .. the call; no region); run 1 (+0x1e8 .. the `beq`; no region), whose arm p = 0 runs
   on to +0x210; the arm p <> 0 is taken up again at +0x1f0 with one region (g_s's personality field at s4, written)
   and its shadow entry, and runs to +0x210; the join opf_join (+0x210 .. the `bne`: f + 30 at s6, read, and the spill
   slots s1 + 16 .. s1 + 64, written; then each arm runs to its cut). Every state carries onann_cur: the call's
   acall_kept_g over its window and written range
   (opf_cur_step for the runs: the bytes they write are the personality field, a row of onann_wr, or the spill slots,
   in the call's window; TransportGCg.v dk_kept_trans_nf_g for personality_from_name, whose written range is empty),
   the saved words and the frame's last word; onann_a_ok is carried by opf_a_ok_keep (the own frame's bytes are kept
   by every step). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YI09 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0p YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGNotice.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg check_state_data_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import set_state_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_wake_cg maybe_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_session_tick_cg on_ack_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_personality_from_name_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import diginet_announce_parse_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_cg OnannCutB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TNeed TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec DgnLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TGNA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog.TransportGNotice.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module TN := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TNeed.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module DLib := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnLib.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The model on this piece                                          *)
(* ------------------------------------------------------------------ *)

(* personality_from_name's result: 0 when the name is no personality's, else personalities[i], i = 0 or 1. *)
Lemma opf_pv_cases : forall b,
  (TN.diginet_personality_from_name (onann_name b) = None /\ onann_pv timg_B b = 0) \/
  (exists i, TN.diginet_personality_from_name (onann_name b) = Some i /\ (i = 0 \/ i = 1) /\
     onann_pv timg_B b = TI.ti_personalities timg_B + 24 * i).
Proof.
intros b. unfold onann_pv.
destruct (TN.diginet_personality_from_name (onann_name b)) as [i|] eqn:E.
- right. exists i. split; [reflexivity|]. split; [|reflexivity].
  unfold TN.diginet_personality_from_name, DLib.personalities in E.
  cbn [TN.personality_name_find DLib.dp_announce_name] in E.
  match type of E with context [if ?c then _ else _] => destruct c end; [injection E as <-; left; reflexivity|].
  match type of E with context [if ?c then _ else _] => destruct c end;
    [injection E as <-; right; reflexivity | discriminate E].
- left. split; reflexivity.
Qed.

Lemma opf_pers_val : TI.ti_personalities timg_B = 0xa3b00.
Proof. reflexivity. Qed.

Lemma opf_pv_range : forall b, 0 <= onann_pv timg_B b < 2 ^ 64.
Proof.
intros b. pose proof opf_pers_val as P.
destruct (opf_pv_cases b) as [(_ & E) | (i & _ & Hi & E)]; rewrite E; [lia|]. rewrite P. lia.
Qed.

(* p = 0: the model stores nothing (:192). *)
Lemma opf_w1_none : forall Bw b, onann_pv timg_B b = 0 -> onann_w1 timg_B Bw b = Bw.
Proof.
intros Bw b H. pose proof opf_pers_val as P. unfold onann_w1.
destruct (opf_pv_cases b) as [(E & _) | (i & E & Hi & Ep)]; rewrite E; [reflexivity|].
exfalso. rewrite Ep, P in H. lia.
Qed.

(* p <> 0: the store of p at s + 128 (:193), at its numeral offset. *)
Lemma opf_w1_some : forall Bw b, onann_pv timg_B b <> 0 ->
  onann_w1 timg_B Bw b = TW.upd Bw (TW.OFF_g_s + 128) (TW.put 8 (onann_pv timg_B b)).
Proof.
intros Bw b H. unfold onann_w1.
destruct (opf_pv_cases b) as [(E & Ep) | (i & E & _ & _)].
- exfalso. exact (H Ep).
- rewrite E. exact (onann_st_pers Bw (onann_pv timg_B b)).
Qed.

(* find_mac's result at a cmd other than 0xe1 is -1 (a5 = -1 at +0x240). *)
Lemma opf_off_dn : forall X b, DSpec.fr_cmd b <> 225 -> onann_off X b = -1.
Proof.
intros X b H. unfold onann_off.
destruct (DSpec.fr_cmd b =? TS0.DIGINET_CMD_ANNOUNCE_SESSION) eqn:E; [|reflexivity].
apply Z.eqb_eq in E. unfold TS0.DIGINET_CMD_ANNOUNCE_SESSION in E. lia.
Qed.

(* a.name's bytes: at most 10 (9 copied and the 0), with the 0 among them. *)
Lemma opf_field_len : forall l, (1 <= length (TSS.ann_field l) <= 10)%nat.
Proof.
intros l. unfold TSS.ann_field, DSpec.copy_len. rewrite length_app, length_firstn. cbn [length].
pose proof (DSpec.nz_run_le (firstn (Nat.min 9 (10 - 1)) l)) as H. rewrite length_firstn in H. lia.
Qed.

Lemma opf_field_nul : forall l, In (DSpec.b8 0) (TSS.ann_field l).
Proof. intros l. unfold TSS.ann_field. apply in_or_app. right. left. reflexivity. Qed.

(* beq / bne on literals. *)
Lemma opf_eqb_z : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity. Qed.

(* The value of an atom, an offset from an atom, and an expression by its unsigned value. *)
Lemma opf_den_off : forall E n z v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n z) = Z_to_bv 64 (v + z).
Proof. intros E n z v H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Lemma opf_den_U : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma opf_srl3 : forall E v, U E (SAlu ALU_SRL v (SLit 3)) = U E v / 8.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. pose proof (U_range E v). unfold zcanon, M64 in *.
apply Z.mod_small. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* The shadow address the code spills at s1 + 48: ((f + 30) >> 3) + the shadow base. *)
Lemma opf_den_sh : forall E fp, bv_unsigned (ew E 22) = fp -> bv_unsigned (ew E 24) = SHADOW_OFF ->
  0 <= fp -> fp + 30 < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 30) (SLit 3)) (SOff 24 0)) =
  Z_to_bv 64 (SHADOW_OFF + (fp + 30) / 8).
Proof.
intros E fp H22 H24 H0 H1. apply opf_den_U.
rewrite U_SAlu. cbn [zalu_raw]. rewrite opf_srl3, !U_SOff, H22, H24, Z.add_0_r.
assert (ES : SHADOW_OFF = 2147450880) by reflexivity.
pose proof (Z.div_pos (fp + 30) 8 ltac:(lia) ltac:(lia)) as D1.
assert (D2 : (fp + 30) / 8 <= fp + 30) by (apply Z.div_le_upper_bound; lia).
unfold zcanon, M64. rewrite (Z.mod_small (fp + 30)) by lia. rewrite (Z.mod_small SHADOW_OFF) by lia.
rewrite Z.add_comm. apply Z.mod_small. lia.
Qed.

(* g_s's payload bytes are bytes of G; the personality field is a row of onann_wr. *)
Lemma opf_inG_gs : forall a, ONANN_S <= a < ONANN_S + TW.SZ_g_s -> inG TG.G_HARNESS_B a.
Proof.
intros a Ha. unfold inG. apply Exists_exists. exists (0x5df640, 18264). split.
- unfold TG.G_HARNESS_B. cbn [In]. tauto.
- unfold in_zr, ONANN_S, TB_g_s, TW.SZ_g_s in *. cbn [fst snd]. lia.
Qed.

Lemma opf_wr_pers : forall Bw b a, ONANN_S + 128 <= a < ONANN_S + 136 -> onann_wr Bw b a.
Proof.
intros Bw b a Ha. apply onann_wr_pers. unfold twb_fld, TW.A_S_personality. unfold ONANN_S in Ha. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The instruction after the call (personality_from_name's return address), the instruction after the `beq` (the
   arm p <> 0) and the join at +0x210. *)
Definition OPF_C1 : Z := AF_on_announce + 0x1e8.
Definition OPF_C2 : Z := AF_on_announce + 0x1f0.
Definition OPF_J : Z := AF_on_announce + 0x210.
(* No shadow token in run 0: the span (0, 0); the shadow base s8 (atom 24). *)
Definition OPF_B0 : Z * Z := (0, 0).
Definition OPF_BX : sv := SOff 24 0.
(* run 0 at +0x1e0: no region. *)
Definition opf_ss0 : sstate := mkSS ONANN_PF sr_atoms [] None (mkFacts [] [] []).
(* run 1 at +0x1e8: no region (`mv a6, a0`, the `beq`, and the arm p = 0 to the join). The arm p <> 0 is taken up
   again at +0x1f0: g_s's personality at s4 (atom 20, written); s4 = s, s8 = the shadow base; the shadow entry of the
   check of the 8-byte store at s + 128. *)
Definition opf_rg_pers : YP09.region := YP09.mkRegion (Some 20%nat) 128 136 128 136 [].
Definition opf_fa2 : facts :=
  mkFacts [(20%nat, mkAF ONANN_S ONANN_S 6); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition opf_ss2 : sstate := mkSS OPF_C2 sr_atoms [opf_rg_pers] None opf_fa2.
Definition OPF_SH2 : list shent := [mkSHE 20 128 136].
(* the join at +0x210: f + 30 at s6 (atom 22, read: atom 32 = cmd), the spill slots s1 + 16 .. s1 + 64 (atom 9,
   written); s1 32-aligned, s6 = fp 8-aligned; the shadow entry of the check of the 1-byte load at f + 30. *)
Definition opf_rg_f30 : YP09.region :=
  YP09.mkRegion (Some 22%nat) 30 31 0 0 [YP09.mkChunk 30 (YP09.CVal 1 (SOff 32 0))].
Definition opf_rg_sp : YP09.region := YP09.mkRegion (Some 9%nat) 16 64 16 64 [].
Definition opf_faj : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF ONANN_S ONANN_S 6); (22%nat, mkAF 4096 (2 ^ 47 - 4096) 3);
           (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 255 0)] [] [].
Definition opf_ssj : sstate := mkSS OPF_J sr_atoms [opf_rg_f30; opf_rg_sp] None opf_faj.
Definition OPF_SHJ : list shent := [mkSHE 22 30 31].

(* The register and region readers of a symbolic state: at a pc of the listing (st_ok_pi) and in the form a run leaves
   at a call (st_ok at the callee's pc). *)
Ltac opf_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.
(* Register r of the machine state of HS, whose symbolic value is atom n, the start value of register rn: the run's
   valuation agrees with the earlier valuations below atom 1024 (E1, E2), the first reads the registers (EE). *)
Ltac opf_kreg_of HS E1 E2 EE r n rn Q H :=
  lazymatch type of Q with _ = ?v =>
    opf_reg HS r v H
      ltac:(cbn [sv_denot]; try rewrite (E2 n ltac:(lia)); try rewrite (E1 n ltac:(lia));
            rewrite (EE n rn eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
Ltac opf_kreg HS E1 E2 EE r n Q H := opf_kreg_of HS E1 E2 EE r n r Q H.
Ltac opf_region HS i HR :=
  lazymatch type of HS with
  | st_ok_pi ?sg ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let r0 := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
      assert (HR : region_ok sg Ex (ms_mem (restrict Hh msx)) r0)
        by (let HS' := fresh in pose proof HS as HS'; unfold st_ok_pi in HS';
            eapply (can_region_nth Ex _ (restrict Hh msx) i r0 HS'); vm_compute; reflexivity)
  end; cbn [ms_mem restrict] in HR.
Ltac opf_in := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac opf_awr_rs :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
(* The windows of a run's start state, computed, against the bytes Zs a run may change. *)
Ltac opf_win Hin Hx U :=
  lazymatch type of Hin with In ?y ?l => let l' := eval vm_compute in l in change (In y l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin];
          [injection Hin as <- <- <-; cbn [base_val] in Hx; rewrite ?U in Hx; lia |]);
  destruct Hin.
Ltac opf_name_md md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (md := m) in *; clearbody md end.
(* After a run: its valuation agrees with the start valuation E0 below atom 1024 (Hlo), its machine state is m. *)
Ltac opf_lo HS E0 Hlo m :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?EF _ (restrict _ ?mf) =>
      assert (Hlo : forall n, (n < 1024)%nat -> ew EF n = ew E0 n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity); rename mf into m
  end.
(* The valuation of HS, named. *)
Ltac opf_setE HS E :=
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ => set (E := EF) in * end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The valuations: the 32 registers (and, at the join, atom 32 = cmd). *)
Definition opf_E (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).
Definition opf_Ej (regs : bvmap 5 word) (c : Z) : env := Eimg (PI := PI_transportb) (Ereg regs [Z_to_bv 64 c]).

Lemma opf_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_E regs) n = YK11.getr regs r.
Proof. intros regs n r Hn. unfold opf_E. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma opf_ewj : forall regs c n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_Ej regs c) n = YK11.getr regs r.
Proof. intros regs c n r Hn. unfold opf_Ej. apply can_ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma opf_ewj32 : forall regs c, ew (opf_Ej regs c) 32 = Z_to_bv 64 c.
Proof. intros regs c. unfold opf_Ej. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.

(* One byte read off the view, in val_mem's form. *)
Lemma opf_val_mem1 : forall H (m : word -> option byte) a v,
  aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. replace k with 0%nat by lia. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte segs (mrestrict H m) a) as [x|]; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal. apply bv_eq.
pose proof (bv_unsigned_in_range 8 x) as R. change (bv_modulus 8) with 256 in R.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
rewrite !(Z.mod_small (bv_unsigned x) 256 R). reflexivity.
Qed.

(* The bytes of a value in memory, read byte by byte through the view; eight of them as a word. *)
Lemma opf_aview_of_val : forall H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> forall j, (j < n)%nat ->
  aview segs H m (a + Z.of_nat j) = Some (YO0f.le_byte v n j).
Proof.
intros H m a n v HV j Hj. unfold aview. rewrite (HV j Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
unfold YO0f.le_byte. apply Z.mod_mod. lia.
Qed.

Lemma opf_rdword_of_val : forall H (m : word -> option byte) a v, 0 <= v < 2 ^ 64 ->
  val_mem segs (mrestrict H m) a 8 v -> rdword (aview segs H m) a = Some v.
Proof.
intros H m a v Hv HV. pose proof (opf_aview_of_val H m a 8 v HV) as K. unfold rdword.
pose proof (K 0%nat ltac:(lia)) as H0. pose proof (K 1%nat ltac:(lia)) as H1.
pose proof (K 2%nat ltac:(lia)) as H2. pose proof (K 3%nat ltac:(lia)) as H3.
pose proof (K 4%nat ltac:(lia)) as H4. pose proof (K 5%nat ltac:(lia)) as H5.
pose proof (K 6%nat ltac:(lia)) as H6. pose proof (K 7%nat ltac:(lia)) as H7.
cbv [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3, H4, H5, H6, H7.
rewrite Z.add_0_r in H0.
rewrite H0, H1, H2, H3, H4, H5, H6, H7. f_equal. apply le_bytes8. exact Hv.
Qed.

(* A state with no region at any pc of the listing. *)
Lemma opf_entry0 : forall (W : world segs) regs mem pc,
  st_ok_pi segs VAL (opf_E regs) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

(* g_s's bytes [s + 128, s + 136) are addressable at every AR state: a whole granule of the record's zero shadow. *)
Lemma opf_ra_pers : forall ly S (W : world segs) mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (ONANN_S + 128) 8.
Proof.
intros ly S W mem md HZ HAR x Hx.
exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hx8 : ONANN_S <= 8 * (x / 8) /\ 8 * (x / 8) + 8 <= ONANN_S + TW.SZ_g_s)
  by (unfold ONANN_S, TB_g_s, TW.SZ_g_s in *; lia).
assert (Hz := decode_zshadow_rd B ly S W mem md ONANN_S (ONANN_S + TW.SZ_g_s) (8 * (x / 8)) HAR
  ltac:(rewrite Z.mul_comm; apply Z_mod_mult) (proj1 Hx8) (proj2 Hx8) HZ).
unfold shadow_of_addr.
replace (SHADOW_OFF + x / 8) with (FCells.shadow_addr (8 * (x / 8))); [exact Hz|].
unfold FCells.shadow_addr, FCells.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The symbolic state at +0x1f0 holds of the machine state there, and its run's shadow entry holds. *)
Lemma opf_entry2 : forall ly S (W : world segs) regs mem md,
  trans_onann_cells B -> @AR rc segs B ly S W mem md ->
  YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 24 = w64 SHADOW_OFF ->
  st_ok_pi segs VAL (opf_E regs) opf_ss2
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OPF_C2)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OPF_BX OPF_SH2 (opf_E regs) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md HSC HAR R20 R24.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U20 : bv_unsigned (ew (opf_E regs) 20) = ONANN_S)
  by (rewrite (opf_ew regs 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (opf_E regs) 24) = SHADOW_OFF)
  by (rewrite (opf_ew regs 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
split.
- rewrite restrict_mkst_fx. unfold opf_ss2.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_nil]. unfold opf_rg_pers, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (ONANN_S + o) G_HARNESS_B_rw).
    apply opf_inG_gs. unfold TW.SZ_g_s. lia.
  + apply pairwise_disjoint_of_extents.
    unfold opf_rg_pers, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  + unfold opf_fa2, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U24.
    change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- pose proof (opf_ra_pers ly S W mem md HSC HAR) as HRA.
  assert (UB : U (opf_E regs) OPF_BX = SHADOW_OFF).
  { unfold U, OPF_BX. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OPF_SH2. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OPF_BX 20 (ONANN_S + 128) 8 ONANN_S 128 136 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U20, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF. lia.
Qed.

(* The symbolic state at +0x210 holds of the machine state there, and the join's shadow entry holds. *)
Lemma opf_entry_j : forall (W : world segs) regs mem (sp1 fp c : Z),
  YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 20 = w64 ONANN_S -> YK11.getr regs 22 = w64 fp ->
  YK11.getr regs 24 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp1 -> sp1 + 64 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 16 <= o < 64 -> apresent (w_H W) mem (sp1 + o)) ->
  4096 <= fp -> fp <= 2 ^ 47 - 4096 -> fp + 64 <= sp1 -> fp mod 8 = 0 -> amem_range fp 64 ->
  0 <= c < 256 -> aview segs (w_H W) mem (fp + 30) = Some c ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (fp + 30) 1 ->
  st_ok_pi segs VAL (opf_Ej regs c) opf_ssj
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + OPF_J)) mem (YK11.seg_rom segs))) /\
  sh_ok segs OPF_BX OPF_SHJ (opf_Ej regs c) (mrestrict (w_H W) mem).
Proof.
intros W regs mem sp1 fp c R9 R20 R22 R24 Hs1 Hs2 Hs3 Hsp Hf1 Hf1' Hf2 Hf3 HAM Hc Hv HRA.
assert (CS : ONANN_S = 6157888) by reflexivity.
assert (U9 : bv_unsigned (ew (opf_Ej regs c) 9) = sp1)
  by (rewrite (opf_ewj regs c 9 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (opf_Ej regs c) 20) = ONANN_S)
  by (rewrite (opf_ewj regs c 20 20%bv eq_refl), R20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew (opf_Ej regs c) 22) = fp)
  by (rewrite (opf_ewj regs c 22 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew (opf_Ej regs c) 24) = SHADOW_OFF)
  by (rewrite (opf_ewj regs c 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew (opf_Ej regs c) 32) = c)
  by (rewrite opf_ewj32; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold opf_ssj.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold opf_rg_f30, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs (opf_Ej regs c) _ fp 30 1 (SOff 32 0) c);
        [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | lia |].
      exact (opf_val_mem1 _ _ _ _ Hv).
    * unfold opf_rg_sp, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply Hsp. lia.
  + apply pairwise_disjoint_of_extents.
    unfold extent_of_region, opf_rg_f30, opf_rg_sp. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U9, U22. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  + unfold opf_faj, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U20, U22, U24, U32.
    change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; rewrite ?CS; unfold SHADOW_OFF;
    first [lia | reflexivity].
- assert (UB : U (opf_Ej regs c) OPF_BX = SHADOW_OFF).
  { unfold U, OPF_BX. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  unfold sh_ok, OPF_SHJ. constructor; [|constructor].
  apply (shent_ok_of_range segs (w_H W) mem _ OPF_BX 22 (fp + 30) 1 fp 30 31 HRA UB).
  + unfold U. cbn [sv_denot]. rewrite U22, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx.
    unfold amem_range, kLowMemEnd, kHighMemBeg, SHADOW_OFF in HAM |- *. lia.
Qed.
End ent.

(* ------------------------------------------------------------------ *)
(* 3. The cut's facts carried, the join, and the piece                 *)
(* ------------------------------------------------------------------ *)

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head segs B).
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Lemma opf_stk : 208 + PFROM_STK <= ONANN_STK.
Proof. cbv. congruence. Qed.

(* onann_cur at a later memory of the same state whose view differs at most at Zs: bytes of the call's window below
   the saved words (the spill slots), or bytes of G in onann_wr Bw b (the personality field). *)
Lemma opf_cur_step : AR_laws segs B -> gx_ok segs B TG.G_HARNESS_B ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout)
         (S2 : astate) (W2 : world segs) (mem2 mem3 : word -> option byte) (md2 md3 : Model) (e : Z)
         (Zs : Z -> Prop),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem2 md2 e ->
    ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mem3 md3 (k + e) ->
    (forall a, Zs a -> (spZ regs - ONANN_STK <= a < spZ regs - 104) \/ (inG TG.G_HARNESS_B a /\ onann_wr Bw b a)) ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a) ->
    (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mem3 md3 e.
Proof.
intros LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
  ly2 S2 W2 mem2 mem3 md2 md3 e Zs HFIX HCUR HJ3 HZ KD GA.
destruct (onann_cur_ar B MT LAWS HFIX HCUR) as (HARc & HAR2 & _ & _ & _ & _ & Hin2 & EF2 & _ & _ & HFG & HF0 & _ &
  HFc & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof opf_stk as HSTK.
assert (HP0 : 0 <= PFROM_STK) by (cbv; congruence).
refine (conj HJ3 (conj He (conj Hfrs (conj Hperm (conj HlyF (conj HMO (conj _ (conj _ _)))))))).
- apply (dk_kept_step_gw segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc W2 mem2 mem3
    (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) Zs HARc HK KD GA).
  + intros a Hz Hc. destruct (HZ a Hz) as [Hw | [Hg _]]; [lia|]. exfalso.
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B a HGX Hg) as Hl. unfold kLowMemEnd in Hl. lia.
  + intros b0 m i Hb Hi Hz. destruct (HZ _ Hz) as [Hw | [_ Hw]]; [|exact Hw]. exfalso.
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m HARc Hb) as (_ & H4096 & Hbce & _). lia.
  + intros a Hz Hi HnG _ _. destruct (HZ a Hz) as [Hw | [Hg _]]; [|exact (HnG Hg)].
    pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl. lia.
  + intros c p a Hin Hr Hz. destruct (HZ a Hz) as [Hw | [_ Hw]]; [|exact Hw]. exfalso.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc c p HARc Hin) as (F4096 & Fce & _).
    pose proof (fs_frame_bytes_nonneg c) as Hfs.
    destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
    pose proof (shadow_range_end (frame_addr lyc c p) (fs_frame_bytes c) Hfs) as Hse.
    assert (Hd : (frame_addr lyc c p + fs_frame_bytes c) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc c p) 8 ltac:(lia) ltac:(lia)).
    unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
- apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros Hz.
  destruct (HZ _ Hz) as [Hw | [Hg _]]; [lia|].
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl. lia.
- unfold ONANN_FBYTES in *. rewrite <- HFL. apply YCbq.rdword_ext. intros i Hi. apply KD; [lia|]. intros Hz.
  destruct (HZ _ Hz) as [Hw | [Hg _]]; [lia|]. exact (HFG (F + 512 - 8 + i) ltac:(lia) Hg).
Qed.

(* onann_a_ok at a later memory whose view keeps a's 40 bytes and its 5 shadow bytes. *)
Lemma opf_a_ok_keep : forall (W W' : world segs) (m m' : word -> option byte) F buf b,
  onann_a_ok W m F buf b ->
  (forall a, F + 32 <= a < F + 72 -> aview segs (w_H W') m' a = aview segs (w_H W) m a) ->
  (forall i, 4 <= i < 9 ->
     aview segs (w_H W') m' (SHADOW_OFF + F / 8 + i) = aview segs (w_H W) m (SHADOW_OFF + F / 8 + i)) ->
  onann_a_ok W' m' F buf b.
Proof.
intros W W' m m' F buf b (A1 & A2 & A3 & A4 & A5) KV KS.
pose proof (opf_field_len (skipn 15 (DSpec.fr_body b))) as L1.
pose proof (opf_field_len (skipn 24 (DSpec.fr_body b))) as L2.
unfold onann_a_ok, ONANN_A in *.
split; [apply (garr8_frame segs _ _ _ _ A1); intros a Ha; rewrite length_map in Ha;
        apply (mbyte_of_aview segs); apply KV; lia|].
split; [apply (garr8_frame segs _ _ _ _ A2); intros a Ha; rewrite length_map in Ha;
        apply (mbyte_of_aview segs); apply KV; lia|].
split; [rewrite <- A3; apply YCbq.rdword_ext; intros i Hi; apply KV; lia|].
split; [rewrite <- A4; apply YCbq.rdword_ext; intros i Hi; apply KV; lia|].
intros i Hi. rewrite (KS i Hi). exact (A5 i Hi).
Qed.

(* THE JOIN, +0x210 .. +0x24c and the two arms: fp & 7 (folded), the check of f + 30, the spills, cmd, `bne a1, a2`;
   cmd = 0xe1 runs one instruction to the find_mac cut, any other cmd runs +0x270 .. +0x274 to the desk notice cut.
   The world is onann_w1 timg_B Bw b on both paths (run 1's two arms end here). *)
Lemma opf_join : onann_laws B MT -> onann_callees B MT -> @onann_fm_at fx rc B MT -> @onann_dn_at fx rc B MT ->
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (fp buf now : Z)
         (b fj : list byte) (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly3 : alayout)
         (S3 : astate) (W3 : world segs) (mJ : word -> option byte) (mdJ : Model) (rJ : bvmap 5 word),
    onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F ->
    onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mJ mdJ 0 ->
    tw_at TMAP_B (aview segs (w_H W3) mJ) (onann_w1 timg_B Bw b) -> onann_ign b = false ->
    onann_a_ok W3 mJ F buf b ->
    onann_regs_ign regs rJ sp1 F ->
    YK11.getr rJ 22 = w64 fp -> YK11.getr rJ 23 = w64 now -> YK11.getr rJ 26 = w64 (F + ONANN_A) ->
    YK11.getr rJ 16 = w64 (onann_pv timg_B b) ->
    SRr segs W3 (mkCfg (@YK11.mkst fx rJ (Z_to_bv 64 (BASE + OPF_J)) mJ (YK11.seg_rom segs)) mdJ)
      (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Proof.
intros HLAWS HCALL FM DN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
  sp1 F ly3 S3 W3 mJ mdJ rJ HFIX HCUR Htw Hig HA HREGS R22 R23 R26 R16.
pose proof HLAWS as (_ & _ & HSC & _ & _ & _ & _ & LAWS & _ & _ & _ & _ & _ & HGX & _).
pose proof HFIX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & Hnow & _).
destruct (onann_cur_ar B MT LAWS HFIX HCUR) as (HARc & HAR3 & _ & _ & _ & _ & Hin3 & EF3 & _ & _ & HFG & HF0 &
  HF64 & HFc & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _ & _ & _ & Hsp1r & Hsp132 & Hsp146).
pose proof HCUR as (HJ & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
destruct HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof opf_stk as HSTK.
assert (HP0 : 0 <= PFROM_STK) by (cbv; congruence).
unfold ONANN_A in *.
(* f + 30 at the join: the command and its shadow byte 0 (on_announce_seg_kit.v onann_f30) *)
destruct (onann_f30 B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F ly3 S3 W3 mJ mdJ 0 regs ONANN_STK HFIX HCUR ltac:(lia) ltac:(lia))
  as (Hfp0 & Hfpc & Hfp8 & _ & _ & _ & Hfrd & _ & Hcmd & Hf30 & _ & Hsh30 & _).
unfold FRAME_F_SIZE in Hfpc.
assert (HAM : amem_range fp 64) by exact (proj1 (proj2 (proj2 (proj2 Hfrd)))).
assert (HRA30 : range_addressable (aview segs (w_H W3) mJ) SHADOW_OFF (fp + 30) 1).
{ intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace x with (fp + 30) by lia. exact Hsh30. }
(* the spill slots are bytes of the call's window, present *)
assert (HSP : forall o, 16 <= o < 64 -> apresent (w_H W3) mJ (sp1 + o)).
{ intros o Ho. destruct HK as (_ & _ & _ & _ & _ & K6). apply K6. lia. }
(* the join's symbolic state *)
destruct (opf_entry_j (fx := fx) W3 rJ mJ sp1 fp (DSpec.fr_cmd b) R9 R20 R22 R24 Hsp146 ltac:(lia) Hsp132 HSP Hfp0
  ltac:(lia) ltac:(lia) Hfp8 HAM Hcmd Hf30 HRA30) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (opf_Ej rJ (DSpec.fr_cmd b))) by (unfold opf_Ej; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_Ej rJ (DSpec.fr_cmd b)) n = YK11.getr rJ r)
  by (intros n r Hn; exact (opf_ewj rJ _ n r Hn)).
assert (U9 : bv_unsigned (ew (opf_Ej rJ (DSpec.fr_cmd b)) 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* run A, +0x210 .. +0x24c: it stops at the `bne` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ opf_awr_rs.
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
  apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9 in Ha.
  left. split; [unfold awr_byte; left; lia | lia]. }
opf_name_md mdA.
opf_lo HS (opf_Ej rJ (DSpec.fr_cmd b)) EAlo msA.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 64) ->
  aview segs (w_H W3) (ms_mem msA) a = aview segs (w_H W3) mJ a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 64) HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx U9. }
assert (GAa : forall a, apresent (w_H W3) mJ a -> apresent (w_H W3) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
opf_setE HS EA.
assert (U9A : bv_unsigned (ew EA 9) = sp1) by (rewrite (EAlo 9%nat ltac:(lia)); exact U9).
assert (U32A : bv_unsigned (ew EA 32) = DSpec.fr_cmd b)
  by (rewrite (EAlo 32%nat ltac:(lia)), opf_ewj32; apply unsigned_lit_small; lia).
(* what both arms close with: the cut's facts at the arm's final memory *)
assert (TAIL : forall (mF : word -> option byte) (mdF : Model),
  ajournal_gx TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly3 S3 W3 mF mdF (k + 0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 64) ->
     aview segs (w_H W3) mF a = aview segs (w_H W3) mJ a) ->
  (forall a, apresent (w_H W3) mJ a -> apresent (w_H W3) mF a) ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mF mdF 0 /\
  tw_at TMAP_B (aview segs (w_H W3) mF) (onann_w1 timg_B Bw b) /\ onann_a_ok W3 mF F buf b).
{ intros mF mdF HJF KF GF.
  split; [|split].
  - apply (opf_cur_step LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 mJ mF mdJ mdF 0 (fun x => sp1 + 16 <= x < sp1 + 64) HFIX HCUR HJF); [| exact KF | exact GF].
    intros a Ha. left. cbv beta in Ha. lia.
  - apply (tw_kept_GB (aview segs (w_H W3) mJ)); [exact Htw|]. intros b0 n i Hbn Hi.
    assert (Hg : inG TG.G_HARNESS_B (b0 + i))
      by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KF; lia.
  - apply (opf_a_ok_keep W3 W3 mJ mF F buf b HA).
    + intros a Ha. apply KF; lia.
    + intros i Hi.
      assert (HF8 : 0 <= F / 8 <= 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
      apply KF; unfold SHADOW_OFF; lia. }
(* the spill slots at an arm's final memory *)
assert (SLOTS : forall (EB : env) (mF : word -> option byte) cs,
  region_ok segs EB (mrestrict (w_H W3) mF) (YP09.mkRegion (Some 9%nat) 16 64 16 64 cs) ->
  bv_unsigned (ew EB 9) = sp1 -> bv_unsigned (ew EB 22) = fp -> bv_unsigned (ew EB 23) = now ->
  bv_unsigned (ew EB 24) = SHADOW_OFF -> bv_unsigned (ew EB 26) = F + 32 ->
  In (YP09.mkChunk 16 (YP09.CVal 8 (SOff 26 0))) cs -> In (YP09.mkChunk 24 (YP09.CVal 8 (SOff 23 0))) cs ->
  In (YP09.mkChunk 56 (YP09.CVal 8 (SOff 22 30))) cs ->
  In (YP09.mkChunk 48 (YP09.CVal 8 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 30) (SLit 3)) (SOff 24 0)))) cs ->
  onann_slots_dn W3 mF fp now sp1 F).
{ intros EB mF cs HR V9 V22 V23 V24 V26 I16 I24 I56 I48.
  unfold onann_slots_dn, onann_slot, ONANN_A.
  split; [|split; [|split]].
  - apply opf_rdword_of_val; [unfold SHADOW_OFF; pose proof (Z.div_pos (fp + 30) 8 ltac:(lia) ltac:(lia));
                              assert ((fp + 30) / 8 <= fp + 30) by (apply Z.div_le_upper_bound; lia); lia|].
    exact (can_field_of_region EB _ 9 sp1 _ 16 64 16 64 48 8%N _ _ HR V9 I48
      (opf_den_sh EB fp V22 V24 ltac:(lia) ltac:(lia))
      ltac:(unfold SHADOW_OFF; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64);
            pose proof (Z.div_pos (fp + 30) 8 ltac:(lia) ltac:(lia));
            assert ((fp + 30) / 8 <= fp + 30) by (apply Z.div_le_upper_bound; lia); lia)
      ltac:(cbn; lia)).
  - apply opf_rdword_of_val; [lia|].
    exact (can_field_of_region EB _ 9 sp1 _ 16 64 16 64 56 8%N _ _ HR V9 I56 (opf_den_off EB 22 30 fp V22)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
  - apply opf_rdword_of_val; [exact Hnow|].
    pose proof (can_field_of_region EB _ 9 sp1 _ 16 64 16 64 24 8%N _ _ HR V9 I24 (opf_den_off EB 23 0 now V23)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as X.
    rewrite Z.add_0_r in X. exact X.
  - apply opf_rdword_of_val; [lia|].
    pose proof (can_field_of_region EB _ 9 sp1 _ 16 64 16 64 16 8%N _ _ HR V9 I16 (opf_den_off EB 26 0 (F + 32) V26)
      ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)) as X.
    rewrite Z.add_0_r in X. exact X. }
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* cmd <> 0xe1: +0x270 `sltiu a1, a0, 1`, `j` to the desk notice cut +0x300 *)
  cbn [branch_taken sv_denot] in Hc. rewrite U32A, Z.add_0_r, (opf_eqb_z (DSpec.fr_cmd b) 225) in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONANN_DN.
  { opf_awr_rs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9A in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  opf_name_md mdB.
  opf_lo HS EA EBlo msB.
  (* the registers the desk notice cut reads *)
  opf_kreg HS EAlo EBlo EE (2%bv : bv 5) 2%nat R2 X2. opf_kreg HS EAlo EBlo EE (3%bv : bv 5) 3%nat R3 X3.
  opf_kreg HS EAlo EBlo EE (4%bv : bv 5) 4%nat R4 X4. opf_kreg HS EAlo EBlo EE (8%bv : bv 5) 8%nat R8 X8.
  opf_kreg HS EAlo EBlo EE (9%bv : bv 5) 9%nat R9 X9. opf_kreg HS EAlo EBlo EE (18%bv : bv 5) 18%nat R18 X18.
  opf_kreg HS EAlo EBlo EE (19%bv : bv 5) 19%nat R19 X19. opf_kreg HS EAlo EBlo EE (25%bv : bv 5) 25%nat R25 X25.
  opf_kreg HS EAlo EBlo EE (20%bv : bv 5) 20%nat R20 X20. opf_kreg HS EAlo EBlo EE (24%bv : bv 5) 24%nat R24 X24.
  opf_kreg HS EAlo EBlo EE (22%bv : bv 5) 22%nat R22 X22. opf_kreg HS EAlo EBlo EE (26%bv : bv 5) 26%nat R26 X26.
  opf_kreg HS EAlo EBlo EE (16%bv : bv 5) 16%nat R16 X16.
  opf_reg HS (15%bv : bv 5) (w64 (onann_off (onann_w1 timg_B Bw b) b)) X15
    ltac:(rewrite (opf_off_dn (onann_w1 timg_B Bw b) b Hc); unfold w64; cbn [sv_denot]; apply bv_eq;
          rewrite !Z_to_bv_unsigned; reflexivity).
  opf_reg HS (11%bv : bv 5) (w64 1) X11 ltac:(reflexivity).
  (* the run kept every byte but the spill slots *)
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 64) ->
    aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mJ a).
  { intros a Ha Hn. rewrite <- (KA a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 64) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx U9A. }
  assert (GB : forall a, apresent (w_H W3) mJ a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  destruct (TAIL (ms_mem msB) mdB HJ KB GB) as (CUR & TWB & HAB).
  opf_region HS 1%nat HR.
  assert (SL : onann_slots_dn W3 (ms_mem msB) fp now sp1 F).
  { apply (SLOTS _ (ms_mem msB) _ HR).
    - try rewrite (EBlo 9%nat ltac:(lia)); exact U9A.
    - try rewrite (EBlo 22%nat ltac:(lia)); rewrite (EAlo 22%nat ltac:(lia)), (EE 22%nat 22%bv eq_refl), R22.
      apply unsigned_lit_small. lia.
    - try rewrite (EBlo 23%nat ltac:(lia)); rewrite (EAlo 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl), R23.
      apply unsigned_lit_small. lia.
    - try rewrite (EBlo 24%nat ltac:(lia)); rewrite (EAlo 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl), R24.
      apply unsigned_lit_small. unfold SHADOW_OFF. lia.
    - try rewrite (EBlo 26%nat ltac:(lia)); rewrite (EAlo 26%nat ltac:(lia)), (EE 26%nat 26%bv eq_refl), R26.
      apply unsigned_lit_small. lia.
    - opf_in.
    - opf_in.
    - opf_in.
    - opf_in. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Q) end.
  apply (DN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem msB) mdB (ms_regs msB) HFIX).
  + exact (conj CUR (conj TWB (conj Hig (conj HAB SL)))).
  + exact (conj (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))) (conj X20 X24))
      (conj X22 (conj X26 (conj X16 (conj X15 X11))))).
- (* cmd = 0xe1: the find_mac cut +0x250 *)
  cbn [branch_taken sv_denot] in Hc. rewrite U32A, Z.add_0_r, (opf_eqb_z (DSpec.fr_cmd b) 225) in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan ONANN_FM.
  { opf_awr_rs.
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9A in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  opf_name_md mdB.
  opf_lo HS EA EBlo msB.
  opf_kreg HS EAlo EBlo EE (2%bv : bv 5) 2%nat R2 X2. opf_kreg HS EAlo EBlo EE (3%bv : bv 5) 3%nat R3 X3.
  opf_kreg HS EAlo EBlo EE (4%bv : bv 5) 4%nat R4 X4. opf_kreg HS EAlo EBlo EE (8%bv : bv 5) 8%nat R8 X8.
  opf_kreg HS EAlo EBlo EE (9%bv : bv 5) 9%nat R9 X9. opf_kreg HS EAlo EBlo EE (18%bv : bv 5) 18%nat R18 X18.
  opf_kreg HS EAlo EBlo EE (19%bv : bv 5) 19%nat R19 X19. opf_kreg HS EAlo EBlo EE (25%bv : bv 5) 25%nat R25 X25.
  opf_kreg HS EAlo EBlo EE (20%bv : bv 5) 20%nat R20 X20. opf_kreg HS EAlo EBlo EE (24%bv : bv 5) 24%nat R24 X24.
  opf_kreg HS EAlo EBlo EE (22%bv : bv 5) 22%nat R22 X22. opf_kreg HS EAlo EBlo EE (26%bv : bv 5) 26%nat R26 X26.
  opf_kreg HS EAlo EBlo EE (16%bv : bv 5) 16%nat R16 X16.
  opf_reg HS (10%bv : bv 5) (w64 0) X10 ltac:(reflexivity).
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 16 <= a < sp1 + 64) ->
    aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mJ a).
  { intros a Ha Hn. rewrite <- (KA a Ha Hn).
    apply (kept_of_frame _ _ _ _ _ (fun x => sp1 + 16 <= x < sp1 + 64) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx U9A. }
  assert (GB : forall a, apresent (w_H W3) mJ a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  destruct (TAIL (ms_mem msB) mdB HJ KB GB) as (CUR & TWB & HAB).
  opf_region HS 1%nat HR.
  assert (SL : onann_slots_dn W3 (ms_mem msB) fp now sp1 F).
  { apply (SLOTS _ (ms_mem msB) _ HR).
    - try rewrite (EBlo 9%nat ltac:(lia)); exact U9A.
    - try rewrite (EBlo 22%nat ltac:(lia)); rewrite (EAlo 22%nat ltac:(lia)), (EE 22%nat 22%bv eq_refl), R22.
      apply unsigned_lit_small. lia.
    - try rewrite (EBlo 23%nat ltac:(lia)); rewrite (EAlo 23%nat ltac:(lia)), (EE 23%nat 23%bv eq_refl), R23.
      apply unsigned_lit_small. lia.
    - try rewrite (EBlo 24%nat ltac:(lia)); rewrite (EAlo 24%nat ltac:(lia)), (EE 24%nat 24%bv eq_refl), R24.
      apply unsigned_lit_small. unfold SHADOW_OFF. lia.
    - try rewrite (EBlo 26%nat ltac:(lia)); rewrite (EAlo 26%nat ltac:(lia)), (EE 26%nat 26%bv eq_refl), R26.
      apply unsigned_lit_small. lia.
    - opf_in.
    - opf_in.
    - opf_in.
    - opf_in. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_FM)) mm rom) mdx) Q) end.
  apply (FM HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly3 S3 W3 (ms_mem msB) mdB (ms_regs msB) HFIX).
  + exact (conj CUR (conj TWB (conj Hig (conj Hc (conj HAB SL))))).
  + exact (conj (conj (conj X2 (conj X3 (conj X4 (conj X8 (conj X9 (conj X18 (conj X19 X25))))))) (conj X20 X24))
      (conj X22 (conj X26 (conj X16 X10)))).
Qed.

(* THE PIECE: run 0 (+0x1e0, a0 = a + 10, `jal`), personality_from_name through gx_call_cg, run 1 (+0x1e8 .. the
   `beq`), the arm p = 0 to +0x210, the arm p <> 0 (+0x1f0 .. +0x20c, the store of p at s + 128) to +0x210, the join. *)
Lemma opf_holds : @onann_pf_stmt fx rc B MT.
Proof.
unfold onann_pf_stmt, onann_pf_at.
intros FM DN HLAWS HCALL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
  sp1 F ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
pose proof HLAWS as (_ & _ & HSC & _ & _ & HRU & HRE & LAWS & MTL & _ & _ & _ & FFL & HGX & HGE).
pose proof HCALL as (_ & _ & HPF & _).
pose proof HCUR as (HCUR0 & Htw2 & Hig & HA).
pose proof HCUR0 as (HJ1 & He & Hfrs & Hperm & HlyF & HMO & HK & HSV & HFL).
destruct HREGS as (((R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25) & R20 & R24) & R22 & R23 & R26).
pose proof HFIX as (HJe & _ & _ & Hgp & Htp & _ & _ & _ & Hsp16 & Hwlo & Hwhi & Hnow & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Hnev & _ & EF & _).
destruct (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & Elo2 & Ehi2 & EFA & EFL & Hin2 & EF2 & HFb & HFsh &
  HFG & HF0 & HF64 & HFc & HFapp & Hceil & Hslo & Hshi & H47 & _ & _ & _ & _ & _ & Hsp1r & Hsp132 & Hsp146).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof opf_stk as HSTK.
assert (HP0 : 0 <= PFROM_STK) by (cbv; congruence).
assert (HEV : 0 <= ONANN_EV) by (cbv; congruence).
assert (CS : ONANN_S = 6157888) by reflexivity.
unfold ONANN_A in R26.
assert (Hsp116 : sp1 mod 16 = 0).
{ pose proof (Z.div_mod sp1 32 ltac:(lia)) as D. rewrite Hsp132, Z.add_0_r in D. rewrite D.
  replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia. apply Z_mod_mult. }
assert (HF8 : F mod 8 = 0).
{ pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D. rewrite D.
  replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z_mod_mult. }
assert (HFsh8 : 0 <= F / 8 <= 2 ^ 47) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
pose proof (opf_field_len (skipn 24 (DSpec.fr_body b))) as Ltb.
pose proof (opf_pv_range b) as Hpvr.
pose proof (onann_rom_cur B MT HLAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
  Bw' pos sp1 F ly2 S2 W2 mem2 md2 0 HFIX HCUR0) as Hrom2.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
(* ---- run 0, +0x1e0 .. +0x1e4: a0 = a + 10, `jal diginet_personality_from_name` ---- *)
pose proof (opf_entry0 (fx := fx) W2 regs2 mem2 ONANN_PF) as HS.
assert (SHOK : sh_ok segs OPF_BX [] (opf_E regs2) (mrestrict (w_H W2) mem2)) by constructor.
assert (HEI : img_env VAL A_LIM (opf_E regs2)) by (unfold opf_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_E regs2) n = YK11.getr regs2 r)
  by (intros n r Hn; exact (opf_ew regs2 n r Hn)).
pose proof HJ1 as HJ.
paj_run_tok RUN HS HJ SHOK OPF_B0.
{ opf_awr_rs. apply awr_ok_x_nil. }
opf_name_md md1.
opf_lo HS (opf_E regs2) E1lo ms1.
opf_reg HS (1%bv : bv 5) (Z_to_bv 64 (BASE + 27664)) Q1 ltac:(apply codeptr_val; assumption).
opf_kreg HS E1lo E1lo EE (2%bv : bv 5) 2%nat R2 Q2. opf_kreg HS E1lo E1lo EE (3%bv : bv 5) 3%nat R3 Q3.
opf_kreg HS E1lo E1lo EE (4%bv : bv 5) 4%nat R4 Q4. opf_kreg HS E1lo E1lo EE (8%bv : bv 5) 8%nat R8 Q8.
opf_kreg HS E1lo E1lo EE (9%bv : bv 5) 9%nat R9 Q9. opf_kreg HS E1lo E1lo EE (18%bv : bv 5) 18%nat R18 Q18.
opf_kreg HS E1lo E1lo EE (19%bv : bv 5) 19%nat R19 Q19. opf_kreg HS E1lo E1lo EE (25%bv : bv 5) 25%nat R25 Q25.
opf_kreg HS E1lo E1lo EE (20%bv : bv 5) 20%nat R20 Q20. opf_kreg HS E1lo E1lo EE (24%bv : bv 5) 24%nat R24 Q24.
opf_kreg HS E1lo E1lo EE (22%bv : bv 5) 22%nat R22 Q22. opf_kreg HS E1lo E1lo EE (23%bv : bv 5) 23%nat R23 Q23.
opf_kreg HS E1lo E1lo EE (26%bv : bv 5) 26%nat R26 Q26.
opf_reg HS (10%bv : bv 5) (w64 (F + 32 + 10)) Q10
  ltac:(cbn [sv_denot]; try rewrite (E1lo 26%nat ltac:(lia)); rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64;
        rewrite unsigned_lit_small by lia; reflexivity).
assert (KA0 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem ms1) a = aview segs (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx E1lo. }
assert (GA0 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms1) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
set (rC := ms_regs ms1) in *. set (mC := ms_mem ms1) in *.
assert (NSP : spZ rC = sp1) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the cut's facts at the call memory: run 0 wrote nothing *)
assert (CUR1 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 mC md1 0)
  by exact (opf_cur_step LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
    pos sp1 F ly2 S2 W2 mem2 mC md2 md1 0 (fun _ => False) HFIX HCUR0 HJ ltac:(intros a [])
    ltac:(intros a Ha _; exact (KA0 a Ha)) GA0).
pose proof CUR1 as (_ & _ & _ & _ & _ & _ & KC1 & HSV1 & HFL1).
assert (Htw1 : tw_at TMAP_B (aview segs (w_H W2) mC) Bw).
{ apply (tw_kept_GB (aview segs (w_H W2) mem2)); [exact Htw2|]. intros b0 n i Hbn Hi.
  assert (Hg : inG TG.G_HARNESS_B (b0 + i))
    by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
  pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
  apply KA0. lia. }
assert (HA1 : onann_a_ok W2 mC F buf b).
{ apply (opf_a_ok_keep W2 W2 mem2 mC F buf b HA).
  - intros a Ha. apply KA0. lia.
  - intros i Hi. apply KA0. unfold SHADOW_OFF. lia. }
assert (Hrom1 : trans_rom_view_rd W2 mC).
{ intros a Ha. pose proof (trans_ro_rd_bounds a Ha) as Rb. rewrite (KA0 a ltac:(lia)). exact (Hrom2 a Ha). }
(* personality_from_name's premises at the call *)
assert (EBR : BASE + 27664 = 0x87eb0) by (vm_compute; reflexivity).
assert (P_ra : YK0s.ret_ok (YK11.getr rC 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PI_transportb)); [lia | reflexivity]).
assert (P_ra4 : 4096 <= raZ rC) by (unfold raZ; rewrite Q1, EBR, unsigned_lit_small by lia; lia).
assert (P_gp : YK11.getr rC 3 = w64 (as_gp B)) by (rewrite Q3; exact Hgp).
assert (P_tp : YK11.getr rC 4 = w64 (as_tp B)) by (rewrite Q4; exact Htp).
assert (P_sp16 : spZ rC mod 16 = 0) by (rewrite NSP; exact Hsp116).
assert (P_win1 : sp0 - STK <= spZ rC - PFROM_STK) by (rewrite NSP; lia).
assert (P_win2 : spZ rC <= sp0) by (rewrite NSP; lia).
assert (P_x : F + 32 + 10 <> 0) by lia.
assert (P_garr : garr8 segs (mrestrict (w_H W2) mC) (F + 32 + 10)
  (map DSpec.bz (TSS.ann_field (skipn 24 (DSpec.fr_body b))))) by exact (proj1 (proj2 HA1)).
assert (P_src : trans_src_ok B ly2 S2 W2 mC (F + 32 + 10) (Z.of_nat (length (TSS.ann_field (skipn 24 (DSpec.fr_body b)))))).
{ right. split.
  - left. exists ONANN_CID, pos. split; [exact Hin2|]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - split; [|split; [|split; [|split; [|split]]]].
    + intros a Ha. apply aview_some_of_apresent. apply GA0. exact (proj1 (HFb a ltac:(lia))).
    + apply (TGNA.frame_ra_zero _ F _ _ 4 9); [lia | exact HF8 | lia | lia |].
      intros i Hi. exact (proj2 (proj2 (proj2 (proj2 HA1))) i Hi).
    + apply (TGNA.frame_hull_vis _ F 512); [lia | exact HF64 | reflexivity | lia | lia | lia |].
      intros i Hi. unfold shadow_addr. apply aview_some_of_apresent. apply GA0.
      change (512 / 8) with 64 in Hi. exact (proj1 (HFsh i Hi)).
    + unfold in_app, ASAN_CEIL in HFapp. unfold amem_range.
      destruct HFapp as [Hap1 [Hap2 | (Hap2 & Hap3)]]; [left | right];
        unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
    + lia.
    + lia. }
assert (P_off : decode_off_win rC PFROM_STK (F + 32 + 10) (Z.of_nat (length (TSS.ann_field (skipn 24 (DSpec.fr_body b))))))
  by (unfold decode_off_win; left; rewrite NSP; lia).
assert (P_ev : st_nev S + (k + 0) + PFROM_EV <= EV_MAX) by (unfold PFROM_EV; lia).
(* ---- +0x1e4: diginet_personality_from_name, a donor-form callee, through gx_call_cg ---- *)
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (@cfg_at fx sg (transportb_sigma TB_diginet_personality_from_name) rg mm mdx) Q) end.
eapply SRr_bind.
{ apply (gx_call_cg segs B MT TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mC md1
    (k + 0) _ rC PFROM_STK PFROM_EV 0 (fun _ => False)
    (fun regs3 _ _ => YK11.getr regs3 10 = w64 (trans_pfrom_res (TSS.ann_field (skipn 24 (DSpec.fr_body b)))))
    HGX HGE HJ).
  intros memS HJS. eapply SRr_mono.
  { exact (HPF fx STK sp0 FP ly S W0 memS md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 mC md1 (k + 0) rC (F + 32 + 10)
      (TSS.ann_field (skipn 24 (DSpec.fr_body b))) HJS P_ra P_ra4 P_gp P_tp Q10 P_sp16 P_win1 P_win2 P_x P_garr
      (opf_field_nul _) P_src P_off Hrom1 P_ev). }
  intros W3 c3 _ H3. apply decode_cg_post_dcg. exact H3. }
cbv beta. intros W3 c3 _ Hpost.
destruct Hpost as (ly3 & S3 & regs3 & mem3 & md3 & e' & Hc3 & He' & HJ3 & HP3 & Hfr3 & Hperm3 & HK3 & HMO3 & HX3 & HGK3).
subst c3.
assert (He0 : e' = 0) by (unfold PFROM_EV in He'; lia). subst e'.
replace (k + 0 + 0) with (k + 0) in HJ3 by lia.
rewrite NSP in HK3.
rewrite Q1.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OPF_C1)) mm rom) mdx) Q) end.
(* the cut's facts at the return *)
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
assert (ELF3 : ly_F ly3 = ly_F lyc).
{ pose proof HJe as (_ & _ & (memS0 & HJi & _) & _). pose proof HJi as (_ & Hlyc & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJ3i & _) & _). pose proof HJ3i as (_ & Hly3 & _).
  pose proof Hly3 as (_ & _ & _ & _ & _ & E3 & _). pose proof Hlyc as (_ & _ & _ & _ & _ & Ec & _).
  rewrite E3, Ec. reflexivity. }
assert (Hbl2 : forall bm, In bm (ablocks B lyc Sc) -> In bm (ablocks B ly2 S2))
  by (intros bm Hb; eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hb]).
destruct (dkg_nf_sep_gw segs B LAWS transportb_segs_low lyc Sc ly2 S2 W2 mem2 md2 ONANN_CID pos F
  (flag_addr lyc ONANN_CID pos) HAR2 Hfrs Hbl2 HlyF EF eq_refl FFL) as (N1 & N2 & N3 & N4).
assert (K3 : acall_kept_g segs B TG.G_HARNESS_B lyc Sc W memc W3 mem3 (spZ regs - ONANN_STK) (spZ regs)
  (onann_wr Bw b)).
{ assert (Hce1 : alloc_ceiling <= spZ regs - ONANN_STK) by lia.
  assert (Hsh1 : spZ regs <= 2 ^ 64) by lia.
  apply (dk_kept_trans_nf_g segs B TG.G_HARNESS_B lyc Sc ly2 S2 W memc W2 mC W3 mem3
    (spZ regs - ONANN_STK) (spZ regs) (sp1 - PFROM_STK) sp1 (onann_wr Bw b) (fun _ => False)
    (dkg_nf ONANN_CID F (flag_addr lyc ONANN_CID pos)) Hce1 Hsh1 EFA
    ltac:(intros f Hf; rewrite Hfrs; right; exact Hf) Hbl2 N1 N3 KC1 HK3); [lia | lia | intros a []]. }
assert (HSV3 : Forall (fun o : Z * Z => rdword (aview segs (w_H W3) mem3) (spZ regs - fst o) =
    Some (bv_unsigned (YK11.getr regs (Z_to_bv 5 (snd o))))) ONANN_SAVED).
{ apply Forall_forall. intros o Hin. cbv beta.
  pose proof (proj1 (Forall_forall _ _) HSV1 o Hin) as Hv. cbv beta in Hv.
  assert (Ho : 8 <= fst o <= 104).
  { unfold ONANN_SAVED in Hin. cbn [In] in Hin.
    repeat (destruct Hin as [Hin | Hin]; [subst o; cbn [fst]; lia |]). destruct Hin. }
  rewrite <- Hv. apply YCbq.rdword_ext. intros i Hi. destruct HK3 as (L1 & _). apply L1; lia. }
assert (HFL3 : rdword (aview segs (w_H W3) mem3) (F + ONANN_FBYTES - 8) = Some (flag_addr lyc ONANN_CID pos)).
{ rewrite <- HFL1. apply YCbq.rdword_ext. intros i Hi. destruct HK3 as (_ & _ & _ & L4 & _).
  unfold ONANN_FBYTES. apply (L4 ONANN_CID pos (F + 512 - 8 + i) Hin2); [|intros []].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 512. lia. }
assert (CUR3 : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3 mem3 md3 0).
{ refine (conj HJ3 (conj He (conj (eq_trans Hfr3 Hfrs) (conj (Permutation_trans Hperm3 Hperm)
    (conj ELF3 (conj (mo_le_trans MT MTL Sc S2 S3 0 0 HMO HMO3) (conj K3 (conj HSV3 HFL3)))))))). }
assert (Htw3 : tw_at TMAP_B (aview segs (w_H W3) mem3) Bw).
{ apply (tw_kept_GB (aview segs (w_H W2) mC)); [exact Htw1|]. intros b0 n i Hbn Hi.
  exact (gx_kept_rows segs _ W2 mC W3 mem3 HGK3 b0 n i Hbn Hi). }
assert (HA3 : onann_a_ok W3 mem3 F buf b).
{ apply (opf_a_ok_keep W2 W3 mC mem3 F buf b HA1).
  - intros a Ha. destruct HK3 as (_ & _ & _ & L4 & _). apply (L4 ONANN_CID pos a Hin2); [|intros []].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF2. change (fs_frame_bytes ONANN_CID) with 512. lia.
  - intros i Hi. destruct HK3 as (_ & _ & _ & L4 & _). apply (L4 ONANN_CID pos _ Hin2); [|intros []].
    right. unfold in_zr. cbn [fst snd]. rewrite EF2. unfold shadow_addr.
    change (fs_frame_bytes ONANN_CID / 8) with 64. lia. }
assert (Y2 : YK11.getr regs3 2 = w64 sp1) by exact (eq_trans (HP3 2 ltac:(hnf; lia)) Q2).
assert (Y3 : YK11.getr regs3 3 = YK11.getr regs 3) by exact (eq_trans (HP3 3 ltac:(hnf; lia)) Q3).
assert (Y4 : YK11.getr regs3 4 = YK11.getr regs 4) by exact (eq_trans (HP3 4 ltac:(hnf; lia)) Q4).
assert (Y8 : YK11.getr regs3 8 = w64 (spZ regs)) by exact (eq_trans (HP3 8 ltac:(hnf; lia)) Q8).
assert (Y9 : YK11.getr regs3 9 = w64 sp1) by exact (eq_trans (HP3 9 ltac:(hnf; lia)) Q9).
assert (Y18 : YK11.getr regs3 18 = w64 (SHADOW_OFF + F / 8)) by exact (eq_trans (HP3 18 ltac:(hnf; lia)) Q18).
assert (Y19 : YK11.getr regs3 19 = w64 F) by exact (eq_trans (HP3 19 ltac:(hnf; lia)) Q19).
assert (Y25 : YK11.getr regs3 25 = w64 F) by exact (eq_trans (HP3 25 ltac:(hnf; lia)) Q25).
assert (Y20 : YK11.getr regs3 20 = w64 ONANN_S) by exact (eq_trans (HP3 20 ltac:(hnf; lia)) Q20).
assert (Y24 : YK11.getr regs3 24 = w64 SHADOW_OFF) by exact (eq_trans (HP3 24 ltac:(hnf; lia)) Q24).
assert (Y22 : YK11.getr regs3 22 = w64 fp) by exact (eq_trans (HP3 22 ltac:(hnf; lia)) Q22).
assert (Y23 : YK11.getr regs3 23 = w64 now) by exact (eq_trans (HP3 23 ltac:(hnf; lia)) Q23).
assert (Y26 : YK11.getr regs3 26 = w64 (F + 32)) by exact (eq_trans (HP3 26 ltac:(hnf; lia)) Q26).
assert (Y10 : YK11.getr regs3 10 = w64 (onann_pv timg_B b)) by (rewrite HX3; f_equal; apply onann_pv_res).
clear HS SHOK HEI HJ.
(* ---- run 1, +0x1e8 .. +0x1ec: `mv a6, a0`, `beq a0, zero` ---- *)
pose proof (opf_entry0 (fx := fx) W3 regs3 mem3 OPF_C1) as HS.
assert (SHOK : sh_ok segs OPF_BX [] (opf_E regs3) (mrestrict (w_H W3) mem3)) by constructor.
assert (HEI : img_env VAL A_LIM (opf_E regs3)) by (unfold opf_E; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_E regs3) n = YK11.getr regs3 r)
  by (intros n r Hn; exact (opf_ew regs3 n r Hn)).
assert (U10 : bv_unsigned (ew (opf_E regs3) 10) = onann_pv timg_B b)
  by (rewrite (EE3 10%nat 10%bv eq_refl), Y10; apply unsigned_lit_small; exact Hpvr).
pose proof HJ3 as HJ.
paj_run_tok RUN HS HJ SHOK OPF_B0.
{ opf_awr_rs. apply awr_ok_x_nil. }
opf_name_md mdA.
opf_lo HS (opf_E regs3) EAlo msA.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msA) a = aview segs (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx EAlo. }
assert (GAa : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
opf_setE HS EA.
assert (U10A : bv_unsigned (ew EA 10) = onann_pv timg_B b) by (try rewrite (EAlo 10%nat ltac:(lia)); exact U10).
psrr_branch_tok RUN BR HS SHOK OPF_B0.
- (* p = 0: the model stores nothing; to the join +0x210 *)
  cbn [branch_taken sv_denot] in Hc. rewrite U10A, Z.add_0_r, (opf_eqb_z (onann_pv timg_B b) 0) in Hc by lia.
  apply Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK OPF_B0 OPF_J.
  { opf_awr_rs. apply awr_ok_x_nil. }
  opf_name_md mdJ.
  opf_lo HS EA EJlo msJ.
  opf_kreg HS EAlo EJlo EE3 (2%bv : bv 5) 2%nat Y2 Z2. opf_kreg HS EAlo EJlo EE3 (3%bv : bv 5) 3%nat Y3 Z3.
  opf_kreg HS EAlo EJlo EE3 (4%bv : bv 5) 4%nat Y4 Z4. opf_kreg HS EAlo EJlo EE3 (8%bv : bv 5) 8%nat Y8 Z8.
  opf_kreg HS EAlo EJlo EE3 (9%bv : bv 5) 9%nat Y9 Z9. opf_kreg HS EAlo EJlo EE3 (18%bv : bv 5) 18%nat Y18 Z18.
  opf_kreg HS EAlo EJlo EE3 (19%bv : bv 5) 19%nat Y19 Z19. opf_kreg HS EAlo EJlo EE3 (25%bv : bv 5) 25%nat Y25 Z25.
  opf_kreg HS EAlo EJlo EE3 (20%bv : bv 5) 20%nat Y20 Z20. opf_kreg HS EAlo EJlo EE3 (24%bv : bv 5) 24%nat Y24 Z24.
  opf_kreg HS EAlo EJlo EE3 (22%bv : bv 5) 22%nat Y22 Z22. opf_kreg HS EAlo EJlo EE3 (23%bv : bv 5) 23%nat Y23 Z23.
  opf_kreg HS EAlo EJlo EE3 (26%bv : bv 5) 26%nat Y26 Z26.
  opf_kreg_of HS EAlo EJlo EE3 (16%bv : bv 5) 10%nat (10%bv : bv 5) Y10 Z16.
  assert (KJ : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msJ) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx EJlo. }
  assert (GJ : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msJ) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  assert (CURJ : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3
    (ms_mem msJ) mdJ 0)
    by exact (opf_cur_step LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
      Bw' pos sp1 F ly3 S3 W3 mem3 (ms_mem msJ) md3 mdJ 0 (fun _ => False) HFIX CUR3 HJ ltac:(intros a [])
      ltac:(intros a Ha _; exact (KJ a Ha)) GJ).
  assert (TWJ : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msJ)) (onann_w1 timg_B Bw b)).
  { rewrite (opf_w1_none Bw b Hc). apply (tw_kept_GB (aview segs (w_H W3) mem3)); [exact Htw3|].
    intros b0 n i Hbn Hi.
    assert (Hg : inG TG.G_HARNESS_B (b0 + i))
      by (unfold inG; apply Exists_exists; exists (b0, n); split; [exact Hbn | unfold in_zr; cbn [fst snd]; lia]).
    pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B _ HGX Hg) as Hl. unfold kLowMemEnd in Hl.
    apply KJ. lia. }
  assert (HAJ : onann_a_ok W3 (ms_mem msJ) F buf b).
  { apply (opf_a_ok_keep W3 W3 mem3 (ms_mem msJ) F buf b HA3).
    - intros a Ha. apply KJ. lia.
    - intros i Hi. apply KJ. unfold SHADOW_OFF. lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OPF_J)) mm rom) mdx) Q) end.
  exact (opf_join HLAWS HCALL FM DN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
    Bw' pos sp1 F ly3 S3 W3 (ms_mem msJ) mdJ (ms_regs msJ) HFIX CURJ TWJ Hig HAJ
    (conj (conj Z2 (conj Z3 (conj Z4 (conj Z8 (conj Z9 (conj Z18 (conj Z19 Z25))))))) (conj Z20 Z24))
    Z22 Z23 Z26 Z16).
- (* p <> 0: to +0x1f0, then s & 7 (folded), the check of s + 128 and the store of p there, to +0x210 *)
  cbn [branch_taken sv_denot] in Hc. rewrite U10A, Z.add_0_r, (opf_eqb_z (onann_pv timg_B b) 0) in Hc by lia.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK OPF_B0 OPF_C2.
  { opf_awr_rs. apply awr_ok_x_nil. }
  opf_name_md mdB.
  opf_lo HS EA EBlo msB.
  opf_kreg HS EAlo EBlo EE3 (2%bv : bv 5) 2%nat Y2 W2'. opf_kreg HS EAlo EBlo EE3 (3%bv : bv 5) 3%nat Y3 W3'.
  opf_kreg HS EAlo EBlo EE3 (4%bv : bv 5) 4%nat Y4 W4'. opf_kreg HS EAlo EBlo EE3 (8%bv : bv 5) 8%nat Y8 W8'.
  opf_kreg HS EAlo EBlo EE3 (9%bv : bv 5) 9%nat Y9 W9'. opf_kreg HS EAlo EBlo EE3 (18%bv : bv 5) 18%nat Y18 W18'.
  opf_kreg HS EAlo EBlo EE3 (19%bv : bv 5) 19%nat Y19 W19'. opf_kreg HS EAlo EBlo EE3 (25%bv : bv 5) 25%nat Y25 W25'.
  opf_kreg HS EAlo EBlo EE3 (20%bv : bv 5) 20%nat Y20 W20'. opf_kreg HS EAlo EBlo EE3 (24%bv : bv 5) 24%nat Y24 W24'.
  opf_kreg HS EAlo EBlo EE3 (22%bv : bv 5) 22%nat Y22 W22'. opf_kreg HS EAlo EBlo EE3 (23%bv : bv 5) 23%nat Y23 W23'.
  opf_kreg HS EAlo EBlo EE3 (26%bv : bv 5) 26%nat Y26 W26'.
  opf_kreg_of HS EAlo EBlo EE3 (16%bv : bv 5) 10%nat (10%bv : bv 5) Y10 W16'.
  assert (KB : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W3) (ms_mem msB) a = aview segs (w_H W3) mem3 a).
  { intros a Ha. rewrite <- (KA a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx EBlo. }
  assert (GB : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msB) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAa a Ha))).
  clear HF HFr HG.
  (* +0x1f0 taken up again with g_s's personality field as a region *)
  pmkst HS.
  clear HS SHOK.
  set (rB := ms_regs msB) in *. set (mB := ms_mem msB) in *. clearbody rB mB.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARB.
  destruct (opf_entry2 (fx := fx) B ly3 S3 W3 rB mB mdB HSC HARB W20' W24') as [HS SHOK].
  assert (HEIb : img_env VAL A_LIM (opf_E rB)) by (unfold opf_E; apply Eimg_env).
  assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (opf_E rB) n = YK11.getr rB r)
    by (intros n r Hn; exact (opf_ew rB n r Hn)).
  assert (U20b : bv_unsigned (ew (opf_E rB) 20) = ONANN_S)
    by (rewrite (EE2 20%nat 20%bv eq_refl), W20'; apply unsigned_lit_small; lia).
  assert (U16b : bv_unsigned (ew (opf_E rB) 16) = onann_pv timg_B b)
    by (rewrite (EE2 16%nat 16%bv eq_refl), W16'; apply unsigned_lit_small; exact Hpvr).
  lazymatch goal with |- SRr _ ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr segs Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OPF_C2)) mm rom) mdx) Q) end.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan OPF_J.
  { opf_awr_rs.
    apply awr_ok_x_cons_g;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U20b in Ha;
      apply opf_inG_gs; unfold TW.SZ_g_s; lia |].
    apply awr_ok_x_nil. }
  opf_name_md mdJ.
  opf_lo HS (opf_E rB) EJlo msJ.
  opf_kreg HS EJlo EJlo EE2 (2%bv : bv 5) 2%nat W2' Z2. opf_kreg HS EJlo EJlo EE2 (3%bv : bv 5) 3%nat W3' Z3.
  opf_kreg HS EJlo EJlo EE2 (4%bv : bv 5) 4%nat W4' Z4. opf_kreg HS EJlo EJlo EE2 (8%bv : bv 5) 8%nat W8' Z8.
  opf_kreg HS EJlo EJlo EE2 (9%bv : bv 5) 9%nat W9' Z9. opf_kreg HS EJlo EJlo EE2 (18%bv : bv 5) 18%nat W18' Z18.
  opf_kreg HS EJlo EJlo EE2 (19%bv : bv 5) 19%nat W19' Z19. opf_kreg HS EJlo EJlo EE2 (25%bv : bv 5) 25%nat W25' Z25.
  opf_kreg HS EJlo EJlo EE2 (20%bv : bv 5) 20%nat W20' Z20. opf_kreg HS EJlo EJlo EE2 (24%bv : bv 5) 24%nat W24' Z24.
  opf_kreg HS EJlo EJlo EE2 (22%bv : bv 5) 22%nat W22' Z22. opf_kreg HS EJlo EJlo EE2 (23%bv : bv 5) 23%nat W23' Z23.
  opf_kreg HS EJlo EJlo EE2 (26%bv : bv 5) 26%nat W26' Z26. opf_kreg HS EJlo EJlo EE2 (16%bv : bv 5) 16%nat W16' Z16.
  (* the run wrote [s + 128, s + 136) only, with p *)
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (ONANN_S + 128 <= a < ONANN_S + 136) ->
    aview segs (w_H W3) (ms_mem msJ) a = aview segs (w_H W3) mem3 a).
  { intros a Ha Hn. rewrite <- (KB a Ha).
    apply (kept_of_frame _ _ _ _ _ (fun x => ONANN_S + 128 <= x < ONANN_S + 136) HFr); [| exact Ha | exact Hn].
    intros b0 wlo whi x Hin Hx. cbv beta. opf_win Hin Hx U20b. }
  assert (GW : forall a, apresent (w_H W3) mem3 a -> apresent (w_H W3) (ms_mem msJ) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GB a Ha))).
  opf_region HS 0%nat HRw.
  lazymatch type of HRw with region_ok _ ?Ex _ (YP09.mkRegion _ _ _ _ _ [YP09.mkChunk _ (CVal _ ?ev)]) =>
    assert (DEN : sv_denot Ex ev = Z_to_bv 64 (onann_pv timg_B b))
      by (cbn [sv_denot]; try rewrite (EJlo 16%nat ltac:(lia)); rewrite U16b, Z.add_0_r; reflexivity);
    assert (U20f : bv_unsigned (ew Ex 20) = ONANN_S) by (try rewrite (EJlo 20%nat ltac:(lia)); exact U20b);
    pose proof (can_field_of_region Ex _ 20 ONANN_S _ 128 136 128 136 128 8%N ev (onann_pv timg_B b) HRw U20f
      ltac:(opf_in) DEN ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hpvr) ltac:(cbn; lia)) as VB
  end.
  change (N.to_nat 8) with 8%nat in VB.
  clear HRw DEN U20f.
  assert (TWJ : tw_at TMAP_B (aview segs (w_H W3) (ms_mem msJ)) (onann_w1 timg_B Bw b)).
  { rewrite (opf_w1_some Bw b Hc).
    apply (tw_write TMAP_B (aview segs (w_H W3) mem3) (aview segs (w_H W3) (ms_mem msJ)) Bw TW.OFF_g_s TB_g_s
      TW.SZ_g_s 128 8 _ TMAP_B_ok Htw3 TMAP_B_g_s); [lia | unfold TW.SZ_g_s; lia | |].
    - intros j Hj. exact (opf_aview_of_val _ _ _ 8 _ VB j Hj).
    - intros x Hx Hn.
      assert (Hg : inG TG.G_HARNESS_B x).
      { destruct Hx as (o & b0 & n & Hin & Hb). pose proof (TMAP_B_in_G o b0 n Hin) as HG0.
        unfold inG. apply Exists_exists. exists (b0, n). split; [exact HG0 | unfold in_zr; cbn [fst snd]; lia]. }
      pose proof (inG_low segs B transportb_segs_low TG.G_HARNESS_B x HGX Hg) as Hl. unfold kLowMemEnd in Hl.
      apply KW; [lia|]. intros X. apply Hn. unfold ONANN_S in X. lia. }
  assert (CURJ : onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly3 S3 W3
    (ms_mem msJ) mdJ 0).
  { apply (opf_cur_step LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
      pos sp1 F ly3 S3 W3 mem3 (ms_mem msJ) md3 mdJ 0 (fun x => ONANN_S + 128 <= x < ONANN_S + 136) HFIX CUR3 HJ);
      [| exact KW | exact GW].
    intros a Ha. cbv beta in Ha. right. split; [apply opf_inG_gs; unfold TW.SZ_g_s; lia | exact (opf_wr_pers Bw b a Ha)]. }
  assert (HAJ : onann_a_ok W3 (ms_mem msJ) F buf b).
  { apply (opf_a_ok_keep W3 W3 mem3 (ms_mem msJ) F buf b HA3).
    - intros a Ha. apply KW; [lia|]. intros X. exact (HFG a ltac:(lia) (opf_inG_gs a ltac:(unfold TW.SZ_g_s; lia))).
    - intros i Hi. apply KW; unfold SHADOW_OFF, ONANN_S, TB_g_s; lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + OPF_J)) mm rom) mdx) Q) end.
  exact (opf_join HLAWS HCALL FM DN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw
    Bw' pos sp1 F ly3 S3 W3 (ms_mem msJ) mdJ (ms_regs msJ) HFIX CURJ TWJ Hig HAJ
    (conj (conj Z2 (conj Z3 (conj Z4 (conj Z8 (conj Z9 (conj Z18 (conj Z19 Z25))))))) (conj Z20 Z24))
    Z22 Z23 Z26 Z16).
Qed.
End main.

(* The personality piece of the walk of on_announce (OnannCutB.v onann_pf_stmt), at every machine, run ceiling,
   record and meter. *)
Lemma onann_pf_piece : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @onann_pf_stmt fx rc B MT.
Proof. intros fx rc B MT. exact (@opf_holds fx rc B MT). Qed.
