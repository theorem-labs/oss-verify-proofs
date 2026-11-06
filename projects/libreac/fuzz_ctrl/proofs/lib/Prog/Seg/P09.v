(* Segment P09 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13660, 0x13690], K13660 -> K13694 (j = 0, left > 0)
   or K13db4 (left = 0) (#38, #39: the bytes '?' 0 at QMARK; first_frag F1: FS_0 = (have 0, nb 0, body []); AF3: M7
   at sp+8). *)
(* libreac v1.9.0 (internal path, sha256 9e0909d16182...), on the v1.9 cut bundle
   lib/Prog/SlotInv.v. rule 24: no function proved. S_P09 is CHANGED (plain segment table
   v190-segment-table-plain.md (a working note, not in this delivery), fuzz_ctrl.c v1.9.0:714): pc +0x10; the left count
   n - c is in s11 (0x13674 `beqz s11,0x13db4`; v1.8 s7); v1.8's four zero stores [sp+40] / [sp+16] / [sp+24] /
   [sp+32] of `first` are replaced by 0x1367c `li s3,0` (nb, v1.9's `first` byte 4) and 0x13680 `sd zero,16(sp)`
   (have), so the turn-0 state is FSb's v1.9 form: have [sp+16] = 0, nb s3 = 0, body [] at sp+40; the write set is
   [sp+8, sp+24) (was [sp+8, sp+48)); M7 at sp+8 and s10 = 0 as before; frame 1920 -> 1936. Exits K13694 / K13db4
   (renamed from K1368c / K13d80). Statements: seg_P09 names K13694 / K13db4 / K13660 for K1368c / K13d80 / K13650
   (SlotInv.v's renames); p09z_evt / p09_evt take s11 for s7 and the 0x13660 .. 0x13694 walk, p09_evt's post has
   s3 = 0 and the two q64 facts at sp+8 / sp+16 (was five, sp+8 .. sp+40), and drops the cells at sp+24 .. sp+40. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv
  reac_ctrl_kind_name_c reac_ctrl_kind_name.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcKind RcIdentModel RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b1 Tac_b4.
Import ListNotations.
Open Scope Z_scope.

(* #38, #39: kind_name(14) = "?", so the bytes at QMARK are '?' 0. *)
Lemma p09_qm : forall m, mem_inv rsegs m ->
  ov_read_bytes rsegs m (wa QMARK) 1 = Some [Z_to_bv 8 63] /\
  ov_read_bytes rsegs m (wa (QMARK + 1)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m MI. destruct (reac_ctrl_kind_name_in_image m MI) as (_ & HS).
  pose proof (HS 14 ltac:(lia)) as H.
  change (kind_name_addr 14) with QMARK in H.
  change (RcKind.cstr_bytes (RcKind.kind_name 14)) with [Z_to_bv 8 63; Z_to_bv 8 0] in H.
  split.
  - replace (wa QMARK) with (wa (QMARK + Z.of_nat 0)) by (f_equal; lia).
    rewrite (bytes_at_ov_read rsegs m QMARK _ 0 1 H) by (cbn; lia). reflexivity.
  - replace (wa (QMARK + 1)) with (wa (QMARK + Z.of_nat 1)) by (f_equal; lia).
    rewrite (bytes_at_ov_read rsegs m QMARK _ 1 1 H) by (cbn; lia). reflexivity.
Qed.

(* left = 0: J = 0 (fJ_from stops at once). *)
Lemma p09_fJ0 : forall inp, nlen inp - c0 inp = 0 -> fJ inp = 0%nat.
Proof.
  intros inp H. unfold fJ.
  change (fJ_from inp 0 256) with (if 0 <? f_left inp (fc inp 0) then fJ_from inp 1 255 else 0%nat).
  change (fc inp 0) with (c0 inp). unfold f_left. rewrite H. reflexivity.
Qed.

(* The struct invariants hold for the zero state: id_ok ID0, frag_ok z72, FI z72 fs0. *)
Lemma p09_id_ok : RcIdentModel.id_ok RcIdentModel.ID0.
Proof.
  assert (E : forall j, RcIdentModel.bz (RcIdentModel.nthb RcIdentModel.ID0 j) = 0).
  { intros j. unfold RcIdentModel.nthb, RcIdentModel.ID0. rewrite nth_repeat. reflexivity. }
  unfold RcIdentModel.id_ok, RcIdentModel.has_fw, RcIdentModel.has_model_name, RcIdentModel.has_reac_version,
    RcIdentModel.fw_milli, RcIdentModel.major, RcIdentModel.minor, RcIdentModel.patch, RcIdentModel.be16.
  repeat split; intros; rewrite ?E in *; lia.
Qed.

Lemma p09_bat6 : RcFrag.bat z72 6 = 0.
Proof. reflexivity. Qed.

Lemma p09_frag_ok : frag_ok z72.
Proof. unfold frag_ok. rewrite p09_bat6. split; [left; reflexivity | intros H; discriminate H]. Qed.

Lemma p09_FI : FI z72 fs0.
Proof. unfold FI. rewrite p09_bat6. split; intros H; discriminate H. Qed.

(* left = 0: '?' 0 read, beqz s11 taken to 0x13db4. *)
Lemma p09z_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    a0 = Z_to_bv 64 QMARK -> s11 = Z_to_bv 64 0 -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists a0' a1' a2' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                       t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13db4) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13660) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m -> -> MI.
  destruct (p09_qm m MI) as (HR1 & HR2). clear MI.
  step. step. step. if_false. step. step. if_false. step. if_true.
  apply evt_done. eexists _, _, _. reflexivity.
Qed.

(* left > 0: '?' 0 read, beqz s11 not taken, s10 = 0, nb s3 = 0, have [sp+16] = 0, M7 at sp+8; to 0x13694. *)
Lemma p09_evt :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv v : Z) (j8 j16 : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 QMARK -> s11 = Z_to_bv 64 v -> 0 < v < 2 ^ 64 ->
    0 <= spv -> spv + 1936 < 2 ^ 64 -> mem_inv rsegs m ->
    Step.rw_cells rsegs m (spv + 8) [Cells.CB 8 j8] ->
    Step.rw_cells rsegs m (spv + 16) [Cells.CB 8 j16] ->
    evt rsegs
      (fun ms' => exists (a0' a1' a2' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9
                       (Z_to_bv 64 0) s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x13694) fc None m' (seg_rom rsegs) /\
         munch [(spv + 8, spv + 24)] m m' /\ wmono rsegs m m' /\
         q64 m' (spv + 8) 0xfffffff9fffffff9 /\ q64 m' (spv + 16) 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13660) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv v j8 j16 Esp E0 E11 Hv Hs0 Hs1 MI C8 C16.
  subst sp a0 s11.
  destruct (p09_qm m MI) as (HR1 & HR2). clear MI.
  pose proof (munch_refl [(spv + 8, spv + 24)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. if_false. step. step. if_false. step. if_false_by (b1_beq0 v Hv).
  step. step. step. step. step. step. step.
  apply evt_done. eexists _, _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
  pose proof (sl_cells_bytes _ _ _ C8) as B8. pose proof (sl_cells_bytes _ _ _ C16) as B16.
  cbn [Cells.cells_bytes Cells.cbytes] in B8, B16.
  rewrite app_nil_r in B8, B16.
  unfold q64.
  split; [exact B8 | exact B16].
Qed.

Section P09.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.

Lemma seg_P09 : Hat B APIf ra (Inv_K13694_at B APIf ra empty) 0%nat -> Hcut B APIf ra (Inv_K13db4 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13660 B APIf ra empty).
Proof.
  intros H1 H0 g c (L & A & regs & mem & md & -> & HFR & HP & HP0 & HZ & H10).
  pose proof HP0 as (((Hc & H21 & H27) & HOUR) & HID & HFG).
  pose proof (sl_fr_bnd B APIf ra empty FF g _ L A regs mem md HFR) as (Hsp & _ & HS1 & HS2 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF g _ L A regs mem md HFR) as ST.
  pose proof HFR as ((Hn & _) & _).
  unfold SLOT_K, SLOT_STACK, fsp, SLOT_FRAME, SL_TOP in *.
  unfold rg in H10, H21, H27.
  destruct (Z.eq_dec (g_n g - c0 (g_in g)) 0) as [Hz|Hnz].
  - (* left = 0: to 0x13db4 *)
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ []); [exact HFR | exact HP | | | |].
    + intros x Hx O. exfalso. apply O. exact I.
    + rewrite sl_mkR_of. apply p09z_evt.
      * exact H10.
      * rewrite Hz in H27. exact H27.
      * exact (mem_inv_normalize rsegs mem).
    + intros ms (? & ? & ? & ->).
      do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (? & ? & ? & HE). injection HE; intros; subst.
      apply H0. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold IDj, IDb. rewrite (p09_fJ0 (g_in g) Hz).
      change (t_ID (g_in g) 0) with RcIdentModel.ID0.
      split; [exact (bytes_at_transport rsegs [] mem m' _ _ HID MU' I) | exact p09_id_ok].
  - (* left > 0: to 0x13694, j = 0 *)
    assert (Hv : 0 < g_n g - c0 (g_in g) < 2 ^ 64) by lia.
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 8) 8 ST ltac:(lia) ltac:(lia)) as (j8 & C8).
    destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 16) 8 ST ltac:(lia) ltac:(lia)) as (j16 & C16).
    set (W := [(g_S g - 1936 + 8, g_S g - 1936 + 24)]).
    eapply (b4_mid B APIf ra empty FF g [] L A regs mem md _ W); [exact HFR | exact HP | | | |].
    + intros x Hx O. refine (b4_fp g W x _ Hx O). unfold W, SLOT_K, SLOT_STACK.
      apply Forall_cons; [cbn [fst snd]; lia | apply Forall_nil].
    + rewrite sl_mkR_of.
      apply p09_evt with (spv := g_S g - 1936) (v := g_n g - c0 (g_in g)) (j8 := j8) (j16 := j16).
      * exact Hsp.
      * exact H10.
      * exact H27.
      * exact Hv.
      * lia.
      * lia.
      * exact (mem_inv_normalize rsegs mem).
      * exact C8.
      * exact C16.
    + intros ms (? & ? & ? & m' & -> & MU & WM & _).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      destruct HQ as (? & ? & ? & m'' & HE & _ & _ & B8 & B16).
      injection HE; intros; subst.
      assert (HP0' : P0 g regs' m').
      { apply (b4_P0_keep g regs regs' mem m' W HP0 MU').
        - unfold W, spk, fsp, SLOT_FRAME. cbn [disjoint_from]. split; [lia | exact I].
        - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
        - rewrite (sl_getr_eqv _ _ _ Hx). reflexivity. }
      destruct HP0' as ((HCUR' & HOUR') & HID' & HFG').
      apply H1. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      unfold LI, IFS, IDj, FGj, FSj, IDb, FGb, FSb, M7.
      change (t_c (g_in g) 0) with (c0 (g_in g)).
      change (t_ID (g_in g) 0) with RcIdentModel.ID0.
      change (t_FG (g_in g) 0) with z72.
      change (fst_at (g_in g) 0) with fs0.
      change (fs_have fs0) with 0. change (fs_nb fs0) with 0. change (fs_body fs0) with (@nil byte).
      change (t_left (g_in g) 0) with (nlen (g_in g) - c0 (g_in g)).
      unfold spk, fsp, SLOT_FRAME.
      split; [lia|].
      split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split; [exact HCUR'|].
      split; [unfold g_n in Hnz, Hc; lia|].
      split; [exact HOUR'|].
      split; [|exact (b1_out _ _ _ _ Hrel B8)].
      split; [split; [exact HID' | exact p09_id_ok]|].
      split; [split; [exact HFG' | exact p09_frag_ok]|].
      split; [exact (b1_out _ _ _ _ Hrel B16)|].
      split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split; [apply sl_bytes_nil; lia|].
      split; [reflexivity|].
      exact p09_FI.
Qed.

End P09.
