(* Segment X01 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x13db4, 0x13dc8], P4n: memchr over model_name.
   K13db4 -> K13dcc (has_model_name = 1, after memchr), K13dd0 (has_model_name = 0).
   libreac v1.9.0 (table 5a S_X01: IDENTICAL-RENUMBER, OLD 0x13d80 .. 0x13d94): pcs, id 138 -> 154 (has_model_name
   158 -> 174, model_name 141 -> 157), frame 1920 -> 1936; cuts K13d80 -> K13db4, K13d98 -> K13dcc, K13d9c ->
   K13dd0 (SlotInv.v's renames), so seg_X01 is stated on the renamed cuts. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Exec Step Tac Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcIdentModel SlotModel SlotInv memchr_c memchr_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b8 Tac_b8m.
Import ListNotations.
Open Scope Z_scope.

Lemma x01_byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (b8_bz_range b) as H. exact H. Qed.

Lemma x01_eqb_zxb : forall (b : byte) c, 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (x01_byte_range b). unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

Lemma x01_find0 : forall l, (first_zero l < length l)%nat -> find_byte 0 l = Some (first_zero l).
Proof.
  induction l as [|b l IH]; intros H; cbn in *; [lia|].
  unfold bz in *. destruct (bv_unsigned b =? 0); [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma x01_fz_le : forall l k, (k < length l)%nat -> bz (nth k l (zb 0)) = 0 -> (first_zero l <= k)%nat.
Proof.
  induction l as [|b l IH]; intros k Hk H; cbn in *; [lia|].
  destruct (Z.eqb_spec (bz b) 0) as [E|E]; [lia|].
  destruct k as [|k]; [contradiction|]. specialize (IH k ltac:(lia) H). lia.
Qed.

Lemma x01_rp_len : forall idb len g, length idb = 38%nat -> length (rp_id idb len g) = 38%nat.
Proof. intros idb len g H. unfold rp_id. destruct (RcReply.ir len g); [apply ING_length; exact H | exact H]. Qed.

Lemma x01_fg_len : forall idb len st g, length idb = 38%nat -> length (fg_id idb len st g) = 38%nat.
Proof. intros idb len st g H. unfold fg_id. destruct (fg_rf len st g =? 1); [apply ING_length; exact H | exact H]. Qed.

Lemma x01_turn_id : forall s len g, fs_id (turn s len g) = fg_id (rp_id (fs_id s) len g) len (fs_fg s) g.
Proof. intros s len g. unfold turn. destruct (f_opens len g); reflexivity. Qed.

Lemma x01_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. unfold t_ID. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S, x01_turn_id. apply x01_fg_len, x01_rp_len, IH.
Qed.

Lemma x01_mn_length : forall idb, length idb = 38%nat -> length (model_name idb) = 17%nat.
Proof. intros idb H. unfold model_name, get. rewrite length_firstn, length_skipn, H. reflexivity. Qed.

Lemma x01_mn_nth : forall idb k, (k < 17)%nat -> nth k (model_name idb) (zb 0) = nthb idb (3 + k).
Proof.
  intros idb k Hk. unfold model_name, get, nthb, NAME_CAP, OFF_NAME. rewrite nth_firstn.
  destruct (Nat.ltb_spec k 17); [|lia]. rewrite nth_skipn. reflexivity.
Qed.

Lemma x01_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|x bs IH]; intros k d H; cbn in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma kX01z : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (sp0 : Z) (hb : byte),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 174)) 1 = Some [hb] -> bv_unsigned hb = 0 ->
  Exec.evt rsegs
    (fun ms' => exists y, ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22
                                  x23 x24 x25 x26 x27 x28 x29 x30 x31) F (Z_to_bv 64 0x13dd0) fc None m ro)
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13db4) fc None m ro).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
    x29 x30 x31 F fc m ro sp0 hb E2 H0 H1 R Hb.
  subst x2. step. step.
  if_cases HC; [apply evt_done; eexists; reflexivity|].
  exfalso. rewrite ?x01_eqb_zxb in HC by lia. rewrite Hb in HC. discriminate HC.
Qed.

Lemma kX01c : memchr_ro_contract -> forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
    x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (sp0 : Z) (hb : byte) (buf : list byte),
  x2 = Z_to_bv 64 sp0 -> 0 <= sp0 -> sp0 + 1936 < 2 ^ 64 ->
  ov_read_bytes rsegs m (wa (sp0 + 174)) 1 = Some [hb] -> bv_unsigned hb <> 0 ->
  bytes_at rsegs m (sp0 + 157) buf -> length buf = 35%nat -> MemNorm.ro_agree rsegs m ->
  Exec.evt rsegs
    (fun ms' => exists R pc' m', ms' = MS R F pc' fc None m' (seg_rom rsegs) /\
       (pc' = Z_to_bv 64 0x13dcc /\ getr R 10 = Z_to_bv 64 (memchr_res (sp0 + 157) 0 17 buf) /\
        getr R 2 = Z_to_bv 64 sp0 /\ getr R 3 = x3 /\ getr R 4 = x4 /\ getr R 8 = x8 /\ getr R 9 = x9 /\
        getr R 18 = x18 /\ getr R 19 = x19 /\ getr R 20 = x20 /\ getr R 21 = x21 /\ getr R 22 = x22 /\
        getr R 23 = x23 /\ getr R 24 = x24 /\ getr R 25 = x25 /\ getr R 26 = x26 /\ getr R 27 = x27 /\
        munch [] m m' /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31) F (Z_to_bv 64 0x13db4) fc None m (seg_rom rsegs)).
Proof.
  intros MCHR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 F fc m sp0 hb buf E2 H0 H1 R Hb HB Hl HRO.
  subst x2. step. step.
  if_cases HC; [exfalso; rewrite ?x01_eqb_zxb in HC by lia; apply Z.eqb_eq in HC; exact (Hb HC)|].
  step. step. step. step.
  eapply evt_cut.
  { eapply MCHR with (buf := buf).
    - rewrite unsigned_lit by lia. exact HB.
    - unfold memchr_ok. destruct (find_byte _ _); [left|]; rewrite Hl, (unsigned_lit 17) by lia; lia.
    - exact HRO. }
  intros ms' (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MU & WM & RO & BB).
  subst ms'. apply evt_done. eexists _, _, _. split; [reflexivity|].
  split; [apply b8_ret_pc; lia|].
  split; [rewrite !unsigned_lit by lia; reflexivity|].
  repeat (split; [reflexivity|]). split; [exact MU|]. split; [exact WM | exact RO].
Qed.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCHR : memchr_ro_contract.

Lemma seg_X01 : Hcut B APIf ra (Inv_K13dcc B APIf ra empty) -> Hcut B APIf ra (Inv_K13dd0 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13db4 B APIf ra empty).
Proof.
  intros H98 H9c g c HC.
  eapply (b8_cut_open B APIf ra empty); [exact HC|]. intros L A regs mem md HF HP (HID & Hok).
  pose proof (b8_FR_sp B APIf ra empty g _ L A regs mem md HF) as (Hsp & H16 & HSK & HS47).
  pose proof alloc_ceiling_value as HAC.
  set (idb := t_ID (g_in g) (fJ (g_in g))) in *.
  assert (Hlen : length idb = 38%nat) by apply x01_ID_length.
  assert (R174 : ov_read_bytes rsegs mem (wa (g_S g - 1936 + 174)) 1 = Some [nthb idb 20]).
  { replace (g_S g - 1936 + 174) with (spk g 154 + Z.of_nat 20) by (unfold spk, fsp, SLOT_FRAME; lia).
    unfold IDB in HID. rewrite (bytes_at_ov_read _ _ _ _ 20 1 HID) by lia.
    unfold nthb. rewrite (x01_firstn1 idb 20 (zb 0)) by lia. reflexivity. }
  destruct (Z.eq_dec (bz (nthb idb 20)) 0) as [Z0|NZ].
  - eapply (b8_run_ex B APIf ra empty FF); [exact HF | unfold rmk; eapply kX01z with (sp0 := g_S g - 1936);
      [exact Hsp | lia | lia | exact R174 | exact Z0] |].
    intros y regs' HG. apply H9c. apply (b8_cut_close B APIf ra empty _ _ _ _ L A); [| exact HP | exact I].
    apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF); b8rg HG.
  - pose proof Hok as (Hfw & Hnm & _ & H19 & _).
    assert (Hhas : has_model_name idb = 1) by (unfold has_model_name, OFF_HAS_NAME in *; lia).
    assert (HB157 : bytes_at rsegs mem (g_S g - 1936 + 157) (skipn 3 idb)).
    { unfold IDB in HID. rewrite <- (firstn_skipn 3 idb) in HID. apply bytes_at_app in HID as [_ HID].
      rewrite length_firstn in HID. replace (g_S g - 1936 + 157) with (spk g 154 + Z.of_nat (Nat.min 3 (length idb)))
        by (rewrite Hlen; unfold spk, fsp, SLOT_FRAME; cbn; lia). exact HID. }
    pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HMR & _).
    unfold MI in HMI. rewrite (b8_segs B APIf ra empty FF) in HMI.
    destruct (b8_md B APIf L A mem md HMR) as [Hh Hz].
    eapply (kb_run B regs (Z_to_bv 64 0x13db4) mem md _ (Post B APIf ra g) Hh Hz).
    { rewrite (b8_segs B APIf ra empty FF). unfold rmk.
      eapply (kX01c MCHR) with (sp0 := g_S g - 1936) (hb := nthb idb 20) (buf := skipn 3 idb);
        [exact Hsp | lia | lia | exact R174 | exact NZ | exact HB157 | rewrite length_skipn, Hlen; reflexivity | exact HMI]. }
    intros R pc' m' regs' (Epc & H10 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 &
      E27 & MU & WM & RO) HG.
    subst pc'. apply H98.
    apply (b8_cut_close B APIf ra empty _ _ _ _ L A).
    + apply (b8_FR_frame B APIf ra empty FF g _ L A regs' mem md m').
      * apply (b8_FR_regs B APIf ra empty _ _ _ _ _ _ _ _ HF).
        -- rewrite HG, E2. symmetry. exact Hsp.
        -- rewrite HG, E3. reflexivity.
        -- rewrite HG, E4. reflexivity.
      * exact HP.
      * intros x _. apply MU. exact I.
      * exact WM.
    + exact HP.
    + split; [|split].
      * split; [|exact Hok]. unfold IDB. apply (b8_ba_munch rsegs [] mem m' _ _ HID MU). intros; exact I.
      * exact Hhas.
      * unfold rg. rewrite HG, H10. f_equal.
        assert (Hfz : (first_zero (model_name idb) <= 16)%nat).
        { apply x01_fz_le; [rewrite x01_mn_length by exact Hlen; lia|]. rewrite x01_mn_nth by lia. exact H19. }
        unfold memchr_res. change (firstn (Z.to_nat 17) (skipn 3 idb)) with (model_name idb).
        rewrite x01_find0 by (rewrite x01_mn_length by exact Hlen; lia).
        cbv beta iota. unfold spk, fsp, SLOT_FRAME. change (t_ID (g_in g) (fJ (g_in g))) with idb. lia.
Qed.

End X01.
