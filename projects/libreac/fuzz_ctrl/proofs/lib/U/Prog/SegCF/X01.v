(* Segment X01 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan): [0x140f8, 0x1410c], has_model_name(ID_J) at sp+96
   and memchr(sp+79, 0, 17) (MCHR; buf = the 35 bytes sp+79 .. 113 of id at sp+76). U140f8 -> U14114 when
   has_model_name = 0; U14110 otherwise, a0 = sp+79 + first_zero(model_name(ID_J)) (id_ok: byte 19 of ID is 0, so
   the 0 is found). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF memchr_c memchr_ro_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u8m Tac_u8.
Import ListNotations.
Open Scope Z_scope.

Lemma x01_eqb_zxb : forall (b : byte) c, 0 <= c < 2 ^ 64 -> bv_eqb (zxb b) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof.
  intros b c Hc. pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb.
  change (2 ^ Z.of_N 8) with 256 in Hb.
  unfold bv_eqb, zxb. rewrite !MState.unsigned_lit by lia. reflexivity.
Qed.

Lemma x01_eqb_ub : forall (b : byte) c, 0 <= c < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 c) = (bv_unsigned b =? c).
Proof. exact x01_eqb_zxb. Qed.

Lemma x01_find0 : forall l, (RcIdentModel.first_zero l < length l)%nat ->
  find_byte 0 l = Some (RcIdentModel.first_zero l).
Proof.
  induction l as [|b l IH]; intros H; cbn in *; [lia|].
  unfold RcIdentModel.bz in *. destruct (bv_unsigned b =? 0); [reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Lemma x01_fz_le : forall l k, (k < length l)%nat ->
  RcIdentModel.bz (nth k l (RcIdentModel.zb 0)) = 0 -> (RcIdentModel.first_zero l <= k)%nat.
Proof.
  induction l as [|b l IH]; intros k Hk H; cbn in *; [lia|].
  destruct (Z.eqb_spec (RcIdentModel.bz b) 0) as [E|E]; [lia|].
  destruct k as [|k]; [contradiction|]. specialize (IH k ltac:(lia) H). lia.
Qed.

Lemma x01_mn_length : forall idb, length idb = 38%nat -> length (RcIdentModel.model_name idb) = 17%nat.
Proof.
  intros idb H. unfold RcIdentModel.model_name, RcIdentModel.get. rewrite length_firstn, length_skipn, H.
  reflexivity.
Qed.

Lemma x01_mn_nth : forall idb k, (k < 17)%nat ->
  nth k (RcIdentModel.model_name idb) (RcIdentModel.zb 0) = RcIdentModel.nthb idb (3 + k).
Proof.
  intros idb k Hk. unfold RcIdentModel.model_name, RcIdentModel.get, RcIdentModel.nthb, RcIdentModel.NAME_CAP,
    RcIdentModel.OFF_NAME. rewrite nth_firstn.
  destruct (Nat.ltb_spec k 17); [|lia]. rewrite nth_skipn. reflexivity.
Qed.

Lemma x01_firstn1 : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
Proof.
  induction bs as [|x bs IH]; intros k d H; cbn in H; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

(* has_model_name = 0: 0x140fc `beqz a0` taken to 0x14114. *)
Lemma x01_z :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (hb : byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 96)) 1 = Some [hb] -> bv_unsigned hb = 0 ->
    evt rsegs
      (fun ms' => exists y, ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 y a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                      s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x14114) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140f8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv hb -> H0 H1 R Hb.
  step. step.
  if_cases HC; [apply evt_done; eexists; reflexivity|].
  exfalso. rewrite ?x01_eqb_zxb, ?x01_eqb_ub in HC by lia. rewrite Hb in HC. discriminate HC.
Qed.

(* has_model_name <> 0: 0x140fc not taken, then memchr(sp+79, 0, 17) returns to 0x14110. *)
Lemma x01_c : memchr_ro_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv : Z) (hb : byte) (buf : list byte),
    sp = Z_to_bv 64 spv -> 0 <= spv -> spv + 1936 < 2 ^ 64 ->
    ov_read_bytes rsegs m (wa (spv + 96)) 1 = Some [hb] -> bv_unsigned hb <> 0 ->
    bytes_at rsegs m (spv + 79) buf -> length buf = 35%nat -> MemNorm.ro_agree rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x14110) sp gp tp t0' t1' t2' s0 s1
                       (Z_to_bv 64 (memchr_res (spv + 79) 0 17 buf))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x14110) fc None m' (seg_rom rsegs) /\
         munch [] m m' /\ wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x140f8) fc None m (seg_rom rsegs)).
Proof.
  intros MCHR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv hb buf -> H0 H1 R Hb HB Hl HRO.
  step. step.
  if_cases HC; [exfalso; rewrite ?x01_eqb_zxb, ?x01_eqb_ub in HC by lia; apply Z.eqb_eq in HC; exact (Hb HC)|].
  step. step. step. step.
  eapply evt_cut.
  { eapply MCHR with (buf := buf).
    - rewrite ?MState.unsigned_lit by lia. exact HB.
    - unfold memchr_ok. destruct (find_byte _ _); [left|]; rewrite Hl, ?MState.unsigned_lit by lia; lia.
    - exact HRO. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU & WM & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x14110)) with (Z_to_bv 64 0x14110)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite ?MState.unsigned_lit by lia.
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU | exact WM].
Qed.

Section X01.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis MCHR : memchr_ro_contract.

(* A straight run that changes no memory and leaves one register unknown. *)
Lemma x01_run_ex : forall g hb L A regs mem md pc (Rf : word -> bvmap 5 word) pc' (Q : config -> Prop),
  FR B APIf ra empty g hb L A regs mem md ->
  Exec.evt rsegs (fun ms => exists y, ms = MState.MS (Rf y) fp_regs pc' fp_csr None mem (YK11.seg_rom rsegs))
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (YK11.seg_rom rsegs)) ->
  (forall y regs', (forall r, YK11.getr regs' r = YK11.getr (Rf y) r) ->
     SR (ms_segs B) (mkCfg (YK11.mkst regs' pc' mem (YK11.seg_rom (ms_segs B))) md) Q) ->
  SR (ms_segs B) (mkCfg (YK11.mkst regs pc mem (YK11.seg_rom (ms_segs B))) md) Q.
Proof.
  intros g hb L A regs mem md pc Rf pc' Q HF HE HK.
  pose proof (sl_segs B APIf ra empty FF) as ES.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HM & _).
  destruct (kb_md B (APIf rc) L A mem md HM) as [Hh Hl].
  apply (kb_run B regs pc mem md (fun R p m => (exists y, R = Rf y) /\ p = pc' /\ m = mem) Q Hh Hl).
  - rewrite ES. eapply Exec.evt_mono; [exact HE|]. intros ms (y & ->). exists (Rf y), pc', mem.
    split; [reflexivity | split; [exists y; reflexivity | split; reflexivity]].
  - intros R p m regs' ((y & ->) & -> & ->) HG. exact (HK y regs' HG).
Qed.

Lemma seg_X01 : Hcut B APIf ra (Inv_U14110 B APIf ra empty) -> Hcut B APIf ra (Inv_U14114 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U140f8 B APIf ra empty).
Proof.
  intros H20 H24 g c (L & A & regs & mem & md & -> & HF & HP & (HID & Hok)).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HF) as (Hsp & H16 & HSK & HS47 & HMI).
  set (idb := t_ID (g_in g) (fJ (g_in g))) in *.
  assert (Hlen : length idb = 38%nat) by apply u8_tID_len.
  unfold IDB in HID.
  assert (R96 : forall m, bytes_at rsegs m (spk g 76) idb ->
      ov_read_bytes rsegs m (wa (g_S g - 1936 + 96)) 1 = Some [RcIdentModel.nthb idb 20]).
  { intros m Hm. replace (g_S g - 1936 + 96) with (spk g 76 + Z.of_nat 20) by (unfold spk, fsp, SLOT_FRAME; lia).
    rewrite (bytes_at_ov_read _ _ _ _ 20 1 Hm) by lia.
    unfold RcIdentModel.nthb. rewrite (x01_firstn1 idb 20 (RcIdentModel.zb 0)) by lia. reflexivity. }
  unfold fsp, SLOT_FRAME in Hsp. unfold SLOT_K, SLOT_STACK, SL_TOP in *.
  destruct (Z.eq_dec (RcIdentModel.bz (RcIdentModel.nthb idb 20)) 0) as [Z0|NZ].
  - eapply x01_run_ex; [exact HF | unfold rmk; eapply x01_z with (spv := g_S g - 1936);
      [exact Hsp | lia | lia | exact (R96 mem HID) | exact Z0] |].
    intros y regs' HG. apply H24. apply (u8_cut_close B APIf ra empty _ _ _ _ L A); [| exact HP | exact I].
    apply (u8_FR_regs B APIf ra empty _ _ _ _ regs); [exact HF | rewrite HG; reflexivity ..].
  - pose proof Hok as (_ & Hnm & _ & H19 & _).
    assert (Hhas : RcIdentModel.has_model_name idb = 1)
      by (unfold RcIdentModel.has_model_name, RcIdentModel.OFF_HAS_NAME in *; lia).
    assert (HB79 : forall m, bytes_at rsegs m (spk g 76) idb ->
        bytes_at rsegs m (g_S g - 1936 + 79) (skipn 3 idb)).
    { intros m Hm. rewrite <- (firstn_skipn 3 idb) in Hm. apply bytes_at_app in Hm as [_ Hm].
      rewrite length_firstn, Hlen in Hm. change (Nat.min 3 38) with 3%nat in Hm.
      replace (g_S g - 1936 + 79) with (spk g 76 + Z.of_nat 3) by (unfold spk, fsp, SLOT_FRAME; lia).
      exact Hm. }
    pose proof (bytes_at_normalize rsegs mem _ _ HMI HID) as HIDn.
    eapply (u8_mid B APIf ra empty FF g _ L A regs mem md _ []); [exact HF | exact HP | u8_fp_tac | | |].
    + rewrite sl_mkR_of.
      apply (x01_c MCHR) with (spv := g_S g - 1936) (hb := RcIdentModel.nthb idb 20) (buf := skipn 3 idb);
        [exact Hsp | lia | lia | exact (R96 _ HIDn) | exact NZ | exact (HB79 _ HIDn)
        | rewrite length_skipn, Hlen; reflexivity | exact (u8_ro_norm mem)].
    + intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM).
      do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
      pose proof (fun r => sl_getr_eqv _ _ r Hx) as HG.
      destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _).
      injection HE; intros; subst.
      apply H20. exists L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [|split].
      * split; [|exact Hok]. unfold IDB. apply (u8_ba [] mem m' _ _ HID MU'). exact I.
      * exact Hhas.
      * unfold rg. transitivity (Z_to_bv 64 (memchr_res (g_S g - 1936 + 79) 0 17 (skipn 3 idb)));
          [rewrite HG; reflexivity|]. f_equal.
        assert (Hfz : (RcIdentModel.first_zero (RcIdentModel.model_name idb) <= 16)%nat).
        { apply x01_fz_le; [rewrite x01_mn_length by exact Hlen; lia|]. rewrite x01_mn_nth by lia. exact H19. }
        unfold memchr_res. change (firstn (Z.to_nat 17) (skipn 3 idb)) with (RcIdentModel.model_name idb).
        rewrite x01_find0 by (rewrite x01_mn_length by exact Hlen; lia).
        cbv beta iota. unfold spk, fsp, SLOT_FRAME. change (t_ID (g_in g) (fJ (g_in g))) with idb. lia.
Qed.

End X01.
