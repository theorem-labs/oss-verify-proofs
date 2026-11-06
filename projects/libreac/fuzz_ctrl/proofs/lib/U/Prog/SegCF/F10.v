(* Segment F10 of fuzz_ctrl LLVMFuzzerTestOneInput (ubsan, libreac v1.9.0): [0x13984, 0x139b8], U13984 -> U139bc
   (kind_name(k) is not "?" (P1c), the three reply slots sp+1750/1736/1728 zeroed,
   reac_ctrl_identity_reply(Φ (s7), len (s6), ...) (0x14b5c; v1.8 had Φ in s6, len in s5); reply frame 176). Port
   of the plain seg_F10 (a working branch lib/Prog/Seg/F10.v). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From Stdlib Require String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog Require Import SlotModel SlotInvCF
  reac_ctrl_kind_name_c reac_ctrl_kind_name reac_ctrl_identity_reply_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.U.Prog.SegCF Require Import Tac_slot Tac_u4.
Import ListNotations.
Open Scope Z_scope.

Lemma f10_c1 : forall k, 0 <= k <= 13 ->
  negb (bv_eqb (zxb (nth 0 (cstr_bytes (kind_name k)) (Z_to_bv 8 0))) (Z_to_bv 64 63)) = true.
Proof. intros k Hk. u4_cases13 k. Qed.

Lemma f10_first : forall k,
  firstn 1 (skipn 0 (cstr_bytes (kind_name k))) = [nth 0 (cstr_bytes (kind_name k)) (Z_to_bv 8 0)].
Proof. intros k. unfold cstr_bytes. destruct (String.list_ascii_of_string (kind_name k)); reflexivity. Qed.

Lemma f10_ka : forall x, 0 <= kind_name_addr x < 2 ^ 64.
Proof.
  intros x. unfold kind_name_addr. destruct (x <=? 13); [|unfold QMARK; lia].
  generalize (Z.to_nat x) as n. intros n. unfold kind_name_addrs.
  do 14 (destruct n as [|n]; [cbn [nth]; lia|]). destruct n; cbn [nth]; unfold QMARK; lia.
Qed.

Lemma f10_evt : reac_ctrl_identity_reply_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi len k : Z) (fr ja jp jn : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 (kind_name_addr k) -> s7 = Z_to_bv 64 phi -> s6 = Z_to_bv 64 len ->
    0 <= k <= 13 -> 176 <= spv -> spv + 1936 <= 2 ^ 64 -> spv mod 16 = 0 ->
    0 < phi -> 0 <= len < 2 ^ 64 -> phi + 50 <= spv - 176 ->
    stk rsegs m (spv - 176) spv -> mem_inv rsegs m -> length fr = 50%nat ->
    (50 <= len -> bytes_at rsegs m phi fr) ->
    rw_cells rsegs m (spv + 1750) [CB 2 ja] -> rw_cells rsegs m (spv + 1736) [CB 8 jp] ->
    rw_cells rsegs m (spv + 1728) [CB 8 jn] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x139bc) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (rp_r len fr))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x139bc) fc None m' (seg_rom rsegs) /\
         munch [(spv - 176, spv); (spv + 1728, spv + 1752)] m m' /\ wmono rsegs m m' /\
         (ir len fr = true -> bytes_at rsegs m' (spv + 1750) (reply_addr fr) /\
            q64 m' (spv + 1736) (phi + 38) /\ q64 m' (spv + 1728) (r_pll fr)) /\
         (ir len fr = false -> u16 m' (spv + 1750) 0 /\ q64 m' (spv + 1736) 0 /\ q64 m' (spv + 1728) 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13984) fc None m (seg_rom rsegs)).
Proof.
  intros RE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi len k fr ja jp jn Hsp Ha0 Hs7 Hs6 Hk H176 Hhi H16 Hphi Hlen Hpb ST MI Hfr Hg Hja Hjp Hjn.
  subst sp a0 s7 s6.
  pose proof (f10_ka k) as Hka.
  assert (HR : ov_read_bytes rsegs m (wa (kind_name_addr k)) 1 =
               Some [nth 0 (cstr_bytes (kind_name k)) (Z_to_bv 8 0)]).
  { pose proof (reac_ctrl_kind_name_strings_in_image m MI) as HKS.
    assert (L : (0 + 1 <= length (cstr_bytes (kind_name k)))%nat)
      by (unfold cstr_bytes; rewrite length_app; cbn [length]; lia).
    pose proof (bytes_at_ov_read rsegs m _ _ 0 1 (HKS k ltac:(lia)) L) as R.
    rewrite f10_first in R. cbn [Z.of_nat] in R. rewrite Z.add_0_r in R. exact R. }
  pose proof (munch_refl [(spv - 176, spv); (spv + 1728, spv + 1752)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. step. step. if_true_by (f10_c1 k Hk).
  step. step. step. step. step. step. step. step. step.
  destruct (rw_cells_forget _ _ _ _ Hja) as (ja' & Hja').
  destruct (rw_cells_forget _ _ _ _ Hjp) as (jp' & Hjp').
  destruct (rw_cells_forget _ _ _ _ Hjn) as (jn' & Hjn').
  cbn [cells_size csize Nat.add] in Hja', Hjp', Hjn'.
  assert (Hrd : reply_args phi (spv + 1750) (spv + 1736) (spv + 1728) = true).
  { unfold reply_args. rewrite !(proj2 (Z.eqb_neq _ _)) by lia. reflexivity. }
  eapply evt_cut.
  { eapply RE with (fr := phi) (len := len) (pa := spv + 1750) (pp := spv + 1736) (pn := spv + 1728)
      (S := spv) (g := fr) (ja := ja') (jp := jp') (jn := jn');
      [ reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | lia | lia | lia | lia | lia | lia | lia | unfold REAC_CTRL_IDENTITY_REPLY_K; lia
      | exact ST | exact MI | exact Hfr | | ].
    - intros _ Hb. split; [lia|]. split.
      + apply (bytes_at_transport rsegs _ m _ _ _ (Hg Hb) MU).
        cbn [disjoint_from]. rewrite Hfr. repeat split; try exact I; lia.
      + unfold REAC_CTRL_IDENTITY_REPLY_K. lia.
    - intros _. unfold REAC_CTRL_IDENTITY_REPLY_K.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [exact Hja'|]. split; [exact Hjp'|]. split; [exact Hjn'|].
      repeat split; lia. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MUc & WMc & MIc & STc & Hok).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x139bc)) with (Z_to_bv 64 0x139bc) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (Hret : reply_ret phi len (spv + 1750) (spv + 1736) (spv + 1728) fr = rp_r len fr).
  { unfold reply_ret, rp_r. rewrite Hrd. reflexivity. }
  assert (Hok' : reply_ok phi len (spv + 1750) (spv + 1736) (spv + 1728) fr = ir len fr).
  { unfold reply_ok. rewrite Hrd. reflexivity. }
  rewrite Hret.
  apply evt_done. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|].
  split.
  { apply (munch_trans _ m m0 m' MU). eapply munch_weaken; [|exact MUc].
    intros x (O1 & O2 & _). unfold reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K.
    destruct (reply_ok _ _ _ _ _ _); cbn [app Frame.outside]; repeat split; try exact I; lia. }
  split; [exact (wmono_trans rsegs m m0 m' WM WMc)|].
  split.
  - intros Hir. rewrite Hok' in Hok. destruct (Hok Hir) as (H1 & H2 & H3).
    split; [exact (sl_rw_bytes _ _ _ _ H1)|].
    split; [exact (sl_rw_bytes _ _ _ _ H2) | exact (sl_rw_bytes _ _ _ _ H3)].
  - intros Hir.
    assert (MUz : munch [(spv - 176, spv)] m0 m').
    { unfold reac_ctrl_identity_reply_fp, REAC_CTRL_IDENTITY_REPLY_K in MUc. rewrite Hok', Hir in MUc. exact MUc. }
    unfold u16, q64.
    split; [|split].
    + apply (bytes_at_transport rsegs _ m0 m' _ _ (u4_c_bytes _ _ _ Hja) MUz).
      cbn [disjoint_from Cells.cbytes]. rewrite length_le2. repeat split; try exact I; lia.
    + apply (bytes_at_transport rsegs _ m0 m' _ _ (u4_c_bytes _ _ _ Hjp) MUz).
      cbn [disjoint_from Cells.cbytes]. rewrite length_le8. repeat split; try exact I; lia.
    + apply (bytes_at_transport rsegs _ m0 m' _ _ (u4_c_bytes _ _ _ Hjn) MUz).
      cbn [disjoint_from Cells.cbytes]. rewrite length_le8. repeat split; try exact I; lia.
Qed.

Section F10.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis REPLY : reac_ctrl_identity_reply_contract.

Lemma seg_F10 : forall j : nat, Hat B APIf ra (Inv_U139bc_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_U13984_at B APIf ra empty) j.
Proof.
  intros j H g c (phi & L & A & regs & mem & md & -> & HFR & HP & HFB & HIFS & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof (sl_fr_stk B APIf ra empty FF _ _ _ _ _ _ _ HFR) as ST.
  pose proof (u4_phi_bnd B APIf ra empty g phi _ L A regs mem md HFR HP) as Hbnd.
  pose proof (u4_len_range (g_in g) j) as (Hl0 & Hb0 & Hbl).
  pose proof (proj1 HFR) as (Hn & _).
  pose proof HFB as (((Hj & H9 & _) & (HS24 & H21 & H22) & H23 & Hphi & H18) & _).
  pose proof (u4_k_range (g_in g) j) as Hk.
  unfold g_n in Hn.
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1750) 2 ST ltac:(lia) ltac:(lia)) as (ja & Hja).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1736) 8 ST ltac:(lia) ltac:(lia)) as (jp & Hjp).
  destruct (sl_rw_of_stk _ _ _ (g_S g - 1936 + 1728) 8 ST ltac:(lia) ltac:(lia)) as (jn & Hjn).
  eapply (u4_mid B APIf ra empty FF g _ L A regs mem md _
            [(g_S g - 1936 - 176, g_S g - 1936); (g_S g - 1936 + 1728, g_S g - 1936 + 1752)]);
    [exact HFR | exact HP | u4_fp_tac | | |].
  - rewrite sl_mkR_of.
    apply (f10_evt REPLY) with (spv := g_S g - 1936) (phi := phi) (len := t_len (g_in g) j)
      (k := t_k (g_in g) j) (fr := t_g (g_in g) j) (ja := ja) (jp := jp) (jn := jn);
      [exact Hsp | exact H10 | exact H23 | exact H22 | exact Hk | lia | lia | lia | lia | lia | lia
      | | | | | exact Hja | exact Hjp | exact Hjn].
    + apply (u4_stk_sub _ _ _ _ _ ST); lia.
    + exact (mem_inv_normalize rsegs mem).
    + apply u4_tg_len.
    + intros Hb. exact (u4_phi_g _ _ _ _ (bytes_at_normalize rsegs mem phi _ HMI Hphi) Hb).
  - intros ms (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MU & WM & _).
    do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _ & Hir1 & Hir0).
    injection HE; intros; subst.
    assert (HKP : SKP regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity).
    apply H. exists phi, L, A, regs', m', md.
    split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
    split; [|split; [|split]].
    + apply (u4_FB_keep g j phi regs regs' mem m' _ HFB HKP MU'); u4_dj.
    + apply (u4_IFS_keep g j mem m' _ HIFS MU'); u4_dj.
    + unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + unfold RPS, spk, fsp, SLOT_FRAME. split.
      * intros Hi. destruct (Hir1 Hi) as (R1 & R2 & R3). unfold q64 in *.
        split; [|split]; apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)); assumption.
      * intros Hi. destruct (Hir0 Hi) as (R1 & R2 & R3). unfold q64, u16 in *.
        split; [|split]; apply (proj2 (bytes_at_rel rsegs _ _ _ _ Hrel)); assumption.
Qed.

End F10.
