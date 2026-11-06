From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition xm_size (n : Z) : Z := if (n =? 0)%Z then 1 else n.

Lemma xm_size_word : forall n, (0 <= n < 2 ^ 64)%Z ->
  Z_to_bv 64 (n + bv_unsigned (v_sltiu (Z_to_bv 64 n) 1)) = Z_to_bv 64 (xm_size n).
Proof.
  intros n Hn. unfold v_sltiu, xm_size. rewrite unsigned_lit by lia.
  destruct (Z.eqb_spec n 0) as [->|Hz].
  - reflexivity.
  - replace (bv_wrap 64 1) with 1%Z by reflexivity.
    replace (n <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. rewrite unsigned_lit by lia. f_equal. lia.
Qed.

Lemma xm_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo n : Z),
  stk rsegs m lo (bv_unsigned sp) -> (lo + 16 <= bv_unsigned sp)%Z ->
  a0 = Z_to_bv 64 n -> (0 <= n < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => exists a1' m' junk,
       ms' = MS (mkR (Z_to_bv 64 0x15a9c) (Z_to_bv 64 (bv_unsigned sp - 16)) gp tp t0 t1 t2 s0 s1
                     (Z_to_bv 64 (xm_size n)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x18c10) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m'
       /\ rw_cells rsegs m' (bv_unsigned sp - 16)%Z [CB 8 junk; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a88) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo n ST LO -> Hn.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 16%nat junk [] [8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  do 5 step.
  apply evt_done.
  do 3 eexists. split.
  { rewrite xm_size_word by lia. reflexivity. }
  split; [eassumption|]. split; [eassumption|]. eassumption.
Qed.

Lemma xm_run2 :
  forall ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 ra0 : word) (junk : list byte) (res : Z),
  rw_cells rsegs m (bv_unsigned sp0 - 16) [CB 8 junk; C8 ra0] ->
  (16 <= bv_unsigned sp0)%Z -> (0 < res < 2 ^ 64)%Z ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
       ms' = MS (mkR ra0 sp0 gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15a9c) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 ra0 junk res FR SPR Hr.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (UR : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  step. if_false. do 3 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 - 16 + 16)) with sp0 by (rewrite Z.sub_add; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done.
  do 14 eexists. reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecKindB xmalloc_c.
Local Open Scope Z_scope.

Lemma xm_ro_agree : forall m m' W, ro_agree rsegs m -> munch W m m' ->
  (forall x, (0 <= x < 2 ^ 20)%Z -> outside W x) -> ro_agree rsegs m'.
Proof.
  intros m m' W H M O a E. unfold mrd. rewrite (M a); [exact (H a E)|].
  pose proof (bv_unsigned_in_range 64 a) as Ra. unfold bv_modulus in Ra. cbn in Ra.
  apply O. split; [lia|]. destruct (Z_lt_ge_dec (bv_unsigned a) (2 ^ 20)) as [Hl|Hl]; [exact Hl|].
  exfalso. pose proof (ro_addr_hi (bv_unsigned a) ltac:(lia)) as F.
  rewrite Z_to_bv_bv_unsigned in F. rewrite F in E. discriminate.
Qed.

Section X.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis MALLOC_PC : ms_malloc B = 0x18c10.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis MALLOC : malloc_contract B API.

Lemma xm_img_low : img_low B.
Proof using SEGS.
  pose proof alloc_ceiling_val as AC.
  apply (img_low_of_check B (2 ^ 21)); [unfold img_check; rewrite SEGS; vm_compute; reflexivity | lia].
Qed.

Theorem xmalloc_holds : xmalloc_contract B API.
Proof using SEGS MALLOC_PC ERRNO_LOW GOTG MALLOC.
  unfold xmalloc_contract.
  intros L A regs mem md n b PRE A0 NR RES ROOM RA.
  change (xmalloc_size n) with (xm_size n) in *.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof xm_img_low as IL.
  assert (KV : XMALLOC_K = 8208) by reflexivity.
  assert (AS : ALLOC_STACK = 8192) by reflexivity.
  assert (SZ : 1 <= xm_size n <= LMAX + 2) by (unfold xm_size; destruct (Z.eqb_spec n 0); unfold LMAX in *; lia).
  pose proof MALLOC as MAL. unfold malloc_contract in MAL. rewrite MALLOC_PC in MAL.
  pose proof PRE as PRE0.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (kb_md B API _ _ _ _ HMR) as [Hh Hl].
  pose proof (kb_stk B API IL _ _ _ _ _ _ PRE0 ltac:(lia)) as ST.
  rewrite SEGS in ST.
  unfold spZ in *.
  set (sp := getr regs 2) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  eapply (kb_run B regs (Z_to_bv 64 XMALLOC) mem md
    (fun R pc' m' => exists a1' junk,
       R = mkR (Z_to_bv 64 0x15a9c) (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 3) (getr regs 4) (getr regs 5)
             (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (Z_to_bv 64 (xm_size n)) a1' (getr regs 12)
             (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
             (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
             (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) /\
       pc' = Z_to_bv 64 0x18c10 /\
       munch [(bv_unsigned sp - 16, bv_unsigned sp)] mem m' /\ wmono rsegs mem m' /\
       rw_cells rsegs m' (bv_unsigned sp - 16) [CB 8 junk; C8 (getr regs 1)])
    _ Hh Hl).
  { unfold rmk. fold sp. rewrite SEGS. eapply evt_cut.
    - eapply (xm_run1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr mem
                (bv_unsigned sp - XMALLOC_K) n); [exact ST | lia | exact A0 | unfold LMAX in NR; lia].
    - intros ms' (a1' & m' & junk & -> & MU & WM & FR). apply evt_done.
      do 3 eexists. split; [reflexivity|]. exists a1', junk.
      split; [reflexivity|]. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. exact FR. }
  intros R pc1 m1 R1 (a1' & junk & -> & -> & MU1 & WM1 & FR1) HG1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15a9c) by (rewrite HG1; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp - 16)) by (rewrite HG1; reflexivity).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite HG1; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (xm_size n)) by (rewrite HG1; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall x, 0 <= x < 2 ^ 64 -> ~ (bv_unsigned sp - 16 <= x < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 16, bv_unsigned sp)] x) by (intros x _ Hx; cbn; split; [exact Hx | exact I]).
  assert (RA1 : ro_agree (ms_segs B) m1).
  { rewrite SEGS in RA |- *. apply (xm_ro_agree mem m1 _ RA MU1). intros x Hx. apply OUT1; lia. }
  assert (PRE1 : call_pre_k B (aa_MR API) ALLOC_STACK L A R1 m1 md).
  { refine (kb_pre_A B API XMALLOC_K 16 ALLOC_STACK L A regs mem md R1 m1 [(bv_unsigned sp - 16, bv_unsigned sp)]
             PRE0 _ _ _ _ _ _ _ _ _ _ _).
    - lia.
    - lia.
    - lia.
    - unfold spZ. rewrite E1_2. rewrite unsigned_lit by lia. reflexivity.
    - rewrite SP1. replace (bv_unsigned sp - 16) with (bv_unsigned sp + (-1) * 16) by ring.
      rewrite Z.mod_add by lia. exact HAL.
    - exact E1_4.
    - rewrite E1_1. apply bv_eq. vm_compute. reflexivity.
    - exact MU1.
    - rewrite SEGS. exact WM1.
    - intros x Hx Hs. apply OUT1; [exact Hx|]. unfold spZ in Hs. fold sp in Hs. lia.
    - intros x Hx _. apply OUT1; lia. }
  assert (ROOM0 : room_slots b (xm_size n)) by (apply room_slots_malloc; [lia | exact ROOM]).
  eapply SR_bind.
  { apply (MAL L A R1 m1 md (xm_size n) b);
      [apply call_pre_k_alloc; exact PRE1 | exact RA1 | exact E1_10 | exact RES | exact ROOM0]. }
  intros c2 RET.
  destruct RET as (L' & A' & R2 & m2 & md2 & res & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RA2 & GK2 & UB2
    & INIT & REG2 & RES').
  pose proof POST as POST0.
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (kb_md B API _ _ _ _ HMR') as [Hh2 Hl2].
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp - 16))
    by exact (eq_trans (HPRES 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp - 16) [CB 8 junk; C8 (getr regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    assert (N1 : ~ owned B L A (bv_unsigned sp - 16 + i))
      by (intro Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho); lia).
    assert (N2 : ~ owned B L' A' (bv_unsigned sp - 16 + i))
      by (intro Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR' Ho); lia).
    rewrite <- SEGS.
    destruct (HFRAME (bv_unsigned sp - 16 + i) ltac:(left; lia) N1 N2
                ltac:(unfold scratch_k; rewrite SP1; intros [H|H]; lia) ltac:(intros F; exact F)) as [E W].
    split; [exact E | apply W]. }
  rewrite E1_1.
  eapply (kb_run B R2 (Z_to_bv 64 0x15a9c) m2 md2
    (fun R pc' m' => pc' = ret_pc (getr regs 1) /\ m' = m2 /\ getr R 10 = Z_to_bv 64 res /\ regs_preserved regs R)
    _ Hh2 Hl2).
  { unfold rmk. rewrite SEGS. rewrite E2_2, A0'. eapply evt_cut.
    - eapply (xm_run2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fp_regs fp_csr m2 sp (getr regs 1)
                junk res); [exact FR2 | lia | lia].
    - intros ms' (t0' & t1' & t2' & b1 & b2 & b3 & b4 & b5 & b6 & b7 & t3' & t4' & t5' & t6' & ->). apply evt_done.
      do 3 eexists. split; [reflexivity|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      intros r Hr. pose proof Hr as Hr0. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|C]; [reflexivity|].
      transitivity (getr R1 (Z_to_bv 5 r)).
      { rewrite <- (HPRES r Hr0). repeat (destruct C as [->|C]; [reflexivity|]). subst r. reflexivity. }
      rewrite HG1. repeat (destruct C as [->|C]; [reflexivity|]). subst r. reflexivity. }
  intros R3 pc3 m3 regs3 (-> & -> & A3 & P3) HG3.
  rewrite (kb_ret_pc _ HRA).
  apply SR_ret.
  exists L', A', regs3, m2, md2, res.
  split; [reflexivity|].
  split.
  { apply kb_post.
    - change (spZ regs) with (bv_unsigned sp).
      apply (kb_mid_E B API _ _ _ _ _ _ (fun a => (fun _ => False) a \/ (fun _ => False) a));
        [|intros a [F|F]; exact F].
      apply (kb_mid_seqAX B API _ _ _ _ _ _ _ m1 ALLOC_STACK (spZ R1) _ L' A' m2 md2).
      + apply (kb_mid_A B API IL _ _ _ _ _ _ m1 [(bv_unsigned sp - 16, bv_unsigned sp)] _ HMR HWF HBD).
        * intros a [Ha|Ha]; [apply HWS; exact Ha | apply HERR; exact Ha].
        * exact MU1.
        * rewrite SEGS. exact WM1.
        * intros x Hx Hs _. apply OUT1; [exact Hx|]. lia.
        * intros x Hx _. apply OUT1; lia.
      + exact (proj1 (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ POST0)).
      + rewrite SP1. lia.
      + rewrite SP1. lia.
      + lia.
      + lia.
      + intros a _ _ F. exact F.
    - apply (kb_preserved_getr regs R3 regs3 P3). intros r. apply HG3. }
  split; [rewrite HG3; exact A3|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|]. split; [exact BLK|].
  split.
  { intros q k i Hq _ Hi. rewrite (KEPT q k i Hq (fun F => F) Hi).
    exact (kb_blocks_munch B API L A mem m1 md _ HMR MU1 ltac:(intros x Hx _; apply OUT1; lia) q k i Hq Hi). }
  split; [exact RA2|].
  split.
  { intros i Hi. rewrite (GK2 i Hi). rewrite GOTG, SEGS.
    apply (munch_mbyte rsegs _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UB2|]. split; [exact INIT|]. split; [exact REG2|]. exact RES'.
Qed.

End X.
