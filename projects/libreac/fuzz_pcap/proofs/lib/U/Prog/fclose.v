From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel fflush_c mclose_c
  __unlist_locked_file_c __ofl_lock_c __ofl_unlock_c fclose_pro.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fclose_mid :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    evt rsegs
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_fclose + 0xac)%Z)) sp gp tp t0 t1 t2 s0 s1 s0 a1 a2 a3 a4 a5 a6 a7
                                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fc None m (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_fclose + 0xa4)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros. do 2 step. apply evt_done. reflexivity.
Qed.

Lemma out3 : forall x a1 b1 a2 b2 a3 b3, ~ (a1 <= x < b1) -> ~ (a2 <= x < b2) -> ~ (a3 <= x < b3) ->
  outside [(a1, b1); (a2, b2); (a3, b3)] x.
Proof. intros. cbn. tauto. Qed.

Lemma mfile_cells_size : forall h b n fl pad0 rpos rend prev next mode pad1 pos pad2 ung buf,
  cells_size (mfile_cells h b n fl pad0 rpos rend prev next mode pad1 pos pad2 ung buf) = 1304%nat.
Proof. reflexivity. Qed.

Lemma ofl_not_ro : forall i, 0 <= i < 8 -> Mem.ro_addr rsegs (Z_to_bv 64 (A_OFL_HEAD + i)) = false.
Proof.
  intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import KindB fclose_c.
Local Open Scope Z_scope.

Lemma mstl_normalize : forall m h b Fc p prev next, ro_agree rsegs m ->
  (forall i, 0 <= i < 1304 -> Mem.ro_addr rsegs (Z_to_bv 64 (h + i)) = false) ->
  mstl m h b Fc p prev next -> mstl (normalize rsegs m) h b Fc p prev next.
Proof.
  intros m h b Fc p prev next RO HR (fl & md & q & rb & HMF & R1 & R2 & R3 & R4).
  exists fl, md, q, rb. refine (conj _ (conj R1 (conj R2 (conj R3 R4)))).
  destruct HMF as (buf & (pad0 & pad1 & pad2 & ung & HC & L1 & L2 & H0 & H16) & Hq & Hrb & HFc & Hb0 & Hd).
  unfold mfile; cbv zeta. exists buf.
  refine (conj _ (conj Hq (conj Hrb (conj (bytes_at_normalize rsegs _ _ _ RO HFc) (conj Hb0 Hd))))).
  unfold mfile_raw. exists pad0, pad1, pad2, ung. refine (conj _ (conj L1 (conj L2 (conj H0 H16)))).
  apply rw_cells_normalize; [exact RO | exact HC |]. intros i Hi. apply HR.
  rewrite mfile_cells_size in Hi. lia.
Qed.

Lemma in_blocks_user : forall L A q k, In (q, k) (blocks L A) ->
  exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = q.
Proof.
  intros L A q k H. unfold blocks in H. apply in_map_iff in H as ([p k'] & E & Hp).
  cbn in E. injection E as E1 E2. subst k'. exists p. split; [exact Hp | exact E1].
Qed.

Lemma in_blocks_of_user : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ H). Qed.

Section K.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis FREE_PC : ms_free B = (symaddr Symbols.Ubsan.s_free).
Hypothesis PIN_GUARD : ms_guard B = (symaddr Symbols.Ubsan.s___stack_chk_guard).
Hypothesis PIN_GOTG : ms_got_guard B = (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z).
Hypothesis PIN_CTX : ms_ctx B = (symaddr Symbols.Ubsan.s___malloc_context).
Hypothesis PIN_LOCK : ms_lock B = (symaddr Symbols.Ubsan.s___malloc_lock).
Hypothesis PIN_LIBC : ms_libc B = (symaddr Symbols.Ubsan.s___libc).
Hypothesis PIN_SIZEC : ms_size_classes B = (symaddr Symbols.Ubsan.s___malloc_size_classes).
Hypothesis PIN_SMALLC : ms_small_cnt B = (symaddr Symbols.Ubsan.s_small_cnt_tab).
Hypothesis PIN_MEDC : ms_med_cnt B = (symaddr Symbols.Ubsan.s_med_cnt_tab).
Hypothesis PIN_DEBR : ms_debruijn B = (symaddr (Symbols.Ubsan.Sec.s_rodata + 0x1c4)%Z).
Hypothesis PIN_TP : ms_tp B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0xc8)%Z).
Hypothesis PIN_ERRNO : ms_errno_off B = -164.
Hypothesis PIN_VML : ms_vmlock B = None.
Hypothesis PIN_DBLEN : ms_debruijn_len B = 32.
Hypothesis FREE : free_contract B API.
Hypothesis FREE0 : free_null_contract B.
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis BW : blocks_writable B API.
Hypothesis HFF : fflush_contract.
Hypothesis HMC : mclose_contract.
Hypothesis HUL : __unlist_locked_file_contract.
Hypothesis HOL : __ofl_lock_contract.
Hypothesis HOU : __ofl_unlock_contract.

Lemma in_img_span : ms_segs B = rsegs -> forall lo hi a,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true ->
  lo <= a < hi -> in_img B a.
Proof.
  intros HS lo hi a E Ha. apply existsb_exists in E as (s & Hs & E).
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2.
  pose proof (N2Z.is_nonneg (seg_base s)) as P.
  destruct (find_segment rsegs a 1) as [seg|] eqn:F.
  - exact (in_img_of_seg B HS a seg ltac:(lia) F).
  - exfalso. exact (find_segment_some rsegs s a 1 Hs ltac:(lia) ltac:(lia) F).
Qed.

Lemma in_img_glob : ms_segs B = rsegs -> forall a, (symaddr Symbols.Ubsan.s___stack_chk_guard) <= a < (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z) -> in_img B a.
Proof. intros HS a Ha. apply (in_img_span HS (symaddr Symbols.Ubsan.s___stack_chk_guard) (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z)); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma in_img_got : ms_segs B = rsegs -> forall a, (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) <= a < (symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z) -> in_img B a.
Proof. intros HS a Ha. apply (in_img_span HS (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) (symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z)); [vm_compute; reflexivity | exact Ha]. Qed.

Lemma blocks_not_img : forall L A mem md q k i, aa_MR API L A mem md -> In (q, k) (blocks L A) -> 0 <= i < k ->
  ~ in_img B (q + i).
Proof.
  intros L A mem md q k i HM Hin Hi. destruct (in_blocks_user L A q k Hin) as (p & Hp & <-).
  exact (ax_blocks_img AX L A mem md p k i HM Hp Hi).
Qed.

Lemma blk_img_disj : forall L A mem md q k lo hi, aa_MR API L A mem md -> In (q, k) (blocks L A) ->
  0 < k -> lo < hi -> (forall a, lo <= a < hi -> in_img B a) -> q + k <= lo \/ hi <= q.
Proof.
  intros L A mem md q k lo hi HM Hin Hk Hlh HI.
  destruct (Z_le_gt_dec (q + k) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (blocks_not_img L A mem md q k (Z.max q lo - q) HM Hin ltac:(lia)).
  replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply HI. lia.
Qed.

Lemma stdio_not_owned : ms_segs B = rsegs -> forall L A mem md a, aa_MR API L A mem md ->
  (a = (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z) \/ (symaddr Symbols.Ubsan.s_ofl_lock) <= a < (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z)) -> ~ owned B L A a.
Proof.
  intros HS L A mem md a HM Ha [Ho|Ho].
  - pose proof (ax_img AX L A mem md a HM (in_img_glob HS a ltac:(lia)) Ho) as C.
    rewrite PIN_CTX in C. unfold CTX_SIZE in C. lia.
  - unfold static_owned in Ho.
    rewrite PIN_LOCK, PIN_LIBC, PIN_GOTG, PIN_GUARD, PIN_DEBR, PIN_SIZEC, PIN_SMALLC, PIN_MEDC in Ho.
    unfold vml_lo, vml_len in Ho. rewrite PIN_VML, PIN_DBLEN in Ho. change (Z.max 32 32) with 32 in Ho. lia.
Qed.

Theorem fclose_holds : fclose_contract B API.
Proof.
  unfold fclose_contract.
  intros L A regs mem md h b p Fc b0 HSEG PRE A0 INH INB HST HOFL HSO HGU RO RES.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  unfold FCLOSE_K in *.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (zr_word sp) as RSP. unfold inr64 in RSP.
  rewrite HSEG in RO, HWS, HERR.
  assert (EV : errno_addr B = (symaddr (Symbols.Ubsan.s_builtin_tls + 0x24)%Z)) by (unfold errno_addr; rewrite PIN_TP, PIN_ERRNO; reflexivity).
  destruct (in_blocks_user L A h 1304 INH) as (ph & Hph & Eh).
  destruct (block_facts B _ LAWS L A mem md h 1304 0 HMR INH ltac:(lia)) as (_ & Hh4k & HhC & _).
  destruct (in_blocks_user L A b _ INB) as (pb & Hpb & Eb).
  pose proof (mr_blocks_range B _ LAWS L A mem md pb _ HMR Hpb) as (Hb4k & HbC). rewrite Eb in Hb4k, HbC.
  pose proof (mr_blocks_aligned B _ LAWS L A mem md pb _ HMR Hpb) as Hb16. rewrite Eb in Hb16.
  pose proof HST as (fl0 & md0 & q0 & rb0 & (buf0 & _ & _ & _ & _ & _ & HSEP) & _).
  assert (DG : h + 1304 <= (symaddr Symbols.Ubsan.s___stack_chk_guard) \/ (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z) <= h)
    by exact (blk_img_disj L A mem md h 1304 (symaddr Symbols.Ubsan.s___stack_chk_guard) (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z) HMR INH ltac:(lia) ltac:(lia) (in_img_glob HSEG)).
  assert (DGOT : h + 1304 <= (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) \/ (symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z) <= h)
    by exact (blk_img_disj L A mem md h 1304 (symaddr (Symbols.Ubsan.Sec.s_got + 0x80)%Z) (symaddr (Symbols.Ubsan.Sec.s_got + 0x88)%Z) HMR INH ltac:(lia) ltac:(lia) (in_img_got HSEG)).
  assert (DBO : b + Z.of_nat (length Fc) <= (symaddr Symbols.Ubsan.s_ofl_head) \/ (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z) <= b).
  { destruct (Z.eq_dec (Z.of_nat (length Fc)) 0) as [Z0|Z0].
    - rewrite Z0. clear - Hb16. Z.div_mod_to_equations. lia.
    - apply (blk_img_disj L A mem md b _ (symaddr Symbols.Ubsan.s_ofl_head) (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z) HMR INB); [lia | lia |].
      intros a Ha. apply (in_img_glob HSEG). lia. }
  assert (RN0 : mem_rel rsegs mem (normalize rsegs mem)) by (apply mem_rel_normalize; exact RO).
  assert (ST : stk rsegs mem (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|].
    destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb. unfold mrd, wa. rewrite E. reflexivity. }
  rewrite HSEG.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp. unfold FCLOSE.
    apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO |].
    eapply (fclose_pro HFF HMC HUL HOL HOU) with (lo := bv_unsigned sp - 8240) (h := h) (b := b) (p := p) (Fc := Fc).
    - exact A0.
    - apply mstl_normalize; [exact RO | | exact HST]. intros i Hi.
      apply (ro_addr_out B HSEG); [lia|]. exact (blocks_not_img L A mem md h 1304 i HMR INH Hi).
    - unfold ofl_one in *. apply rw_cells_normalize; [exact RO | exact HOFL |].
      intros i Hi. cbn in Hi. apply ofl_not_ro. lia.
    - destruct HSO as (S1 & S2 & S3).
      exact (conj (bytes_at_normalize rsegs _ _ _ RO S1)
               (conj (bytes_at_normalize rsegs _ _ _ RO S2) (bytes_at_normalize rsegs _ _ _ RO S3))).
    - destruct HGU as (G1 & g & G2).
      split; [exact (bytes_at_normalize rsegs _ _ _ RO G1) | exists g; exact (bytes_at_normalize rsegs _ _ _ RO G2)].
    - apply mem_inv_normalize.
    - lia.
    - apply stk_normalize; [exact ST | lia].
    - lia.
    - lia.
    - lia.
    - lia.
    - unfold A_LIBC, A_OFL_HEAD. lia.
    - unfold A_GUARD. lia.
    - unfold A_GOT_GUARD. lia.
    - unfold A_OFL_HEAD. lia. }
  intros ms1 (can1 & (s1 & Q1 & REL1 & ROS1) & EQ1).
  unfold fclose_pro_post in Q1.
  destruct Q1 as (sp1 & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1n & junk
    & -> & SP1 & FR & MU & WM & MI & ST1 & OFE & SO1 & GU1 & BF & HJ).
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL1) as [CAN1 HR1].
  remember (ms_mem can1) as m1 eqn:Em1. subst can1. clear Em1.
  pose proof (munch_rel rsegs _ _ _ _ _ RN0 HR1 ROS1 MU) as MU1.
  pose proof (wmono_rel rsegs _ _ _ _ RN0 HR1 ROS1 WM) as WM1.
  pose proof (ro_agree_same rsegs _ _ RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 FR) as FR1.
  unfold ofl_empty in OFE. pose proof (rw_cells_of_rel rsegs _ _ _ _ HR1 OFE) as OFE1.
  destruct SO1 as (S1n & S2n & S3n).
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR1) S1n) as S1.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR1) S3n) as S3.
  pose proof (proj2 (bytes_at_rel rsegs _ _ _ _ HR1) BF) as BF1.
  clear MU WM MI ST1 OFE S1n S2n S3n GU1 BF HJ FR.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1).
  unfold A_OFL_HEAD, A_OFL_LOCK, A_LIBC, A_GUARD, A_GOT_GUARD in *.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_fclose + 0xa4)%Z)) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); reflexivity).
  assert (E1_2 : getr R1 2 = sp1) by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); reflexivity).
  assert (E1_8 : getr R1 8 = wz h) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); reflexivity).
  assert (E1_9 : getr R1 9 = wz 0) by (rewrite (getr_of_eqv _ _ 9 X1 eq_refl); reflexivity).
  assert (E1_10 : getr R1 10 = wz 0) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); reflexivity).
  assert (E1_18 : getr R1 18 = wz 0) by (rewrite (getr_of_eqv _ _ 18 X1 eq_refl); reflexivity).
  assert (OWN_OUT : forall a, owned B L A a ->
    0 <= a < 2 ^ 64 /\ outside [(bv_unsigned sp - 128, bv_unsigned sp); (h, h + 1304); ((symaddr Symbols.Ubsan.s_ofl_head), (symaddr Symbols.Ubsan.s_ofl_head) + 8)] a).
  { intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
    split; [lia|]. apply out3; [lia | |].
    - intros Hin. destruct (block_facts B _ LAWS L A mem md h 1304 (a - h) HMR INH ltac:(lia)) as (_ & _ & _ & N).
      apply N. replace (h + (a - h)) with a by ring. exact Ho.
    - intros Hin. exact (stdio_not_owned HSEG L A mem md a HMR ltac:(lia) Ho). }
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (OWN_OUT a Ho) as [R O]. exact (munch_mbyte _ _ _ _ a MU1 R O).
    - intros a Ho Hp. destruct (OWN_OUT a Ho) as [R O]. exact (munch_present _ _ _ a MU1 R O Hp).
    - intros q n i Hin Hi. pose proof (in_blocks_of_user L A q n Hin) as INq.
      destruct (block_facts B _ LAWS L A mem md _ _ i HMR INq Hi) as (_ & Hq1 & Hq2 & _).
      apply (present_of_writable_out B HSEG m1 (ptr_addr L q + i) ltac:(lia)
               (blocks_not_img L A mem md _ _ i HMR INq Hi)).
      pose proof (BW L A mem md _ _ i HMR INq Hi) as W. rewrite HSEG in W. apply WM1. exact W.
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  pose proof FREE0 as F0. unfold free_null_contract in F0. rewrite HSEG, FREE_PC in F0.
  eapply SR_bind.
  { unfold FREE_FN. apply (F0 R1 m1 md); [rewrite E1_1; apply bv_eq; vm_compute; reflexivity | exact E1_10 | exact Hh | exact Hl]. }
  intros c2 ->. rewrite E1_1.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. apply fclose_mid. }
  intros ms2 (can2 & -> & EQ2).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ2 eq_refl eq_refl) as (R2 & -> & X2).
  assert (E2_1 : getr R2 1 = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_fclose + 0xac)%Z)) by (rewrite (getr_of_eqv _ _ 1 X2 eq_refl); reflexivity).
  assert (E2_10 : getr R2 10 = wz h) by (rewrite (getr_of_eqv _ _ 10 X2 eq_refl); exact E1_8).
  assert (E21 : forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    repeat (destruct C as [C|C]; [subst r; rewrite (getr_of_eqv _ _ _ X2) by reflexivity; reflexivity|]).
    subst r; rewrite (getr_of_eqv _ _ _ X2) by reflexivity; reflexivity. }
  assert (G2 : getr R2 2 = sp1) by exact (eq_trans (E21 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (G4 : getr R2 4 = reg_get regs 4) by exact (eq_trans (E21 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (SP2 : spZ R2 = bv_unsigned sp - 48) by (unfold spZ; rewrite G2; exact SP1).
  pose proof FREE as FR0. unfold free_contract in FR0. rewrite HSEG, FREE_PC in FR0.
  eapply SR_bind.
  { eapply (FR0 L A R2 m1 md ph 1304 b0); [ | exact RO1 | exact Hph | rewrite Eh; exact E2_10 | exact RES].
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E2_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP2; replace (bv_unsigned sp - 48) with (bv_unsigned sp + (-3) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP2; change ALLOC_STACK with 8192; lia|].
    split; [rewrite SP2; lia|].
    split; [intros a Ha; rewrite SP2 in Ha; change ALLOC_STACK with 8192 in Ha; rewrite HSEG; apply WM1; apply HWS; lia|].
    split; [rewrite G4; exact HTP|].
    split; [intros a Ha; rewrite HSEG; apply WM1; apply HERR; exact Ha|].
    intros HI. specialize (HAUX HI). rewrite SP2.
    destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
    exists av, ar.
    refine (conj _ (conj _ (conj _ (conj _ (conj B1 (conj B2 (conj B3 (conj B4 (conj _ _))))))))).
    - eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk. rewrite PIN_LIBC.
      split; [lia|]. apply out3; lia.
    - intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
      split; [lia|]. apply out3; lia.
    - eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia|]. apply out3; lia.
    - eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia|]. apply out3; lia.
    - lia.
    - lia. }
  intros c3 RET.
  destruct RET as (L' & A' & R3 & m3 & md3 & -> & POST & BLK & KEPT & RO3 & GK & UBK & INIT & RLEN & RES').
  destruct POST as (HMR' & HWF' & HBD' & HLE & HSTAB & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR') as (Hh3 & Hl3 & Hmat3).
  destruct BLK as (b1 & b2 & BLK1 & BLK2). rewrite Eh in BLK1.
  unfold blocks_kept in KEPT. cbv beta in KEPT, HFRAME. rewrite Eh in KEPT, HFRAME.
  rewrite E2_1.
  assert (E31 : forall r, callee_saved r -> getr R3 (Z_to_bv 5 r) = getr R1 (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HPRES r Hr). exact (E21 r Hr). }
  assert (G3_2 : getr R3 2 = sp1) by exact (eq_trans (E31 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (G3_9 : getr R3 9 = wz 0) by exact (eq_trans (E31 9 ltac:(unfold callee_saved; lia)) E1_9).
  assert (G3_18 : getr R3 18 = wz 0) by exact (eq_trans (E31 18 ltac:(unfold callee_saved; lia)) E1_18).
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L' A' a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR' Ho)]; lia. }
  assert (HI2 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp - 48) ->
     mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m3 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFRAME; [left; exact Ha | exact N1 | exact N2 | | lia].
    unfold scratch. rewrite SP2, EV. change ALLOC_STACK with 8192. intros [H|H]; lia. }
  assert (GLOB : forall a, (a = (symaddr (Symbols.Ubsan.s___libc + 0x1)%Z) \/ (symaddr Symbols.Ubsan.s_ofl_lock) <= a < (symaddr (Symbols.Ubsan.Sec.s_bss + 198696)%Z)) ->
     mbyte rsegs m3 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a <-> writable_at rsegs m3 a)).
  { intros a Ha. rewrite <- HSEG. apply HFRAME.
    - right. apply (in_img_glob HSEG). lia.
    - exact (stdio_not_owned HSEG L A mem md a HMR Ha).
    - exact (stdio_not_owned HSEG L' A' m3 md3 a HMR' Ha).
    - unfold scratch. rewrite SP2, EV. change ALLOC_STACK with 8192. intros [H|H]; lia.
    - lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp - 48)
                  [CB 8 junk; C8 (reg_get regs 19); C8 (reg_get regs 18); C8 (reg_get regs 9); C8 (reg_get regs 8);
                   C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FR1|]. intros i Hi. cbn in Hi.
    rewrite <- HSEG. destruct (HI2 (bv_unsigned sp - 48 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of.
    eapply fclose_epi with (sp0 := sp) (junk := junk) (ra0 := reg_get regs 1) (s0o := reg_get regs 8)
      (s1o := reg_get regs 9) (s2o := reg_get regs 18) (s3o := reg_get regs 19).
    - rewrite <- SP1. f_equal. exact G3_2.
    - exact G3_9.
    - exact G3_18.
    - exact FR3. }
  intros ms5 (can5 & -> & EQ5).
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (R5 & -> & X5).
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  apply SR_ret.
  exists L', A', R5, m3, md3.
  split; [reflexivity|].
  split.
  { split; [exact HMR'|]. split; [exact HWF'|]. split; [exact HBD'|]. split; [exact HLE|]. split; [exact HSTAB|].
    split.
    { intros r Hr. pose proof Hr as Hc. unfold callee_saved in Hc.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      clear Hc.
      repeat (destruct C as [C|C];
        [subst r; rewrite (getr_of_eqv _ _ _ X5) by reflexivity;
         first [ reflexivity
               | lazymatch goal with |- _ = getr _ ?k =>
                   transitivity (getr R3 k); [reflexivity|];
                   rewrite (E31 _ Hr); rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity end ] |]).
      subst r; rewrite (getr_of_eqv _ _ _ X5) by reflexivity;
         first [ reflexivity
               | lazymatch goal with |- _ = getr _ ?k =>
                   transitivity (getr R3 k); [reflexivity|];
                   rewrite (E31 _ Hr); rewrite (getr_of_eqv _ _ _ X1) by reflexivity; reflexivity end ]. }
    split; [exact HVM|].
    split.
    { intros a HA NO1 NO2 NS NE. unfold fclose_writes, A_OFL_HEAD in NE.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct HA as [HA|HA]; [lia | pose proof (in_img_low B HSEG a HA); lia]).
      assert (NSP : ~ (bv_unsigned sp - 8240 <= a < bv_unsigned sp)).
      { intro H. apply NS. left. unfold spZ. change (getr regs 2) with sp. lia. }
      assert (NER : ~ (errno_addr B <= a < errno_addr B + 4)) by (intro H; apply NS; right; exact H).
      assert (O1 : outside [(bv_unsigned sp - 128, bv_unsigned sp); (h, h + 1304); ((symaddr Symbols.Ubsan.s_ofl_head), (symaddr Symbols.Ubsan.s_ofl_head) + 8)] a)
        by (apply out3; lia).
      pose proof (munch_mbyte (ms_segs B) _ _ _ a MU1 AR O1) as E01.
      pose proof (munch_writable (ms_segs B) _ _ _ a MU1 AR O1) as W01.
      assert (H13 : mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m3 a)).
      { apply HFRAME; [exact HA | exact NO1 | exact NO2 | | lia].
        unfold scratch. rewrite SP2. change ALLOC_STACK with 8192. intros [H|H]; [lia | exact (NER H)]. }
      split; [rewrite (proj1 H13), E01; reflexivity | rewrite W01, (proj2 H13); tauto]. }
    split.
    { intros q n i Hin Hin' Hi. pose proof (in_blocks_of_user L A q n Hin) as INq.
      destruct (block_facts B _ LAWS L A mem md _ _ i HMR INq Hi) as (_ & Hq1 & Hq2 & _).
      assert (INA : In (ptr_addr L q, n) (b1 ++ b2)).
      { rewrite <- BLK2. rewrite <- (HSTAB q n Hin Hin'). exact (in_blocks_of_user L' A' q n Hin'). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR BLK1 INA) as Dj.
      rewrite (HBLKS q n i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply out3; [lia | lia |]].
      intro Hof. apply (blocks_not_img L A mem md _ _ i HMR INq Hi). apply (in_img_glob HSEG). lia. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 48)) as [D|D].
      + apply HSCR. unfold scratch. rewrite SP2. change ALLOC_STACK with 8192. left. lia.
      + apply (proj2 (HI2 a ltac:(lia) ltac:(lia))). rewrite HSEG. apply WM1. apply HWS. lia.
    - apply HSCR. right. exact Ha. }
  split; [rewrite (getr_of_eqv _ _ 10 X5 eq_refl); reflexivity|].
  split; [exists b1, b2; split; [exact BLK1 | exact BLK2]|].
  split.
  { unfold blocks_kept. intros q k i Hq Hne Hi. cbv beta in Hne.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    assert (Hq' : In (q, k) (b1 ++ b2)).
    { pose proof Hq as Hq0. rewrite BLK1 in Hq0. apply in_app_or in Hq0 as [Hq0|[Hq0|Hq0]].
      - apply in_or_app. left. exact Hq0.
      - injection Hq0 as E1 E2. exfalso. apply Hne. symmetry. exact E1.
      - apply in_or_app. right. exact Hq0. }
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR BLK1 Hq') as Dj.
    rewrite (KEPT q k i Hq Hne Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply out3; [lia | lia |]].
    intro Hof. apply (blocks_not_img L A mem md _ _ i HMR Hq Hi). apply (in_img_glob HSEG). lia. }
  split.
  { intros q k Hq Hne. apply UBK; [exact Hq|]. intros ->. apply Hne. exact Eh. }
  split; [exact INIT|]. split; [exact RLEN|]. split; [exact RES'|].
  split.
  { unfold ofl_empty. apply (rw_cells_transfer rsegs m1); [exact OFE1|]. intros i Hi. cbn in Hi.
    destruct (GLOB ((symaddr Symbols.Ubsan.s_ofl_head) + i) ltac:(lia)) as [E W]. split; [exact E | apply W]. }
  split.
  { unfold stdio_ok. refine (conj _ (conj _ _)).
    - apply (bytes_at_transfer rsegs m1); [exact S1|]. intros i Hi. cbn in Hi.
      exact (proj1 (GLOB ((symaddr Symbols.Ubsan.s___libc) + 1 + i) ltac:(lia))).
    - destruct (ax_statics AX L' A' m3 md3 HMR') as (_ & _ & L3). rewrite PIN_LIBC, HSEG in L3.
      unfold A_LIBC. apply bytes_at_of_mbyte; [lia | cbn [length]; lia |].
      intros i Hi. cbn [length] in Hi. destruct i as [|i]; [|lia].
      replace ((symaddr Symbols.Ubsan.s___libc) + 3 + Z.of_nat 0) with ((symaddr Symbols.Ubsan.s___libc) + 3) by lia. exact L3.
    - apply (bytes_at_transfer rsegs m1); [exact S3|]. intros i Hi. rewrite length_le4 in Hi.
      exact (proj1 (GLOB ((symaddr Symbols.Ubsan.s_ofl_lock) + i) ltac:(lia))). }
  split.
  { unfold guard_ok. destruct (ax_statics AX L' A' m3 md3 HMR') as (Gw & (g & Hg & Gg) & _).
    rewrite PIN_GOTG, PIN_GUARD, HSEG in Gw. rewrite PIN_GUARD, HSEG in Gg.
    split.
    - unfold A_GOT_GUARD, A_GUARD, wz. apply (KindBGlue.word_mem_le8 rsegs); [exact Gw | lia | lia | lia].
    - exists (Z_to_bv 64 g). unfold A_GUARD. apply (KindBGlue.word_mem_le8 rsegs); [exact Gg | lia | lia | lia]. }
  split; [exact RO3|].
  apply (bytes_at_transfer rsegs m1); [exact BF1|]. intros i Hi.
  rewrite <- HSEG. apply (KEPT b _ i INB); [cbv beta; intro E; lia | lia].
Qed.

End K.
