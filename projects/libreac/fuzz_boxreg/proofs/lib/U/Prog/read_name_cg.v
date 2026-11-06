From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable Require YK14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Contract.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import memcpy_c read_name_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import read_name LLVMFuzzerTestOneInput_cfb read_name_ccf.
Import ListNotations.
Open Scope Z_scope.

Lemma rn_head_cf : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (lo c p : Z) (pl : list byte),
  a0 = Z_to_bv 64 c -> c mod 8 = 0 ->
  rw_cells rsegs m c [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
  bytes_at rsegs m p pl ->
  0 <= p < 2 ^ 64 ->
  (pl <> [] -> 1 <= p /\ p + Z.of_nat (length pl) <= lo) ->
  stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= c ->
  evt rsegs
    (fun ms' => exists (s0' s1' a0' a1' a2' a3' a4' a5' cp cn : word) (m' : word -> option byte),
       ms' = MS (mkR (Z_to_bv 64 0x13800) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0' s1' a0' a1' a2' a3' a4'
                     a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 MALLOC) fc None m' ro /\
       munch [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16)] m m' /\
       wmono rsegs m m' /\
       rw_cells rsegs m' (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] /\
       rw_cells rsegs m' c [C8 cp; C8 cn] /\
       stk rsegs m' lo (bv_unsigned sp + -32) /\
       s0' = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1) /\
       s1' = Z_to_bv 64 (rn_k pl) /\ a0' = Z_to_bv 64 (rn_k pl + 1) /\
       cp = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl) /\
       cn = Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 READ_NAME) fc None m ro).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ro
    lo c p pl -> CA CU PB HP PL ST LO SPC.
  unfold READ_NAME, MALLOC.
  pose proof (bytes_at_bound rsegs m p _ PB) as PBB.
  pose proof (rw_cells_bound rsegs m c _ CU) as CUB. cbn [cells_size csize Nat.add] in CUB.
  pose proof (rn_k_range pl) as KR.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (c, c + 16)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  assert (NR : Z.of_nat (length pl) < 2 ^ 64)
    by (destruct pl as [|y r]; [cbn; lia | specialize (PL ltac:(discriminate)); lia]).
  destruct (Z.eqb_spec (Z.of_nat (length pl)) 0) as [N0|N1].
  - rewrite (rn_k_nil pl) by lia. rewrite N0 in CU |- *.
    carve_frame 32%nat ST.
    do 6 step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    do 3 step. if_true.
    step. step. if_true.
    step.
    destruct (Z.eq_dec p 0) as [P0|P0].
    + rn_mid.
    + rn_mid.
  - destruct (nth_error pl 0) as [x|] eqn:NX;
      [|destruct pl; [cbn in N1; lia|discriminate]].
    assert (PL' : 1 <= p /\ p + Z.of_nat (length pl) <= lo) by (apply PL; intros E; subst pl; cbn in N1; lia).
    clear PL.
    rewrite (rn_k_cons pl x NX) in *.
    pose proof (byte_range x) as XR.
    pose proof (Z.mod_pos_bound (bv_unsigned x) 48 ltac:(lia)) as XM.
    carve_frame 32%nat ST.
    do 6 step.
    rewrite (unsigned_lit c) by lia. rewrite land7 by lia.
    step. if_false.
    do 3 step.
    rewrite eqb_lit by lia.
    if_false.
    do 5 step.
    rewrite ltu_lit by lia. ltb_dec.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (first_byte mm p pl x PB NX) as RD end.
    do 9 step.
    lazymatch goal with |- context [Z.land ?T 255] => change (Z.land T 255) with (m48 (bv_unsigned (zxb x))) end.
    rewrite zxb_unsigned, m48_val by exact XR.
    do 2 step.
    destruct (Z.ltb_spec (bv_unsigned x mod 48) (Z.of_nat (length pl) + -1)) as [LT|GE].
    + assert (BC : bv_ltu (Z_to_bv 64 (bv_unsigned x mod 48)) (Z_to_bv 64 (Z.of_nat (length pl) + -1)) = true)
        by (rewrite ltu_lit by lia; apply Z.ltb_lt; exact LT).
      rewrite BC; cbv iota.
      rn_mid.
    + assert (BC : bv_ltu (Z_to_bv 64 (bv_unsigned x mod 48)) (Z_to_bv 64 (Z.of_nat (length pl) + -1)) = false)
        by (rewrite ltu_lit by lia; apply Z.ltb_ge; exact GE).
      rewrite BC; cbv iota.
      step.
      rn_mid.
Qed.

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Import OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Reusable.YK11.
Local Open Scope Z_scope.

Lemma canon_mkst_cf : forall regs pc mem ro,
  canonical_register_state (mkst regs pc mem ro) = MS (mkR_of regs) fp_regs pc fp_csr None mem ro.
Proof. reflexivity. Qed.

Lemma eqv_mkst : forall can ms R pc m ro, can = mkst R pc m ro -> ms_eqv can ms ->
  ms = mkst (ms_regs ms) pc m ro /\ forall r, getr (ms_regs ms) r = getr R r.
Proof.
  intros can ms R pc m ro -> H. destruct ms as [R' F' pc' sv' rv' fc' m' ro'].
  destruct H as (HR & HF & HP & HS & HV & HC & HM & HO). cbn in *. subst. split; [reflexivity|].
  intros r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  symmetry. apply HR. rewrite <- bv_eqb0_is_x0. exact E.
Qed.

Lemma head_canon_cf : forall regs mem ro lo c p (pl : list byte),
  getr regs 10 = Z_to_bv 64 c -> c mod 8 = 0 ->
  rw_cells rsegs mem c [C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (Z.of_nat (length pl)))] ->
  bytes_at rsegs mem p pl -> 0 <= p < 2 ^ 64 ->
  (pl <> [] -> 1 <= p /\ p + Z.of_nat (length pl) <= lo) ->
  stk rsegs mem lo (bv_unsigned (getr regs 2)) -> lo + 32 <= bv_unsigned (getr regs 2) ->
  bv_unsigned (getr regs 2) <= c ->
  evt rsegs
    (fun ms' => exists m', ms' = mkst (ms_regs ms') (Z_to_bv 64 MALLOC) m' ro /\
       getr (ms_regs ms') 1 = Z_to_bv 64 0x13800 /\
       getr (ms_regs ms') 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32) /\
       getr (ms_regs ms') 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1) /\
       getr (ms_regs ms') 9 = Z_to_bv 64 (rn_k pl) /\
       getr (ms_regs ms') 10 = Z_to_bv 64 (rn_k pl + 1) /\
       (forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr (ms_regs ms') (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       munch [(bv_unsigned (getr regs 2) + -32, bv_unsigned (getr regs 2)); (c, c + 16)] mem m' /\
       wmono rsegs mem m' /\
       rw_cells rsegs m' (bv_unsigned (getr regs 2) + -32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] /\
       rw_cells rsegs m' c [C8 (Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl));
                            C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))] /\
       stk rsegs m' lo (bv_unsigned (getr regs 2) + -32))
    (canonical_register_state (mkst regs (Z_to_bv 64 READ_NAME) mem ro)).
Proof.
  intros regs mem ro lo c p pl A0 CA CU PB HP PL ST LO SPC.
  rewrite canon_mkst_cf. unfold mkR_of.
  eapply evt_mono.
  { apply rn_head_cf with (F := fp_regs) (fc := fp_csr) (m := mem) (ro := ro) (lo := lo) (c := c) (p := p) (pl := pl);
      [exact A0 | exact CA | exact CU | exact PB | exact HP | exact PL | exact ST | exact LO | exact SPC]. }
  intros ms' (s0' & s1' & a0' & a1' & a2' & a3' & a4' & a5' & cp & cn & m' & -> & MU & WM & FR & CU' & ST' & E0 & E1 & E2 & E3 & E4).
  subst s0' s1' a0' cp cn.
  exists m'. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr.
    assert (Hr' : r = 3 \/ r = 4 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                  r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact FR|]. split; [exact CU'|]. exact ST'.
Qed.

Lemma tail_canon_cf : memcpy_contract -> forall regs mem (s k src sp2 : Z) (name j1 j2 : list byte) (rao s0o s1o s2o : word),
  getr regs 10 = Z_to_bv 64 s -> getr regs 8 = Z_to_bv 64 src -> getr regs 9 = Z_to_bv 64 k ->
  getr regs 2 = Z_to_bv 64 sp2 -> 0 <= sp2 < 2 ^ 64 ->
  0 < s -> 0 <= k -> s + k + 1 <= sp2 -> src < 2 ^ 64 ->
  (src + k <= s \/ s + k <= src) ->
  bytes_at rsegs mem src name -> Z.of_nat (length name) = k ->
  rw_cells rsegs mem s [CB (Z.to_nat k) j1] -> rw_cells rsegs mem (s + k) [CB 1 j2] ->
  rw_cells rsegs mem sp2 [C8 s2o; C8 s1o; C8 s0o; C8 rao] ->
  ro_agree rsegs mem ->
  (forall i, 0 <= i < k + 1 -> ro_addr rsegs (wa (s + i)) = false) ->
  evt rsegs
    (fun ms' => exists m', ms' = mkst (ms_regs ms') (ret_pc rao) m' (PropExec.seg_rom rsegs) /\
       getr (ms_regs ms') 2 = Z_to_bv 64 (sp2 + 32) /\
       getr (ms_regs ms') 8 = s0o /\ getr (ms_regs ms') 9 = s1o /\ getr (ms_regs ms') 10 = Z_to_bv 64 s /\
       getr (ms_regs ms') 18 = s2o /\
       (forall r, r = 3 \/ r = 4 \/ 19 <= r <= 27 -> getr (ms_regs ms') (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
       munch [(s, s + k + 1)] mem m' /\ wmono rsegs mem m' /\ ro_agree rsegs m' /\
       bytes_at rsegs m' s (name ++ [Z_to_bv 8 0]) /\
       rw_cells rsegs m' sp2 [C8 s2o; C8 s1o; C8 s0o; C8 rao])
    (canonical_register_state (mkst regs (Z_to_bv 64 0x13800) mem (PropExec.seg_rom rsegs))).
Proof.
  intros MEMCPY regs mem s k src sp2 name j1 j2 rao s0o s1o s2o A0 S0 S1 SP R2 SPOS K0 SB SRCR DJ NB NL C1 C2 FR RA RO.
  rewrite canon_mkst_cf. unfold mkR_of.
  replace (LinuxProcessSemantics.Riscv.Sem.reg_get regs 2) with (Z_to_bv 64 sp2) by (symmetry; exact SP).
  eapply evt_mono.
  { apply (rn_tail MEMCPY) with (F := fp_regs) (fc := fp_csr) (m := mem) (s := s) (k := k) (src := src) (name := name)
      (j1 := j1) (j2 := j2) (rao := rao) (s0o := s0o) (s1o := s1o) (s2o := s2o);
      [exact A0 | exact S0 | exact S1 | exact SPOS | exact K0 | rewrite unsigned_lit by lia; exact SB | exact SRCR |
       exact DJ | exact NB | exact NL | exact C1 | exact C2 | rewrite unsigned_lit by lia; exact FR | exact RA | exact RO]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & pc' & m' & -> & EPC &
              MU & WM & MI' & NM & FR').
  subst pc'. rewrite unsigned_lit in FR' by lia.
  exists m'. split; [reflexivity|].
  split; [rewrite unsigned_lit by lia; reflexivity|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr.
    assert (Hr' : r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/
                  r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]; reflexivity. }
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact NM|]. exact FR'.
Qed.

Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem read_name_holds_cf : malloc_contract_ag B API -> memcpy_contract -> read_name_contract_cf B API.
Proof.
  intros MALLOCH MEMCPY. unfold read_name_contract_cf.
  intros L A regs mem md c p pl b SEGS MPC ERRL CP INIT A0 CAL SPC CUR CWR PR PAY PBLK RAG ROK ROOM.
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_value as ACV.
  pose proof (rn_k_range pl) as KR.
  unfold call_pre_k in CP.
  destruct CP as (HMR & HWF & HBD & HRA & HAL & HCE & H63 & HWS & HTP & HWE & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (HH & HLZ & HMT).
  unfold spZ in *. unfold ALLOC_STACK in *.
  unfold malloc_contract_ag in MALLOCH. rewrite SEGS in MALLOCH.
  rewrite SEGS in CUR, CWR, PAY, RAG, HWS, HWE. rewrite SEGS.
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. unfold bv_modulus in RSP.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in RSP.
  assert (PLB : pl <> [] -> exists a len, In (a, len) (blocks L A) /\ a <= p /\ p + Z.of_nat (length pl) <= a + len /\
                  4096 <= a /\ a + len <= YM05.alloc_ceiling).
  { intros NE. destruct (PBLK NE) as (a & len & Hin & H1 & H2). destruct (blocks_in _ _ _ _ Hin) as (q & Eq & Hq).
    pose proof (mr_blocks_range _ _ LAWS _ _ _ _ _ _ HMR Hq) as R. subst a.
    exists (ptr_addr L q), len. repeat split; first [exact Hin | lia]. }
  eapply (evt_SRcf_canon_r B ltac:(segs_tac)); [ | exact HH | exact HLZ | ].
  { apply (head_canon_cf regs mem _ (bv_unsigned (getr regs 2) - (32 + 8192)) c p pl).
    - exact A0.
    - exact CAL.
    - split; [split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact CUR] | exact CWR].
    - exact PAY.
    - exact PR.
    - intros NE. destruct (PLB NE) as (a & len & _ & H1 & H2 & H3 & H4). split; lia.
    - apply stk_high; [lia | lia | intros a Ha; apply HWS; lia].
    - lia.
    - exact SPC. }
  intros ms1 (can1 & HQ1 & EQ1).
  destruct HQ1 as (m1 & E1 & G1 & G2 & G8 & G9 & G10 & GR & MU1 & WM1 & FR1 & CU1 & ST1).
  destruct (eqv_mkst _ _ _ _ _ _ E1 EQ1) as [EM1 GE1].
  rewrite EM1. set (R1 := ms_regs ms1) in *. clearbody R1.
  assert (Q1 : getr R1 1 = Z_to_bv 64 0x13800) by (rewrite GE1; exact G1).
  assert (Q2 : getr R1 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32)) by (rewrite GE1; exact G2).
  assert (Q8 : getr R1 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1)) by (rewrite GE1; exact G8).
  assert (Q9 : getr R1 9 = Z_to_bv 64 (rn_k pl)) by (rewrite GE1; exact G9).
  assert (Q10 : getr R1 10 = Z_to_bv 64 (rn_k pl + 1)) by (rewrite GE1; exact G10).
  assert (QR : forall r, r = 3 \/ r = 4 \/ 18 <= r <= 27 -> getr R1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
    by (intros r Hr; rewrite GE1; exact (GR r Hr)).
  clear GE1 G1 G2 G8 G9 G10 GR E1 EQ1 EM1 can1 ms1.
  assert (MR1 : aa_MR API L A m1 md).
  { apply (mr_frame _ _ LAWS L A mem m1 md md HMR).
    - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) as Hl.
      mb MU1.
    - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR Ho) as Hl.
      exists x. rewrite <- Hx. apply MU1. rewrite unsigned_lit by lia. outs.
    - intros q n0 i Hq Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as ([x Hx] & H1 & H2 & _).
      exists x. rewrite <- Hx. apply MU1. rewrite unsigned_lit by lia. outs.
    - reflexivity.
    - exact HH.
    - exact HLZ.
    - exact HMT. }
  assert (RA1 : ro_agree rsegs m1).
  { intros x Hx. pose proof (ro_low x Hx) as Hl. pose proof (bv_unsigned_in_range 64 x) as Rx.
    unfold mrd. rewrite (MU1 x ltac:(outs)). exact (RAG x Hx). }
  eapply (SRcf_bind B).
  { replace (Z_to_bv 64 MALLOC) with (Z_to_bv 64 (ms_malloc B)) by (rewrite MPC; reflexivity).
    apply (MALLOCH L A R1 m1 md (rn_k pl + 1) b).
    - unfold call_pre, spZ. rewrite Q2, unsigned_lit by lia. rewrite SEGS. unfold ALLOC_STACK.
      split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
      split; [rewrite Q1; apply ret_ok_even; rewrite unsigned_lit by lia; reflexivity|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply WM1; apply HWS; lia|].
      split; [rewrite <- HTP; exact (QR 4 ltac:(lia))|].
      split; [intros a Ha; apply WM1; apply HWE; exact Ha|].
      intros E. rewrite INIT in E. discriminate.
    - exact RA1.
    - exact Q10.
    - exact ROK.
    - exact ROOM. }
  intros c2 RET.
  destruct RET as (L' & A' & regs2 & mem2 & md2 & s & -> & CPOST & A0s & SNZ & S16 & FRESH & BLKS & KEPT & RA2 & GK &
                   UBK & INIT' & REGL & ROK').
  rewrite Q1, SEGS. rewrite SEGS in RA2.
  unfold call_post_k in CPOST.
  destruct CPOST as (MR2 & WF2 & BD2 & LL2 & PA2 & RP2 & VM2 & FRM2 & BK2 & SCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ MR2) as (HH2 & HLZ2 & HMT2).
  destruct FRESH as (F1 & F2 & F3).
  destruct BLKS as (b1 & b2 & BL' & BL).
  assert (NBin : In (s, rn_k pl + 1) (blocks L' A')) by (rewrite BL'; apply in_or_app; right; left; reflexivity).
  destruct (blocks_in _ _ _ _ NBin) as (qn & Eqn & Hqn).
  assert (NBP : forall i, 0 <= i < rn_k pl + 1 -> present mem2 (s + i) /\ ~ owned B L' A' (s + i)).
  { intros i Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR2 Hqn Hi) as (H1 & _ & _ & H4).
    rewrite Eqn in H1, H4. split; assumption. }
  assert (DISJ : forall a len, In (a, len) (blocks L A) -> s + (rn_k pl + 1) <= a \/ a + len <= s).
  { intros a len Hin. rewrite BL in Hin. pose proof (mr_blocks_disjoint _ _ LAWS _ _ _ _ MR2) as PW.
    rewrite BL' in PW. exact (pw_mid b1 b2 (s, rn_k pl + 1) (a, len) PW Hin). }
  assert (P8 : getr regs2 8 = Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1)).
  { rewrite <- Q8. exact (RP2 8 ltac:(unfold callee_saved; lia)). }
  assert (P9 : getr regs2 9 = Z_to_bv 64 (rn_k pl)).
  { rewrite <- Q9. exact (RP2 9 ltac:(unfold callee_saved; lia)). }
  assert (P2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned (getr regs 2) + -32)).
  { rewrite <- Q2. exact (RP2 2 ltac:(unfold callee_saved; lia)). }
  assert (NAME : bytes_at rsegs mem2 (p + Z.min (Z.of_nat (length pl)) 1) (bsub pl 1 (rn_k pl))).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - apply length_zero_iff_nil in E0. subst pl. cbn. apply bytes_at_nil. lia.
    - assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
      destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4).
      assert (PAY1 : bytes_at rsegs m1 p pl).
      { apply (bytes_at_pt rsegs mem m1 p pl PAY). intros i Hi.
        mb MU1. }
      assert (PAY2 : bytes_at rsegs mem2 p pl).
      { apply (bytes_at_pt rsegs m1 mem2 p pl PAY1). intros i Hi. rewrite <- SEGS.
        replace (p + i) with (a + (p - a + i)) by lia. apply (KEPT a len (p - a + i) Hin (fun H => H)). lia. }
      replace (p + Z.min (Z.of_nat (length pl)) 1) with (p + 1) by lia.
      apply bytes_at_sub; [exact PAY2 | lia | lia | lia]. }
  assert (NL : Z.of_nat (length (bsub pl 1 (rn_k pl))) = rn_k pl).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - apply length_zero_iff_nil in E0. subst pl. reflexivity.
    - rewrite bsub_length by lia. lia. }
  assert (DJ : p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl <= s \/ s + rn_k pl <= p + Z.min (Z.of_nat (length pl)) 1).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0].
    - rewrite (rn_k_nil pl E0). lia.
    - assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
      destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4). pose proof (DISJ a len Hin). lia. }
  assert (STB : stk rsegs mem2 s (s + (rn_k pl + 1))).
  { apply stk_present; [lia | lia |]. intros a Ha. replace a with (s + (a - s)) by lia.
    exact (proj1 (NBP (a - s) ltac:(lia))). }
  destruct (stk_carve rsegs mem2 s (s + (rn_k pl + 1)) 1 STB ltac:(lia)) as [STB1 [j2 C2]].
  replace (s + (rn_k pl + 1) - Z.of_nat 1) with (s + rn_k pl) in STB1, C2 by lia.
  destruct (stk_carve rsegs mem2 s (s + rn_k pl) (Z.to_nat (rn_k pl)) STB1 ltac:(lia)) as [_ [j1 C1]].
  replace (s + rn_k pl - Z.of_nat (Z.to_nat (rn_k pl))) with s in C1 by lia.
  assert (FRMx : forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> bv_unsigned (getr regs 2) + -32 <= a ->
                  mbyte rsegs mem2 a = mbyte rsegs m1 a /\ (writable_at rsegs m1 a -> writable_at rsegs mem2 a)).
  { intros a Ha Hb.
    assert (N1 : ~ owned B L A a) by (intros Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR1 Ho); lia).
    assert (N2 : ~ owned B L' A' a) by (intros Ho; pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho); lia).
    assert (N3 : ~ scratch_k B ALLOC_STACK R1 a)
      by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
    destruct (FRM2 a (or_introl Ha) N1 N2 N3 (fun H => H)) as [E1 E2].
    rewrite SEGS in E1, E2. split; [exact E1 | apply E2]. }
  assert (FR2 : rw_cells rsegs mem2 (bv_unsigned (getr regs 2) + -32)
                  [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { apply (rw_cells_pt rsegs m1 mem2 _ _ FR1). intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    apply FRMx; lia. }
  assert (CU2 : rw_cells rsegs mem2 c [C8 (Z_to_bv 64 (p + Z.min (Z.of_nat (length pl)) 1 + rn_k pl));
                  C8 (Z_to_bv 64 (Z.of_nat (length pl) - Z.min (Z.of_nat (length pl)) 1 - rn_k pl))]).
  { pose proof (rw_cells_bound rsegs m1 c _ CU1) as CB. cbn [cells_size csize Nat.add] in CB.
    apply (rw_cells_pt rsegs m1 mem2 _ _ CU1). intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    apply FRMx; lia. }
  assert (ROB : forall i, 0 <= i < rn_k pl + 1 -> ro_addr rsegs (wa (s + i)) = false).
  { intros i Hi. unfold ro_addr. rewrite wa_unsigned by lia.
    rewrite (no_seg B (s + i) SEGS (or_intror (F3 i Hi))). reflexivity. }
  assert (SRCR : p + Z.min (Z.of_nat (length pl)) 1 < 2 ^ 64).
  { destruct (Nat.eq_dec (length pl) 0) as [E0|E0]; [lia|].
    assert (NE : pl <> []) by (intros E; subst pl; cbn in E0; lia).
    destruct (PLB NE) as (a & len & Hin & H1 & H2 & H3 & H4). lia. }
  change (YK11.seg_rom rsegs) with (PropExec.seg_rom rsegs).
  eapply (evt_SRcf_canon_r B ltac:(segs_tac)); [ | exact HH2 | exact HLZ2 | ].
  { apply (tail_canon_cf MEMCPY regs2 mem2 s (rn_k pl) (p + Z.min (Z.of_nat (length pl)) 1)
             (bv_unsigned (getr regs 2) + -32) (bsub pl 1 (rn_k pl)) j1 j2 (getr regs 1) (getr regs 8) (getr regs 9)
             (getr regs 18)); try assumption; lia. }
  intros ms3 (can3 & HQ3 & EQ3).
  destruct HQ3 as (m3 & E3 & T2 & T8 & T9 & T10 & T18 & TR & MU3 & WM3 & RA3 & NM3 & FR3).
  destruct (eqv_mkst _ _ _ _ _ _ E3 EQ3) as [EM3 GE3].
  rewrite EM3. set (R3 := ms_regs ms3) in *. clearbody R3.
  apply (SRcf_ret B).
  exists L', A', R3, m3, md2, s.
  split. { rewrite (ret_pc_ok _ HRA). reflexivity. }
  split. { exact RA3. }
  split.
  { unfold guard_kept. intros i Hi.
    assert (GO : owned B L A (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    assert (GO' : owned B L' A' (ms_got_guard B + i)) by (right; unfold static_owned; do 4 right; left; lia).
    pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ HMR GO) as GL.
    assert (NI : ~ (s <= ms_got_guard B + i < s + rn_k pl + 1)).
    { intros Hr. destruct (NBP (ms_got_guard B + i - s) ltac:(lia)) as [_ Hn].
      replace (s + (ms_got_guard B + i - s)) with (ms_got_guard B + i) in Hn by lia. exact (Hn GO'). }
    rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (ms_got_guard B + i) MU3 ltac:(outs) ltac:(lia))).
    rewrite (GK i Hi).
    mb MU1. }
  split.
  { unfold call_post_k.
    split.
    { apply (mr_frame _ _ LAWS L' A' mem2 m3 md2 md2 MR2).
      - intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho) as Hl.
        assert (NI : ~ (s <= a < s + rn_k pl + 1)).
        { intros Hr. destruct (NBP (a - s) ltac:(lia)) as [_ Hn]. replace (s + (a - s)) with a in Hn by lia.
          exact (Hn Ho). }
        mb MU3.
      - intros a Ho [x Hx]. pose proof (mr_owned_low _ _ LAWS _ _ _ _ _ MR2 Ho) as Hl.
        assert (NI : ~ (s <= a < s + rn_k pl + 1)).
        { intros Hr. destruct (NBP (a - s) ltac:(lia)) as [_ Hn]. replace (s + (a - s)) with a in Hn by lia.
          exact (Hn Ho). }
        exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
      - intros q n0 i Hq Hi. destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ MR2 Hq Hi) as ([x Hx] & H1 & H2 & _).
        destruct (Z.ltb_spec (ptr_addr L' q + i) s) as [Lt|Ge].
        + exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
        + destruct (Z.ltb_spec (ptr_addr L' q + i) (s + rn_k pl + 1)) as [Lt2|Ge2].
          * replace (ptr_addr L' q + i) with (s + (ptr_addr L' q + i - s)) by lia.
            apply (present_of_bytes B m3 s _ SEGS NM3).
            { intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply F3. lia. }
            rewrite length_app. cbn [length]. lia.
          * exists x. rewrite <- Hx. apply MU3. rewrite unsigned_lit by lia. outs.
      - reflexivity.
      - exact HH2.
      - exact HLZ2.
      - exact HMT2. }
    split; [exact WF2|]. split; [exact BD2|]. split; [exact LL2|]. split; [exact PA2|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (Hc : r = 2 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 3 \/ r = 4 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                   r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hc as [->|[->|[->|[->|Hc]]]].
      - rewrite GE3. etransitivity; [exact T2|].
        replace (bv_unsigned (getr regs 2) + -32 + 32) with (bv_unsigned (getr regs 2)) by lia.
        exact (Z_to_bv_bv_unsigned (getr regs 2)).
      - rewrite GE3. exact T8.
      - rewrite GE3. exact T9.
      - rewrite GE3. exact T18.
      - assert (Hr3 : r = 3 \/ r = 4 \/ 19 <= r <= 27) by lia.
        rewrite GE3, (TR r Hr3), (RP2 r ltac:(unfold callee_saved; lia)). apply QR. lia. }
    split; [exact VM2|].
    split.
    { intros a Ha Ho Ho' Hs He. unfold scratch_k, spZ in Hs. unfold rn_writes in He.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Ha as [Ha|Ha]; [lia | pose proof (img_low B a SEGS Ha); lia]).
      assert (AL : YM05.alloc_ceiling <= a \/ a < 140735332483072)
        by (destruct Ha as [Ha|Ha]; [left; lia | right; pose proof (img_low B a SEGS Ha); lia]).
      destruct (munch_byte (ms_segs B) _ _ _ a MU3 ltac:(outs) AR) as [E3a E3b].
      assert (N3 : ~ scratch_k B ALLOC_STACK R1 a)
        by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
      destruct (FRM2 a Ha Ho Ho' N3 (fun H => H)) as [E2a E2b].
      destruct (munch_byte (ms_segs B) _ _ _ a MU1 ltac:(outs) AR) as [E1a E1b].
      split; [rewrite E3a, E2a, E1a; reflexivity | tauto]. }
    split.
    { intros q n0 i Hq Hq' Hi.
      assert (Hb : In (ptr_addr L q, n0) (blocks L A))
        by (unfold blocks; exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hq)).
      destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as (_ & B1 & B2 & _).
      pose proof (DISJ _ _ Hb) as D.
      rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (ptr_addr L q + i) MU3 ltac:(outs) ltac:(lia))).
      rewrite (BK2 q n0 i Hq Hq' Hi).
      mb MU1. }
    { intros a Hs. unfold scratch_k, spZ in Hs.
      assert (Hcase : (bv_unsigned (getr regs 2) - 32 <= a < bv_unsigned (getr regs 2)) \/ scratch_k B ALLOC_STACK R1 a)
        by (unfold scratch_k, spZ; rewrite Q2, unsigned_lit by lia; unfold ALLOC_STACK; lia).
      rewrite SEGS. apply WM3.
      destruct Hcase as [Hf|Hk].
      - apply (proj2 (FRMx a ltac:(lia) ltac:(lia))). apply WM1. apply HWS. lia.
      - pose proof (SCR2 a Hk) as W. rewrite SEGS in W. exact W. } }
  split. { rewrite GE3. exact T10. }
  split. { lia. }
  split. { split; [lia | split; [lia | exact F3]]. }
  split. { exists b1, b2. split; assumption. }
  split. { exact NM3. }
  split.
  { destruct CU2 as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
    pose proof (bytes_at_bound rsegs mem2 c _ HB) as CB.
    apply (bytes_at_pt rsegs mem2 m3 c _ HB). intros i Hi.
    mb MU3. }
  split.
  { unfold blocks_kept. intros a len i Hin _ Hi.
    destruct (blocks_in _ _ _ _ Hin) as (q & Eq & Hq).
    destruct (mr_blocks _ _ LAWS _ _ _ _ _ _ _ HMR Hq Hi) as (_ & B1 & B2 & _). rewrite Eq in B1, B2.
    pose proof (DISJ _ _ Hin) as D.
    rewrite (proj1 (munch_byte (ms_segs B) _ _ _ (a + i) MU3 ltac:(outs) ltac:(lia))).
    rewrite (KEPT a len i Hin (fun H => H) Hi).
    mb MU1. }
  split; [exact INIT' | exact ROK'].
Qed.

End P.
