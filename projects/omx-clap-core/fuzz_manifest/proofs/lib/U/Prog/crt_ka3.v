From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem printf_facts_c snprintf_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import crt_text crt_ka0 crt_snp crt_whole.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition body_regs (s0 s1 s2 s7 s8 : word) (u : list byte) (k : nat) (res : Z) : Prop :=
  s1 = Z_to_bv 64 (3 * Z.of_nat (length u) + 64) /\ s2 = Z_to_bv 64 res /\
  s8 = Z_to_bv 64 (bv_unsigned s0 + Z.of_nat k) /\ s7 = Z_to_bv 64 (Z.of_nat k) /\
  (1 <= k < length u)%nat /\ (length u <= 255)%nat /\ 0 < bv_unsigned s0 /\ bv_unsigned s0 + 256 < 2 ^ 64.

Lemma zb_skip : forall (u : list byte) k, skipn k (zbytes u) = zbytes (skipn k u).
Proof.
  intros u k. unfold zbytes. revert u. induction k as [|k IH]; intros [|b u]; cbn [skipn map]; auto.
Qed.

Lemma crt_t2 : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte) (k : nat),
  body_regs s0 s1 s2 s7 s8 u k res -> a0 = Z_to_bv 64 1 -> s11 = Z_to_bv 64 1 -> s4 = Z_to_bv 64 0x10416 ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x1355c) sp gp tp t0' t1' t2' s0 s1 s2 s0 a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13e10) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_t2 (zbytes u) k)) (skipn (length (txt_t2 (zbytes u) k) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13530) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk k (-> & -> & -> & -> & Hk & Hu & HU0 & HU1) -> -> -> FRM
    (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt) (CU & U0 & UL & UD).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  assert (UK : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
  assert (US3 : bv_unsigned (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat k)) = bv_unsigned s0 + Z.of_nat k) by (apply unsigned_lit; lia).
  assert (LK : (k <= length (zbytes u))%nat) by (rewrite length_zb; lia).
  zstep. if_lit.
  do 7 zstep.
  assert (LT : (length (txt_t2 (zbytes u) k) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite (len_t2 _ _ LK), length_zb; lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_t2 (zbytes u) k))
    by (apply nz_t2; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_t2) (ps := ps_t2)
        (args := [AInt (Z.of_nat k); APtr (zbytes u); APtr (skipn k (zbytes u))])
        (T := txt_t2 (zbytes u) k) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66582)) with FMT_T2. exact (proj1 (proj2 (proj2 (proj2 (proj2 CS))))).
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_t2.
    - split; [|split; [|split; [|exact I]]].
      + cbn [pf_arg_ok]. rewrite UK. split; [lia | reflexivity].
      + apply aptr_ok with (sl := us); [exact CU | lia | left; lia |]. rewrite URes, USz. exact UD.
      + rewrite zb_skip. apply aptr_ok with (sl := us).
        * rewrite US3. apply cstr_sfx; [exact CU | lia].
        * rewrite US3. lia.
        * rewrite US3, length_skipn. left. lia.
        * rewrite US3, length_skipn, URes, USz. lia.
    - exact (text_t2 (zbytes u) k LK).
    - rewrite URes, USz. exact BLK.
    - rewrite USz. lia.
    - rewrite (len_t2 _ _ LK), length_zb. lia.
    - rewrite URes. lia.
    - rewrite URes, USz. left. lia.
    - rewrite URes, USz. exact RI.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - exact S63.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GC. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m1 &
    E & MU1 & WM1 & MI1 & TMp & FRM1 & _ & _ & BT).
  subst ms'.
  rewrite USz, URes in MU1, BT. rewrite (firstn_all2 _ LT) in MU1, BT.
  replace (ret_pc (Z_to_bv 64 0x13550)) with (Z_to_bv 64 0x13550) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m1 res (pf_bytes (txt_t2 (zbytes u) k)) (skipn (length (txt_t2 (zbytes u) k) + 1) junk)).
  { apply (text_cstr m m1 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK BT MU1);
      [| exact NZ | rewrite (len_t2 _ _ LK), length_zb; lia].
    cbn [disjoint_from]. rewrite (len_t2 _ _ LK), length_zb. lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m1. split; [reflexivity|].
  split; [exact FRM1|]. split.
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. rewrite (len_t2 _ _ LK), length_zb. lia. }
  split; [exact WM1|]. split; [exact MI1 | exact TC].
Qed.

Lemma crt_t3 : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte) (k : nat),
  body_regs s0 s1 s2 s7 s8 u k res -> a0 = Z_to_bv 64 1 -> s11 = Z_to_bv 64 1 -> s5 = Z_to_bv 64 0x103bf ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x13588) sp gp tp t0' t1' t2' s0 s1 s2 s0 a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13e10) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_t3 (zbytes u) k)) (skipn (length (txt_t3 (zbytes u) k) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1355c) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk k (-> & -> & -> & -> & Hk & Hu & HU0 & HU1) -> -> -> FRM
    (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt) (CU & U0 & UL & UD).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  assert (UK : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
  assert (US3 : bv_unsigned (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat k)) = bv_unsigned s0 + Z.of_nat k) by (apply unsigned_lit; lia).
  assert (LK : (k <= length (zbytes u))%nat) by (rewrite length_zb; lia).
  zstep. if_lit.
  do 7 zstep.
  assert (LT : (length (txt_t3 (zbytes u) k) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite (len_t3 _ _ LK), length_zb; lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_t3 (zbytes u) k))
    by (apply nz_t3; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_t3) (ps := ps_t3)
        (args := [AInt (Z.of_nat k); APtr (zbytes u); APtr (skipn k (zbytes u))])
        (T := txt_t3 (zbytes u) k) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66495)) with FMT_T3. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CS)))))).
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_t3.
    - split; [|split; [|split; [|exact I]]].
      + cbn [pf_arg_ok]. rewrite UK. split; [lia | reflexivity].
      + apply aptr_ok with (sl := us); [exact CU | lia | left; lia |]. rewrite URes, USz. exact UD.
      + rewrite zb_skip. apply aptr_ok with (sl := us).
        * rewrite US3. apply cstr_sfx; [exact CU | lia].
        * rewrite US3. lia.
        * rewrite US3, length_skipn. left. lia.
        * rewrite US3, length_skipn, URes, USz. lia.
    - exact (text_t3 (zbytes u) k LK).
    - rewrite URes, USz. exact BLK.
    - rewrite USz. lia.
    - rewrite (len_t3 _ _ LK), length_zb. lia.
    - rewrite URes. lia.
    - rewrite URes, USz. left. lia.
    - rewrite URes, USz. exact RI.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - exact S63.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GC. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m1 &
    E & MU1 & WM1 & MI1 & TMp & FRM1 & _ & _ & BT).
  subst ms'.
  rewrite USz, URes in MU1, BT. rewrite (firstn_all2 _ LT) in MU1, BT.
  replace (ret_pc (Z_to_bv 64 0x1357c)) with (Z_to_bv 64 0x1357c) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m1 res (pf_bytes (txt_t3 (zbytes u) k)) (skipn (length (txt_t3 (zbytes u) k) + 1) junk)).
  { apply (text_cstr m m1 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK BT MU1);
      [| exact NZ | rewrite (len_t3 _ _ LK), length_zb; lia].
    cbn [disjoint_from]. rewrite (len_t3 _ _ LK), length_zb. lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m1. split; [reflexivity|].
  split; [exact FRM1|]. split.
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. rewrite (len_t3 _ _ LK), length_zb. lia. }
  split; [exact WM1|]. split; [exact MI1 | exact TC].
Qed.

Lemma crt_t1x : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte) (k : nat),
  body_regs s0 s1 s2 s7 s8 u k res -> a0 = Z_to_bv 64 1 -> s11 = Z_to_bv 64 1 -> s6 = Z_to_bv 64 0x10391 ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x135b4) sp gp tp t0' t1' t2' s0 s1 s2 s0 a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13c08) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_t1x (zbytes u) k)) (skipn (length (txt_t1x (zbytes u) k) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13588) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk k (-> & -> & -> & -> & Hk & Hu & HU0 & HU1) -> -> -> FRM
    (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt) (CU & U0 & UL & UD).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  assert (UK : bv_unsigned (Z_to_bv 64 (Z.of_nat k)) = Z.of_nat k) by (apply unsigned_lit; lia).
  assert (US3 : bv_unsigned (Z_to_bv 64 (bv_unsigned s0 + Z.of_nat k)) = bv_unsigned s0 + Z.of_nat k) by (apply unsigned_lit; lia).
  assert (LK : (k <= length (zbytes u))%nat) by (rewrite length_zb; lia).
  zstep. if_lit.
  do 7 zstep.
  assert (LT : (length (txt_t1x (zbytes u) k) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite (len_t1x _ _ LK), length_zb; lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_t1x (zbytes u) k))
    by (apply nz_t1x; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_t1x) (ps := ps_t1x)
        (args := [AInt (Z.of_nat k); APtr (zbytes u); APtr (skipn k (zbytes u))])
        (T := txt_t1x (zbytes u) k) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66449)) with FMT_T1X. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CS)))))).
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_t1x.
    - split; [|split; [|split; [|exact I]]].
      + cbn [pf_arg_ok]. rewrite UK. split; [lia | reflexivity].
      + apply aptr_ok with (sl := us); [exact CU | lia | left; lia |]. rewrite URes, USz. exact UD.
      + rewrite zb_skip. apply aptr_ok with (sl := us).
        * rewrite US3. apply cstr_sfx; [exact CU | lia].
        * rewrite US3. lia.
        * rewrite US3, length_skipn. left. lia.
        * rewrite US3, length_skipn, URes, USz. lia.
    - exact (text_t1x (zbytes u) k LK).
    - rewrite URes, USz. exact BLK.
    - rewrite USz. lia.
    - rewrite (len_t1x _ _ LK), length_zb. lia.
    - rewrite URes. lia.
    - rewrite URes, USz. left. lia.
    - rewrite URes, USz. exact RI.
    - exact ST.
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - exact S63.
    - exact FRM.
    - exact MI.
    - exact TM.
    - exact GG.
    - exact GC. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m1 &
    E & MU1 & WM1 & MI1 & TMp & FRM1 & _ & _ & BT).
  subst ms'.
  rewrite USz, URes in MU1, BT. rewrite (firstn_all2 _ LT) in MU1, BT.
  replace (ret_pc (Z_to_bv 64 0x135a8)) with (Z_to_bv 64 0x135a8) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m1 res (pf_bytes (txt_t1x (zbytes u) k)) (skipn (length (txt_t1x (zbytes u) k) + 1) junk)).
  { apply (text_cstr m m1 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK BT MU1);
      [| exact NZ | rewrite (len_t1x _ _ LK), length_zb; lia].
    cbn [disjoint_from]. rewrite (len_t1x _ _ LK), length_zb. lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m1. split; [reflexivity|].
  split; [exact FRM1|]. split.
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. rewrite (len_t1x _ _ LK), length_zb. lia. }
  split; [exact WM1|]. split; [exact MI1 | exact TC].
Qed.
