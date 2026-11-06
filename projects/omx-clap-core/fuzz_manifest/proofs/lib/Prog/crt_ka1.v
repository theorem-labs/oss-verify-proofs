From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem printf_facts_c snprintf_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_text crt_ka0 crt_snp crt_whole.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Lemma crt_wx : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte),
  a0 = Z_to_bv 64 1 -> s1 = Z_to_bv 64 (3 * Z.of_nat (length u) + 64) -> s2 = Z_to_bv 64 res ->
  (1 <= length u <= 255)%nat ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x133bc) sp gp tp t0' t1' t2' s0 s1 s2 s0 a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13a38) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_wholex (zbytes u))) (skipn (length (txt_wholex (zbytes u)) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13390) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk -> -> -> Hn FRM (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt)
    (CU & U0 & UL & UD).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  zstep. zstep. if_lit.
  do 6 zstep.
  assert (LT : (length (txt_wholex (zbytes u)) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite len_wholex, length_zb; lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_wholex (zbytes u)))
    by (apply nz_wholex; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_tx) (ps := ps_tx) (args := [APtr (zbytes u)])
        (T := txt_wholex (zbytes u)) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66200)) with FMT_TX. exact (proj1 (proj2 (proj2 CS))).
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_tx.
    - split; [|exact I]. apply aptr_ok with (sl := us); [exact CU | lia | left; lia |].
      rewrite URes, USz. exact UD.
    - exact (text_tx (zbytes u)).
    - rewrite URes, USz. exact BLK.
    - rewrite USz. lia.
    - rewrite len_wholex, length_zb. lia.
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
  replace (ret_pc (Z_to_bv 64 0x133b0)) with (Z_to_bv 64 0x133b0) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m1 res (pf_bytes (txt_wholex (zbytes u))) (skipn (length (txt_wholex (zbytes u)) + 1) junk)).
  { apply (text_cstr m m1 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK BT MU1); [| exact NZ | rewrite len_wholex, length_zb; lia].
    cbn [disjoint_from]. rewrite len_wholex, length_zb. lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m1. split; [reflexivity|].
  split; [exact FRM1|]. split.
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. rewrite len_wholex, length_zb. lia. }
  split; [exact WM1|]. split; [exact MI1 | exact TC].
Qed.

Lemma crt_init1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (j : list byte)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  s3 = Z_to_bv 64 1 ->
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = exit_state xra (bv_unsigned sp) gp tp t0 t1 t2 xs0 xs1 s2 a1 a2 a3 a4 a5 a6 a7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m j
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra -> FR HI.
  zstep. zstep. if_lit.
  eapply crt_exit; [exact FR | exact HI].
Qed.

Lemma crt_init : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z),
  s3 = Z_to_bv 64 n -> 2 <= n <= 255 -> bv_unsigned s0 + 256 < 2 ^ 64 ->
  evt rsegs (fun ms' => exists (a0' a1' a2' a3' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                    s2 (Z_to_bv 64 (bv_unsigned s0 + 1)) (Z_to_bv 64 0x1035d) (Z_to_bv 64 0x1041d)
                    (Z_to_bv 64 0x103bf) (Z_to_bv 64 0x10391) (Z_to_bv 64 1) (Z_to_bv 64 (n - 1))
                    (Z_to_bv 64 1) (Z_to_bv 64 62) t3 t4 t5 t6)
               F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x133bc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n
    -> Hn H0.
  zstep. zstep. if_false_by (bveq_ne (n + -1) 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  do 12 zstep.
  replace (n + -1) with (n - 1) by lia.
  apply evt_done. do 4 eexists. reflexivity.
Qed.

Lemma crt_next : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n k : Z),
  s3 = Z_to_bv 64 (bv_unsigned s0 + k) -> s8 = Z_to_bv 64 k -> s9 = Z_to_bv 64 (n - k) ->
  1 <= k -> k + 1 < n -> n <= 255 -> bv_unsigned s0 + 256 < 2 ^ 64 ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                    s2 (Z_to_bv 64 (bv_unsigned s0 + (k + 1))) s4 s5 s6 s7 (Z_to_bv 64 (k + 1)) (Z_to_bv 64 (n - (k + 1)))
                    s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x133f4) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n k
    -> -> -> H1 H2 H3 H4.
  assert (SW : bv_swrap 32 (k + 1) = k + 1).
  { apply bv_swrap_small. replace (bv_half_modulus 32) with 2147483648 by (vm_compute; reflexivity). lia. }
  do 4 zstep.
  if_true_by (f_equal negb (bveq_ne (n - k + -1) 0 ltac:(lia) ltac:(lia) ltac:(lia))).
  rewrite SW.
  replace (bv_unsigned s0 + k + 1) with (bv_unsigned s0 + (k + 1)) by lia.
  replace (n - k + -1) with (n - (k + 1)) by lia.
  apply evt_done. reflexivity.
Qed.

Lemma crt_last : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n k : Z) (j : list byte)
    (xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra : word),
  s9 = Z_to_bv 64 (n - k) -> 1 <= k -> k + 1 = n -> n <= 255 ->
  rw_cells rsegs m (bv_unsigned sp) (frame_cells j xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra) ->
  bv_unsigned sp + 112 < 2 ^ 64 ->
  evt rsegs (fun ms' => ms' = exit_state xra (bv_unsigned sp) gp tp t0 t1 t2 xs0 xs1 s2 a1 a2 a3 a4 a5 a6 a7
                                 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x134b4) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n k j
    xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xra -> H1 H2 H3 FR HI.
  do 4 zstep.
  if_false_by (f_equal negb (bveq_eq (n - k + -1) 0 ltac:(lia) ltac:(lia) ltac:(lia))).
  eapply crt_exit; [exact FR | exact HI].
Qed.
