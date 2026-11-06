From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes FP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem printf_facts_c snprintf_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import crt_text crt_ka0 crt_snp.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition snp_env (m : word -> option byte) (lo S res sz : Z) (junk : list byte) : Prop :=
  stk rsegs m lo S /\ lo + SNPRINTF_K <= S /\ IMG_END <= lo /\ S < 2 ^ 63 /\
  mem_inv rsegs m /\ crt_strings m /\
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ (exists canary, bytes_at rsegs m GUARD (le8 canary)) /\
  rw_cells rsegs m res [CB (Z.to_nat sz) junk] /\ 4096 <= res /\ res + sz <= lo /\
  pf_img_free res sz /\ MemNorm.task_mem rsegs m /\ S <= TASK_SIZE.

Definition u_env (m : word -> option byte) (lo res sz U : Z) (u us : list byte) : Prop :=
  cstr_at m U u us /\ 0 < U /\ U + Z.of_nat (length u) + 1 + Z.of_nat (length us) <= lo /\
  (U + Z.of_nat (length u) + 1 + Z.of_nat (length us) <= res \/ res + sz <= U).

Lemma crt_whole : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo res : Z) (u us junk : list byte),
  a0 = Z_to_bv 64 res -> s1 = Z_to_bv 64 (3 * Z.of_nat (length u) + 64) -> (1 <= length u <= 255)%nat ->
  frm0 fc -> snp_env m lo (bv_unsigned sp) res (3 * Z.of_nat (length u) + 64) junk ->
  u_env m lo res (3 * Z.of_nat (length u) + 64) (bv_unsigned s0) u us ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (Ft : bvmap 5 word) (fc' : bv 32) m',
      ms' = MS (mkR (Z_to_bv 64 0x13488) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) s0 a2' a3' a4' a5' a6' a7'
                    (Z_to_bv 64 res) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               Ft (Z_to_bv 64 0x13e10) fc' None m' (seg_rom rsegs) /\
      frm0 fc' /\ munch [(lo, bv_unsigned sp); (res, res + (3 * Z.of_nat (length u) + 64))] m m' /\
      wmono rsegs m m' /\ mem_inv rsegs m' /\
      cstr_at m' res (pf_bytes (txt_whole (zbytes u))) (skipn (length (txt_whole (zbytes u)) + 1) junk))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1345c) fc None m (seg_rom rsegs)).
Proof.
  intros SNP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo res u us junk -> -> Hn FRM (ST & LO & IE & S63 & MI & CS & GG & (canary & GC) & BLK & R4 & RL & RI & TM & SPt)
    (CU & U0 & UL & UD).
  pose proof (zr_word sp) as Rsp. unfold inr64 in Rsp.
  unfold IMG_END, SNPRINTF_K, RO_LO in *.
  assert (Hres : 0 <= res < 2 ^ 64) by lia.
  assert (URes : bv_unsigned (Z_to_bv 64 res) = res) by (apply unsigned_lit; lia).
  assert (T1 : 0 <= 3 * Z.of_nat (length u) + 64 < 2 ^ 64) by lia.
  assert (USz : bv_unsigned (Z_to_bv 64 (3 * Z.of_nat (length u) + 64)) = 3 * Z.of_nat (length u) + 64) by (apply unsigned_lit; exact T1).
  zstep. if_false_by (bveq_ne res 0 ltac:(lia) ltac:(lia) ltac:(lia)).
  do 7 zstep.
  assert (LT : (length (txt_whole (zbytes u)) <= Z.to_nat (3 * Z.of_nat (length u) + 64 - 1))%nat)
    by (rewrite len_whole, length_zb; lia).
  assert (NZ : Forall (fun c => 0 < c < 256) (txt_whole (zbytes u)))
    by (apply nz_whole; apply zb_nz; exact (proj1 (proj2 CU))).
  eapply evt_cut.
  { eapply SNP with (lo := lo) (canary := canary) (fmt := fmt_tw) (ps := ps_tw) (args := [APtr (zbytes u)])
        (T := txt_whole (zbytes u)) (junk := junk).
    - change (bv_unsigned (Z_to_bv 64 66372)) with FMT_TW. exact (proj1 (proj2 CS)).
    - vm_compute. discriminate.
    - vm_compute. discriminate.
    - exact parse_tw.
    - split; [|exact I]. apply aptr_ok with (sl := us); [exact CU | lia | left; lia |].
      rewrite URes, USz. exact UD.
    - exact (text_tw (zbytes u)).
    - rewrite URes, USz. exact BLK.
    - rewrite USz. lia.
    - rewrite len_whole, length_zb. lia.
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
  replace (ret_pc (Z_to_bv 64 0x1347c)) with (Z_to_bv 64 0x1347c) by (apply bv_eq; vm_compute; reflexivity).
  do 3 zstep.
  assert (TC : cstr_at m1 res (pf_bytes (txt_whole (zbytes u))) (skipn (length (txt_whole (zbytes u)) + 1) junk)).
  { apply (text_cstr m m1 res (3 * Z.of_nat (length u) + 64) junk _ _ BLK BT MU1); [| exact NZ | rewrite len_whole, length_zb; lia].
    cbn [disjoint_from]. rewrite len_whole, length_zb. lia. }
  apply evt_done. do 13 eexists. exists Ft, fc', m1. split; [reflexivity|].
  split; [exact FRM1|]. split.
  { eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside] in *. rewrite len_whole, length_zb. lia. }
  split; [exact WM1|]. split; [exact MI1 | exact TC].
Qed.
