(* lib/A/Prog/strchr_wrap.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8), re-run against the
   local-shadow statement FMss_strchr_wrap_c.v: the range check comes from chk_ok_of_loc (FMss_shv.v) and the post's
   shadow fact from shvis_kept; every other line is the original's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import strchr_wrap_c wrap_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMss_strchr_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.asan_region_is_poisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strchrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_strchrc.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module ARP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.asan_region_is_poisoned.
Module BzH := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strchrw.
Module RC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_strchrc.
Module BzR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_m2s.
Module BzP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.

Lemma find_byte_bz : forall c l, find_byte c l = BzSF.find_byte c l.
Proof. intros c l. induction l as [|b l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma chr_res_eq : forall A c str, c <> 0 -> strchr_val A c str = BzH.chr_res A c str.
Proof.
  intros A c str Hc. unfold strchr_val, strchr_res, BzH.chr_res.
  rewrite (proj2 (Z.eqb_neq c 0) Hc), find_byte_bz. reflexivity.
Qed.

Lemma chr_idx_eq : forall c str, strchrnul_idx c str = BzH.chr_idx c str.
Proof. intros c str. unfold strchrnul_idx, BzH.chr_idx. rewrite find_byte_bz. reflexivity. Qed.

Lemma chr_n_eq : forall A c str, c <> 0 -> strchr_n A c str = BzH.chr_n A c str.
Proof. intros A c str Hc. unfold strchr_n, BzH.chr_n. rewrite !chr_res_eq by exact Hc. reflexivity. Qed.

Lemma chr_proof : BzH.chr_stmt.
Proof.
  unfold BzH.chr_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack full lo
    ST BUF PREF NZ LEN MI CP LO SEP SPH.
  apply AMC.evt_to_bz.
  apply (evt_mono rsegs (RC.strchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 str full lo m)).
  - apply (RC.strchr_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m str slack full lo ST BUF PREF NZ).
    + rewrite chr_idx_eq. exact LEN.
    + exact (AMC.mem_inv_of_bz m MI).
    + exact CP.
    + exact LO.
    + exact SEP.
  - intros st (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & B).
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [rewrite E, chr_res_eq by lia; reflexivity|].
    split; [exact MU|]. split; [exact WM|].
    split; [|split; [exact ST' | exact B]].
    apply BzM.mem_inv_intro; [intros x; exact (BzM.mem_inv_seg_below _ _ _ MI)|].
    intros x b Hx. split; [exact (MI' x b Hx)|].
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp - 32)) as [L|L];
      [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned sp)) as [L2|L2]].
    + rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
    + unfold BzM.UTOP. lia.
    + rewrite (MU x) in Hx by (cbn [outside]; split; [lia | exact I]). exact (BzM.mem_inv_ov_below _ _ _ _ MI Hx).
Qed.

Lemma icells_chr_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m REAL_STRCHR (le8 (wa STRCHR)) -> bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
  bytes_at rsegs m (CF + 245) [Z_to_bv 8 0] -> bytes_at rsegs m (CF + 253) [Z_to_bv 8 1] ->
  BzH.icells_chr (normalize_cj rsegs m).
Proof.
  intros m HMI HC HRS HG HF5 HF3. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (inited_norm m HMI HC) as HI.
  destruct HC as (HK & HGK & _).
  unfold REAL_STRCHR, STRCHR, GOT_CF, CF in *.
  unfold BzH.icells_chr. split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HG].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGK].
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HK].
  - exact HI.
  - apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRS].
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF5].
  - apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF3].
Qed.

Theorem strchr_wrap_holds_L : strchr_wrap_contract_L.
Proof.
  unfold strchr_wrap_contract_L.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str slack lo.
  cbv zeta. intros BUF NZ PAD HMI HC0 HN AD EA A7 SEP HST HK HLO HSP HC HSR HRS HGCF HCF5 HCF3.
  unfold STRCHR_WRAP_K in *.
  pose proof HSR as HSR0. pose proof AD as AD0.
  rewrite (chr_n_eq _ _ _ HC0) in HN, AD, EA, HSR.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof AD as (S0 & N0 & SE & _).
  pose proof (BzH.chr_n_le (bv_unsigned a0) (bv_unsigned a1 mod 256) str) as NL.
  pose proof (BzH.chr_n_ge (bv_unsigned a0) (bv_unsigned a1 mod 256) str) as NG.
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  pose proof (Z.mod_pos_bound (- (bv_unsigned a0 + BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)) 8 ltac:(lia)) as K8.
  pose proof (round8_le (bv_unsigned a0 + BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)
                ltac:(unfold APPMEM_END in SE; lia)) as R8.
  assert (LL : BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str
               + (- (bv_unsigned a0 + BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)) mod 8
               <= Z.of_nat (length str) + 1 + Z.of_nat (length slack)).
  { pose proof (BzH.pad_mono2 (bv_unsigned a0) _ _ NL) as PM.
    replace (bv_unsigned a0 + (Z.of_nat (length str) + 1)) with (bv_unsigned a0 + Z.of_nat (length str) + 1) in PM by lia.
    lia. }
  set (L := Z.to_nat (BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str
                      + (- (bv_unsigned a0 + BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)) mod 8)).
  assert (LZ : Z.of_nat L = BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str
                            + (- (bv_unsigned a0 + BzH.chr_n (bv_unsigned a0) (bv_unsigned a1 mod 256) str)) mod 8)
    by (unfold L; rewrite Z2Nat.id by lia; reflexivity).
  assert (BUF' : bytes_at rsegs m (bv_unsigned a0) (firstn L (str ++ Z_to_bv 8 0 :: slack))).
  { apply (bytes_at_prefix m _ _ (skipn L (str ++ Z_to_bv 8 0 :: slack))). rewrite firstn_skipn. exact BUF. }
  assert (LF : length (firstn L (str ++ Z_to_bv 8 0 :: slack)) = L)
    by (rewrite length_firstn, length_app; cbn [length]; lia).
  apply (evt_mono rsegs (fun st => exists st0,
            BzH.istrchr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
              (BzH.chr_res (bv_unsigned a0) (bv_unsigned a1 mod 256) str) lo (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (bz_run _ _ F _ fc m HMI).
    apply BzH.tramp_strchr.
    apply (BzH.istrchr_spec BzP.rip_proof chr_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) (bv_unsigned a0) str slack L lo).
    + symmetry. apply Z_to_bv_bv_unsigned.
    + exact (stk_normalize m lo (bv_unsigned sp) HMI HST ltac:(unfold TASK_SIZE, APPMEM_END in *; lia)).
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + lia.
    + assert (HL : bv_unsigned a0 + Z.of_nat (length (firstn L (str ++ Z_to_bv 8 0 :: slack))) <= TASK_SIZE)
        by (rewrite LF; unfold TASK_SIZE; lia).
      exact (bytes_normalize_low m _ _ RO HL BUF').
    + exact NZ.
    + lia.
    + lia.
    + lia.
    + lia.
    + exact (chk_ok_of_loc m (bv_unsigned a0) _ HMI HSR AD EA (or_intror A7) HN).
    + exact (ARP.m2s_cells_normalize m HMI HC).
    + exact (icells_chr_norm m HMI HC HRS HGCF HCF5 HCF3).
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    rewrite <- (chr_res_eq _ _ _ HC0) in E0. subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (stack_W_ok (bv_unsigned sp - 2224) (bv_unsigned sp) ltac:(lia) ltac:(lia) ltac:(lia)) as [AW DJ].
    destruct (wrap_post_L [(bv_unsigned sp - 2224, bv_unsigned sp)] m (ms_mem st) m0' lo (bv_unsigned sp)
                HMI HC E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & MK').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [exact ST'|split; [exact HC'|split; [exact (shvis_kept _ _ _ _ HSR0 MK' (addressable_app _ _ _ AD0))|]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 2224, bv_unsigned sp)] m (ms_mem st)); [exact BUF | exact MU' |].
      rewrite length_app. cbn [length disjoint_from]. split; [lia | exact I].
Qed.
