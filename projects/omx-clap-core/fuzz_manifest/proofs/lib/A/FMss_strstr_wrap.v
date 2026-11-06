(* lib/A/Prog/strstr_wrap.v (a Theorem Labs lane's port, unchanged from a working branch affce6489c8), re-run over the
   local-shadow statements (FMss_strstr_wrap_c.v, FMss_strstr_c.v and the FMss_* wrappers).  Changed lines: the
   imports and module names; the two range checks (chk_ok_of_loc, the haystack's through shvis_prefix); the inner
   musl strstr's shadow premise (shvis_norm + shvis_kept, where the original used shadow_rw_norm + shadow_rw_kept;
   shadow_rw_norm is dropped); the post (wrap_post_L + shvis_kept). *)
From Stdlib Require Import ZArith NArith Arith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest Require Import lib.MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge FMss_shv.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog Require Import strstr_wrap_c wrap_kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMss_TwAsan FMss_strstr_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strstr_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strstr.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strchr_wrap.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_memchr_wrap.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_memcmp_wrap.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.strstr_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.strchr_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.memchr_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.memcmp_wrap_c.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.asan_memcpy.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.BzCallBridge.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strstrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module ISS := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_strstrw.
Module SSc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.strstr_c.
Module SScL := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strstr_c.
Module SSp := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strstr.
Module TWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.twoway_strstr_c.
Module SCW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_strchr_wrap.
Module MCW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_memchr_wrap.
Module MPW := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.FMss_memcmp_wrap.
Module SCWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.strchr_wrap_c.
Module MCWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.memchr_wrap_c.
Module MPWc := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.memcmp_wrap_c.
Module AMC := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.asan_memcpy.
Module BCB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.BzCallBridge.
Module WK := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.wrap_kit.
Module BB := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.BzBridge.
Module BzQ := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_qck.
Module BzR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_m2s.
Module BzP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.

Lemma prefix_eqb_len : forall nd h, prefix_eqb nd h = true -> (length nd <= length h)%nat.
Proof.
  induction nd as [|a nd IH]; intros [|b h] P; cbn in *; try lia; try discriminate.
  apply andb_prop in P as [_ P]. apply IH in P. lia.
Qed.

Lemma ff_len : forall h nd i, find_first h nd = Some i -> (i + length nd <= length h)%nat.
Proof.
  induction h as [|a h IH]; intros nd i FF; cbn in FF.
  - destruct (prefix_eqb nd []) eqn:P; [|discriminate].
    injection FF as <-. pose proof (prefix_eqb_len nd [] P) as HL. cbn in HL. lia.
  - destruct (prefix_eqb nd (a :: h)) eqn:P.
    + injection FF as <-. pose proof (prefix_eqb_len nd (a :: h) P) as HL. cbn [length] in HL |- *. lia.
    + destruct (find_first h nd) as [j|] eqn:E; cbn in FF; [|discriminate].
      injection FF as <-. pose proof (IH nd j E) as HL. cbn [length]. lia.
Qed.

Lemma ss_val_lo : forall A hb nb, 0 <= A -> 0 <= strstr_val A hb nb.
Proof. intros A hb nb HA. unfold strstr_val. destruct (find_first _ _) as [i|]; lia. Qed.

Lemma ss_val_rr : forall A hb nb,
  strstr_val A hb nb = 0
  \/ (A <= strstr_val A hb nb /\ strstr_val A hb nb - A + Z.of_nat (length nb) <= Z.of_nat (length hb)).
Proof.
  intros A hb nb. unfold strstr_val.
  destruct (find_first (map bv_unsigned hb) (map bv_unsigned nb)) as [i|] eqn:FF; [|left; reflexivity].
  right. pose proof (ff_len _ _ _ FF) as HL. rewrite !length_map in HL. split; lia.
Qed.

Lemma addressable_norm : forall m p n, mem_inv rsegs m -> addressable m p n -> addressable (normalize_cj rsegs m) p n.
Proof.
  intros m p n HMI (A0 & A1 & A2 & H). pose proof (ro_agree_of_mem_inv m HMI) as RO.
  split; [exact A0|]. split; [exact A1|]. split; [exact A2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  assert (Hs : 0 <= shadow_addr (p + i) < TASK_SIZE).
  { unfold shadow_addr, ASAN_K, TASK_SIZE, APPMEM_END in *.
    pose proof (Z.div_pos (p + i) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (p + i) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  rewrite mrd_normalize_cj; [exact Hb | exact RO |]. right. right.
  rewrite wa_unsigned by (unfold TASK_SIZE in Hs; lia). lia.
Qed.

Lemma asan_cells_norm : forall m, mem_inv rsegs m -> asan_cells m -> asan_cells (normalize_cj rsegs m).
Proof.
  intros m HMI HC. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  unfold CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND,
    MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET in *.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17).
  unfold asan_cells, CELL_K, GOT_CELL_K, INITED, REPLACE, GOT_REPLACE, UAR, GOT_UAR, CANPOISON, HIEND, GOT_HIEND,
    MIDBEG, GOT_MIDBEG, MIDEND, GOT_MIDEND, REAL_MEMCPY, REAL_MEMSET, GOT_REAL_MEMSET.
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]]]].
  all: apply (bytes_normalize_low m _ _ RO);
    [ rewrite ?length_le8, ?length_le4; cbn [length]; unfold TASK_SIZE; lia | assumption ].
Qed.

Lemma icells_ss_norm : forall m, mem_inv rsegs m -> asan_cells m ->
  bytes_at rsegs m GOT_CF (le8 (wa CF)) -> bytes_at rsegs m REAL_STRSTR (le8 (wa STRSTR)) ->
  bytes_at rsegs m (CF + 245) [Z_to_bv 8 0] -> bytes_at rsegs m (CF + 246) [Z_to_bv 8 1] ->
  ISS.icells_ss (normalize_cj rsegs m).
Proof.
  intros m HMI HC HGCF HRS HF5 HF6. pose proof (ro_agree_of_mem_inv m HMI) as RO.
  destruct HC as (HK & HGK & HI & _).
  unfold ISS.icells_ss.
  split; [apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HGCF]|].
  split; [apply (AMC.ro_c8_norm m _ _ RO); [unfold GOT_CELL_K, TASK_SIZE; lia | exact HGK]|].
  split; [apply (AMC.ro_c8_norm m _ _ RO); [unfold CELL_K, TASK_SIZE; lia | exact HK]|].
  split; [apply (WK.rw_c1_norm m _ _ HMI); [unfold INITED, TASK_SIZE; lia | vm_compute; reflexivity | exact HI]|].
  split; [apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRS]|].
  split; [apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF5]|].
  apply (AMC.ro_c1_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HF6].
Qed.

Lemma bnm : forall m mm W A bs, ro_agree rsegs m -> A + Z.of_nat (length bs) <= TASK_SIZE ->
  munch W (normalize_cj rsegs m) mm -> disjoint_from W A (Z.of_nat (length bs)) ->
  bytes_at rsegs m A bs -> bytes_at rsegs mm A bs.
Proof.
  intros m mm W A bs RO HL MU DJ H.
  apply (bytes_at_transport rsegs W (normalize_cj rsegs m) mm);
    [exact (bytes_normalize_low m A bs RO HL H) | exact MU | exact DJ].
Qed.

Theorem strstr_wrap_holds : strstr_wrap_contract.
Proof.
  unfold strstr_wrap_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m hb hs nb lo g.
  cbv zeta.
  intros BUF NZH PAD HNZ BN NZN HMI HGG HG LH LN ADH ADN EAH EAN A7H A7N SEPH SEPN HST HKsp HLO HSP HC HSR
    HRSS HRSC HRMC HRMP HGCF HF245 HF246 HF253 HF254 HF255.
  unfold STRSTR_WRAP, STRSTR_WRAP_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. pose proof (bv_unsigned_in_range 64 a1) as RA1.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RA0, RA1, RSP. cbn in RA0, RA1, RSP.
  pose proof ADH as (H0 & _ & SEH & _). pose proof ADN as (N0 & _ & SEN & _).
  unfold APPMEM_END in SEH, SEN, HSP. unfold HIGHMEM_BEG in HLO.
  set (H := bv_unsigned a0) in *. set (ND := bv_unsigned a1) in *. set (usp := bv_unsigned sp) in *.
  set (r := strstr_val H hb nb) in *.
  pose proof (Z.mod_pos_bound (- (H + Z.of_nat (length hb) + 1)) 8 ltac:(lia)) as K8.
  set (sl := firstn (Z.to_nat ((- (H + Z.of_nat (length hb) + 1)) mod 8)) hs).
  assert (LSL : Z.of_nat (length sl) = (- (H + Z.of_nat (length hb) + 1)) mod 8)
    by (unfold sl; rewrite length_firstn; lia).
  assert (BUFsl : bytes_at rsegs m H (hb ++ Z_to_bv 8 0 :: sl)).
  { apply (WK.bytes_at_prefix m _ _ (skipn (Z.to_nat ((- (H + Z.of_nat (length hb) + 1)) mod 8)) hs)).
    rewrite <- app_assoc. cbn [app]. unfold sl. rewrite firstn_skipn. exact BUF. }
  pose proof (WK.round8_le (H + Z.of_nat (length hb) + 1) ltac:(unfold TASK_SIZE; lia)) as R8.
  assert (BNsl : bytes_at rsegs m ND (nb ++ [Z_to_bv 8 0])) by exact BN.
  assert (R0 : 0 <= r) by (apply ss_val_lo; lia).
  assert (RRv : r = 0 \/ (H <= r /\ r - H + Z.of_nat (length nb) <= Z.of_nat (length hb))) by apply ss_val_rr.
  assert (RHI : r <= H + Z.of_nat (length hb)) by (destruct RRv as [->|(A & B)]; lia).
  assert (CHN : BzQ.chk_ok (normalize_cj rsegs m) ND (Z.of_nat (length nb) + 1)).
  { apply (chk_ok_of_loc m ND _ HMI (proj2 HSR) ADN EAN); [| exact LN].
    right. replace (ND + 7) with (ND + 0 + 7) by lia. apply A7N. lia. }
  assert (SCKLE : 0 <= ISS.sck_n1 H r hb nb <= Z.of_nat (length hb) + 1).
  { unfold ISS.sck_n1. destruct (Z.eqb_spec r 0) as [E|NE]; [lia|].
    destruct RRv as [->|(A & B)]; [lia|]. lia. }
  assert (CHH : BzQ.chk_ok (normalize_cj rsegs m) H (ISS.sck_n1 H r hb nb)).
  { apply (chk_ok_of_loc m H _ HMI).
    - apply (shvis_prefix m _ _ _ (proj1 HSR)). exact (proj2 SCKLE).
    - apply (addressable_prefix m H (Z.of_nat (length hb) + 1) _ ADH). exact SCKLE.
    - destruct (Z.eq_dec (ISS.sck_n1 H r hb nb) (Z.of_nat (length hb) + 1)) as [E|NE].
      + rewrite E. exact EAH.
      + right. pose proof ADH as (_ & _ & _ & HAD). destruct (HAD (ISS.sck_n1 H r hb nb) ltac:(lia)) as [AP _]. exact AP.
    - right. replace (H + 7) with (H + 0 + 7) by lia. apply A7H. lia.
    - lia. }
  assert (M2S : BzR.m2s_cells (normalize_cj rsegs m)) by exact (BCB.m2s_cells_normalize m HMI HC).
  assert (ICS : ISS.icells_ss (normalize_cj rsegs m)) by (apply icells_ss_norm; assumption).
  assert (SSH : ISS.ss_stmt (normalize_cj rsegs m) usp H ND r lo).
  { pose proof (SSp.strstr_holds SCW.strchr_wrap_holds_L MCW.memchr_wrap_holds_L MPW.memcmp_wrap_holds_L) as SSC.
    unfold ISS.ss_stmt. unfold SScL.strstr_contract in SSC.
    intros gp2 tp2 t0b t1b t2b s0b s1b a2b a3b a4b a5b a6b a7b s2b s3b s4b s5b s6b s7b s8b s9b s10b s11b
      t3b t4b t5b t6b F2 fc2 mm MU2 WM2 MI2 ST2.
    assert (MU2' : munch [(usp - 4608, usp)] (normalize_cj rsegs m) mm) by exact MU2.
    assert (WM2' : wmono rsegs (normalize_cj rsegs m) mm) by exact WM2.
    assert (EHslot : Z_to_bv 64 H = a0) by (unfold H; apply Z_to_bv_bv_unsigned).
    assert (ENslot : Z_to_bv 64 ND = a1) by (unfold ND; apply Z_to_bv_bv_unsigned).
    rewrite EHslot, ENslot.
    assert (EU48 : bv_unsigned (Z_to_bv 64 (usp + -48)) = usp + -48) by (apply unsigned_lit; lia).
    destruct (WK.stack_W_ok (usp - 4608) usp ltac:(unfold HIGHMEM_BEG; lia) ltac:(lia) ltac:(unfold APPMEM_END; lia)) as [AWm DJm].
    pose proof (munch_meta _ (normalize_cj rsegs m) mm MU2' AWm) as MKm.
    assert (HBhay : H + Z.of_nat (length (hb ++ Z_to_bv 8 0 :: sl)) <= TASK_SIZE).
    { rewrite length_app; cbn [length]. rewrite Nat2Z.inj_add, Nat2Z.inj_succ, LSL. unfold TASK_SIZE. lia. }
    assert (HBned : ND + Z.of_nat (length (nb ++ [Z_to_bv 8 0])) <= TASK_SIZE).
    { rewrite length_app; cbn [length]. rewrite Nat2Z.inj_add. unfold TASK_SIZE. lia. }
    apply AMC.evt_to_bz.
    apply (evt_mono rsegs (SScL.strstr_post (Z_to_bv 64 0x429a8) (Z_to_bv 64 (usp + -48)) gp2 tp2 s0b s1b s2b s3b s4b
             s5b s6b s7b s8b s9b s10b s11b F2 fc2 a0 a1 hb sl nb lo mm)).
    - apply (SSC (Z_to_bv 64 0x429a8) (Z_to_bv 64 (usp + -48)) gp2 tp2 t0b t1b t2b s0b s1b a0 a1
               a2b a3b a4b a5b a6b a7b s2b s3b s4b s5b s6b s7b s8b s9b s10b s11b t3b t4b t5b t6b F2 fc2 mm hb sl nb lo g).
      + unfold SSc.STRSTR_K. rewrite EU48. exact ST2.
      + unfold SSc.STRSTR_K. rewrite EU48. lia.
      + apply (bnm m mm _ H _ RO HBhay MU2').
        * rewrite length_app; cbn [length]. cbn [disjoint_from]. split; [|exact I].
          destruct SEPH as [S|S]; [left; unfold H in *; lia | right; unfold usp, H in *; lia].
        * exact BUFsl.
      + exact NZH.
      + rewrite LSL. unfold H; lia.
      + exact HNZ.
      + apply (bnm m mm _ ND _ RO HBned MU2').
        * rewrite length_app; cbn [length]. cbn [disjoint_from]. split; [|exact I].
          destruct SEPN as [S|S]; [left; unfold ND in *; lia | right; unfold usp, ND in *; lia].
        * exact BNsl.
      + exact NZN.
      + exact (AMC.mem_inv_of_bz mm MI2).
      + unfold SSc.STRSTR_K. rewrite EU48, LSL.
        destruct SEPH as [S|S]; [left; unfold H in *; lia | right; unfold usp, H in *; lia].
      + unfold SSc.STRSTR_K. rewrite EU48.
        destruct SEPN as [S|S]; [left; unfold ND in *; lia | right; unfold usp, ND in *; lia].
      + apply (bnm m mm _ GOT_GUARD _ RO ltac:(rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold GOT_GUARD, usp in *; lia.
        * exact HGG.
      + apply (bnm m mm _ GUARD _ RO ltac:(rewrite length_le8; unfold GUARD, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold GUARD, usp in *; lia.
        * exact HG.
      + unfold SSc.STRSTR_K. rewrite EU48. unfold TWc.GUARD; lia.
      + unfold SSc.STRSTR_K. rewrite EU48. unfold TWc.GOT_GUARD; lia.
      + exact LH.
      + exact LN.
      + exact (addressable_kept _ mm H _ (addressable_norm m _ _ HMI ADH) MKm).
      + exact (addressable_kept _ mm ND _ (addressable_norm m _ _ HMI ADN) MKm).
      + exact EAH.
      + exact EAN.
      + exact A7H.
      + exact A7N.
      + unfold HIGHMEM_BEG; lia.
      + rewrite EU48. unfold APPMEM_END; lia.
      + exact (asan_cells_kept _ _ mm (asan_cells_norm m HMI HC) MU2' DJm).
      + split.
        * exact (shvis_kept _ _ _ _ (shvis_norm m _ _ HMI (proj1 HSR) (addressable_app _ _ _ ADH)) MKm
                   (addressable_app _ _ _ ADH)).
        * exact (shvis_kept _ _ _ _ (shvis_norm m _ _ HMI (proj2 HSR) (addressable_app _ _ _ ADN)) MKm
                   (addressable_app _ _ _ ADN)).
      + apply (bnm m mm _ SCWc.REAL_STRCHR _ RO ltac:(rewrite length_le8; unfold SCWc.REAL_STRCHR, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold SCWc.REAL_STRCHR, usp in *; lia.
        * exact HRSC.
      + apply (bytes_at_transport rsegs [(usp - 4608, usp)] (normalize_cj rsegs m) mm);
          [ apply (bytes_normalize_low m _ _ RO); [cbn [length]; unfold SCWc.CF, TASK_SIZE; lia | exact HF245]
          | exact MU2' | cbn [length]; cbn [disjoint_from]; split; [|exact I]; left; unfold SCWc.CF, usp in *; lia ].
      + apply (bytes_at_transport rsegs [(usp - 4608, usp)] (normalize_cj rsegs m) mm);
          [ apply (bytes_normalize_low m _ _ RO); [cbn [length]; unfold SCWc.CF, TASK_SIZE; lia | exact HF253]
          | exact MU2' | cbn [length]; cbn [disjoint_from]; split; [|exact I]; left; unfold SCWc.CF, usp in *; lia ].
      + apply (bnm m mm _ MCWc.REAL_MEMCHR _ RO ltac:(rewrite length_le8; unfold MCWc.REAL_MEMCHR, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold MCWc.REAL_MEMCHR, usp in *; lia.
        * exact HRMC.
      + apply (bnm m mm _ MPWc.REAL_MEMCMP _ RO ltac:(rewrite length_le8; unfold MPWc.REAL_MEMCMP, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold MPWc.REAL_MEMCMP, usp in *; lia.
        * exact HRMP.
      + apply (bnm m mm _ MPWc.GOT_CF _ RO ltac:(rewrite length_le8; unfold MPWc.GOT_CF, TASK_SIZE; lia) MU2').
        * rewrite length_le8. cbn [disjoint_from]. split; [|exact I]. left. unfold MPWc.GOT_CF, usp in *; lia.
        * exact HGCF.
      + apply (bytes_at_transport rsegs [(usp - 4608, usp)] (normalize_cj rsegs m) mm);
          [ apply (bytes_normalize_low m _ _ RO); [cbn [length]; unfold MPWc.CF, TASK_SIZE; lia | exact HF254]
          | exact MU2' | cbn [length]; cbn [disjoint_from]; split; [|exact I]; left; unfold MPWc.CF, usp in *; lia ].
      + apply (bytes_at_transport rsegs [(usp - 4608, usp)] (normalize_cj rsegs m) mm);
          [ apply (bytes_normalize_low m _ _ RO); [cbn [length]; unfold MPWc.CF, TASK_SIZE; lia | exact HF255]
          | exact MU2' | cbn [length]; cbn [disjoint_from]; split; [|exact I]; left; unfold MPWc.CF, usp in *; lia ].
    - intros st Q. unfold SScL.strstr_post in Q. unfold ISS.ss_post.
      destruct Q as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m' &
                     E & MU & WM & MI & ST & _ & _ & _ & _).
      unfold SSc.STRSTR_K in MU. rewrite EU48 in MU, ST.
      assert (STmm : stk rsegs mm lo (usp + -48)) by exact ST2.
      assert (WRAT : wr_at rsegs mm (usp + -48 - 4560) 4560).
      { destruct STmm as (SL0 & SL1 & SLW). split; [lia|]. split; [lia|].
        intros i Hi. exact (proj1 (SLW (usp + -48 - 4560 + i) ltac:(lia))). }
      assert (MUbz : munch [(usp + -48 - 4560, usp + -48 - 4560 + 4560)] mm m').
      { replace (usp + -48 - 4560 + 4560) with (usp + -48) by lia. exact MU. }
      exists t0c, t1c, t2c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, m'.
      split; [unfold r, H; exact E|]. split; [exact MU|]. split; [exact WM|].
      split; [exact (BCB.bz_mem_inv_after mm m' (usp + -48 - 4560) 4560 MI2 WRAT MI MUbz)|]. exact ST. }
  apply (evt_mono rsegs (fun st => exists st0,
            ISS.istrstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r lo (normalize_cj rsegs m) st0
            /\ ms_rel_cj rsegs st st0 /\ cj_same rsegs m (ms_mem st))).
  - apply (bz_run _ _ F _ fc m HMI).
    apply (ISS.istrstr_spec BzP.rip_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (normalize_cj rsegs m) H ND r hb nb lo).
    + unfold H. symmetry. apply Z_to_bv_bv_unsigned.
    + unfold ND. symmetry. apply Z_to_bv_bv_unsigned.
    + exact SSH.
    + exact (stk_normalize m lo usp HMI HST ltac:(unfold TASK_SIZE; lia)).
    + unfold usp in *; lia.
    + unfold BzR.kHighShadowEnd. lia.
    + unfold usp in *; lia.
    + apply (bytes_normalize_low m H _ RO); [rewrite length_app; cbn [length]; unfold TASK_SIZE; lia|].
      apply (WK.bytes_at_prefix m H _ hs). unfold H.
      replace ((hb ++ [Z_to_bv 8 0]) ++ hs) with (hb ++ Z_to_bv 8 0 :: hs) by (rewrite <- app_assoc; reflexivity).
      exact BUF.
    + exact NZH.
    + apply (bytes_normalize_low m ND _ RO); [rewrite length_app; cbn [length]; unfold TASK_SIZE; lia | exact BN].
    + exact NZN.
    + unfold H; lia.
    + unfold H; lia.
    + unfold ND; lia.
    + unfold ND; lia.
    + destruct SEPH as [S|S]; [left; unfold H, usp in *; lia | right; unfold H, usp in *; lia].
    + destruct SEPN as [S|S]; [left; unfold ND, usp in *; lia | right; unfold ND, usp in *; lia].
    + split; [exact R0|]. unfold r in *; lia.
    + exact RRv.
    + exact CHH.
    + exact CHN.
    + exact M2S.
    + exact ICS.
    + exact (bz_mem_inv_normalize m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0c & t1c & t2c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m0' &
                    E0 & MU & WM & MI & ST).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (WK.stack_W_ok (usp - 4608) usp ltac:(unfold HIGHMEM_BEG; lia) ltac:(lia) ltac:(unfold APPMEM_END; lia)) as [AW DJ].
    destruct (wrap_post_L [(usp - 4608, usp)] m (ms_mem st) m0' lo usp HMI HC E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & MK').
    unfold strstr_wrap_post, STRSTR_WRAP_K.
    exists t0c, t1c, t2c, a1c, a2c, a3c, a4c, a5c, a6c, a7c, t3c, t4c, t5c, t6c, (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [exact ST'|split; [exact HC'|split; [split; [exact (shvis_kept _ _ _ _ (proj1 HSR) MK' (addressable_app _ _ _ ADH)) | exact (shvis_kept _ _ _ _ (proj2 HSR) MK' (addressable_app _ _ _ ADN))]|]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. unfold r, H. reflexivity.
    + split.
      * apply (bytes_at_transport rsegs [(usp - 4608, usp)] m (ms_mem st)); [exact BUF | exact MU' |].
        rewrite length_app; cbn [length]. cbn [disjoint_from]. split; [|exact I].
        destruct SEPH as [S|S]; [left; unfold H, usp in *; lia | right; unfold H, usp in *; lia].
      * apply (bytes_at_transport rsegs [(usp - 4608, usp)] m (ms_mem st)); [exact BN | exact MU' |].
        rewrite length_app; cbn [length]. cbn [disjoint_from]. split; [|exact I].
        destruct SEPN as [S|S]; [left; unfold ND, usp in *; lia | right; unfold ND, usp in *; lia].
Qed.
