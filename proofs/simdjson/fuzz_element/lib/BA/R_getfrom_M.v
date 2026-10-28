(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac ImageA Arr Walk SysStep ITree.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout R_small R_m2s R_thread. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_ensurefa_B R_popfree R_popfree_T R_popfree_B R_getfrom R_getfrom_A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Section GFAM.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition gfa_M_W (sp : word) (SB c R muser msz sa sn T : Z) : list (Z * Z) :=
  [(rb SB c + muser, rb SB c + muser + msz); (sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
   (bv_unsigned sp - 640, bv_unsigned sp)]%Z.

Definition gfa_M_cells (m : mem) (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (junk : list byte)
    (SB c R CH n nfree mfa auser muser msz sa sn T TCX : Z) (mm0 md0 : word) (ws chs : list word) (rand : word)
    (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) : Prop :=
  efs_A_cells m (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) (Z_to_bv 64 pfa_retE) (Z_to_bv 64 R)
    (Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 (rb SB c))
    (Z_to_bv 64 (pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 (muser + msz - auser)) R (fa SB c + mfa)
    (round_fa (4 * (nfree + pfa_newc auser muser msz (ClassSize c))) - mfa)
    (round_fa (4 * (nfree + pfa_newc auser muser msz (ClassSize c)))) lo
  /\ rw_cells asegs m (bv_unsigned sp - 128 - 64)
       [C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 CH); C8 (Z_to_bv 64 (fa SB c)); C8 (Z_to_bv 64 2305843009213693952);
        C8 (Z_to_bv 64 (R + 8)); C8 (Z_to_bv 64 INST); C8 (Z_to_bv 64 R); C8 (Z_to_bv 64 gfa_retP)]
  /\ rw_cells asegs m (bv_unsigned sp - 128)
       [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
  /\ ri_lock m R 1152921504606846976
  /\ ri_core m R nfree mfa auser (muser + msz)
  /\ rw_cells asegs m (R + 64) [C4 rand] /\ rw_cells asegs m (R + 68) [C1 exh]
  /\ rw_cells asegs m (R + 69) [CB 3 pad; C8 (Z_to_bv 64 nalloc); C8 (Z_to_bv 64 nfreed); C8 (Z_to_bv 64 r0);
                                C8 (Z_to_bv 64 r1); C8 (Z_to_bv 64 r2); C8 (Z_to_bv 64 r3)]
  /\ fl_arr m SB c ws /\ u32arr asegs m CH chs
  /\ rw_cells asegs m (rb SB c + muser) [CB (Z.to_nat msz) (repeat (Z_to_bv 8 0) (Z.to_nat msz))]
  /\ rw_cells asegs m sa [CB (Z.to_nat sn) (repeat (Z_to_bv 8 250) (Z.to_nat sn))]
  /\ rw_cells asegs m (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + msz))]
  /\ (exists w, rw_cells asegs m (T + 2792) [C8 w])
  /\ thread_cells TCX T m /\ PC m.

Definition gfa_M_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R CH n nfree mfa auser muser msz sa sn T TCX : Z) (mm0 md0 : word) (ws chs : list word) (rand : word)
    (exh : byte) (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a6' t3' t4' t5' t6' : word) (m' : mem) (junk : list byte),
    ms' = MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) - 48)) gp tp
                          t0' t1' t2' a6' (fa SB c + mfa)
                          (round_fa (4 * (nfree + pfa_newc auser muser msz (ClassSize c))) - mfa)
                          (Z_to_bv 64 str_freearray) (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST)
                          (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500) (Z_to_bv 64 16140901064495857663) s10 s11
                          t3' t4' t5' t6') F
                (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m' (seg_rom asegs)
    /\ munch (gfa_M_W sp SB c R muser msz sa sn T) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ gfa_M_cells m' sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk SB c R CH n nfree mfa auser muser msz sa sn T TCX mm0 md0
         ws chs rand exh pad nalloc nfreed r0 r1 r2 r3 lo.

Lemma gfa_M_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R CH n nfree mfa auser muser msz sa sn T TCX : Z)
    (mm0 md0 w0 : word) (shj : list byte) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (junk : list byte),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= nfree < n)%Z ->
  (0 <= auser <= muser)%Z -> (muser < auser + (n - nfree) * ClassSize c)%Z -> (muser mod 2^18 = 0)%Z ->
  msz = umap_size auser muser (n - nfree) (ClassSize c) -> (muser + msz <= 0xE0000000)%Z ->
  (0 <= mfa <= 2^29)%Z -> (mfa mod 2^18 = 0)%Z -> (4 * Z.of_nat (length ws) = mfa)%Z ->
  (mfa < 4 * (nfree + pfa_newc auser muser msz (ClassSize c)))%Z ->
  (round_fa (4 * (nfree + pfa_newc auser muser msz (ClassSize c))) <= 2^29)%Z ->
  sa = shad (rb SB c + muser) -> sn = (msz / 8)%Z ->
  tsep ACEIL SB T TCX ->
  (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z -> length chs = 16%nat -> length pad = 3%nat -> (0 <= nalloc < 2^64)%Z ->
  inst_cells SB m ->
  pfa_cells1 m (Z_to_bv 64 (bv_unsigned sp - 128)) (Z_to_bv 64 gfa_retP) (Z_to_bv 64 R) (Z_to_bv 64 INST)
    (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c)) (Z_to_bv 64 CH) (Z_to_bv 64 n)
    R (cstats T) (rb SB c) muser msz lo ->
  rw_cells asegs m (bv_unsigned sp - 128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ri_lock m R 1152921504606846976 ->
  ri_core m R nfree mfa auser muser ->
  ri_tail m R rand exh pad nalloc nfreed r0 r1 r2 r3 ->
  fl_arr m SB c ws -> u32arr asegs m CH chs ->
  thread_cells TCX T m ->
  rw_cells asegs m (T + 2792) [C8 w0] ->
  rw_cells asegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells asegs m sa [CB (Z.to_nat sn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 640)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (gfa_M_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R CH n nfree mfa auser
               muser msz sa sn T TCX mm0 md0 ws chs rand exh pad nalloc nfreed r0 r1 r2 r3 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 64)) gp
                           (Z_to_bv 64 tpA) t0 t1 t2 a6 (rb SB c + muser) msz (Z_to_bv 64 str_regiondata)
                           (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                           (Z_to_bv 64 16140901064495857663) s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom asegs))
          (mkEffect (Z_to_bv 64 (rb SB c + muser)) [] [(Z_to_bv 64 (rb SB c + muser), Z_to_bv 64 msz)])).
Proof.
  intros until junk. intros HSB Hc ER Hn Hnf Hau Htot Hmual Emsz Hcap Hmfa Hmfal Hws Hgrow Hnew Esa Esn HTS HCHT Hchs Hpad Hna
    IC AC FRG LK RC RT FL CHS TC SAM ST8 SH PCm HLO HLOH HLO2 HSP MI.
  destruct IC as (IC1 & IC2). unfold i_spacebeg, i_premapped, INST, g_instance in IC1, IC2.
  change (1508824 + 32)%Z with 1508856%Z in IC1. change (1508824 + 56)%Z with 1508880%Z in IC2.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
    unfold kHighShadowEnd in HLOH. lia. }
  destruct (ri_tail_split _ _ _ _ _ _ _ _ _ _ _ RT Hpad) as (RT1 & RT2 & RT3). clear RT.
  unfold ri_lock, fl_arr in *.

  eapply evt_cut; [eapply (pfa_mid_spec PC HPS HPF) with (k := (n - nfree)%Z) (nfree := nfree) (mfa := mfa) (ACEIL := ACEIL)
                     (lo := lo) (SB := SB) (auser := auser) (muser := muser) (T := T) (TCX := TCX) (w0 := w0)
                     (mm0 := mm0) (md0 := md0) (shj := shj) (R := R) (sa := sa) (sn := sn) (ra := Z_to_bv 64 gfa_retP)
                     (s0o := Z_to_bv 64 R) (s1o := Z_to_bv 64 INST) (s2o := Z_to_bv 64 (R + 8))
                     (s3o := Z_to_bv 64 2305843009213693952) (s4o := Z_to_bv 64 (fa SB c)) (s5o := Z_to_bv 64 CH)
                     (s6o := Z_to_bv 64 n) | ].
  all: first [ assumption | (arith_goal; try rewrite Esp; unfold kHighShadowEnd in *; lia) | idtac ].
  intros ms1 PO. unfold pfa_mid_post in PO. destruct_exs PO.
  destruct PO as (E & MU1 & WM1 & MI1 & FRP & ZU & SHN & RC1 & ST81 & SAM1 & GC1 & TC1 & PC1 & ST1). subst ms1.
  unfold pfa_W1 in MU1. rewrite Esp in MU1.
  unfold kHighShadowEnd, rinfo, RIS_of, cstats in *.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  assert (UM : (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= fa SB c)%Z) by (unfold fa, rb; lia).
  pose proof (round_fa_ge (auser + (n - nfree) * ClassSize c - muser) ltac:(lia)) as RG.
  unfold umap_size in Emsz. rewrite <- Emsz in RG.
  assert (Hsh : (0x7fff8000 <= sa /\ sa + sn <= 0x10007fff8000 /\ 0 < sn)%Z).
  { subst sa sn. assert (Hn8 : ((rb SB c + muser) mod 8 = 0 /\ msz mod 8 = 0)%Z).
    { pose proof (round_fa_aligned (auser + (n - nfree) * ClassSize c - muser)) as RA. rewrite <- Emsz in RA.
      unfold rb. split; Z.div_mod_to_equations; lia. }
    destruct (shad_range (rb SB c + muser) msz ltac:(lia) ltac:(lia) (proj1 Hn8) (proj2 Hn8) ltac:(lia)) as (SH1 & SH2 & SH3).
    unfold kHighShadowEnd in SH2. lia. }
  assert (Hmsz0 : (0 < msz)%Z) by lia.
  apply box in SEPTCX, SEPTT, OUTTCX, HT5, HTCXI, HT2, HSB2, Hmual, Emsz, Htot.
  tr_from0 m MU1 WM1 FRG. tr_from0 m MU1 WM1 LK. tr_from0 m MU1 WM1 RT1. tr_from0 m MU1 WM1 RT2. tr_from0 m MU1 WM1 RT3.
  tr_from0a m MU1 WM1 FL. tr_from0a m MU1 WM1 CHS.
  pose proof (unbox _ HT5) as HT5'. unfold img_hull_lo, img_hull_hi in HT5'.
  tr_from0 m MU1 WM1 IC1. tr_from0 m MU1 WM1 IC2. clear HT5'.
  apply box in Esa, Esn.
  clear AC SAM ST8 SH RC TC PC1.
  lazymatch type of MU1 with munch _ _ ?mc => rename mc into m1 end.
  apply (munch_weaken _ (gfa_M_W sp SB c R muser msz sa sn T)) in MU1; [| unfold sub_fp, gfa_M_W; cbn [outside]; intros; lia].
  unfold gfa_M_W in MU1.
  destruct SAM1 as (w1 & SAM1). destruct TC1 as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  unfold ri_core, pfa_frame in *.

  rewrite Esp. rewrite Esp in ST1, FRP.
  assert (Esp2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) = (bv_unsigned sp - 128 - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hnewc : (n - nfree <= pfa_newc auser muser msz (ClassSize c) <= 2^28)%Z).
  { unfold pfa_newc. split.
    - apply Z.div_le_lower_bound; [lia|]. pose proof (unbox _ Htot). lia.
    - apply Z.div_le_upper_bound; [lia|]. lia. }
  eapply evt_cut; [eapply efs_A_spec with (ACEIL := ACEIL) (SB := SB) (c := c) (R := R)
                     (num := (nfree + pfa_newc auser muser msz (ClassSize c))%Z) (nfree := nfree) (mfa := mfa)
                     (auser := auser) (muser := (muser + msz)%Z) (lo := lo) | post_call asegs m1].
  all: first [ assumption | (arith_goal; unfold rinfo, RIS_of; lia) | (arith_goal; lia) | (pose proof (unbox _ Hmual); lia)
             | (unfold inst_cells, i_spacebeg, i_premapped, INST, g_instance; split; assumption)
             | (unfold ri_core; assumption) | (rewrite Esp2; assumption) | (arith_goal; rewrite Esp2; lia) | idtac ].
  lazymatch type of MU1 with munch _ _ ?mc =>
    assert (PCf : PC mc) by (apply (HPF m mc _ PCm MU1 WM1); pose proof (unbox _ HT5) as HT5';
                             unfold img_hull_lo, img_hull_hi in *; cbn [disjoint_from]; lia) end.
  apply evt_done. unfold gfa_M_post, gfa_M_cells.
  do 10 eexists. split; [reflexivity|].
  split; [exact MU1|]. split; [exact WM1|]. split; [assumption|].
  split; [exact POST|]. split; [exact FRP|]. split; [exact FRG|]. split; [assumption|]. split; [exact RC1|].
  split; [exact RT1|]. split; [exact RT2|]. split; [exact RT3|]. split; [exact FL|]. split; [exact CHS|].
  split; [exact ZU|]. split; [exact SHN|]. split; [exact ST81|]. split; [eexists; exact SAM1|].
  split; [unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
          split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]|].
  exact PCf.
Qed.
End GFAM.
