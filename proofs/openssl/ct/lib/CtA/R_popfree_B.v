(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk SysStep ITree. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_classid R_prim_defs R_mmapfixed R_ensurefa R_ensurefa_B R_popfree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Notation mem := (word -> option byte).

Definition pfa_retE : Z := 0x1a1268.

(* [comment removed for export] *)
Definition pfa_newc (auser muser msz size : Z) : Z := ((muser + msz - auser) / size)%Z.

Lemma divu_lit : forall a b, (0 <= a < 2^64)%Z -> (0 < b < 2^64)%Z ->
  mul_div M_DIVU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
Proof.
  intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia. replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, (unsigned_lit b), unsigned_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Section PFAB.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition pfa_W1 (sp : word) (SB c R muser msz sa sn T : Z) : list (Z * Z) :=
  [(rb SB c + muser, rb SB c + muser + msz); (sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
   (bv_unsigned sp - 464, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition pfa_mid_post (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R nfree mfa auser muser msz sa sn T TCX : Z) (mm0 md0 : word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 pfa_retE) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1' t2' (Z_to_bv 64 R)
                  (Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 INST) (Z_to_bv 64 R)
                  (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) a4' a5' a6' a7'
                  (Z_to_bv 64 (rb SB c)) (Z_to_bv 64 (pfa_newc auser muser msz (ClassSize c))) (Z_to_bv 64 (muser + msz - auser))
                  (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) s7 s8 s9 s10 s11 t3' t4' t5' t6') F
             (Z_to_bv 64 efs_entry) fc None m' (seg_rom ctasegs)
    /\ munch (pfa_W1 sp SB c R muser msz sa sn T) m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ pfa_frame m' sp ra s0o s1o s2o s3o s4o s5o s6o
    /\ rw_cells ctasegs m' (rb SB c + muser) [CB (Z.to_nat msz) (repeat (Z_to_bv 8 0) (Z.to_nat msz))]
    /\ rw_cells ctasegs m' sa [CB (Z.to_nat sn) (repeat (Z_to_bv 8 250) (Z.to_nat sn))]
    /\ ri_core m' R nfree mfa auser (muser + msz)
    /\ rw_cells ctasegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned mm0 + 1)); C8 (Z_to_bv 64 (bv_unsigned md0 + msz))]
    /\ (exists w, rw_cells ctasegs m' (T + 2792) [C8 w])
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk ctasegs m' lo (bv_unsigned sp - 64).

Lemma pfa_mid_spec : forall ra sp gp t0 t1 t2 a6 s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R k nfree mfa auser muser msz sa sn T TCX : Z)
    (mm0 md0 w0 : word) (shj : list byte) (lo : Z),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (0 <= auser <= muser)%Z -> (muser < auser + k * ClassSize c)%Z -> (1 <= k <= 64)%Z -> (muser mod 2^18 = 0)%Z ->
  msz = umap_size auser muser k (ClassSize c) -> (muser + msz <= 0xE0000000)%Z ->
  (0 <= nfree < 2^32)%Z -> (0 <= mfa <= 2^29)%Z ->
  sa = shad (rb SB c + muser) -> sn = (msz / 8)%Z ->
  tsep ACEIL SB T TCX ->
  pfa_cells1 m sp ra s0o s1o s2o s3o s4o s5o s6o R (cstats T) (rb SB c) muser msz lo ->
  ri_core m R nfree mfa auser muser ->
  thread_cells TCX T m ->
  rw_cells ctasegs m (T + 2792) [C8 w0] ->
  rw_cells ctasegs m (T + 2872) [C8 mm0; C8 md0] ->
  rw_cells ctasegs m sa [CB (Z.to_nat sn) shj] ->
  PC m ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 464)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (pfa_mid_post ra sp gp (Z_to_bv 64 tpA) s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc SB c R nfree mfa
               auser muser msz sa sn T TCX mm0 md0 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 pfa_retB1) (Z_to_bv 64 (bv_unsigned sp - 64)) gp (Z_to_bv 64 tpA) t0 t1 t2 a6
                           (rb SB c + muser) msz (Z_to_bv 64 str_regiondata) (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST)
                           s7 s8 s9 s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom ctasegs))
          (mkEffect (Z_to_bv 64 (rb SB c + muser)) [] [(Z_to_bv 64 (rb SB c + muser), Z_to_bv 64 msz)])).
Proof.
  intros until lo. intros HSB Hc ER Hau Htot Hk Hmual Emsz Hcap Hnf Hmfa Esa Esn HTS
    AC RC TC SAM ST8 SH PCm HLO HLOH HLO2 HSP MI.
  destruct HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  destruct HSB as (HSB1 & HSB2 & HSB3 & HSB4). destruct HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  destruct AC as (FM & FR & ST & GC). unfold pfa_frame in FR.
  unfold ri_core in RC. unfold kHighShadowEnd, img_hull_lo, img_hull_hi, cstats in *. unfold rinfo, RIS_of in ER.
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hks : (k * ClassSize c <= 2^22)%Z).
  { assert (H1 : (k * ClassSize c <= 64 * 65536)%Z) by (apply Z.mul_le_mono_nonneg; lia). lia. }
  pose proof (round_fa_ge (auser + k * ClassSize c - muser) ltac:(lia)) as RG.
  pose proof (round_fa_aligned (auser + k * ClassSize c - muser)) as RA.
  unfold umap_size in Emsz. rewrite <- Emsz in RG, RA.
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = (bv_unsigned sp - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  rewrite Esp in ST.
  assert (UM : (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= SB + 2^37)%Z) by (unfold rb; lia).
  assert (Hn8 : ((rb SB c + muser) mod 8 = 0 /\ msz mod 8 = 0)%Z).
  { unfold rb. split; Z.div_mod_to_equations; lia. }
  destruct (shad_range (rb SB c + muser) msz ltac:(lia) ltac:(lia) (proj1 Hn8) (proj2 Hn8) ltac:(lia)) as (SH1 & SH2 & SH3).
  rewrite <- Esa in SH1, SH2. rewrite <- Esn in SH2, SH3. unfold kHighShadowEnd in SH2.
  assert (Hmsz0 : (0 < msz)%Z) by lia. assert (Hsn : (0 < sn)%Z) by lia.
  pose proof (munch_refl (pfa_W1 sp SB c R muser msz sa sn T) m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  unfold pfa_W1 in MU.
  pose proof GC as GC0. apply box in TC, GC0, PCm.
  apply box in Emsz, Esa, Esn, Hmual, HSB2, HT2, Hn8, HT5, HTCXI, SEPTT, OUTT, OUTTCX, SEPTCX, SEPT, SH3, RA, RG, Hks, Htot, Hk.
  (* [comment removed for export] *)
  pose proof (unbox _ SEPT) as SEPT'.
  eapply evt_cut; [eapply (mfi_B_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m _ _ _ _ _ (rb SB c + muser) msz _ lo) |
                   post_call ctasegs m].
  1:{ unfold img_hull_hi. lia. }
  1:{ lia. }
  1:{ lia. }
  1:{ exact FM. }
  1:{ exact GC. }
  all: rewrite ?Esp; try lia; try assumption.
  clear POST SEPT'.
  lazymatch type of MU with munch _ _ ?mc =>
    pose proof (munch_refl [(sa, sa + sn); (T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
                            (bv_unsigned sp - 464, bv_unsigned sp)]%Z mc) as MU2;
    pose proof (wmono_refl ctasegs mc) as WM2; rename mc into m1 end.
  apply box in PC0.
  unfold pfa_retB1.
  replace (ret_pc (Z_to_bv 64 1708532)) with (Z_to_bv 64 1708532) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  zhide.
  zstep. ifF.
  zstep.
  zstep. ifF.
  do 3 zstep.
  zstep.
  (* [comment removed for export] *)
  pose proof (unbox _ Esa) as Esa'. pose proof (unbox _ Esn) as Esn'. pose proof (unbox _ Hn8) as Hn8'.
  rewrite Esa', Esn' in SH.
  assert (PCm1 : PC m1).
  { pose proof (unbox _ HT5). apply (HPF m m1 _ (unbox _ PCm) MU WM). unfold img_hull_lo, img_hull_hi. cbn [disjoint_from]. lia. }
  pose proof (unbox _ OUTT) as OUTT'.
  eapply evt_cut; [eapply (HPS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (rb SB c + muser)%Z msz lo shj) | ].
  1-3: try unfold zal in *; lia. 1: unfold kHighShadowEnd; lia. 1: lia. 1: exact SH. 1: exact PCm1. 1: exact PC1.
  1-3: unfold kHighShadowEnd; rewrite ?Esp; lia. 1: assumption.
  intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
  rewrite <- Esa', <- Esn' in MUc, PO. clear Esa' Esn' Hn8' SH PCm1.
  lazymatch type of MUc with munch _ _ ?mc => transport_after_call ctasegs m1 mc MUc WMc; rename mc into m2 end.
  clear MUc WMc MI0 OUTT'.
  destruct PO as (SHN & ST1 & PCm2). clear PCm2.
  pose proof (munch_refl [(T + 2792, T + 2800); (T + 2872, T + 2888); (R + 48, R + 56);
                          (bv_unsigned sp - 464, bv_unsigned sp)]%Z m2) as MU3.
  pose proof (wmono_refl ctasegs m2) as WM3.
  apply box in SHN.
  replace (ret_pc (Z_to_bv 64 1708560)) with (Z_to_bv 64 1708560) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  zstep.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  clear SEPTCX' OUTTCX' SEPTT'.
  call (gcts_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ TCX T lo).
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
  all: rewrite ?Esp in *; try lia; try assumption.
  clear KI K TS T0 TT.
  (* [comment removed for export] *)
  pose proof (unbox _ SEPT) as SEPT'.
  do 6 zstep.
  do 2 zstep.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (T + 2792)) = true).
  { try unfold zal in *. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. apply Z.eqb_eq. pose proof (unbox _ HT2). lia. }
  amo_step AMO.
  do 4 zstep.
  do 8 zstep.
  rewrite divu_lit by lia. rewrite unsigned_lit by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace ((muser + msz + - auser) / ClassSize c)%Z with (pfa_newc auser muser msz (ClassSize c)) by (unfold pfa_newc; f_equal; lia).
  (* [comment removed for export] *)
  pose proof (unbox _ OUTT) as OUTT'.
  apply unbox in PC0, SHN.
  tr_from m1 MU2 WM2 PC0. tr_from m2 MU3 WM3 SHN.
  clear OUTT'.
  destruct (unbox _ TC) as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  destruct (unbox _ GC0) as (G1 & G2 & G3 & G4 & G5).
  pose proof (unbox _ HT5) as HT5'.
  tr_from m MU WM KI. tr_from m MU WM K. tr_from m MU WM TS. tr_from m MU WM T0.
  tr_from m MU WM G1. tr_from m MU WM G2. tr_from m MU WM G3. tr_from m MU WM G4. tr_from m MU WM G5.
  lazymatch type of MU with munch _ _ ?mc =>
    assert (PCf : PC mc) by (apply (HPF m mc _ (unbox _ PCm) MU WM); unfold img_hull_lo, img_hull_hi; cbn [disjoint_from]; lia) end.
  clear HT5'.
  pose proof (unbox _ SEPTCX) as SEPTCX'. pose proof (unbox _ OUTTCX) as OUTTCX'. pose proof (unbox _ SEPTT) as SEPTT'.
  tr_from m MU WM TT.
  unfold efs_entry, pfa_retE.
  finish.
  1:{ eexists. eassumption. }
  1:{ unfold mm_gcells. repeat (split; [assumption|]). assumption. }
  1:{ unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main.
      split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]. }
Qed.
End PFAB.
