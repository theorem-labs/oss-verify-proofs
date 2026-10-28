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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_prim_kit R_mmapfixed R_ensurefa R_ensurefa_B R_popfree R_popfree_T R_popfree_B R_getfrom R_getfrom_A R_getfrom_M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac arith_goal := lazymatch goal with
  | |- @eq Z _ _ => idtac | |- @eq nat _ _ => idtac | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac | |- Z.ge _ _ => idtac
  | |- Z.gt _ _ => idtac | |- le _ _ => idtac | |- lt _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac
  | |- False => idtac end.
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

(* [comment removed for export] *)
Ltac tr_bx m0 MU WM H GE SE :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (rw_cells_transport ctasegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes;
      let G := fresh "G" in let S := fresh "S" in
      pose proof (unbox _ GE) as G; pose proof (unbox _ SE) as S; clear - G S; repeat split; lia ]
  end.
Ltac tr_bxa m0 MU WM H X GE SE :=
  lazymatch type of MU with munch ?W _ ?mc =>
    apply (u32arr_transport ctasegs W m0 mc _ _) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes;
      let G := fresh "G" in let S := fresh "S" in
      pose proof (unbox _ GE) as G; pose proof (unbox _ SE) as S; clear - G S X; repeat split; lia ]
  end.
Ltac sub_bx GE := let G := fresh "G" in pose proof (unbox _ GE) as G; clear - G; solve_sub_fp2.

Section GFAB2.
Variable PC : mem -> Prop.
Hypothesis HPS : poison_stmt PC.
Hypothesis HPF : PC_framed PC.

Definition gfa_B2_W (sp : word) (SB c R CH n new esa esn T : Z) : list (Z * Z) :=
  [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80); (fa SB c, fa SB c + new); (esa, esa + esn);
   (T + 2872, T + 2888); (CH, CH + 4 * n); (bv_unsigned sp - 640, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Definition gfa_B2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SB c R CH n nfree mfa new auser muser msz sa sn esa esn T TCX : Z) (mm0 md0 : word) (ws chs : list word) (rand : word)
    (pad : list byte) (nalloc nfreed r0 r1 r2 r3 lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch (gfa_B2_W sp SB c R CH n new esa esn T) m m' /\ wmono ctasegs m m' /\ mem_inv ctasegs m'
    /\ ri_lock m' R 0
    /\ ri_core m' R (nfree + pfa_newc auser muser msz (ClassSize c) - n) new
         (auser + pfa_newc auser muser msz (ClassSize c) * ClassSize c) (muser + msz)
    /\ ri_tail m' R rand (Z_to_bv 8 0) pad (nalloc + n) nfreed r0 r1 r2 r3
    /\ fl_arr m' SB c (carve (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))
                         (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                         (Z.to_nat (pfa_newc auser muser msz (ClassSize c))))
    /\ u32arr ctasegs m' CH (dest (carve (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))
                                       (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                                       (Z.to_nat (pfa_newc auser muser msz (ClassSize c)))) chs
                               (nfree + pfa_newc auser muser msz (ClassSize c) - n) (Z.to_nat n))
    /\ rw_cells ctasegs m' (rb SB c + muser) [CB (Z.to_nat msz) (repeat (Z_to_bv 8 0) (Z.to_nat msz))]
    /\ rw_cells ctasegs m' sa [CB (Z.to_nat sn) (repeat (Z_to_bv 8 250) (Z.to_nat sn))]
    /\ rw_cells ctasegs m' esa [CB (Z.to_nat esn) (repeat (Z_to_bv 8 250) (Z.to_nat esn))]
    /\ rw_cells ctasegs m' (T + 2872) [C8 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned mm0 + 1)) + 1));
                                     C8 (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned md0 + msz)) + (new - mfa)))]
    /\ (exists w, rw_cells ctasegs m' (T + 2792) [C8 w])
    /\ mm_gcells m' /\ thread_cells TCX T m' /\ PC m'
    /\ stk ctasegs m' lo (bv_unsigned sp).

Lemma gfa_B2_spec : forall ra sp gp t0 t1 t2 a6 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (ACEIL SB c R CH n nfree mfa new auser muser msz sa sn esa esn T TCX : Z)
    (mm0 md0 : word) (shj : list byte) (ws chs : list word) (rand : word) (exh : byte) (pad : list byte)
    (nalloc nfreed r0 r1 r2 r3 lo : Z) (junk : list byte),
  SB_ok ACEIL SB -> (1 <= c <= 31)%Z -> R = rinfo (RIS_of SB) c ->
  (1 <= n <= 16)%Z -> (0 <= nfree < n)%Z ->
  (0 <= auser <= muser)%Z -> (muser < auser + (n - nfree) * ClassSize c)%Z -> (muser mod 2^18 = 0)%Z ->
  msz = umap_size auser muser (n - nfree) (ClassSize c) -> (muser + msz <= 0xE0000000)%Z ->
  (0 <= mfa <= 2^29)%Z -> (mfa mod 2^18 = 0)%Z -> (4 * Z.of_nat (length ws) = mfa)%Z ->
  (mfa < 4 * (nfree + pfa_newc auser muser msz (ClassSize c)))%Z ->
  new = round_fa (4 * (nfree + pfa_newc auser muser msz (ClassSize c))) -> (new <= 2^29)%Z ->
  sa = shad (rb SB c + muser) -> sn = (msz / 8)%Z -> esa = shad (fa SB c + mfa) -> esn = ((new - mfa) / 8)%Z ->
  tsep ACEIL SB T TCX ->
  (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z -> length chs = 16%nat -> length pad = 3%nat -> (0 <= nalloc < 2^64)%Z ->
  gfa_M_cells PC m sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 junk SB c R CH n nfree mfa auser muser msz sa sn T TCX mm0 md0
    ws chs rand exh pad nalloc nfreed r0 r1 r2 r3 lo ->
  rw_cells ctasegs m esa [CB (Z.to_nat esn) shj] ->
  (ACEIL <= lo)%Z -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 640)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (gfa_B2_post ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SB c R CH n nfree mfa new
               auser muser msz sa sn esa esn T TCX mm0 md0 ws chs rand pad nalloc nfreed r0 r1 r2 r3 lo m)
    (nret (MSsvc (mfi_regs (Z_to_bv 64 efs_retB) (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) - 48)) gp
                           (Z_to_bv 64 tpA) t0 t1 t2 a6 (fa SB c + mfa) (new - mfa) (Z_to_bv 64 str_freearray)
                           (Z_to_bv 64 (ClassSize c)) (Z_to_bv 64 INST) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500)
                           (Z_to_bv 64 16140901064495857663) s10 s11 t3 t4 t5 t6) F
                 (Z_to_bv 64 mmap_ecall_pc) (Z_to_bv 64 222) fc None m (seg_rom ctasegs))
          (mkEffect (Z_to_bv 64 (fa SB c + mfa)) [] [(Z_to_bv 64 (fa SB c + mfa), Z_to_bv 64 (new - mfa))])).
Proof.
  intros until junk. intros HSB Hc ER Hn Hnf Hau Htot Hmual Emsz Hcap Hmfa Hmfal Hws Hgrow Enew Hnew Esa Esn Eesa Eesn HTS
    HCHT Hchs Hpad Hna MC SHF HLO HLOH HLO2 HSP MI.
  pose proof HSB as (HSB1 & HSB2 & HSB3 & HSB4).
  pose proof HTS as (HT & HTCX0 & HTCX1 & HTCXI & SEPT & SEPTCX & SEPTT & OUTT & OUTTCX).
  pose proof HT as (HT1 & HT2 & HT3 & HT4 & HT5).
  destruct MC as (AC & FRP & FRG & LK & RC & RT1 & RT2 & RT3 & FL & CHS & ZU & SHN & ST8 & SAM & TC & PCm).
  assert (Esp : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) = (bv_unsigned sp - 128 - 64)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
    unfold kHighShadowEnd in HLOH. lia. }
  pose proof (ClassSize_range c Hc) as HCS.
  assert (Hnewc : (n - nfree <= pfa_newc auser muser msz (ClassSize c) <= 2^28)%Z).
  { pose proof (round_fa_ge (auser + (n - nfree) * ClassSize c - muser) ltac:(lia)) as RG.
    unfold umap_size in Emsz. rewrite <- Emsz in RG. unfold pfa_newc. split.
    - apply Z.div_le_lower_bound; [lia|]. lia.
    - apply Z.div_le_upper_bound; [lia|]. lia. }
  pose proof (round_fa_ge (4 * (nfree + pfa_newc auser muser msz (ClassSize c))) ltac:(lia)) as RGN.
  pose proof (round_fa_aligned (4 * (nfree + pfa_newc auser muser msz (ClassSize c)))) as RAN.
  rewrite <- Enew in RGN, RAN.
  (* [comment removed for export] *)
  apply box in FRG, RT1, RT3, CHS, ZU, SHN, SAM.
  apply box in SEPT, SEPTCX, SEPTT, OUTT, OUTTCX, HT5, HTCXI, HT2, HSB2, Htot, Emsz.
  (* [comment removed for export] *)
  eapply evt_cut; [eapply (efs_B_spec PC HPS HPF) with (ACEIL := ACEIL) (SB := SB) (c := c) (R := R) (mfa := mfa) (new := new)
                     (T := T) (TCX := TCX) (nfree := nfree) (auser := auser) (muser := (muser + msz)%Z)
                     (mm0 := Z_to_bv 64 (bv_unsigned mm0 + 1)) (md0 := Z_to_bv 64 (bv_unsigned md0 + msz)) (shj := shj)
                     (lo := lo) (esa := esa) (esn := esn) (ra := Z_to_bv 64 pfa_retE) (s0 := Z_to_bv 64 R)
                     (s1 := Z_to_bv 64 (nfree + pfa_newc auser muser msz (ClassSize c))) (s2 := Z_to_bv 64 (rb SB c))
                     (s3 := Z_to_bv 64 (pfa_newc auser muser msz (ClassSize c))) (s4 := Z_to_bv 64 (muser + msz - auser)) | ].
  all: first [ assumption | (arith_goal; lia) | (rewrite Enew; exact AC) | idtac ].
  intros ms1 PO. unfold efs_B_post in PO. destruct_exs PO.
  destruct PO as (E1 & MU1 & WM1 & MI1 & ZNEW & SHN2 & RC2 & ST82 & GC2 & TC2 & PC2 & ST1). subst ms1.
  unfold efs_WB in MU1. rewrite Esp in MU1.
  unfold kHighShadowEnd, rinfo, RIS_of, cstats, ri_lock, fl_arr, ri_core in *.
  assert (FAB : (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z) by (unfold fa, rb; lia).
  assert (UM : (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= fa SB c)%Z) by (unfold fa, rb; lia).
  assert (Hsh : (0x7fff8000 <= sa /\ sa + sn <= esa /\ esa + esn <= 0x10007fff8000 /\ 0 < sn /\ 0 < esn)%Z).
  { pose proof (round_fa_aligned (auser + (n - nfree) * ClassSize c - muser)) as RA.
    pose proof (round_fa_ge (auser + (n - nfree) * ClassSize c - muser) ltac:(pose proof (unbox _ Htot); lia)) as RG.
    pose proof (unbox _ Emsz) as Emsz'. unfold umap_size in Emsz'. rewrite <- Emsz' in RA, RG.
    pose proof (unbox _ Hmual) as Hmual'. pose proof (unbox _ HSB2) as HSB2'. pose proof (unbox _ Htot) as Htot'.
    subst sa sn esa esn. unfold shad, SHB, fa, rb in *. Z.div_mod_to_equations; lia. }
  assert (Hmsz0 : (0 < msz)%Z) by lia.
  assert (Esp0 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { apply unsigned_lit. pose proof (bv_unsigned_in_range 64 sp) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr. lia. }
  assert (GEO : R = (SB + 2^37 + 128 * c)%Z /\ (1 <= c <= 31)%Z /\ (17594333495295 < SB)%Z /\ (SB + 2^37 + 4096 <= ACEIL)%Z
     /\ (ACEIL <= lo)%Z /\ (17594333495303 <= lo)%Z /\ (lo <= bv_unsigned sp - 640)%Z /\ (bv_unsigned sp <= 2^47)%Z
     /\ (SB + 2^32 <= fa SB c /\ fa SB c + 2^29 <= SB + 2^37)%Z
     /\ (SB + 2^32 <= rb SB c + muser /\ rb SB c + muser + msz <= fa SB c)%Z
     /\ (0x7fff8000 <= sa /\ sa + sn <= esa /\ esa + esn <= 0x10007fff8000 /\ 0 < sn /\ 0 < esn)%Z
     /\ (4 * (nfree + pfa_newc auser muser msz (ClassSize c)) <= new <= 2^29)%Z /\ (0 <= mfa < new)%Z
     /\ (4 * Z.of_nat (length ws) = mfa)%Z /\ (0 < msz)%Z /\ (1 <= n <= 16)%Z
     /\ (T + 208 <= CH /\ CH + 64 <= T + 2768)%Z /\ (0 < T)%Z /\ (T + 4096 <= ACEIL)%Z /\ (0 < TCX)%Z /\ (TCX + 160 <= ACEIL)%Z
     /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) = (bv_unsigned sp - 128 - 64)%Z
     /\ bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) = (bv_unsigned sp - 128)%Z).
  { repeat split; first [assumption | lia]. }
  assert (SEP : (T + 4096 <= SB \/ SB + 2^37 + 4096 <= T)%Z /\ (T + 4096 <= 2147450880 \/ 17594333495295 < T)%Z
     /\ (T + 4096 <= 65536 \/ 12365824 <= T)%Z /\ (TCX + 160 <= SB \/ SB + 2^37 + 4096 <= TCX)%Z
     /\ (TCX + 160 <= T \/ T + 4096 <= TCX)%Z).
  { pose proof (unbox _ SEPT) as X1. pose proof (unbox _ OUTT) as X2. pose proof (unbox _ HT5) as X3. pose proof (unbox _ SEPTCX) as X4.
    pose proof (unbox _ SEPTT) as X5. clear - X1 X2 X3 X4 X5. unfold img_hull_lo, img_hull_hi in *. tauto. }
  apply box in GEO, SEP.
  apply box in Esa, Esn, Eesa, Eesn, RAN, Hmfal, Enew.
  tr_bx m MU1 WM1 FRP GEO SEP. tr_bx m MU1 WM1 LK GEO SEP. tr_bx m MU1 WM1 RT2 GEO SEP. tr_bxa m MU1 WM1 FL Hws GEO SEP.
  apply box in GC2, TC2, PC2, SHN2, ST82.
  clear AC RC ST8 TC SHF.
  lazymatch type of MU1 with munch _ _ ?mc => rename mc into m1 end.
  (* [comment removed for export] *)
  assert (Ek : Z.to_nat (new - mfa) = (4 * Z.to_nat ((new - mfa) / 4))%nat).
  { pose proof (unbox _ RAN). pose proof (unbox _ Hmfal). Z.div_mod_to_equations. lia. }
  rewrite Ek in ZNEW.
  replace (fa SB c + mfa)%Z with (fa SB c + 4 * Z.of_nat (length ws))%Z in ZNEW by lia.
  pose proof (u32arr_app_zeros m1 (fa SB c) ws (Z.to_nat ((new - mfa) / 4)) FL ZNEW) as FL2. clear FL ZNEW.
  unfold pfa_retE.
  replace (ret_pc (Z_to_bv 64 1708648)) with (Z_to_bv 64 1708648) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  rewrite Esp in ST1.
  replace (Z_to_bv 64 (bv_unsigned sp - 128 - 64)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 128)) - 64))
    by (rewrite Esp0; reflexivity).
  rewrite <- Esp0 in FRP, ST1.
  eapply evt_cut; [eapply (pfa_T_spec (Z_to_bv 64 gfa_retP) (Z_to_bv 64 (bv_unsigned sp - 128)) gp (Z_to_bv 64 tpA)
     (Z_to_bv 64 R) (Z_to_bv 64 INST) (Z_to_bv 64 (R + 8)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (fa SB c))
     (Z_to_bv 64 CH) (Z_to_bv 64 n) (Z_to_bv 64 1152921504606846976) (Z_to_bv 64 1500) (Z_to_bv 64 16140901064495857663)
     s10 s11 F fc ACEIL SB c R nfree new auser (muser + msz) (pfa_newc auser muser msz (ClassSize c)) lo
     (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))) | ].
  all: first [ assumption | (arith_goal; rewrite ?Esp0; lia) | (unfold pfa_newc; reflexivity) | (arith_goal; rewrite app_length, repeat_length; lia) | idtac ].
  1:{ exact RT2. }
  intros ms2 PO2. unfold pfa_Q, pfa_tail_post in PO2. destruct_exs PO2.
  destruct PO2 as (E2 & MU3 & WM3 & MI3 & FL3 & RC3 & EXH3 & ST3). subst ms2.
  unfold pfa_tail_W in MU3. rewrite Esp0 in MU3.
  lazymatch type of MU3 with munch _ ?mb ?mc => tr_bx mb MU3 WM3 LK GEO SEP; rename mc into m2 end.
  (* [comment removed for export] *)
  assert (MU13 : munch [(R + 16, R + 56); (R + 68, R + 69); (fa SB c, fa SB c + new); (esa, esa + esn); (T + 2872, T + 2888);
                        (bv_unsigned sp - 640, bv_unsigned sp - 128)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU1]| eapply munch_weaken; [|exact MU3]]; sub_bx GEO. }
  assert (WM13 : wmono ctasegs m m2) by (eapply wmono_trans; [exact WM1| exact WM3]).
  unfold gfa_retP.
  replace (ret_pc (Z_to_bv 64 1708168)) with (Z_to_bv 64 1708168) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  unfold ri_core in RC3. unfold fl_arr in FL3. rewrite Esp0 in ST3.
  pose proof (carve_length (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4)))
                (nfree + pfa_newc auser muser msz (ClassSize c)) auser (ClassSize c)
                (Z.to_nat (pfa_newc auser muser msz (ClassSize c)))) as CL3.
  rewrite app_length, repeat_length in CL3.
  zhide.
  zstep. ifF. zstep. zstep. zstep. ifF.
  do 5 zstep.
  apply unbox in FRG, RT1, RT3, CHS.
  tr_bx m MU13 WM13 FRG GEO SEP. tr_bx m MU13 WM13 RT1 GEO SEP. tr_bx m MU13 WM13 RT3 GEO SEP. tr_bxa m MU13 WM13 CHS Hchs GEO SEP.
  pose proof (ri_tail_join _ _ _ _ _ _ _ _ _ _ _ RT1 EXH3 RT3) as RT.
  eapply evt_mono; [eapply (gfa_tail_spec ra sp gp (Z_to_bv 64 tpA) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ACEIL SB c R CH n
     (nfree + pfa_newc auser muser msz (ClassSize c) - n) lo
     (carve (ws ++ repeat (Z_to_bv 64 0) (Z.to_nat ((new - mfa) / 4))) (nfree + pfa_newc auser muser msz (ClassSize c)) auser
        (ClassSize c) (Z.to_nat (pfa_newc auser muser msz (ClassSize c))))
     chs rand (Z_to_bv 8 0) pad nalloc nfreed r0 r1 r2 r3) | ].
  all: first [ assumption | (arith_goal; lia) | (eexists; eassumption)
             | (let G := fresh "G" in let S := fresh "S" in
                pose proof (unbox _ GEO) as G; pose proof (unbox _ SEP) as S; clear - G S; lia) | idtac ].
  intros ms3 PO3. unfold gfa_Q, gfa_ret_post in PO3. destruct_exs PO3.
  destruct PO3 as (E3 & MU4 & WM4 & MI4 & LK4 & RT4 & CHS4 & ST4). subst ms3.
  unfold gfa_tail_W in MU4.
  lazymatch type of MU4 with munch _ ?mb ?mc => tr_bx mb MU4 WM4 RC3 GEO SEP; tr_bxa mb MU4 WM4 FL3 CL3 GEO SEP; rename mc into m4 end.
  (* [comment removed for export] *)
  assert (MUf : munch (gfa_B2_W sp SB c R CH n new esa esn T) m m4).
  { unfold gfa_B2_W. eapply munch_trans; [eapply munch_weaken; [|exact MU13]| eapply munch_weaken; [|exact MU4]]; sub_bx GEO. }
  assert (WMf : wmono ctasegs m m4) by (eapply wmono_trans; [exact WM13| exact WM4]).
  assert (MU1f : munch [(R, R + 8); (R + 16, R + 56); (R + 68, R + 69); (R + 72, R + 80); (fa SB c, fa SB c + new);
                        (CH, CH + 4 * n); (bv_unsigned sp - 640, bv_unsigned sp)]%Z m1 m4).
  { eapply munch_trans; [eapply munch_weaken; [|exact MU3]| eapply munch_weaken; [|exact MU4]]; sub_bx GEO. }
  assert (WM1f : wmono ctasegs m1 m4) by (eapply wmono_trans; [exact WM3| exact WM4]).
  unfold gfa_B2_W in MUf.
  apply unbox in ZU, SHN, SAM, GC2, TC2, PC2, SHN2, ST82.
  destruct SAM as (w1 & SAM). destruct GC2 as (G1 & G2 & G3 & G4 & G5). destruct TC2 as [(KI & K & TS & T0) TT].
  unfold g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main in KI, K, TS, T0.
  tr_bx m MUf WMf ZU GEO SEP. tr_bx m MUf WMf SAM GEO SEP. tr_bx m1 MU1f WM1f ST82 GEO SEP.
  tr_bx m MUf WMf SHN GEO SEP. tr_bx m1 MU1f WM1f SHN2 GEO SEP.
  tr_bx m1 MU1f WM1f G1 GEO SEP. tr_bx m1 MU1f WM1f G2 GEO SEP. tr_bx m1 MU1f WM1f G3 GEO SEP. tr_bx m1 MU1f WM1f G4 GEO SEP.
  tr_bx m1 MU1f WM1f G5 GEO SEP. tr_bx m1 MU1f WM1f KI GEO SEP. tr_bx m1 MU1f WM1f K GEO SEP. tr_bx m1 MU1f WM1f TS GEO SEP.
  tr_bx m1 MU1f WM1f T0 GEO SEP.
  assert (PCf : PC m4) by (apply (HPF m1 m4 _ PC2 MU1f WM1f); cbn [disjoint_from];
    let G := fresh "G" in let S := fresh "S" in
    pose proof (unbox _ GEO) as G; pose proof (unbox _ SEP) as S; unfold img_hull_lo, img_hull_hi; clear - G S; lia).
  tr_bx m1 MU1f WM1f TT GEO SEP.
  unfold gfa_B2_post.
  do 15 eexists. split; [reflexivity|].
  split; [exact MUf|]. split; [exact WMf|].
  split; [assumption|]. split; [assumption|]. split; [exact RC3|]. split; [assumption|]. split; [exact FL3|].
  split; [assumption|]. split; [exact ZU|]. split; [exact SHN|]. split; [exact SHN2|]. split; [exact ST82|].
  split; [eexists; exact SAM|].
  split; [unfold mm_gcells; repeat (split; [assumption|]); assumption|].
  split; [unfold thread_cells, tsd_cells, g_tsd_key_inited, g_tsd_key, pth_tsd, g_pthread_tsd_main;
          split; [split; [exact KI|split; [exact K|split; [exact TS|exact T0]]]|exact TT]|].
  split; [exact PCf| exact ST4].
Qed.
End GFAB2.
