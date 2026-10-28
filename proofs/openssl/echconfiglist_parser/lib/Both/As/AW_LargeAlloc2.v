(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit F_memset.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_Leaves AW_PoisonShadow AW_MmapFixed AW_SecMmap CidBits SecMsb AW_Combined AW_AllocBase AW_LargeAlloc1 AllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition moframe (sp : word) (msz : Z) (stat : word) (m2 : mem) (j12 : list byte) : Prop :=
  rw_cells asegs m2 (bv_unsigned sp + -144) [CB 12 j12; C4 (wz 34); C8 (wz msz); C8 (wz (AINST + 64)); C8 stat; C8 (wz 0x19b9f0)].

Definition large_alloc_seg2_post (sp gp tp s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size msz a sha sht nres nch TH : Z) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra stat : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a5 a6 a7 t3 t4 t5 t6 : word) (j8 : list byte) m',
    ms' = MS (mkR (wz 0x19ba5c) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2
                  stat (wz (AINST + 64)) (wz (a + 4096)) a1 a2 (wz nch) (wz nres) a5 a6 a7
                  (wz msz) (wz (clzbits msz)) (wz a) (wz a) (wz (a + msz)) (wz (a + 4096 + size)) (wz 7) (wz (a + 4096)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bb94) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (sha, sha + 512); (sht, sht + (msz - 4096 - size) / 8); (a, a + 24);
              (TH + 2800, TH + 3168); (AINST + 680, AINST + 684)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ laframe sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra m' j8
    /\ u8arr asegs m' sha (repeat (b8 0xfa) 512)
    /\ u8arr asegs m' sht (repeat (b8 0xfa) (Z.to_nat ((msz - 4096 - size) / 8)))
    /\ rw_cells asegs m' a [C8 (wz a); C8 (wz msz); C8 (wz size)]
    /\ stk asegs m' (a + 24) (a + 4096)
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (AINST + 680) [C4 (wz 1); C4 (wz 0)].

Lemma land_low0 : forall x j, 0 <= j -> x mod 2^j = 0 -> Z.land x (2^j - 1) = 0.
Proof. intros x j Hj Hx. replace (2^j - 1) with (Z.pred (2^j)) by lia. rewrite <- Z.ones_equiv, Z.land_ones by lia. exact Hx. Qed.

Lemma rw_cells_C8_zero_split' : forall m A cs, rw_cells asegs m A (C8 (Z_to_bv 64 0) :: cs) -> rw_cells asegs m A (C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: cs).
Proof. intros m A cs [[[_ W] B] R]. exact (conj (conj (conj I (conj I W)) B) R). Qed.

End HCW.


Ltac remregF n name eqname folded :=
  remreg n name eqname; match type of eqname with ?e = _ => change (e = folded) in eqname end.

Section Seg2.
  Context {HCEIL : HeapCeil}.
  Variables (sp gp tp t0 t1 t2 a6 s4 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (s0 s1 s2 s3 s5 s8 ra stat : word) (j8 j12 : list byte).
  Variables (lo size msz a sha sht size8 TSD CTX TH pa nres nch : Z) (sbs1 sbs3 : list byte).
  Hypothesis DEFS : hidden (msz = round_up size 4096 + 4096 /\ sha = sh a /\ sht = sh (a + 4096 + size)).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -144).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 416 <= bv_unsigned sp. Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPH : bv_unsigned sp + 16 <= 2^47.
  Hypothesis SZ : 0x10000 < size /\ size <= 2^41 /\ size = 8 * size8.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil. Hypothesis AAL : hidden (a mod 4096 = 0).
  Hypothesis SHT : sht = sha + 512 + size8.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis NCH : 0 <= nch <= nres /\ nres + 16384 <= 2^20.
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)).
  Hypothesis ENV : SENV tp TSD CTX TH m.
  Hypothesis FR : laframe sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra m j8.
  Hypothesis MOFR : moframe sp msz stat m j12.
  Hypothesis INST64 : rw_cells asegs m (AINST + 64) [C8 (wz 4096); C8 (wz pa); C8 (wz pa)].
  Hypothesis NRES : rw_cells asegs m (AINST + 112) [C8 (wz nres); C8 (wz nch); C8 (wz 0)].
  Hypothesis MTX : rw_cells asegs m (AINST + 680) [C8 (wz 0)].
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis HDR : stk asegs m a (a + 4096).
  Hypothesis SH1 : u8arr asegs m sha sbs1. Hypothesis SH1L : Z.of_nat (length sbs1) = 512.
  Hypothesis SH3 : u8arr asegs m sht sbs3. Hypothesis SH3L : Z.of_nat (length sbs3) = (msz - 4096 - size) / 8.

  Let ARE : 12599296 <= a /\ a + msz <= aceil.
  Proof. destruct DEFS as [(DM & _)]. refine (aapp_env _ _ (proj1 AR) _). rewrite DM. unfold round_up. clear - SZ. Z.div_mod_to_equations. lia. Qed.   (* [comment removed for export] *)
  Theorem large_alloc_seg2 :
    evt asegs (large_alloc_seg2_post sp gp tp s10 s11 F fc m lo size msz a sha sht nres nch TH s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ra stat)
      (MS (mkR (wz 0x1d3268) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 (wz 0x2ebe7) (wz msz) (wz a) (wz msz) (wz 3) (wz 34) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz APAGESZ) (wz size) s4 (wz 8) s6 s7 (wz 7) s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    destruct DEFS as [(DMSZ & DSHA & DSHT)].
    assert (MSZ : size + 4096 <= msz /\ msz < size + 8192 /\ exists q, msz = 4096 * q).
    { rewrite DMSZ. unfold round_up. split; [|split]; try (Z.div_mod_to_equations; lia).
      exists ((size + 4096 - 1) / 4096 + 1). lia. }
    destruct MSZ as (MSZ1 & MSZ2 & mq & MQ).
    assert (AQ : exists aq, a = 4096 * aq) by (destruct AAL as [AAL']; exists (a / 4096); Z.div_mod_to_equations; lia).
    destruct AQ as [aq AQ].
    assert (T8 : exists t8, msz - 4096 - size = 8 * t8 /\ 0 <= t8 < 512) by (exists ((msz - 4096 - size) / 8); Z.div_mod_to_equations; lia).
    destruct T8 as (t8 & T8 & T8R).
    assert (BND : aceil <= lo /\ 12599296 <= CTX /\ CTX + 160 <= aceil /\ 4096 <= TH /\ TH + 4096 <= aceil
                 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ 12109808 <= TSD /\ TSD + 8 <= 12599296
                 /\ 12599296 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil   (* [comment removed for export] *)
                 /\ 2148314624 <= sha /\ sht + t8 <= 17594333495296).
    { destruct RNG as [RNG']; destruct TPR as [TPR']. unfold AHI_LO, AIMG_TOP in *. acb.
      rewrite DSHA in SHT |- *. clear - LO RNG' TPR' AR SHT T8 T8R SZ MSZ1; try acb. unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. aunf; lia. }
    unfold AINST, APAGESZ in *. change (6976152 + 64) with 6976216 in *. change (6976152 + 112) with 6976264 in *.
    change (6976152 + 680) with 6976832 in *. change (6976152 + 684) with 6976836 in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp); (sha, sha + 512); (sht, sht + (msz - 4096 - size) / 8); (a, a + 24);
              (TH + 2800, TH + 3168); (6976832, 6976836)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    replace ((msz - 4096 - size) / 8) with t8 in * by lia.
    unfold laframe in FR. unfold moframe in MOFR. unfold AINST in MOFR. change (6976152 + 64) with 6976216 in MOFR.
    region_table.
    unfold wz in *.
    (* [comment removed for export] *)
    pose proof (se_got _ _ _ _ _ ENV) as Egot. unfold AGOT_VALS in Egot; cbn [map] in Egot. pose proof (se_mlim _ _ _ _ _ ENV) as Emlim.
    callN mmap_or_die_seg2; rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; (first [clear - HI SPH SZ SHT SH3L ARE DSHA DSHT AQ T8 BND ACEILB; lia | lia])); try lia.
    replace (ret_pc (Z_to_bv 64 1686000)) with (Z_to_bv 64 1686000) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
    replace (bv_unsigned sp + -144 + 48) with (bv_unsigned sp + -96) in * by lia.
    clear Egot Emlim.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    unfold wz in *. rewrite ?(unsigned_lit a) in * by lia.
    step. step. step. step.
    replace (Z.land 4095 (bv_unsigned (Z_to_bv 64 a))) with 0.
    2:{ rewrite (unsigned_lit a), Z.land_comm by lia. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. rewrite AQ, Z.mul_comm. symmetry. apply Z_mod_mult. }
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. step. rewrite (unsigned_lit (4096 + a)) by lia.
    replace (Z.land (4096 + a) 7) with 0 by (symmetry; apply (land_low0 (4096 + a) 3); [lia| change (2^3) with 8; rewrite AQ; Z.div_mod_to_equations; lia]).
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step. replace (0 + (4096 + a)) with (a + 4096) by lia. replace (msz + a) with (a + msz) by lia.
    (* [comment removed for export] *)
    step. step. step. rewrite (unsigned_lit (a + 4096 + size)) by lia.
    change 18446744073709551608 with (2^64 - 2^3)%Z. rewrite StrFun.land_align_down by (first [clear - HI SPH SZ SHT SH3L ARE DSHA DSHT AQ T8 BND SPR; lia | lia]).
    replace (a + 4096 + size - (a + 4096 + size) mod 2^3) with (a + 4096 + size) by (change (2^3) with 8; Z.div_mod_to_equations; lia).
    region_sides. name_bands.
    step. rewrite (unsigned_lit (a + 4103)) by lia.
    change 18446744073709551608 with (2^64 - 2^3)%Z. rewrite StrFun.land_align_down by lia.
    replace (a + 4103 - (a + 4103) mod 2^3) with (a + 4096) by (change (2^3) with 8; Z.div_mod_to_equations; lia).
    step. rewrite ?(unsigned_lit (a + 4096)), ?(unsigned_lit a) by lia. replace (a + 4096 - a) with 4096 by lia. step. step.
    (* [comment removed for export] *)
    senv_at ENV MU WM ENV1. destruct ENV1. unfold AGOT_VALS in se_got. cbn [map] in se_got.
    step. rewrite DSHA in SH1.
    callN (poison_shadow_specK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo a (sh a) 512 250 sbs1);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; (lia_guard; (lia_guard; first [clear - HI; lia | lia]))); try (lia_guard; lia).
    all: try (unfold AHI_LO, ALOWSH_LO; clear - BND AR SZ MSZ1 AQ; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    change (Z.to_nat 512) with 512%nat in POST0.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (a + msz)), ?(unsigned_lit (a + 4096 + size)) by lia.
    replace (a + msz - (a + 4096 + size)) with (8 * t8) by lia. step. step.
    step. rewrite DSHT in SH3.
    callN (poison_shadow_specK0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (a + 4096 + size) (sh (a + 4096 + size)) t8 250 sbs3);
      rewrite ?unsigned_lit by lia; try eassumption; try reflexivity; try (acb; (lia_guard; (lia_guard; first [clear - HI; lia | lia]))); try (lia_guard; (lia_guard; lia)).
    all: try (unfold AHI_LO, ALOWSH_LO; clear - BND AR SZ MSZ1 AQ T8 T8R; aunf; repeat split; try lia; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    step. callN getcurthreadstats_spec; rewrite ?unsigned_lit by lia; try eassumption; try reflexivity;
      try (unfold AIMG_TOP; acb; (first [clear - HI BND; lia | lia])); try lia.
    clear se_tsdi se_tp se_tsd se_ctx se_can se_got se_shb se_hme se_thresh se_mlim se_dpm se_rms se_psc se_name.
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ ?mc (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2872) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H;
      destruct (stk_split asegs _ (TH + 2872) (TH + 2888) (TH + 3168) TS2 ltac:(hci; lia)) as [TS3 TS4]; clear TS2;
      destruct (stk_cells _ _ _ TS3 ltac:(hci; lia)) as [tj TJ]; clear TS3 end.
    replace (TH + 2888 - (TH + 2872)) with 16 in TJ by lia. change (Z.to_nat 16) with 16%nat in TJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 tj [] [8;8]%nat) in TJ; [| reflexivity]. cbn [mk_CB_cells app] in TJ.
    repeat match type of TJ with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in TJ end.
    repeat match type of TJ with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in TJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    unfold wz in *.
    step. step.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (a + 4096)) by lia.
    replace (Z.land (a + 4096) 7) with 0 by (symmetry; apply (land_low0 (a + 4096) 3); [lia| change (2^3) with 8; rewrite AQ; Z.div_mod_to_equations; lia]).
    step. step. step. step.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step. step. step. step. rewrite (unsigned_lit (a + 4096)) by lia.
    replace (Z.land 4095 (a + 4096)) with 0 by (rewrite Z.land_comm; symmetry; apply (land_low0 (a + 4096) 12); [lia| change (2^12) with 4096; rewrite AQ; Z.div_mod_to_equations; (first [clear - H H0; lia | lia])]).
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (a + 4096)) by lia. replace (a + 4096 - 4096) with a by lia.
    lazymatch goal with H : stk _ ?mc a (a + 4096) |- _ =>
      destruct (stk_split asegs _ a (a + 24) (a + 4096) H ltac:(hci; lia)) as [HD1 HD2]; clear H;
      destruct (stk_cells _ _ _ HD1 ltac:(hci; lia)) as [hj HJ]; clear HD1 end.
    replace (a + 24 - a) with 24 in HJ by lia. change (Z.to_nat 24) with 24%nat in HJ.
    apply (rw_cells_split_CB asegs _ _ [] 24 hj [] [8;8;8]%nat) in HJ; [| reflexivity]. cbn [mk_CB_cells app] in HJ.
    repeat match type of HJ with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in HJ end.
    repeat match type of HJ with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in HJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    st1. st1. st1.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    apply rw_cells_C8_zero_split' in MTX.
    step. step. step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step.
    assert (MA : 6976832 mod 4 = 0) by reflexivity. assert (MR : 0 <= 6976832 < 2^64) by lia.
    astep.
    (* [comment removed for export] *)
    step. step. step. step.
    repeat match goal with |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
                         | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    astep.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step.
    try match goal with |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step. step. rewrite (unsigned_lit nch), Z.shiftr_div_pow2 by lia.
    replace (nch / 2 ^ 20) with 0 by (symmetry; apply Z.div_small; lia).
    step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    assert (Rmsz : 0 <= msz < 18446744073709551616) by (first [clear - SZ SHT ARE DSHA DSHT MSZ1 MQ T8 T8R BND SPR; lia | lia]).
    step. step. step. step. step. remregF 11 e1 E1 (cb1 msz).
    step. step. step. step. step. remregF 11 e2 E2 (cb2 e1).
    do 8 step. remregF 11 e3 E3 (cb3 e2).
    step. step. remregF 11 e4 E4 (cb4 e3).
    step. step. remregF 11 e5 E5 (cb5 e4).
    step. step. remregF 11 e6 E6 (cb6 e5).
    step. remregF 11 e7 E7 (cb7 e6).
    step. step. step. step. remregF 11 e8 E8 (cb8 e7).
    step. step. step. step. step. step. remregF 11 e9 E9 (cb9 e8).
    step. step. remregF 11 e10 E10 (cb10 e9).
    step. step. step. step. step. remregF 19 e11 E11 (cb11 e10).
    assert (CLZ : e11 = clzbits msz) by (rewrite E11, E10, E9, E8, E7, E6, E5, E4, E3, E2, E1; unfold clzbits, popbits, smear; reflexivity).   (* [comment removed for export] *)
    rewrite CLZ. clear E1 Re1 E2 Re2 E3 Re3 E4 Re4 E5 Re5 E6 Re6 E7 Re7 E8 Re8 E9 Re9 E10 Re10 Re11.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (stk_of_rw_cells _ _ _ _ TJ) as Q2; cbn [cells_size csize Nat.add] in Q2; change (Z.of_nat 16) with 16%Z in Q2;
      replace (TH + 2872 + 16) with (TH + 2888) in Q2 by lia;
      assert (TSTn : stk asegs mc (TH + 2800) (TH + 3168))
        by (eapply stk_merge; [exact TS1| eapply stk_merge; [exact Q2| exact TS4| lia]| lia]) end.
    clear TJ Q2 TS1 TS4.
    rewrite <- DSHA in POST0. rewrite <- DSHT in POST.
    apply evt_done. unfold large_alloc_seg2_post, laframe, AINST.
    change (6976152 + 64) with 6976216. change (6976152 + 680) with 6976832. change (6976152 + 684) with 6976836.
    replace ((msz - 4096 - size) / 8) with t8 by lia.
    do 12 eexists. exists j8. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.
End Seg2.

