(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim Malloc Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import LhPure LhRep.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_iface_pem D_defs D_kit D_agree R_cache_defs Fz_kit I_ut Fz_chk Fz_fkit Fz_I1_img Fz_I1_hash Fz_I1_defs Fz_I1_getrn Fz_I1_retrieve Fz_I1_split Fz_I1_expand Fz_env Fz_M_malloc Fz_M_realloc Fz_M_realloc_array Fz_I1_insw Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition LHI_EPI : Z := 0x20078c.            (* [comment removed for export] *)
Definition SITE_lhi_getrn : Z := 0x200494.     (* [comment removed for export] *)
Definition SITE_lhi_malloc : Z := 0x2006e0.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition lhi_saved (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : list cell :=
  [C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

(* [comment removed for export] *)
Lemma lhi_epi : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo : Z) (sp0 rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) (LOC : list cell),
  sp = Z_to_bv 64 (bv_unsigned sp0 + -192) -> cells_size LOC = 88%nat ->
  rw_cells asegs m (bv_unsigned sp0 + -192) (LOC ++ lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) ->
  stk asegs m lo (bv_unsigned sp0 + -192) -> lo <= bv_unsigned sp0 - 192 -> bv_unsigned sp0 <= 2^47 -> 192 <= bv_unsigned sp0 -> mem_inv asegs m ->
  evt asegs (fun ms' => ms' = MS (mkR rav sp0 gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (ret_pc rav) fc None m (seg_rom asegs)
                        /\ stk asegs m lo (bv_unsigned sp0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 LHI_EPI) fc None m (seg_rom asegs)).
Proof.
  intros until LOC. intros -> SZ FR ST LO HTOP H192 MI. unfold lhi_saved in FR. unfold LHI_EPI.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  cl_eu (bv_unsigned sp0) (-192) EU1.
  apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [FRL FRS]. rewrite SZ in FRS. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in FRS.
  replace (bv_unsigned sp0 + -192 + 88) with (bv_unsigned sp0 + -104) in FRS by lia.
  do 13 zstep. zstep.
  assert (FR : rw_cells asegs m (bv_unsigned sp0 + -192) (LOC ++ lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)).
  { apply rw_cells_app. split; [exact FRL|]. rewrite SZ. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp0 + -192 + 88) with (bv_unsigned sp0 + -104) by lia. exact FRS. }
  eapply stk_release in FR; [| exact ST| lia]. rewrite cells_size_app, SZ in FR. cbn [cells_size csize Nat.add lhi_saved] in FR.
  replace (bv_unsigned sp0 + -192 + Z.of_nat 192) with (bv_unsigned sp0) in FR by lia.
  zstep. apply evt_done. split; [| exact FR]. cbv delta [mkR]. replace (bv_unsigned sp0 + -192 + 192) with (bv_unsigned sp0) by lia. rewrite ?(Z_to_bv_bv_unsigned sp0). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma lh_rep_set_data : forall (GOBJ : Z -> Z -> Prop) (m m' : mem) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    (i : Z) (ns1 rest : list (bptr * Z)) (pk : bptr) (Ak d : Z),
  lapart L -> lh_rep asegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
  0 <= i < g_na g -> nth (Z.to_nat i) bks [] = ns1 ++ (pk, Ak) :: rest ->
  DVerr GOBJ d -> rw_cells asegs m' Ak [C8 (Z_to_bv 64 d)] ->
  LhRep.agree_on asegs (fun a => ~ (Ak <= a < Ak + 8) /\ lh_fp lh B g bks a) m m' ->
  lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks.
Proof.
  intros GOBJ m m' L lh B g bks i ns1 rest pk Ak d LAP REP HI ENTH DVd NEWD AG.
  destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) REP) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  assert (INK : In (pk, Ak) (nth (Z.to_nat i) bks [])) by (rewrite ENTH; apply in_or_app; right; left; reflexivity).
  destruct (S_N _ pk Ak LI INK) as [KL KB].
  pose proof (S_F _ LI) as FO. rewrite ENTH, map_app in FO. cbn [map snd] in FO. destruct (fop_app_inv _ _ _ FO) as (FO1 & FO2 & X12). inversion FO2 as [|x l FA FO3]; subst x l.
  eapply (lh_rep_upd asegs LH_CEIL (DVerr GOBJ) m m' (ownL L) (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g g bks bks (fun j => j = i) REP);
    try reflexivity; try assumption.
  - intros j. destruct (Z.eq_dec j i); [left; assumption| right; assumption].
  - exists x40, x48, err, pad. eapply LhRep.rw_cells_agree; [exact AG| exact SC|]. intros a Ha. unfold lh_cells in Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    split; [lia| left; lia].
  - intros q A n nm _ X. exact X.
  - (* [comment removed for export] *)
    intros j Hj ->. rewrite ENTH. pose proof (CH i Hj) as (c' & SG & TERM). rewrite ENTH in SG.
    destruct (lseg_split asegs LH_CEIL _ _ _ _ _ _ _ SG) as (c1 & SG1 & SG2). cbn [lseg] in SG2. destruct SG2 as (CC & OWN & RG & (d0 & hN & N1 & _ & N2) & SG3).
    assert (INI : forall q A, In (q, A) (ns1 ++ (pk, Ak) :: rest) -> lh_fp lh B g bks A /\ forall a, A <= a < A + 24 -> lh_fp lh B g bks a).
    { intros q A Hq. split; [| intros a Ha]; right; right; exists q, A; (split; [eapply in_concat_nth; [exact LI| rewrite ENTH; exact Hq]| lia]). }
    exists c'. split; [| eapply LhRep.rw_cells_agree; [exact AG| exact TERM|]].
    2:{ intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
        destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ SG) as [[E ->]|(pre & q & A & E & ->)]; [exfalso; destruct ns1; discriminate E|].
        assert (HqA : In (q, A) (ns1 ++ (pk, Ak) :: rest)) by (rewrite E; apply in_or_app; right; left; reflexivity).
        split; [| exact (proj2 (INI q A HqA) a ltac:(lia))].
        (* [comment removed for export] *)
        destruct (Z.eq_dec A Ak) as [->|NE]; [lia|].
        assert (AP : apart24 A Ak \/ apart24 Ak A).
        { apply in_app_or in HqA. destruct HqA as [H1|[H1|H1]]; [left; apply X12; [apply (in_map snd) in H1; exact H1| left; reflexivity]| injection H1; intros; subst; contradiction| right].
          exact (proj1 (Forall_forall _ _) FA A ltac:(apply (in_map snd) in H1; exact H1)). }
        unfold apart24 in AP. lia. }
    eapply lseg_app.
    + eapply lseg_agree; [exact SG1| | intros ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact AG|]. intros a Ha.
      destruct (lseg_fp_where _ _ _ Ha) as [H0|(q & A & Hq & H0)].
      * split; [lia| right; left; lia].
      * pose proof (X12 A Ak ltac:(apply (in_map snd) in Hq; exact Hq) ltac:(left; reflexivity)) as AP. unfold apart24 in AP.
        split; [lia| exact (proj2 (INI q A ltac:(apply in_or_app; left; exact Hq)) a H0)].
    + cbn [lseg]. split.
      { eapply LhRep.rw_cells_agree; [exact AG| exact CC|]. intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
        destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ SG1) as [[-> ->]|(pre & q & A & -> & ->)]; [split; [lia| right; left; lia]|].
        pose proof (X12 A Ak ltac:(rewrite map_app; apply in_or_app; right; left; reflexivity) ltac:(left; reflexivity)) as AP. unfold apart24 in AP.
        split; [lia| exact (proj2 (INI q A ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) a ltac:(lia))]. }
      split; [exact OWN|]. split; [exact RG|]. split.
      { exists d, hN. split; [exact NEWD|]. split; [exact DVd|]. eapply LhRep.rw_cells_agree; [exact AG| exact N2|]. intros a Ha. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
        split; [lia| exact (proj2 (INI pk Ak ltac:(apply in_or_app; right; left; reflexivity)) a ltac:(lia))]. }
      eapply lseg_agree; [exact SG3| | intros ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact AG|]. intros a Ha.
      destruct (lseg_fp_where _ _ _ Ha) as [H0|(q & A & Hq & H0)]; [split; [lia| exact (proj2 (INI pk Ak ltac:(apply in_or_app; right; left; reflexivity)) a ltac:(lia))]|].
      pose proof (proj1 (Forall_forall _ _) FA A ltac:(apply (in_map snd) in Hq; exact Hq)) as AP. unfold apart24 in AP.
      split; [lia| exact (proj2 (INI q A ltac:(apply in_or_app; right; right; exact Hq)) a H0)].
  - intros j Hj NE. split; [reflexivity|]. eapply LhRep.agree_on_mono; [exact AG|]. intros a [Ha|(q & A & Hq & Ha)].
    + split; [lia| right; left; lia].
    + assert (LJ : (Z.to_nat j < length bks)%nat) by lia.
      pose proof (S_X (Z.to_nat j) (Z.to_nat i) (q, A) (pk, Ak) LJ LI ltac:(intros E; apply NE; lia) Hq INK) as AP. cbn [snd] in AP. unfold apart24 in AP.
      split; [lia|]. right; right. exists q, A. split; [eapply in_concat_nth; [exact LJ| exact Hq]| exact Ha].
Qed.

(* [comment removed for export] *)
Definition lhi_wg_post (sp gp tp s3 s5 s10 s11 : word) (F0 : bvmap 5 word) (lo : Z) (m : mem) (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B data : Z) (g : lh_geo)
    (bks : list (list (bptr * Z))) (jl : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem) (i : Z) (ns1 ns2 : list (bptr * Z)) (rn : Z) (h : word),
    0 <= i < g_nn g /\ nth (Z.to_nat i) bks [] = ns1 ++ ns2 /\ mem_inv asegs m' /\ wmono asegs m m'
    /\ ( (ns2 = [] /\ lseg asegs LH_CEIL (DVerr GOBJ) m' (ownL L) (B + 8 * i) ns1 rn /\ rw_cells asegs m' rn [C8 (Z_to_bv 64 0)]
          /\ ms' = MS (mkR (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
                        (Z_to_bv 64 24) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 130) a3 a4 a5 a6 a7
                        (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
                        (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - 304, bv_unsigned sp - 104)]%Z m m'
          /\ rw_cells asegs m' (bv_unsigned sp + -192) (CB 80 jl :: C8 h :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
          /\ stk asegs m' lo (bv_unsigned sp + -192)
          /\ lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks)
      \/ (exists (pk : bptr) (Ak d0 : Z) (rest : list (bptr * Z)), ns2 = (pk, Ak) :: rest /\ DVerr GOBJ d0
          /\ ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 d0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
                   F (ret_pc rav) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - 304, bv_unsigned sp); (Ak, Ak + 8)]%Z m m'
          /\ stk asegs m' lo (bv_unsigned sp)
          /\ lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks) ).

Lemma lhi_wg : forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (GOBJ : Z -> Z -> Prop) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (data lo : Z) (kw : word)
    (jl jh : list byte) (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  lh_rep asegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks -> lapart L ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> lh + 104 <= lo -> 0x10007fff8000 <= lh ->
  acc asegs m B (8 * g_na g) -> B mod 8 = 0 -> B + 8 * g_na g <= lo -> 0x10007fff8000 <= B ->
  (forall p A, In (p, A) (concat bks) -> acc asegs m A 24 /\ A mod 8 = 0 /\ A + 24 <= lo) -> (forall p A, In (p, A) (concat bks) -> 0x10007fff8000 <= A) ->
  (forall d, DVerr GOBJ d -> (exists e : word, ro_cells asegs m d [C8 e]) /\ acc asegs m d 8) -> IMG_UT_HI <= lo ->
  ro_cells asegs m data [C8 kw] -> acc asegs m data 8 -> data mod 8 = 0 -> data + 8 <= lo -> DVerr GOBJ data -> (data + 8 <= lh \/ lh + 104 <= data) ->
  rw_cells asegs m (bv_unsigned sp + -192) (CB 80 jl :: CB 8 jh :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) ->
  acc asegs m (bv_unsigned sp - 192) 192 -> bv_unsigned sp mod 16 = 0 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)] ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 304 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_wg_post sp gp tp s3 s5 s10 s11 F lo m GOBJ L lh B data g bks jl rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) s5 s3
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LHI_SPLIT_EXIT) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros REP LAP ACCL ALL LLO LHI ACCB ALB BLO BHI NODES NHI DVF UTLO KC KA KAL KLO DVD KSEP FR ACCF SPAL UT SHC ST LO0 LO HTOP MI.
  unfold g_shadow_memory_dynamic_address, SHB in SHC. unfold LHI_SPLIT_EXIT. unfold lhi_saved in FR.
  pose proof REP as (G & OL & RL & (x40 & x48 & err & pad & SC) & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB. pose proof G as (G1 & G2 & G3 & G4 & G5 & G6).
  unfold lh_cells, ERR_FNS_A, lf_comp, lf_hash, lf_hashw, lf_compw, wz, e_err_cmp, e_err_hash, e_err_hash_thunk, e_err_comp_thunk in SC.
  destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) REP) as (S_LB & S_N & S_X & S_F).
  unfold USTACK_TOP, IMG_UT_HI in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (ro_cells_bound _ _ _ _ KC) as KB. cbn [cells_size csize Nat.add] in KB.
  pose proof (munch_refl [(bv_unsigned sp - 304, bv_unsigned sp - 104)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWU : ut_fp W) by ut_fp_lia; assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) (-192) EU1. cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0.
  (* [comment removed for export] *)
  change (CB 80 jl :: CB 8 jh :: ?sv) with ([CB 80 jl] ++ CB 8 jh :: sv) in FR. apply (cb8_c8_in m _ [CB 80 jl] _ _) in FR.
  change ([CB 80 jl] ++ C8 (le_bytes_to_word jh) :: ?sv) with ([CB 80 jl] ++ [C8 (le_bytes_to_word jh)] ++ sv) in FR.
  apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F80 FR]. apply (proj1 (rw_cells_app _ _ _ _)) in FR. destruct FR as [F0 FS].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in F0, FS.
  replace (bv_unsigned sp + -192 + 80) with (bv_unsigned sp + -112) in F0 by lia. replace (bv_unsigned sp + -192 + 80 + 8) with (bv_unsigned sp + -104) in FS by lia.
  assert (HPA : acc asegs m (bv_unsigned sp + -112) 8) by (apply (acc_sub asegs m _ _ _ _ ACCF); lia).
  (* [comment removed for export] *)
  do 3 zstep. zstep.
  eapply evt_cut; [eapply getrn_proof with (GOBJ := GOBJ) (L := L) (lh := lh) (B := B) (g := g) (bks := bks) (data := data) (hp := bv_unsigned sp + -112) (lo := lo) | post_call asegs m];
    [exact REP| exact ACCL| exact ALL| exact LLO| exact ACCB| exact ALB| exact BLO| exact NODES| exact DVF| unfold IMG_UT_HI; lia
    | reflexivity| reflexivity| first [reflexivity| rewrite EU0; reflexivity]
    | exact KC| exact KA| exact KAL| exact KLO| (destruct DVD as (_ & DLO & _); unfold IMG_UT_LO in DLO; clear - DLO; lia)
    | exact F0| exact HPA| Z.div_mod_to_equations; lia| rewrite EU1; lia| unfold USTACK_TOP; lia
    | exact UT| exact SHC| rewrite EU1; exact ST| lia| rewrite EU1; lia| lia| assumption|].

  lazymatch goal with S1 : lseg _ _ _ ?mq _ _ ?n1 ?r, C2 : chain _ _ _ _ _ _ ?n2, HI : 0 <= ?i < _, HP2 : rw_cells _ _ (bv_unsigned sp + -112) [C8 ?hh] |- _ =>
    rename mq into m2; rename r into rn; rename n1 into ns1; rename n2 into ns2; rename i into idx; rename hh into h end.
  lazymatch goal with H : stk asegs m2 lo _ |- _ => rewrite EU1 in H; rename H into ST2 end.
  lazymatch goal with H : lseg _ _ _ m2 _ _ ns1 rn |- _ => rename H into S1 end.
  lazymatch goal with H : chain _ _ _ m2 _ rn ns2 |- _ => rename H into C2 end.
  lazymatch goal with H : nth _ bks [] = ns1 ++ ns2 |- _ => rename H into ENTH end.
  lazymatch goal with H : rw_cells _ m2 (bv_unsigned sp + -112) [C8 h] |- _ => rename H into HP2 end.
  lazymatch goal with H : munch _ m m2 |- _ => rename H into MU2 end. lazymatch goal with H : wmono asegs m m2 |- _ => rename H into WM2 end.
  assert (LI : (Z.to_nat idx < length bks)%nat) by lia.
  destruct (chain_chainv asegs LH_CEIL _ _ _ _ _ C2) as (v & CRN & CV). unfold wz in CRN.
  pose proof (rw_cells_bound _ _ _ _ CRN) as RNB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RNB.
  assert (RNACC : exists p n, acc asegs m p n /\ p mod 8 = 0 /\ 0 <= p /\ p <= rn /\ rn + 8 <= p + n /\ p + n <= 2^47 /\ 0x10007fff8000 <= p).
  { destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & -> & ->)].
    - exists B, (8 * g_na g). split; [exact ACCB|]. split; [exact ALB|]. lia.
    - pose proof (in_concat_nth bks _ _ LI ltac:(rewrite ENTH; apply in_or_app; left; apply in_or_app; right; left; reflexivity) : In (q, A) (concat bks)) as INQ.
      destruct (NODES q A INQ) as (X1 & X2 & X3). pose proof (NHI q A INQ) as X4.
      pose proof (lseg_ranges asegs LH_CEIL _ _ _ _ _ _ S1 q A ltac:(apply in_or_app; right; left; reflexivity)) as [R0 _].
      exists A, 24. split; [exact X1|]. split; [exact X2|]. lia. }

  (* [comment removed for export] *)
  assert (RNAL : rn mod 8 = 0).
  { destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ->]|(pre & q & A & -> & ->)].
    - clear - ALB. lia.
    - destruct (NODES q A ltac:(eapply in_concat_nth; [exact LI| rewrite ENTH; apply in_or_app; left; apply in_or_app; right; left; reflexivity])) as (_ & X2 & _). clear - X2. lia. }
  destruct RNACC as (pa & na' & PACC & PAL & PA0 & PA1 & PA2 & PA3 & PA4).
  zstep.
  do 3 zstep. zstep. th_if_lit. zstep.

  destruct ns2 as [|[pk Ak] rest]; cbn [chainv] in CV.
  - (* [comment removed for export] *)
    subst v. zstep. if_cases K1; zify_cond K1. 2:{ exfalso. apply K1. reflexivity. }
    do 4 zstep. zstep.

    assert (REP2 : lh_rep asegs LH_CEIL (DVerr GOBJ) m2 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
    { eapply lh_rep_agree; [exact REP| | intros ? ? ? ? _ X; exact X]. eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU2 WM2)|].
      intros a Ha. cbn [outside]. destruct Ha as [Ha|[Ha|(q & A & Hq & Ha)]]; [lia| lia|]. destruct (NODES q A Hq) as (_ & _ & X3). lia. }
    apply evt_done. unfold lhi_wg_post. do 14 eexists. exists F, fc, m2, idx, ns1, [], rn, h.
    split; [lia|]. split; [exact ENTH|]. split; [assumption|]. split; [exact WM2|].
    left. split; [reflexivity|]. split; [exact S1|]. split; [exact CRN|].
    split; [unfold SITE_lhi_malloc, LHI_FILE, e_CRYPTO_malloc; cbv delta [mkR]; reflexivity|].
    split; [exact MU2|]. split; [| split; [exact ST2| exact REP2]].
    unfold lhi_saved. change (CB 80 jl :: C8 h :: ?sv) with ([CB 80 jl] ++ [C8 h] ++ sv).
    apply rw_cells_app. split; [eassumption|]. apply rw_cells_app. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    replace (bv_unsigned sp + -192 + 80) with (bv_unsigned sp + -112) by lia. replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia.
    split; [exact HP2| eassumption].

  - (* [comment removed for export] *)
    destruct CV as (-> & OWNk & RGk & (d0 & hN & N1 & DVd0 & N2) & nxr & NXr & CVr). unfold wz in N1, NXr. unfold LH_CEIL, USTACK_TOP in RGk.
    pose proof (in_concat_nth bks _ _ LI ltac:(rewrite ENTH; apply in_or_app; right; left; reflexivity) : In (pk, Ak) (concat bks)) as INK.
    destruct (NODES pk Ak INK) as (Y1 & Y2 & Y3). pose proof (NHI pk Ak INK) as Y4.
    zstep. if_cases K1; zify_cond K1. { exfalso. rewrite ?unsigned_lit in K1 by lia. lia. }
    do 3 zstep. zstep. th_if_lit. zstep.

    assert (MU3 : munch [(bv_unsigned sp - 304, bv_unsigned sp - 104); (Ak, Ak + 8)]%Z m m2) by (eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros; lia).
    clear MU2. lazymatch type of MU3 with munch ?W _ _ => assert (HWU3 : ut_fp W) by ut_fp_lia; assert (HWS3 : sh_fp W) by sh_fp_lia end.
    zstep. zstep.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m3 end.
    lazymatch goal with H : munch _ m m3 |- _ => rename H into MU3' end. lazymatch goal with H : wmono asegs m m3 |- _ => rename H into WM3 end.
    lazymatch goal with H : rw_cells asegs m3 Ak [C8 _] |- _ => rename H into NEWD end.
    assert (FRJ : rw_cells asegs m3 (bv_unsigned sp + -192) ([CB 80 jl; C8 h] ++ lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)).
    { change ([CB 80 jl; C8 h] ++ ?sv) with ([CB 80 jl] ++ [C8 h] ++ sv). apply rw_cells_app. split; [eassumption|]. apply rw_cells_app.
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp + -192 + 80) with (bv_unsigned sp + -112) by lia.
      replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) by lia. unfold lhi_saved. split; [exact HP2| eassumption]. }
    eapply evt_cut; [eapply (lhi_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 lo sp rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v [CB 80 jl; C8 h]);
      [reflexivity| reflexivity| exact FRJ| eassumption| lia| lia| lia| assumption] |].
    intros ms' [-> STF].
    assert (REP3 : lh_rep asegs LH_CEIL (DVerr GOBJ) m3 (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks).
    { eapply (lh_rep_set_data GOBJ m m3 L lh B g bks idx ns1 rest pk Ak data LAP REP ltac:(lia) ENTH DVD NEWD).
      eapply LhRep.agree_on_mono; [exact (LhRep.agree_on_of_munch asegs _ _ _ MU3' WM3)|].
      intros a [NA Ha]. cbn [outside]. destruct Ha as [Ha|[Ha|(q & A & Hq & Ha)]]; [lia| lia|]. destruct (NODES q A Hq) as (_ & _ & X3). lia. }
    apply evt_done. unfold lhi_wg_post. do 14 eexists. exists F, fc, m3, idx, ns1, ((pk, Ak) :: rest), rn, h.
    split; [lia|]. split; [exact ENTH|]. split; [assumption|]. split; [exact WM3|].
    right. exists pk, Ak, d0, rest. split; [reflexivity|]. split; [exact DVd0|]. split; [cbv delta [mkR]; reflexivity|].
    split; [| split; [exact STF| exact REP3]].
    eapply munch_weaken; [| exact MU3']. unfold sub_fp; cbn [outside]; intros; lia.
  Unshelve. all: exact (Z_to_bv 64 0).
Qed.
(* [comment removed for export] *)
Lemma lh_rep_add_node : forall (GOBJ : Z -> Z -> Prop) (m m' : mem) (L : list (Z * Z)) (lh B : Z) (g : lh_geo) (bks : list (list (bptr * Z)))
    (i : Z) (ns1 : list (bptr * Z)) (rn q data : Z) (h : word),
  lapart L -> lh_rep asegs LH_CEIL (DVerr GOBJ) m (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks ->
  0 <= i < g_nn g -> nth (Z.to_nat i) bks [] = ns1 -> lseg asegs LH_CEIL (DVerr GOBJ) m (ownL L) (B + 8 * i) ns1 rn -> g_items g < LH_KMAX ->
  (forall A n, In (A, n) L -> q + 24 <= A \/ A + n <= q) -> 0 < q -> q + 24 <= LH_CEIL ->
  DVerr GOBJ data ->
  rw_cells asegs m' q [C8 (Z_to_bv 64 data)] -> rw_cells asegs m' (q + 8) [C8 (Z_to_bv 64 0)] -> rw_cells asegs m' (q + 16) [C8 h] ->
  rw_cells asegs m' rn [C8 (Z_to_bv 64 q)] ->
  (exists x40 x48 err pad, rw_cells asegs m' lh (lh_cells ERR_FNS_A B (mkGeo (g_nn g) (g_na g) (g_p g) (g_pmax g) (g_items g + 1)) x40 x48 err pad)) ->
  LhRep.agree_on asegs (fun a => lh_fp lh B g bks a /\ ~ (rn <= a < rn + 8) /\ ~ (lh <= a < lh + 104)) m m' ->
  lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL ((q, 24) :: L)) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g)
         (mkGeo (g_nn g) (g_na g) (g_p g) (g_pmax g) (g_items g + 1)) (lupd (Z.to_nat i) (ns1 ++ [(bp q, q)]) bks).
Proof.
  intros GOBJ m m' L lh B g bks i ns1 rn q data h LAP REP HI ENTH S1 ITEMS FRESH Q0 QC DVD ND1 NX1 NH1 RN1 SC' AG.
  destruct (lh_sep asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) REP) as (S_LB & S_N & S_X & S_F).
  pose proof REP as (G & OL & RL & _ & OB & RB & LEN & CH & EMP & ND).
  pose proof (lh_geo_bounds g G) as GB.
  assert (LI : (Z.to_nat i < length bks)%nat) by lia.
  assert (HO : forall p A n nm, ownL L p A n nm -> ownL ((q, 24) :: L) p A n nm) by (intros p A n nm [X ->]; split; [right; exact X| reflexivity]).
  (* [comment removed for export] *)
  assert (QNE : forall A n, In (A, n) L -> 0 < n -> bp q <> bp A).
  { intros A n Hin Hn E. apply bp_inj in E. subst A. destruct (FRESH q n Hin); lia. }
  eapply (lh_rep_upd asegs LH_CEIL (DVerr GOBJ) m m' (ownL L) (ownL ((q, 24) :: L)) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g _ bks _ (fun j => j = i) REP);
    try reflexivity; try assumption.
  - intros j. destruct (Z.eq_dec j i); [left; assumption| right; assumption].
  - apply lh_geo_ok_item; [exact G| exact ITEMS].
  - intros ? ? ? ? _ X. apply HO. exact X.
  - rewrite lupd_length. exact LEN.
  - (* [comment removed for export] *)
    intros j Hj ->. rewrite nth_lupd_eq by exact LI.
    exists (q + 8). split; [| exact NX1]. eapply lseg_app.
    + eapply lseg_agree; [exact S1| | intros ? ? _ X; apply HO; exact X]. eapply LhRep.agree_on_mono; [exact AG|]. intros a Ha.
      pose proof (S_F _ LI) as FO. rewrite ENTH in FO.
      assert (FC : Forall (fun A => apartc A (B + 8 * i)) (map snd ns1)).
      { apply Forall_forall. intros A HA. apply in_map_iff in HA. destruct HA as ([p0 A0] & E & HA). cbn [snd] in E. subst A0.
        destruct (S_N _ p0 A LI ltac:(rewrite ENTH; exact HA)) as [_ X2]. unfold apartc. lia. }
      pose proof (lseg_fp_end asegs LH_CEIL _ _ _ _ _ _ S1 FO FC a Ha) as NRN.
      destruct (lseg_fp_where _ _ _ Ha) as [H0|(p0 & A & HA & H0)].
      * split; [right; left; lia|]. split; [exact NRN| lia].
      * destruct (S_N _ p0 A LI ltac:(rewrite ENTH; exact HA)) as [X1 _].
        split; [right; right; exists p0, A; split; [eapply in_concat_nth; [exact LI| rewrite ENTH; exact HA]| exact H0]|]. split; [exact NRN| lia].
    + cbn [lseg]. unfold wz. split; [exact RN1|]. split; [split; [left; reflexivity| reflexivity]|]. split; [lia|]. split; [| reflexivity].
      exists data, h. split; [exact ND1|]. split; [exact DVD| exact NH1].
  - intros j Hj NE. rewrite nth_lupd_ne by lia. split; [reflexivity|]. eapply LhRep.agree_on_mono; [exact AG|].
    assert (LJ : (Z.to_nat j < length bks)%nat) by lia.
    (* [comment removed for export] *)
    destruct (lseg_end_loc asegs LH_CEIL _ _ _ _ _ _ S1) as [[_ ERN]|(pre & q1 & A1 & E1 & ERN)].
    + intros a [Ha|(p0 & A & HA & Ha)].
      * split; [right; left; lia|]. subst rn. split; lia.
      * destruct (S_N _ p0 A LJ HA) as [X1 X2]. split; [right; right; exists p0, A; split; [eapply in_concat_nth; [exact LJ| exact HA]| exact Ha]|]. subst rn. split; lia.
    + assert (IN1 : In (q1, A1) (nth (Z.to_nat i) bks [])) by (rewrite ENTH, E1; apply in_or_app; right; left; reflexivity).
      destruct (S_N _ q1 A1 LI IN1) as [Y1 Y2].
      intros a [Ha|(p0 & A & HA & Ha)].
      * split; [right; left; lia|]. subst rn. split; lia.
      * destruct (S_N _ p0 A LJ HA) as [X1 X2]. pose proof (S_X _ _ _ _ LJ LI ltac:(intros E; apply NE; lia) HA IN1) as AP. cbn [snd] in AP. unfold apart24 in AP.
        split; [right; right; exists p0, A; split; [eapply in_concat_nth; [exact LJ| exact HA]| exact Ha]|]. subst rn. split; lia.
  - intros j Hj. cbn [g_nn] in Hj. rewrite nth_lupd_ne by lia. apply EMP. exact Hj.
  - (* [comment removed for export] *)
    assert (PM : Permutation (concat (lupd (Z.to_nat i) (ns1 ++ [(bp q, q)]) bks)) ((bp q, q) :: concat bks)).
    { eapply Permutation_trans; [apply concat_lupd; exact LI|].
      eapply Permutation_trans; [| apply perm_skip; apply Permutation_sym; apply (concat_split_perm bks (Z.to_nat i) LI)]. rewrite ENTH.
      rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_cons_app. apply Permutation_refl. }
    eapply Permutation.Permutation_NoDup.
    { apply Permutation_sym. apply perm_skip. apply perm_skip. apply Permutation_map. exact PM. }
    cbn [map fst]. eapply Permutation.Permutation_NoDup; [| constructor; [| exact ND]].
    + eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
    + intros [E|[E|E]].
      * exact (QNE _ _ (proj1 OL) ltac:(lia) (eq_sym E)).
      * exact (QNE _ _ (proj1 OB) ltac:(lia) (eq_sym E)).
      * apply in_map_iff in E. destruct E as ([p0 X] & E1 & Hin). cbn [fst] in E1. subst p0.
        destruct (lh_rep_owned asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ _ REP _ X Hin) as [OX EX]. exact (QNE _ _ OX ltac:(lia) EX).
Qed.

(* [comment removed for export] *)
Definition lhi_w5_post (sp gp tp : word) (lo : Z) (m : mem) (lh q rn data B nn na p pmax items : Z) (x40 x48 err pad h : word)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem),
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6) F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' q [C8 (Z_to_bv 64 data)] /\ rw_cells asegs m' (q + 8) [C8 (Z_to_bv 64 0)] /\ rw_cells asegs m' (q + 16) [C8 h]
    /\ rw_cells asegs m' rn [C8 (Z_to_bv 64 q)]
    /\ rw_cells asegs m' lh (lhs_cells B nn na p pmax (items + 1) x40 x48 err pad).

Lemma lhi_w5 : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (lo lh q rn data B nn na p pmax items pa na' : Z) (x40 x48 err pad h : word) (jq : list byte) (LOC80 : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  rw_cells asegs m lh (lhs_cells B nn na p pmax items x40 x48 err pad) -> 0 <= items < 2^62 ->
  acc asegs m lh 104 -> lh mod 8 = 0 -> 0x10007fff8000 <= lh -> lh + 104 <= lo ->
  rw_cells asegs m q [CB 24 jq] -> acc asegs m q 24 -> q mod 8 = 0 -> 0x10007fff8000 <= q -> q + 24 <= lo ->
  rw_cells asegs m rn [C8 (Z_to_bv 64 0)] -> acc asegs m pa na' -> pa mod 8 = 0 -> 0 <= pa -> pa <= rn -> rn + 8 <= pa + na' -> pa + na' <= 2^47 -> 0x10007fff8000 <= rn -> rn + 8 <= lo ->
  (q + 24 <= lh \/ lh + 104 <= q) -> (q + 24 <= rn \/ rn + 8 <= q) -> (rn + 8 <= lh \/ lh + 104 <= rn) ->
  rw_cells asegs m (bv_unsigned sp + -192) ([CB 80 LOC80; C8 h] ++ lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) ->
  stk asegs m lo (bv_unsigned sp + -192) -> 0x10007fff8000 <= lo -> lo <= bv_unsigned sp - 192 -> bv_unsigned sp <= 2 ^ 47 ->
  mem_inv asegs m ->
  evt asegs (lhi_w5_post sp gp tp lo m lh q rn data B nn na p pmax items x40 x48 err pad h rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
      (MS (mkR (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
               (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SITE_lhi_malloc) fc None m (seg_rom asegs)).
Proof.
  intros until s11v. intros SC IT ACL ALL HIL LLO NQ ACQ ALQ HIQ QLO CRN PACC PAL PA0 PA1 PA2 PA3 HIR RLO SQL SQR SRL FR ST LO0 LO HTOP MI.
  unfold lhs_cells in SC. unfold SITE_lhi_malloc. unfold lhi_saved in FR. cbn [app] in FR.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cl_eu (bv_unsigned sp) 0 EU0. rewrite Z.add_0_r in EU0. cl_eu (bv_unsigned sp) (-192) EU1.
  apply (rw_cells_split_CB asegs m q [] 24 jq [] [8; 8; 8]%nat) in NQ; [| reflexivity]. cbn [mk_CB_cells app firstn skipn] in NQ.
  zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. lia. }
  do 3 zstep. zstep. th_if_lit. zstep.
  do 4 zstep. zstep. th_if_lit. zstep. th_fix_lit_store.
  do 4 zstep. zstep. th_if_lit. zstep. zstep.
  zstep. zstep. th_if_lit. zstep.
  zstep. zstep. th_if_lit. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m5 end.
  lazymatch goal with H : rw_cells asegs m5 (bv_unsigned sp + -192) _ |- _ => rename H into FRJ end.
  lazymatch goal with H : stk asegs m5 lo _ |- _ => rename H into ST5 end.
  eapply evt_cut; [eapply (lhi_epi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m5 lo sp rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v [CB 80 LOC80; C8 h]);
    [reflexivity| reflexivity| exact FRJ| exact ST5| lia| lia| lia| assumption] |].
  intros ms' [-> STF].
  apply evt_done. unfold lhi_w5_post, lhs_cells. do 14 eexists. exists F, fc, m5. split; [cbv delta [mkR]; reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [assumption|]. split; [exact STF|].
  change [C8 (Z_to_bv 64 data); C8 (Z_to_bv 64 0); C8 h] with ([C8 (Z_to_bv 64 data)] ++ [C8 (Z_to_bv 64 0)] ++ [C8 h]) in NQ.
  apply (proj1 (rw_cells_app _ _ _ _)) in NQ. destruct NQ as [NQ1 NQ]. apply (proj1 (rw_cells_app _ _ _ _)) in NQ. destruct NQ as [NQ2 NQ3].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in NQ2, NQ3. replace (q + 8 + 8) with (q + 16) in NQ3 by lia.
  split; [exact NQ1|]. split; [exact NQ2|]. split; [exact NQ3|]. split; [exact CRN| exact SC].
Qed.
(* [comment removed for export] *)
Lemma lh_raw_double : forall (GOBJ : Z -> Z -> Prop) (m m2 : mem) (L : list (Z * Z)) (lh B q na : Z) (bks : list (list (bptr * Z))) (src tail : list byte),
  lapart L -> (forall A n, In (A, n) L -> 0 < n) ->
  lh_raw asegs LH_CEIL (DVerr GOBJ) m (ownL L) lh (bp lh) (bp B) B (8 * na) na bks ->
  rw_cells asegs m B [CB (8 * Z.to_nat na) src] ->
  rw_cells asegs m2 q [CB (8 * Z.to_nat na) (src ++ tail)] ->
  rw_cells asegs m2 (q + 8 * na) [CB (8 * Z.to_nat na) (repeat (Z_to_bv 8 0) (8 * Z.to_nat na))] ->
  LhRep.agree_on asegs (fun a => exists p0 X, In (p0, X) (concat bks) /\ X <= a < X + 24) m m2 ->
  (forall A n, In (A, n) L -> (A, n) <> (B, 8 * na) -> q + 16 * na <= A \/ A + n <= q) -> 0 < q -> q + 16 * na <= LH_CEIL ->
  lh_raw asegs LH_CEIL (DVerr GOBJ) m2 (ownL ((q, 16 * na) :: live_remove B L)) lh (bp lh) (bp q) q (16 * na) (2 * na) (bks ++ repeat [] (Z.to_nat na)).
Proof.
  intros GOBJ m m2 L lh B q na bks src tail LAP POS RAW OLD NEW ZER AGN FRESH Q0 QC.
  pose proof RAW as ([OL EL] & RL & [OB EB] & RB & LEN & CH & ND).
  destruct (lh_sep_raw asegs LH_CEIL _ _ _ _ _ _ _ _ _ _ (ownL_apart L LAP) RAW) as (S_LB & S_N & S_X & S_F).
  assert (NA0 : 0 <= na) by lia.
  (* [comment removed for export] *)
  assert (KEEP : forall p A n nm, ownL L p A n nm -> (A, n) <> (B, 8 * na) -> ownL ((q, 16 * na) :: live_remove B L) p A n nm).
  { intros p A n nm [X ->] NE. split; [| reflexivity]. right. apply (live_remove_keep L B (A, n) X). cbn [fst]. intros ->.
    destruct (LAP B n B (8 * na) X OB NE); pose proof (POS B n X); pose proof (POS B (8 * na) OB); lia. }
  assert (CC2 : concat (bks ++ repeat [] (Z.to_nat na)) = concat bks) by (rewrite concat_app, concat_repeat_nil, app_nil_r; reflexivity).
  assert (OLn : ownL ((q, 16 * na) :: live_remove B L) (bp lh) lh 104 104) by (apply KEEP; [exact (conj OL EL)| intros E; injection E; lia]).
  assert (OBn : ownL ((q, 16 * na) :: live_remove B L) (bp q) q (16 * na) (16 * na)) by (split; [left; reflexivity| reflexivity]).
  unfold lh_raw. split; [exact OLn|]. split; [exact RL|]. split; [replace (8 * (2 * na)) with (16 * na) by lia; exact OBn|]. split; [lia|].
  split; [rewrite length_app, repeat_length; lia|].
  split.
  - intros i Hi. destruct (Z_lt_le_dec i na) as [X|X].
    + rewrite app_nth1 by lia.
      destruct (chain_chainv asegs LH_CEIL _ _ _ _ _ (CH i ltac:(lia))) as (v & CV & CHV).
      eapply (chainv_chain asegs LH_CEIL _ _ _ _ _ v).
      * pose proof (cells_read_back asegs m m2 B q _ _ src tail (Z.to_nat i) (wz v) OLD ltac:(rewrite Z2Nat.id by lia; exact CV) ltac:(lia) NEW) as C1.
        rewrite Z2Nat.id in C1 by lia. exact C1.
      * eapply chainv_own; [eapply chainv_agree; [exact CHV|]|].
        -- eapply LhRep.agree_on_mono; [exact AGN|]. intros a (p0 & X0 & Hin & Ha). exists p0, X0. split; [eapply in_nth_concat; exact Hin| exact Ha].
        -- intros p0 X0 Hin O. apply KEEP; [exact O|]. intros E. injection E; intros E1 E2.
           assert (LI : (Z.to_nat i < length bks)%nat) by lia. destruct (S_N _ p0 X0 LI Hin) as [_ Y]. lia.
    + rewrite app_nth2 by lia. rewrite nth_repeat. exists (q + 8 * i). split; [reflexivity|].
      pose proof (cells_zero asegs m2 (q + 8 * na) (Z.to_nat na) (Z.to_nat (i - na)) ZER ltac:(lia)) as C0.
      replace (q + 8 * na + 8 * Z.of_nat (Z.to_nat (i - na))) with (q + 8 * i) in C0 by lia. unfold wz. exact C0.
  - rewrite CC2. apply NoDup_cons_iff in ND. destruct ND as [NI1 ND']. apply NoDup_cons_iff in ND'. destruct ND' as [NI2 ND2].
    constructor; [| constructor; [| exact ND2]].
    + intros [E|X]; [| apply NI1; right; exact X]. apply bp_inj in E. pose proof (POS B (8 * na) OB). destruct (FRESH lh 104 OL ltac:(intros E2; injection E2; lia)); lia.
    + intros X. apply in_map_iff in X. destruct X as ([p0 X0] & E & Hin). cbn [fst] in E. subst p0.
      apply in_concat in Hin. destruct Hin as (ns & Hns & Hin). destruct (In_nth _ _ [] Hns) as (i & Hi & <-).
      pose proof (chain_owns asegs LH_CEIL _ _ _ _ _ (CH (Z.of_nat i) ltac:(lia))) as OW. rewrite Nat2Z.id in OW.
      destruct (S_N _ _ _ Hi Hin) as [_ Y].
      destruct (OW _ _ Hin) as [O1 E1]. apply bp_inj in E1. subst X0.
      pose proof (POS B (8 * na) OB). destruct (FRESH _ 24 O1 ltac:(intros E2; injection E2; lia)); lia.
Qed.
