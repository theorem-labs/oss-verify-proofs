(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
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
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    sp0 rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v LOC
    SP_AT LOC_88 FRAME STK_AT LO_FITS SP0_LOW SP0_ROOM MEM_OK.
  assert (STK_TOP : stk asegs m lo (bv_unsigned sp0)).
  { pose proof (stk_release asegs m lo _ _ STK_AT FRAME ltac:(lia)) as GROWN.
    rewrite cells_size_app, LOC_88 in GROWN. cbn [lhi_saved cells_size csize Nat.add] in GROWN.
    replace (bv_unsigned sp0 + -192 + Z.of_nat (88 + 104)) with (bv_unsigned sp0) in GROWN by lia.
    exact GROWN. }
  apply rw_cells_blur in FRAME. rewrite LOC_88 in FRAME. unfold lhi_saved in FRAME.
  subst sp. unfold LHI_EPI.
  do 15 zstep.
  apply evt_done. exact (conj eq_refl STK_TOP).
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
  intros GOBJ m m' L lh B g bks i ns1 rest pk Ak d APART REP IRNG BUCKET DVD NEWCELL SAME.
  pose proof (ownL_apart L APART) as OAP.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ OAP REP) as (SEP_LB & SEP_N & SEP_X & SEP_F).
  pose proof REP as (GOK & OWNLH & LHR & (x40 & x48 & err & pad & LHC) & OWNB & BR & LEN & CH & EMPTY & ND).
  assert (ILT : (Z.to_nat i < length bks)%nat) by lia.
  assert (IN_BK : forall p A, In (p, A) ns1 \/ In (p, A) ((pk, Ak) :: rest) -> In (p, A) (concat bks)).
  { intros p A WHERE. apply (in_concat_nth bks (Z.to_nat i)); [exact ILT|]. rewrite BUCKET. apply in_or_app. exact WHERE. }
  assert (AK_POS : (Ak + 24 <= lh \/ lh + 104 <= Ak) /\ (Ak + 24 <= B \/ B + 8 * g_na g <= Ak)).
  { apply (SEP_N (Z.to_nat i) pk Ak ILT). rewrite BUCKET. apply in_or_app. right. left. reflexivity. }
  pose proof (SEP_F (Z.to_nat i) ILT) as ORD. rewrite BUCKET, map_app in ORD. cbn [map snd] in ORD.
  destruct (fop_app_inv _ _ _ ORD) as (_ & ORD_K & CROSS).
  inversion ORD_K as [| ? ? AFTER_K ?]; subst.
  assert (BEFORE : forall p A, In (p, A) ns1 -> apart24 A Ak).
  { intros p A IN1. apply CROSS; [apply (in_map snd ns1 (p, A) IN1) | left; reflexivity]. }
  assert (LATER : forall p A, In (p, A) rest -> apart24 Ak A).
  { intros p A INR. exact (proj1 (Forall_forall _ _) AFTER_K A (in_map snd rest (p, A) INR)). }
  assert (NODE_FP : forall p A a, In (p, A) (concat bks) -> A <= a < A + 24 -> lh_fp lh B g bks a).
  { intros p A a INC RNG. right. right. exists p, A. split; [exact INC| exact RNG]. }
  apply (lh_rep_upd asegs LH_CEIL (DVerr GOBJ) m m' (ownL L) (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g g bks bks
           (fun j => j = i) REP).
  - intros j. destruct (Z.eq_dec j i) as [EQJ|NEJ]; [left; exact EQJ| right; exact NEJ].
  - reflexivity.
  - exact GOK.
  - exists x40, x48, err, pad. apply (LhRep.rw_cells_agree asegs _ m m' lh _ SAME LHC).
    cbn [lh_cells cells_size csize Nat.add]. intros a RNG. split; [lia| left; lia].
  - intros q A n nm _ OWNQ. exact OWNQ.
  - exact LEN.
  - intros j JR ->. destruct (CH i JR) as (cend & SEG & ENDC). rewrite BUCKET in SEG |- *.
    destruct (lseg_split _ _ _ _ _ _ _ _ _ SEG) as (cmid & SEG1 & SEG2).
    pose proof SEG2 as HEAD. cbn [lseg] in HEAD.
    destruct HEAD as (PTR & OWNK & RNGK & (dold & hk & DOLD & DVOLD & HK) & SEG3).
    exists cend. split.
    + apply (lseg_app _ _ _ _ _ _ _ _ cmid).
      * apply (lseg_agree _ _ _ m m' (ownL L) (ownL L) ns1 _ _ SEG1); [| intros p A _ OW; exact OW].
        apply (agree_on_mono asegs _ _ m m' SAME). intros a FP.
        destruct (lseg_fp_where ns1 _ a FP) as [SLOT|(p & A & IN1 & RNG)].
        -- split; [lia| right; left; lia].
        -- pose proof (BEFORE p A IN1) as AP. unfold apart24 in AP.
           split; [lia| apply (NODE_FP p A a); [apply IN_BK; left; exact IN1| exact RNG]].
      * cbn [lseg]. split; [| split; [exact OWNK| split; [exact RNGK| split]]].
        -- apply (LhRep.rw_cells_agree asegs _ m m' cmid _ SAME PTR). cbn [cells_size csize]. intros a RNG.
           destruct (lseg_end_loc _ _ _ _ _ _ _ _ SEG1) as [(_ & CM)|(pre & p' & A' & SPLIT1 & CM)]; rewrite CM in RNG.
           ++ split; [lia| right; left; lia].
           ++ assert (IN' : In (p', A') ns1) by (rewrite SPLIT1; apply in_or_app; right; left; reflexivity).
              pose proof (BEFORE p' A' IN') as AP. unfold apart24 in AP.
              split; [lia| apply (NODE_FP p' A' a); [apply IN_BK; left; exact IN'| lia]].
        -- exists d, hk. split; [exact NEWCELL|]. split; [exact DVD|].
           apply (LhRep.rw_cells_agree asegs _ m m' (Ak + 16) _ SAME HK). cbn [cells_size csize]. intros a RNG.
           split; [lia| apply (NODE_FP pk Ak a); [apply IN_BK; right; left; reflexivity| lia]].
        -- apply (lseg_agree _ _ _ m m' (ownL L) (ownL L) rest _ _ SEG3); [| intros p A _ OW; exact OW].
           apply (agree_on_mono asegs _ _ m m' SAME). intros a FP.
           destruct (lseg_fp_where rest _ a FP) as [SLOT|(p & A & INR & RNG)].
           ++ split; [lia| apply (NODE_FP pk Ak a); [apply IN_BK; right; left; reflexivity| lia]].
           ++ pose proof (LATER p A INR) as AP. unfold apart24 in AP.
              split; [lia| apply (NODE_FP p A a); [apply IN_BK; right; right; exact INR| exact RNG]].
    + apply (LhRep.rw_cells_agree asegs _ m m' cend _ SAME ENDC). cbn [cells_size csize]. intros a RNG.
      destruct (lseg_end_loc _ _ _ _ _ _ _ _ SEG2) as [(NIL & _)|(pre & p'' & A'' & SPLIT2 & CE)]; [discriminate NIL|].
      rewrite CE in RNG.
      assert (IN'' : In (p'', A'') ((pk, Ak) :: rest)) by (rewrite SPLIT2; apply in_or_app; right; left; reflexivity).
      assert (CLEAR : A'' = Ak \/ apart24 Ak A'').
      { destruct IN'' as [EQK|INR]; [left; congruence| right; exact (LATER p'' A'' INR)]. }
      unfold apart24 in CLEAR.
      split; [lia| apply (NODE_FP p'' A'' a); [apply IN_BK; right; exact IN''| lia]].
  - intros j JR NEJ. split; [reflexivity|].
    apply (agree_on_mono asegs _ _ m m' SAME). intros a [SLOT|(p & A & INJ & RNG)].
    + split; [lia| right; left; lia].
    + assert (JLT : (Z.to_nat j < length bks)%nat) by lia.
      pose proof (SEP_X (Z.to_nat i) (Z.to_nat j) (pk, Ak) (p, A) ILT JLT ltac:(lia)
                    ltac:(rewrite BUCKET; apply in_or_app; right; left; reflexivity) INJ) as AP.
      cbn [snd] in AP. unfold apart24 in AP.
      split; [lia| apply (NODE_FP p A a); [exact (in_concat_nth bks _ _ JLT INJ)| exact RNG]].
  - exact EMPTY.
  - exact ND.
Qed.

(* [comment removed for export] *)
Definition lhi_wg_post (sp gp tp s3 s5 s10 s11 : word) (F0 : bvmap 5 word) (lo : Z) (m : mem) (GOBJ : Z -> Z -> Prop) (L : list (Z * Z))
    (lh B data : Z) (g : lh_geo) (bks : list (list (bptr * Z))) (jl : list byte)
    (rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem)
                   (i : Z) (ns1 ns2 : list (bptr * Z)) (rn : Z) (h : word),
    0 <= i < g_nn g /\ nth (Z.to_nat i) bks [] = ns1 ++ ns2 /\ mem_inv asegs m' /\ wmono asegs m m' /\
    ((ns2 = [] /\ lseg asegs LH_CEIL (DVerr GOBJ) m' (ownL L) (B + 8 * i) ns1 rn /\ rw_cells asegs m' rn [C8 (Z_to_bv 64 0)]
      /\ ms = MS (mkR (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
                      (Z_to_bv 64 24) (Z_to_bv 64 LHI_FILE) (Z_to_bv 64 130) a3 a4 a5 a6 a7
                      (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
                      (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 e_CRYPTO_malloc) fc None m' (seg_rom asegs)
      /\ munch [(bv_unsigned sp - 304, bv_unsigned sp - 104)] m m'
      /\ rw_cells asegs m' (bv_unsigned sp + -192) (CB 80 jl :: C8 h :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)
      /\ stk asegs m' lo (bv_unsigned sp + -192)
      /\ lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks)
     \/ (exists (pk : bptr) (Ak d0 : Z) (rest : list (bptr * Z)),
          ns2 = (pk, Ak) :: rest /\ DVerr GOBJ d0
          /\ ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 d0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
                     F (ret_pc rav) fc None m' (seg_rom asegs)
          /\ munch [(bv_unsigned sp - 304, bv_unsigned sp - 104); (Ak, Ak + 8)] m m'
          /\ stk asegs m' lo (bv_unsigned sp)
          /\ lh_rep asegs LH_CEIL (DVerr GOBJ) m' (ownL L) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g) g bks)).

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
  intros ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 F fc m GOBJ L lh B g bks data lo kw jl jh
    rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    REP APART ACC_LH LH_AL LH_LO LH_LOW ACC_B B_AL B_LO B_LOW NODES NODES_LOW DV_OK UT_LO
    KEY ACC_D D_AL D_LO DVD D_SEP FRAME ACC_FR SP_AL UT SHC STK LO_LOW LO_SP SP_TOP MEMOK.
  pose proof (bv_unsigned_in_range 64 sp) as SP_RANGE. unfold bv_modulus in SP_RANGE. cbn in SP_RANGE.
  pose proof (lh_geo_bounds g (proj1 REP)) as GB.
  assert (SPD : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -192)) = bv_unsigned sp + -192) by (apply unsigned_lit; lia).
  assert (D_POS : 0 < data) by (destruct DVD as (_ & DLO & _); unfold IMG_UT_LO in DLO; lia).
  apply (proj1 (lhg_rw_cells_app asegs m _ [CB 80 jl] (CB 8 jh :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)))
    in FRAME.
  destruct FRAME as (LOCALS & FRAME_HI).
  apply (proj1 (lhg_rw_cells_app asegs m _ [CB 8 jh] (lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v))) in FRAME_HI.
  destruct FRAME_HI as (HASH_SLOT & SAVED).
  cbn [cells_size csize Nat.add] in HASH_SLOT, SAVED.
  replace (bv_unsigned sp + -192 + Z.of_nat 80) with (bv_unsigned sp + -112) in HASH_SLOT, SAVED by lia.
  replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) in SAVED by lia.
  apply (cb8_c8_in m _ [] [] jh) in HASH_SLOT. cbn [app] in HASH_SLOT.
  unfold LHI_SPLIT_EXIT.
  do 4 zstep.
  eapply evt_cut.
  { exact (getrn_proof (Z_to_bv 64 2098324) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp s1
             (Z_to_bv 64 lh) (Z_to_bv 64 data) (Z_to_bv 64 (bv_unsigned sp + -112)) a3 a4 a5 a6 a7
             (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 lh) s5 s3
             (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6
             F fc m GOBJ L lh B g bks data (bv_unsigned sp + -112) lo kw (le_bytes_to_word jh)
             REP ACC_LH LH_AL LH_LO ACC_B B_AL B_LO NODES DV_OK UT_LO eq_refl eq_refl eq_refl KEY ACC_D D_AL D_LO D_POS HASH_SLOT
             (acc_sub asegs m _ _ (bv_unsigned sp + -112) 8 ACC_FR ltac:(lia) ltac:(lia)) ltac:(clear - SP_AL; Z.div_mod_to_equations; lia)
             ltac:(rewrite SPD; lia) ltac:(unfold USTACK_TOP; lia) UT SHC
             ltac:(rewrite SPD; exact STK) LO_LOW ltac:(rewrite SPD; lia) ltac:(rewrite SPD; lia) MEMOK). }
  intros ms1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & i & ns1 & ns2 & rn & h
              & -> & MU1 & WM1 & MI1 & ST1 & IRNG & NTH & SEG & CHN & HCELL).
  rewrite SPD in MU1, ST1.
  pose proof REP as (_ & _ & _ & _ & _ & _ & LEN & _).
  assert (MU_A : munch [(bv_unsigned sp - 304, bv_unsigned sp - 104)] m m1).
  { refine (munch_weaken _ _ m m1 _ MU1). intros x (OUT & _). cbn [outside]. split; [lia| split; [lia| exact I]]. }
  assert (HWS_A : sh_fp [(bv_unsigned sp - 304, bv_unsigned sp - 104)]) by sh_fp_lia.
  pose proof (rw_cells_transport asegs _ m m1 _ _ LOCALS MU1 WM1
                ltac:(cbn [disjoint_from cells_size csize Nat.add]; split; [lia| split; [lia| exact I]])) as LOCALS1.
  pose proof (rw_cells_transport asegs _ m m1 _ _ SAVED MU1 WM1
                ltac:(cbn [disjoint_from lhi_saved cells_size csize Nat.add]; split; [lia| split; [lia| exact I]])) as SAVED1.
  clear MU1.
  assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -192)
                  (CB 80 jl :: C8 h :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v)).
  { apply (proj2 (lhg_rw_cells_app asegs m1 _ [CB 80 jl] (C8 h :: lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v))).
    split; [exact LOCALS1|].
    apply (proj2 (lhg_rw_cells_app asegs m1 _ [C8 h] (lhi_saved rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v))).
    cbn [cells_size csize Nat.add].
    replace (bv_unsigned sp + -192 + Z.of_nat 80) with (bv_unsigned sp + -112) by lia.
    replace (bv_unsigned sp + -112 + Z.of_nat 8) with (bv_unsigned sp + -104) by lia.
    split; [exact HCELL| exact SAVED1]. }
  clear LOCALS LOCALS1 SAVED SAVED1 HASH_SLOT HCELL.
  assert (RN_SPOT : exists P N, acc asegs m P N /\ P mod 8 = 0 /\ 0 <= P /\ P <= rn /\ rn + 8 <= P + N /\ P + N <= lo).
  { destruct (lseg_end_loc _ _ _ _ _ _ _ _ SEG) as [(_ & ->)|(pre & p' & A' & SPLIT & ->)].
    - exists B, (8 * g_na g). split; [exact ACC_B|]. split; [exact B_AL|]. lia.
    - assert (INA : In (p', A') (concat bks)).
      { apply (in_concat_nth bks (Z.to_nat i)); [lia|].
        rewrite NTH, SPLIT. apply in_or_app. left. apply in_or_app. right. left. reflexivity. }
      destruct (NODES p' A' INA) as (ACCA & ALA & TOPA). pose proof (NODES_LOW p' A' INA) as LOWA.
      exists A', 24. split; [exact ACCA|]. split; [exact ALA|]. lia. }
  destruct RN_SPOT as (P & N & ACC_P & P_AL & P_NN & P_RN & RN_PN & PN_LO).
  th_ret_lit.
  do 5 zstep. th_if_lit.
  destruct (chain_chainv _ _ _ _ _ _ _ CHN) as (v & SLOTV & CHV).
  unfold MallocRep.wz in *.
  destruct ns2 as [| (pk, Ak) rest].
  - (* rn holds NULL: the new node is allocated *)
    cbn [chainv] in CHV. subst v.
    zstep. zstep. th_if_lit.
    do 5 zstep.
    apply evt_done. unfold lhi_wg_post.
    exists u0, u1, u2, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, m1, i, ns1, [], rn, h.
    split; [exact IRNG|]. split; [exact NTH|]. split; [exact MI1|]. split; [exact WM1|].
    left. split; [reflexivity|]. split; [exact SEG|]. split; [exact SLOTV|].
    split; [reflexivity|]. split; [exact MU_A|]. split; [exact FR1|]. split; [exact ST1|].
    apply (lh_rep_agree _ _ _ m m1 _ _ _ _ _ _ _ _ _ _ REP); [| intros q0 A0 n0 nm0 _ OW; exact OW].
    apply (agree_on_mono asegs _ _ m m1 (agree_on_of_munch asegs _ m m1 MU_A WM1)).
    intros a FP. cbn [outside]. split; [| exact I].
    destruct FP as [X|[X|(p & A & INC & X)]]; [lia| lia|].
    destruct (NODES p A INC) as (_ & _ & TOPA). lia.
  - (* rn holds a node: its data is replaced *)
    cbn [chainv] in CHV. destruct CHV as (-> & OWNK & RNGK & (dold & hk & DOLD & DVOLD & HK) & (nx & NXC & CHR)).
    assert (INK : In (pk, Ak) (concat bks)).
    { apply (in_concat_nth bks (Z.to_nat i)); [lia|]. rewrite NTH. apply in_or_app. right. left. reflexivity. }
    destruct (NODES pk Ak INK) as (ACC_K & K_AL & K_LO). pose proof (NODES_LOW pk Ak INK) as K_LOW.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia) end.
    cbv iota.
    do 4 zstep. th_if_lit.
    assert (MU_B : munch [(bv_unsigned sp - 304, bv_unsigned sp - 104); (Ak, Ak + 8)] m m1).
    { refine (munch_weaken _ _ m m1 _ MU_A). intros x (O1 & O2 & _). split; [exact O1| exact I]. }
    assert (HWS_B : sh_fp [(bv_unsigned sp - 304, bv_unsigned sp - 104); (Ak, Ak + 8)]) by sh_fp_lia.
    clear MU_A HWS_A.
    do 3 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mfin _) =>
      eapply evt_cut;
      [ apply (lhi_epi (Z_to_bv 64 2098324) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp u0 u1 u2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
                 (Z_to_bv 64 dold) (Z_to_bv 64 Ak) b2 b3 b4 b5 b6 b7 (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
                 (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 u3 u4 u5 u6
                 F fc mfin lo sp rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v [CB 80 jl; C8 h]
                 eq_refl eq_refl FR1 ST1 ltac:(lia) SP_TOP ltac:(lia) MI1)
      | intros ms_end (-> & STK_END); apply evt_done; unfold lhi_wg_post;
        exists u0, u1, u2, (Z_to_bv 64 Ak), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, F, fc, mfin, i, ns1, ((pk, Ak) :: rest), rn, h;
        split; [exact IRNG|]; split; [exact NTH|]; split; [exact MI1|]; split; [exact WM1|];
        right; exists pk, Ak, dold, rest;
        split; [reflexivity|]; split; [exact DVOLD|]; split; [reflexivity|];
        split; [exact MU_B|]; split; [exact STK_END|];
        apply (lh_rep_set_data GOBJ m mfin L lh B g bks i ns1 rest pk Ak data APART REP ltac:(lia) NTH DVD DOLD);
        apply (agree_on_mono asegs _ _ m mfin (agree_on_of_munch asegs _ m mfin MU_B WM1));
        intros a (NOT_K & FP); cbn [outside]; split; [| split; [exact NOT_K| exact I]];
        destruct FP as [X|[X|(p & A & INC & X)]]; [lia| lia| destruct (NODES p A INC) as (_ & _ & TOPA); lia] ]
    end.
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
  intros GOBJ m m' L lh B g bks i ns1 rn q data h APART REP IRNG BUCKET SEG ROOM FRESH QPOS QTOP DVD
    QDATA QNEXT QHASH LINK HDR SAME.
  pose proof (ownL_apart L APART) as OAP.
  destruct (lh_sep _ _ _ _ _ _ _ _ _ _ _ _ _ OAP REP) as (SEP_LB & SEP_N & SEP_X & SEP_F).
  pose proof REP as (GOK & OWNLH & LHR & _ & OWNB & BR & LEN & CH & EMPTY & ND).
  pose proof (lh_geo_bounds g GOK) as GB.
  assert (ILT : (Z.to_nat i < length bks)%nat) by lia.
  assert (NODE_FP : forall p A a, In (p, A) (concat bks) -> A <= a < A + 24 -> lh_fp lh B g bks a).
  { intros p A a INC RNG. right. right. exists p, A. split; [exact INC| exact RNG]. }
  assert (IN_I : forall p A, In (p, A) ns1 -> In (p, A) (concat bks)).
  { intros p A IN1. apply (in_concat_nth bks (Z.to_nat i) _ ILT). rewrite BUCKET. exact IN1. }
  assert (POS_I : forall p A, In (p, A) ns1 -> (A + 24 <= lh \/ lh + 104 <= A) /\ (A + 24 <= B \/ B + 8 * g_na g <= A)).
  { intros p A IN1. apply (SEP_N (Z.to_nat i) p A ILT). rewrite BUCKET. exact IN1. }
  (* where the old chain ends: the bucket slot or the next field of its last node *)
  assert (RN_AT : rn = B + 8 * i \/ exists p' A', In (p', A') ns1 /\ rn = A' + 8).
  { destruct (lseg_end_loc _ _ _ _ _ _ _ _ SEG) as [(_ & E)|(pre & p' & A' & SPLIT & E)]; [left; exact E| right].
    exists p', A'. split; [rewrite SPLIT; apply in_or_app; right; left; reflexivity| exact E]. }
  assert (WIDEN : forall p A n nm, ownL L p A n nm -> ownL ((q, 24) :: L) p A n nm).
  { intros p A n nm (INL & EP). split; [right; exact INL| exact EP]. }
  assert (Q_NOT_OWNED : forall A n, In (A, n) L -> 0 < n -> A <> q).
  { intros A n INL NPOS ->. destruct (FRESH q n INL); lia. }
  apply (lh_rep_upd asegs LH_CEIL (DVerr GOBJ) m m' (ownL L) (ownL ((q, 24) :: L)) ERR_FNS_A lh (bp lh) (bp B) B (8 * g_na g)
           g (mkGeo (g_nn g) (g_na g) (g_p g) (g_pmax g) (g_items g + 1)) bks (lupd (Z.to_nat i) (ns1 ++ [(bp q, q)]) bks)
           (fun j => j = i) REP).
  - intros j. destruct (Z.eq_dec j i) as [EQJ|NEJ]; [left; exact EQJ| right; exact NEJ].
  - reflexivity.
  - exact (lh_geo_ok_item g GOK ROOM).
  - exact HDR.
  - intros p A n nm _ OW. exact (WIDEN p A n nm OW).
  - rewrite lupd_length. exact LEN.
  - intros j JR ->. rewrite nth_lupd_eq by exact ILT. exists (q + 8). split; [| exact QNEXT].
    apply (lseg_app _ _ _ _ _ _ _ _ rn).
    + apply (lseg_agree _ _ _ m m' (ownL L) _ ns1 _ _ SEG); [| intros p A _ OW; exact (WIDEN p A 24 24 OW)].
      apply (agree_on_mono asegs _ _ m m' SAME). intros a FP.
      assert (APARTS : ForallOrdPairs apart24 (map snd ns1)) by (rewrite <- BUCKET; exact (SEP_F _ ILT)).
      assert (OFF_SLOT : Forall (fun A => apartc A (B + 8 * i)) (map snd ns1)).
      { apply Forall_forall. intros A INA. apply in_map_iff in INA. destruct INA as ((p & A0) & <- & IN1).
        destruct (POS_I p A0 IN1) as (_ & POSB). cbn [snd]. unfold apartc. lia. }
      pose proof (lseg_fp_end _ _ _ _ _ _ _ _ SEG APARTS OFF_SLOT a FP) as NOT_RN.
      destruct (lseg_fp_where ns1 _ a FP) as [SLOT|(p & A & IN1 & RNG)].
      * split; [right; left; lia|]. split; [exact NOT_RN| lia].
      * destruct (POS_I p A IN1) as (POSL & _).
        split; [exact (NODE_FP p A a (IN_I p A IN1) RNG)|]. split; [exact NOT_RN| lia].
    + cbn [lseg]. split; [exact LINK|]. split; [split; [left; reflexivity| reflexivity]|].
      split; [lia|]. split; [| reflexivity].
      exists data, h. split; [exact QDATA|]. split; [exact DVD| exact QHASH].
  - intros j JR NEJ. split; [apply nth_lupd_ne; lia|].
    apply (agree_on_mono asegs _ _ m m' SAME).
    assert (JLT : (Z.to_nat j < length bks)%nat) by lia.
    intros a [SLOT|(p & A & INJ & RNG)].
    + split; [right; left; lia|]. split; [| lia].
      destruct RN_AT as [->|(p' & A' & IN1 & ->)]; [lia|].
      destruct (POS_I p' A' IN1) as (_ & POSB). lia.
    + destruct (SEP_N (Z.to_nat j) p A JLT INJ) as (POSL & POSB).
      split; [exact (NODE_FP p A a (in_concat_nth bks _ _ JLT INJ) RNG)|]. split; [| lia].
      destruct RN_AT as [->|(p' & A' & IN1 & ->)]; [lia|].
      pose proof (SEP_X (Z.to_nat i) (Z.to_nat j) (p', A') (p, A) ILT JLT ltac:(lia)
                    ltac:(rewrite BUCKET; exact IN1) INJ) as AP.
      cbn [snd] in AP. unfold apart24 in AP. lia.
  - intros j JR. cbn [g_nn] in JR. rewrite nth_lupd_ne by lia. apply EMPTY. lia.
  - assert (PERM : Permutation (concat (lupd (Z.to_nat i) (ns1 ++ [(bp q, q)]) bks)) ((bp q, q) :: concat bks)).
    { eapply Permutation_trans; [apply concat_lupd; exact ILT|].
      eapply Permutation_trans; [apply Permutation_app_tail; apply Permutation_app_comm|]. cbn [app]. apply perm_skip.
      apply Permutation_sym. rewrite <- BUCKET. apply concat_split_perm. exact ILT. }
    apply (Permutation_NoDup (l := bp lh :: bp B :: bp q :: map fst (concat bks))).
    { apply perm_skip. apply perm_skip. apply Permutation_sym. exact (Permutation_map fst PERM). }
    destruct OWNLH as (INLH & _). destruct OWNB as (INB & _).
    assert (NE_LH : bp q <> bp lh) by (intros E; apply bp_inj in E; exact (Q_NOT_OWNED lh 104 INLH ltac:(lia) (eq_sym E))).
    assert (NE_B : bp q <> bp B) by (intros E; apply bp_inj in E; exact (Q_NOT_OWNED B (8 * g_na g) INB ltac:(lia) (eq_sym E))).
    assert (NOT_NODE : ~ In (bp q) (map fst (concat bks))).
    { intros INQ. apply in_map_iff in INQ. destruct INQ as ((p & A) & EP & INC). cbn [fst] in EP. subst p.
      destruct (lh_rep_owned _ _ _ _ _ _ _ _ _ _ _ _ _ REP (bp q) A INC) as (INA & EA).
      apply bp_inj in EA. exact (Q_NOT_OWNED A 24 INA ltac:(lia) (eq_sym EA)). }
    inversion ND as [| ? ? NOT_LH ND1]; subst. inversion ND1 as [| ? ? NOT_B ND2]; subst.
    constructor.
    { intros [E|[E|IN]]; [exact (NOT_LH (or_introl E)) | exact (NE_LH E) | exact (NOT_LH (or_intror IN))]. }
    constructor.
    { intros [E|IN]; [exact (NE_B E) | exact (NOT_B IN)]. }
    constructor; [exact NOT_NODE| exact ND2].
Qed.

(* [comment removed for export] *)
Definition lhi_w5_post (sp gp tp : word) (lo : Z) (m : mem) (lh q rn data B nn na p pmax items : Z)
    (x40 x48 err pad h rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : machine_state -> Prop :=
  fun ms => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem),
    ms = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v t3 t4 t5 t6)
            F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ munch [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)] m m'
    /\ wmono asegs m m'
    /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' q [C8 (Z_to_bv 64 data)]
    /\ rw_cells asegs m' (q + 8) [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (q + 16) [C8 h]
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
  intros sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s5 s10 s11 t3 t4 t5 t6 F fc m lo lh q rn data B nn na p pmax items pa na'
    x40 x48 err pad h jq LOC80 rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v
    HDR ITEMS ACC_LH LH_AL LH_LOW LH_LO QCELLS ACC_Q Q_AL Q_LOW Q_LO RN_NULL ACC_PA PA_AL PA_NN PA_RN RN_PA PA_TOP RN_LOW RN_LO
    QL_SEP QR_SEP RL_SEP FRAME STK LO_LOW LO_SP SP_TOP MEMOK.
  pose proof (bv_unsigned_in_range 64 sp) as SP_RANGE. unfold bv_modulus in SP_RANGE. cbn in SP_RANGE.
  pose proof (munch_refl [(q, q + 24); (rn, rn + 8); (lh + 88, lh + 96)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  lazymatch type of MU with munch ?W _ _ => assert (HWS : sh_fp W) by sh_fp_lia end.
  cbn [app] in FRAME. unfold lhs_cells in HDR. unfold SITE_lhi_malloc.
  zstep.
  replace (bv_eqb (Z_to_bv 64 q) (Z_to_bv 64 0)) with false
    by (symmetry; unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  cbv iota.
  do 4 zstep. th_if_lit.
  zstep.
  do 5 zstep. th_if_lit.
  zstep. th_fix_lit_store.
  do 5 zstep. th_if_lit.
  do 2 zstep.
  do 2 zstep. th_if_lit.
  zstep.
  do 2 zstep. th_if_lit.
  do 4 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mfin _) =>
    eapply evt_cut;
    [ apply (lhi_epi (Z_to_bv 64 SITE_lhi_malloc) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 sp (Z_to_bv 64 (rn ≫ 3 + 2147450880))
               (Z_to_bv 64 0) (Z_to_bv 64 (items + 1)) h a3 a4 a5 a6 a7
               (Z_to_bv 64 (lh + 88)) (Z_to_bv 64 data) (Z_to_bv 64 rn) s5 s3
               (Z_to_bv 64 ((lh + 88) ≫ 3 + 2147450880)) (Z_to_bv 64 ((lh + 96) ≫ 3 + 2147450880)) (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6
               F fc mfin lo sp rav s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v [CB 80 LOC80; C8 h]
               eq_refl eq_refl FRAME STK LO_SP SP_TOP ltac:(lia) MEMOK)
    | intros ms_end (-> & STK_END); apply evt_done;
      destruct (proj1 (lhg_rw_cells_app asegs mfin q [C8 (Z_to_bv 64 data)] [C8 (Z_to_bv 64 0); C8 h]) QCELLS) as (QD & QREST);
      destruct (proj1 (lhg_rw_cells_app asegs mfin _ [C8 (Z_to_bv 64 0)] [C8 h]) QREST) as (QN & QH);
      cbn [cells_size csize] in QN, QH;
      exists t0, t1, t2, (Z_to_bv 64 (items + 1)), h, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc, mfin;
      split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [exact MEMOK|]; split; [exact STK_END|];
      split; [exact QD|];
      split; [replace (q + 8) with (q + Z.of_nat 8) by lia; exact QN|];
      split; [replace (q + 16) with (q + Z.of_nat 8 + Z.of_nat 8) by lia; exact QH|];
      split; [exact RN_NULL| exact HDR] ]
  end.
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
  intros GOBJ m m2 L lh B q na bks src tail APART SIZED RAW OLD NEW ZERO SAME FRESH QPOS QTOP.
  destruct RAW as ((INLH & _) & LHR & (INB & _) & BR & LEN & CH & ND).
  pose proof (SIZED B (8 * na) INB) as NA_POS.
  apply NoDup_cons_iff in ND. destruct ND as (NOT_LH & ND1). apply NoDup_cons_iff in ND1. destruct ND1 as (NOT_B & ND2).
  assert (LH_NE_B : lh <> B) by (intros ->; exact (NOT_LH (or_introl eq_refl))).
  assert (OWNED : forall p A, In (p, A) (concat bks) -> In (A, 24) L /\ p = bp A /\ A <> B).
  { intros p A INC. pose proof INC as INC'. apply in_concat in INC'. destruct INC' as (ns & INNS & INX).
    destruct (In_nth bks ns [] INNS) as (k & KLT & KTH).
    pose proof (CH (Z.of_nat k) ltac:(lia)) as CHK. rewrite Nat2Z.id, KTH in CHK.
    destruct (chain_owns _ _ _ _ _ _ _ CHK p A INX) as (INA & EP). subst p.
    split; [exact INA|]. split; [reflexivity|].
    intros ->. apply NOT_B. apply in_map_iff. exists (bp B, B). split; [reflexivity| exact INC]. }
  assert (KEEP : forall A n, In (A, n) L -> A <> B -> In (A, n) (live_remove B L)).
  { intros A n INL NEB. exact (live_remove_keep L B (A, n) INL NEB). }
  assert (Q_LH : q + 16 * na <= lh \/ lh + 104 <= q).
  { apply (FRESH lh 104 INLH). intros E. injection E as E _. exact (LH_NE_B E). }
  split; [split; [right; exact (KEEP lh 104 INLH LH_NE_B)| reflexivity]|].
  split; [exact LHR|].
  split; [split; [left; f_equal; lia| reflexivity]|].
  split; [lia|].
  split; [rewrite length_app, repeat_length; lia|].
  split.
  - intros j JR. destruct (Z_lt_ge_dec j na) as [LOW|HIGH].
    + rewrite app_nth1 by lia.
      destruct (chain_chainv _ _ _ _ _ _ _ (CH j ltac:(lia))) as (v & SLOT & CV).
      apply (chainv_chain _ _ _ m2 _ _ (q + 8 * j) v).
      * rewrite <- (Z2Nat.id j) in SLOT |- * by lia.
        exact (cells_read_back asegs m m2 B q (Z.to_nat na) (8 * Z.to_nat na) src tail (Z.to_nat j) (wz v) OLD SLOT ltac:(lia) NEW).
      * apply (chainv_own _ _ _ m2 (ownL L)).
        -- apply (chainv_agree _ _ _ m m2 _ _ v CV). apply (agree_on_mono asegs _ _ m m2 SAME).
           intros a (p & A & INX & RNG). exists p, A. split; [| exact RNG].
           apply (in_concat_nth bks (Z.to_nat j)); [lia| exact INX].
        -- intros p A INX (INA & EP). split; [right|exact EP].
           apply KEEP; [exact INA|]. apply (OWNED p A). apply (in_concat_nth bks (Z.to_nat j)); [lia| exact INX].
    + rewrite app_nth2 by lia. rewrite nth_repeat.
      exists (q + 8 * j). split; [reflexivity|].
      pose proof (cells_zero asegs m2 (q + 8 * na) (Z.to_nat na) (Z.to_nat (j - na)) ZERO ltac:(lia)) as CELL.
      replace (q + 8 * na + 8 * Z.of_nat (Z.to_nat (j - na))) with (q + 8 * j) in CELL by lia. exact CELL.
  - rewrite concat_app, concat_repeat_nil, app_nil_r.
    constructor.
    { intros [E|IN]; [| exact (NOT_LH (or_intror IN))].
      apply bp_inj in E. lia. }
    constructor; [| exact ND2].
    intros INQ. apply in_map_iff in INQ. destruct INQ as ((p & A) & EP & INC). cbn [fst] in EP. subst p.
    destruct (OWNED (bp q) A INC) as (INA & EA & NEB). apply bp_inj in EA. subst A.
    destruct (FRESH q 24 INA) as [OV|OV]; [intros E; injection E as E _; exact (NEB E)| lia| lia].
Qed.
