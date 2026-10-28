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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AllocTacX.
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
Definition sec_shadow (size msz : Z) : list byte :=
  repeat (b8 0xfa) 256 ++ repeat (b8 0) (Z.to_nat (size / 8))
  ++ (if size mod 8 =? 0 then [] else [b8 (size mod 8)])
  ++ repeat (b8 0xfa) (Z.to_nat ((msz - 6144 - round_up size 8) / 8)).

(* [comment removed for export] *)
Definition alloc_sec_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list ivl) (lo size a msz TH id : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (b1 : Z) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (a + 6144)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    (* [comment removed for export] *)
    /\ rw_cells asegs m' (a + 6128) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ b1_ok b1
    /\ rw_cells asegs m' (a + 4096) [C8 (wz kAllocBegMagic); C8 (wz (a + 6128))] /\ stk asegs m' (a + 4112) (a + 6128)
    /\ u8arr asegs m' (a + 6144) (repeat (b8 0xbe) 4096)
    /\ stk asegs m' (a + 6144 + 4096) (a + msz)
    /\ u8arr asegs m' (sh (a + 4096)) (sec_shadow size msz)
    (* [comment removed for export] *)
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW.

Section SecTail.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (TSD CTX TH sb : Z).
  Variables (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).   (* [comment removed for export] *)
  Variables (a msz needed q8 r8 id : Z).
  Hypothesis DEFS : hidden (needed = round_up (Z.max size 8) 8 + 4096 /\ msz = round_up needed 4096 + 4096 /\ size = 8 * q8 + r8).
  Let W : list ivl := [(lo, bv_unsigned sp); (a + 4096, a + msz); (sh (a + 4096), sh (a + msz)); (TH + 2800, TH + 3168)]%Z.
  Let AFR := aframe sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 768 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 64512 < size < 2^32. Hypothesis R8 : 0 <= r8 < 8.
  Hypothesis AR : aapp a msz /\ a + msz <= aceil /\ a mod 4096 = 0.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((CTX + 160 <= TH \/ TH + 4096 <= CTX) /\ (TH + 4096 <= a \/ a + msz <= TH) /\ (CTX + 160 <= a \/ a + msz <= CTX)).
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).

  Let ARE : 12599296 <= a /\ a + msz <= aceil.   (* [comment removed for export] *)
  Proof. destruct DEFS as [(DN & DM & _)]. refine (aapp_env _ _ (proj1 AR) _). rewrite DM, DN. unfold round_up. clear. Z.div_mod_to_equations. lia. Qed.
  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DNEED & DMSZ & DSZ)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12599296 <= a /\ a + msz <= aceil /\ 140735332483072 <= aceil   (* [comment removed for export] *)
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296 /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328)
      by (clear - LO RNG ARE TPR SOR; try acb; destruct RNG as [RNG']; destruct TPR as [TPR']; destruct SOR as [SOR']; unfold AHI_LO, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SOR'; aunf; lia);
        region_sides; name_bands;
    assert (GEO : size + 8 <= needed - 4088 /\ needed <= size + 4096 + 8 /\ needed + 4096 <= msz /\ msz < needed + 8192 /\ 8 * q8 <= size /\ size < 8 * q8 + 8
                  /\ needed = 8 * q8 + (if r8 =? 0 then 0 else 8) + 4096)
      by (clear - DNEED DMSZ DSZ SZ R8; try acb; subst needed msz; unfold round_up; destruct (Z.eqb_spec r8 0); Z.div_mod_to_equations; nia);
    assert (ALN : exists thq aq mq, TH = 16 * thq /\ a = 4096 * aq /\ msz = 4096 * mq)
      by (clear - RNG AR DMSZ; try acb; destruct RNG as [RNG']; exists (TH / 16), (a / 4096), (msz / 4096); subst msz; unfold round_up; Z.div_mod_to_equations; aunf; lia);
    destruct ALN as (thq & aq & mq & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (SHR : 2148314624 <= sh (a + 4096) /\ sh (a + msz) <= 17594333495296 /\ sh (a + 4096) = sh a + 512 /\ sh (a + msz) = sh a + 512 * mq
                  /\ sh (a + 6144) = sh a + 768)
      by (clear - BND ALN; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    clear DNEED DMSZ.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma aenv_sec_now : forall m0 m1, AENV tp TSD CTX TH sb SO T rest m0 -> munch W m0 m1 -> wmono asegs m0 m1 -> AENV tp TSD CTX TH sb SO T rest m1.
  Proof.
    intros m0 m1 E MU0 WM0. unfold W in MU0. prep. open_env E. region_table.
    lazymatch goal with MUh : munch ?W0 _ _ |- _ => region_hull_memo W0 end.   (* [comment removed for export] *)
    econstructor; unfold AGOT_VALS; cbn [map repeat];
      first [ eapply rw_cells_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; region_decide]
            | eapply u64arr_transport; [eassumption| exact MU0| exact WM0| cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; region_decide] ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_sec_t2b : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mE : mem) (j8 : list byte) (ob0 : byte) (hb1 : Z) (shd : list byte),
    AENV tp TSD CTX TH sb SO T rest mE -> mem_inv asegs mE ->
    AFR mE j8 -> stk asegs mE lo (bv_unsigned sp + -128) ->
    rw_cells asegs mE (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mE (a + 4096) (a + 6128) -> stk asegs mE (a + 6144) (a + msz) ->
    u8arr asegs mE (sh (a + 4096)) shd -> shd = sec_shadow size msz -> Z.of_nat (length shd) = sh (a + msz) - sh (a + 4096) ->
    stk asegs mE (TH + 2800) (TH + 3168) ->
    evt asegs (alloc_sec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mE W lo size a msz TH id)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x197348) fc None mE (seg_rom asegs)).
  Proof.
    intros until shd. intros ENV MI FR ST HDR HB1R HB1M LRZ USR SHD SHDE SHDN TST.
    prep. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold W.
    pose proof (munch_refl W mE) as MU. pose proof (wmono_refl asegs mE) as WM. unfold W in MU.
    pose proof (bv_unsigned_in_range _ ob0) as OB0. change (bv_modulus 8) with 256 in OB0. rewrite <- (b8_of_byte ob0) in HDR.
    region_table.
    (* [comment removed for export] *)
    step. callD getcurthreadstats_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (lia_guard; (first [clear - HI BND; lia | lia])).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; lia)). all: try (unfold AIMG_TOP; lia).
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2824) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H end.
    destruct (stk_cells _ _ _ TS1 ltac:(hci; lia)) as [sj SJ]. replace (TH + 2824 - (TH + 2800)) with 24 in SJ by lia. change (Z.to_nat 24) with 24%nat in SJ.
    unfold wz.
    step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    lazymatch goal with H : stk _ _ (TH + 2824) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2824) (TH + 2904) (TH + 3168) H ltac:(hci; lia)) as [TS3 TS4]; clear H end.
    destruct (stk_split asegs _ (TH + 2904) (TH + 2912) (TH + 3168) TS4 ltac:(hci; lia)) as [TS5 TS6]. clear TS4.
    destruct (stk_cells _ _ _ TS5 ltac:(hci; lia)) as [hj HJ]. replace (TH + 2912 - (TH + 2904)) with 8 in HJ by lia. change (Z.to_nat 8) with 8%nat in HJ.
    step. step. step.
    (* [comment removed for export] *)
    step. step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. rewrite sx32_wz by lia. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    step.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    change (sx32 (Z_to_bv 64 190)) with (sx32 (wz 190)). rewrite sx32_wz by lia. unfold wz.
    destruct (stk_split asegs _ (a + 6144) (a + 6144 + 4096) (a + msz) USR ltac:(hci; lia)) as [US1 US2].
    destruct (stk_cells _ _ _ US1 ltac:(hci; lia)) as [fj FJ]. replace (a + 6144 + 4096 - (a + 6144)) with 4096 in FJ by lia.
    callD memset_spec. all: rewrite ?unsigned_lit by lia. all: try exact FJ; try eassumption; try (lia_guard; lia).
    lazymatch goal with H : rw_cells asegs _ (a + 6144) [CB _ _] |- _ => rename H into FILLC end. change (190 mod 256) with 190 in FILLC.
    (* [comment removed for export] *)
    step. callD lsan_disabled_spec. all: try eassumption.
    step. rewrite zxb_b8 by lia. step. step. step. step. step.
    pose proof (land_lt_pow2 hb1 243 8 ltac:(hci; lia) ltac:(hci; lia)) as XL. change (2^8) with 256 in XL.
    match goal with |- context [Z_to_bv 64 (Z.lor ?av ?bv)] =>
      replace (Z_to_bv 64 (Z.lor av bv)) with (Z_to_bv 64 (Z.land hb1 243))
        by (f_equal; unfold wz; rewrite (unsigned_lit hb1) by lia;
            replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 0))))) with 0 by (vm_compute; reflexivity);
            change (Z.land 0 12) with 0; rewrite (unsigned_lit 0) by lia; rewrite unsigned_lit by lia; rewrite Z.lor_0_r; reflexivity) end.
    (* [comment removed for export] *)
    st1. step. st1. change (Z_to_bv 8 2) with (b8 2) in HDR.
    replace ((Z.land hb1 243) mod 256) with (Z.land hb1 243) in HDR by (symmetry; apply Z.mod_small; destruct HB1M; lia).
    pose proof (u8arr_of_rw_cells _ _ _ _ _ FILLC) as FILL. change (Z_to_bv 8 190) with (b8 190) in FILL. clear FILLC.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    step. step. if_cases K2; zify_cond K2. { exfalso. rewrite ?unsigned_lit in K2 by lia. lia. } clear K2.
    step. step.
    destruct (stk_split asegs _ (a + 4096) (a + 4112) (a + 6128) LRZ ltac:(hci; lia)) as [MG1 MG2].
    destruct (stk_cells _ _ _ MG1 ltac:(hci; lia)) as [mj MAGC]. replace (a + 4112 - (a + 4096)) with 16 in MAGC by lia. change (Z.to_nat 16) with 16%nat in MAGC.
    step. step. st1.
    (* [comment removed for export] *)
    step. step. step. callD run_malloc_hooks_spec. all: rewrite ?unsigned_lit by (first [clear - HI ARE SPR BND SPQ; lia | lia]). all: try eassumption; try (lia_guard; lia).
    (* [comment removed for export] *)
    do 16 step.
    lazymatch goal with H : stk _ _ lo _ |- _ => release_frame FR H (bv_unsigned sp) end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TST' : stk asegs mm (TH + 2800) (TH + 3168))
        by (apply (stk_merge asegs _ _ (TH + 2824)); [exact TS1| |lia]; apply (stk_merge asegs _ _ (TH + 2904)); [exact TS3| |lia];
            apply (stk_merge asegs _ _ (TH + 2912)); [exact TS5| exact TS6 |lia]) end.
    apply evt_done; unfold alloc_sec_post. do 14 eexists. exists (Z.land hb1 243). eexists. split; [reflexivity|].
    repeat match goal with |- _ /\ _ => split end; try assumption.
    subst shd. exact SHD.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_sec_t2j : forall (x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mE : mem) (j8 : list byte) (ob0 : byte) (hb1 : Z) (gb : byte) (t8 : Z),
    AENV tp TSD CTX TH sb SO T rest mE -> mem_inv asegs mE ->
    AFR mE j8 -> stk asegs mE lo (bv_unsigned sp + -128) ->
    rw_cells asegs mE (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mE (a + 4096) (a + 6128) -> stk asegs mE (a + 6144) (a + msz) ->
    u8arr asegs mE (sh (a + 4096)) (repeat (b8 0xfa) 256 ++ repeat (b8 0) (Z.to_nat q8)) ->
    rw_cells asegs mE (sh (a + 6144) + q8) [C1 gb] ->
    u8arr asegs mE (sh (a + 6144) + q8 + 1) (repeat (b8 0xfa) (Z.to_nat t8)) -> t8 = sh (a + msz) - (sh (a + 6144) + q8 + 1) ->
    stk asegs mE (TH + 2800) (TH + 3168) ->
    r8 <> 0 ->
    evt asegs (alloc_sec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mE W lo size a msz TH id)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) (wz 2147450880) x11 x12 x13 x14 x15 x16 x17
               (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) (wz (a + 6144 + 8 * q8)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x197324) fc None mE (seg_rom asegs)).
  Proof.
    intros until t8. intros ENV MI FR ST HDR HB1R HB1M LRZ USR SHL GB SHT T8 TST R8NZ.
    prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold W.
    pose proof (munch_refl W mE) as MU. pose proof (wmono_refl asegs mE) as WM. unfold W in MU.
    assert (SHLN : Z.of_nat (length (repeat (b8 250) 256 ++ repeat (b8 0) (Z.to_nat q8))) = 256 + q8) by (rewrite length_app, !repeat_length; lia).
    assert (SHTN : Z.of_nat (length (repeat (b8 250) (Z.to_nat t8))) = t8) by (rewrite repeat_length; lia).
    region_table.
    (* [comment removed for export] *)
    step. step. step. rewrite zxb_b8 by lia. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.land ?x ?y))) 7)] =>
      replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (Z.land x y))) 7)) with (Z_to_bv 64 r8) end.
    2:{ f_equal. replace (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (wz 1))))) with (Z.ones 64) by (vm_compute; reflexivity).
        rewrite (unsigned_lit size), Z.land_ones by lia. rewrite Z.mod_small by lia.
        rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - GEO R8 DSZ; try acb. Z.div_mod_to_equations. lia. }
    rewrite (unsigned_lit (a + 6144 + 8 * q8)) by lia.
    replace (2147450880 + (a + 6144 + 8 * q8) ≫ 3) with (sh (a + 6144) + q8 + 0)
      by (rewrite Z.shiftr_div_pow2 by lia; unfold sh, ASHADOW_BASE; clear - ALN GEO; try acb; Z.div_mod_to_equations; lia).
    remember (sh (a + 6144) + q8) as SA eqn:ESA in *.
    (* [comment removed for export] *)
    st1.
    subst SA. replace (r8 mod 256) with r8 in GB by (symmetry; apply Z.mod_small; lia).
    apply rw_cells_C1, (u8arr_of_rw_cells asegs) in GB.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHD' : u8arr asegs mm (sh (a + 4096)) (sec_shadow size msz)) end.
    { unfold sec_shadow. rewrite DSZ.
      replace ((8 * q8 + r8) / 8) with q8 by (clear -R8; Z.div_mod_to_equations; lia). replace ((8 * q8 + r8) mod 8) with r8 by (clear -R8; Z.div_mod_to_equations; lia).
      replace (r8 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (round_up (8 * q8 + r8) 8) with (8 * q8 + 8) by (unfold round_up; clear - R8NZ R8 DSZ; try acb; Z.div_mod_to_equations; lia).
      replace (Z.to_nat ((msz - 6144 - (8 * q8 + 8)) / 8)) with (Z.to_nat t8) by (clear - GEO SHR ALN R8NZ T8 SZ R8 DSZ; try acb; Z.div_mod_to_equations; lia).
      rewrite app_assoc. apply u8arr_app. split; [exact SHL|]. rewrite SHLN. replace (sh (a + 4096) + (256 + q8)) with (sh (a + 6144) + q8) by lia.
      apply u8arr_app. split; [exact GB|]. cbn [length Z.of_nat Pos.of_succ_nat]. exact SHT. }
    eapply evt_mono.
    { eapply (alloc_sec_t2b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j8 ob0 hb1 (sec_shadow size msz));
        try eassumption; try reflexivity; try (unfold wz; eassumption).
      - exact (aenv_sec_now _ _ ENV0 MU WM).
      - unfold sec_shadow. rewrite DSZ.
        replace ((8 * q8 + r8) / 8) with q8 by (clear -R8; Z.div_mod_to_equations; lia). replace ((8 * q8 + r8) mod 8) with r8 by (clear -R8; Z.div_mod_to_equations; lia).
        replace (r8 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (round_up (8 * q8 + r8) 8) with (8 * q8 + 8) by (unfold round_up; clear - R8NZ R8 DSZ; try acb; Z.div_mod_to_equations; lia).
        rewrite !length_app, !repeat_length. cbn [length]. clear - GEO SHR ALN R8NZ T8 SZ R8 DSZ; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    cbv beta. intros ms' P'. unfold alloc_sec_post in P' |- *.
    destruct P' as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & b1 & m' & E' & MU' & WM' & REST).
    exists v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, b1, m'. split; [exact E'|].
    split; [exact (munch_trans _ _ _ _ MU MU')|]. split; [exact (wmono_trans _ _ _ _ WM WM')|]. exact REST.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma alloc_sec_t2 : forall (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (mE : mem) (j8 : list byte) (ob0 : byte) (hb1 : Z) (gb : byte) (t8 : Z),
    AENV tp TSD CTX TH sb SO T rest mE -> mem_inv asegs mE ->
    AFR mE j8 -> stk asegs mE lo (bv_unsigned sp + -128) ->
    rw_cells asegs mE (a + 6128) [C1 ob0; C1 (b8 hb1); C2 (wz 0); C4 (wz size); C8 (wz id)] ->
    0 <= hb1 < 256 -> b1_ok (Z.land hb1 243) ->
    stk asegs mE (a + 4096) (a + 6128) -> stk asegs mE (a + 6144) (a + msz) ->
    u8arr asegs mE (sh (a + 4096)) (repeat (b8 0xfa) 256 ++ repeat (b8 0) (Z.to_nat q8)) ->
    rw_cells asegs mE (sh (a + 6144) + q8) [C1 gb] -> (r8 = 0 -> gb = b8 0xfa) ->
    u8arr asegs mE (sh (a + 6144) + q8 + 1) (repeat (b8 0xfa) (Z.to_nat t8)) -> t8 = sh (a + msz) - (sh (a + 6144) + q8 + 1) ->
    stk asegs mE (TH + 2800) (TH + 3168) ->
    evt asegs (alloc_sec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mE W lo size a msz TH id)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 (wz size) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (a + 4096)) (wz needed) (wz (a + 6144)) (wz (a + 6128)) (wz (8 * q8)) x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1972b4) fc None mE (seg_rom asegs)).
  Proof.
    intros until t8. intros ENV MI FR ST HDR HB1R HB1M LRZ USR SHL GB GBFA SHT T8 TST.
    prep. pose proof ENV as ENV0. open_env ENV. unfold AFR, aframe in FR. unfold wz in *. unfold W.
    pose proof (munch_refl W mE) as MU. pose proof (wmono_refl asegs mE) as WM. unfold W in MU.
    assert (SHLN : Z.of_nat (length (repeat (b8 250) 256 ++ repeat (b8 0) (Z.to_nat q8))) = 256 + q8) by (rewrite length_app, !repeat_length; lia).
    assert (SHTN : Z.of_nat (length (repeat (b8 250) (Z.to_nat t8))) = t8) by (rewrite repeat_length; lia).
    region_table.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
    - (* [comment removed for export] *)
      rewrite (GBFA ltac:(hci; lia)) in GB.
      apply rw_cells_C1, (u8arr_of_rw_cells asegs) in GB.
      assert (SHD' : u8arr asegs mE (sh (a + 4096)) (sec_shadow size msz)).
      { unfold sec_shadow. rewrite K.
        replace (8 * q8 / 8) with q8 by (clear -K; Z.div_mod_to_equations; lia). replace ((8 * q8) mod 8) with 0 by (clear -K; Z.div_mod_to_equations; lia). cbn [Z.eqb app].
        replace (round_up (8 * q8) 8) with (8 * q8) by (unfold round_up; clear - K; try acb; Z.div_mod_to_equations; lia).
        replace (Z.to_nat ((msz - 6144 - 8 * q8) / 8)) with (S (Z.to_nat t8)) by (clear - GEO SHR ALN K T8; try acb; Z.div_mod_to_equations; lia).
        change (repeat (b8 250) (S (Z.to_nat t8))) with ([b8 250] ++ repeat (b8 250) (Z.to_nat t8)).
        rewrite app_assoc. apply u8arr_app. split; [exact SHL|]. rewrite SHLN. replace (sh (a + 4096) + (256 + q8)) with (sh (a + 6144) + q8) by lia.
        apply u8arr_app. split; [exact GB|]. cbn [length Z.of_nat Pos.of_succ_nat]. exact SHT. }
      eapply (alloc_sec_t2b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mE j8 ob0 hb1 (sec_shadow size msz)); try eassumption; try reflexivity; try (unfold wz; eassumption).
      unfold sec_shadow. rewrite K.
      replace (8 * q8 / 8) with q8 by (clear -K; Z.div_mod_to_equations; lia). replace ((8 * q8) mod 8) with 0 by (clear -K; Z.div_mod_to_equations; lia). cbn [Z.eqb].
      replace (round_up (8 * q8) 8) with (8 * q8) by (unfold round_up; clear - K; try acb; Z.div_mod_to_equations; lia).
      rewrite !length_app, !repeat_length. cbn [length]. clear - GEO SHR ALN K T8 SZ R8; try acb. Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *)
      step. callD can_poison_spec. all: try (unfold ACANPOISON; eassumption).
      step. if_cases K2. { exfalso. revert K2. vm_compute. discriminate. } clear K2.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step. step.
      match goal with |- context [Z_to_bv 64 (Z.land ?x 2147450879)] =>
        replace (Z_to_bv 64 (Z.land x 2147450879)) with (Z_to_bv 64 2147450879) by (apply bv_eq; vm_compute; reflexivity) end.
      (* [comment removed for export] *)
      destruct (proj1 AR) as [ALO|AHI].
      { pose proof ALO as ALO'. unfold aapp_lo, AIMG_TOP, ALOWSH_LO in ALO'.
        step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. 2:{ exfalso. clear - K3 ALO' GEO SZ; try acb. lia. } clear K3.
        eapply alloc_sec_t2j; try eassumption. clear - K DSZ R8; lia. }
      pose proof AHI as AHI'. unfold aapp_hi, AHI_LO in AHI'.
      step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia. { exfalso. clear - K3 AHI' GEO SZ; try acb. lia. } clear K3.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      step. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia. 2:{ exfalso. revert K4. rewrite ?unsigned_lit by lia.
        change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615. clear - AHI' GEO SZ; try acb. intros K4. lia. }
      clear K4.
      (* [comment removed for export] *)
      step. step. step. step. step.
      step. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by lia. { exfalso. clear - K5 AHI' GEO SZ; try acb. lia. } clear K5.
      step. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia. { exfalso. clear - K6 AHI' GEO SZ; try acb. lia. } clear K6.
      (* [comment removed for export] *)
      eapply alloc_sec_t2j; try eassumption. clear - K DSZ R8; lia.
  Qed.
End SecTail.

