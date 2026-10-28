(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA RzCPS NodesA SysStep Arr FarCall Bytes Frame.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Str_tac Startup_glue Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface D_defs D_kit D_agree D_clx R_cache_defs PLayout I_lkit I_ut RT_iface_pem D_libiface_pem Fz_kit Fz_ckit Fz_chk Fz_fkit Fz_mkit Fz_env Fz_M_free Fz_M_secure Fz_W1_defs Fz_W1_misc Fz_W1_pploc Fz_W1_grow Fz_W3_iface Fz_W3_defs Fz_W3_lems Fz_W3_aux Fz_W3_aux2 Fz_W3_aux3 Fz_W3_lits Fz_W3_inik Fz_ukit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tslia ::= wp_tslia.
Notation wz := (Z_to_bv 64) (only parsing).
Local Ltac zgo p := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 p) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep; lfix end).
Definition SITE_j0_sm : Z := 0x30c118.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition j0_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
(* [comment removed for export] *)
Definition j0_w0_post (SP : Z) (gp t0 t1 t2 sp a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 : word) (saved : list cell) (F : bvmap 5 word) (fc : bv 32)
    (BI PN PH PD PLN fl lo pd : Z) (m : mem) : machine_state -> Prop :=
  fun ms => exists (a1' a2' : word) (j1 j2 g : list byte) (m' : mem),
    ms = MS (mkR (wz SITE_j0_sm) (wz (SP - 352 - pd)) gp (wz TP_A) t0 t1 t2 sp (wz (SP - 352 - pd)) (wz 96) a1' a2' (wz PD) (wz PLN) (wz fl) a6 a7
                 s2 (wz PLN) (wz fl) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
            F (wz (e_stack_malloc 1)) fc None m' (seg_rom asegs)
    /\ munch [(SP - 352 - pd, SP)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (SP - 352 - pd) [CB 216 j1; C8 (wz BI); CB 24 j2; CB (Z.to_nat pd) g]
    /\ rw_cells asegs m' (SP + -104) saved
    /\ stk asegs m' lo (SP - 352 - pd).

Lemma j0_w0 : forall ra sp gp t0 t1 t2 s0 s1 BI PN PH PD PLN fl a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo pd : Z),
  (pd = 0 \/ pd = 16) -> bv_unsigned sp mod 32 = pd ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 1136 -> 0x10007fff8000 <= lo -> bv_unsigned sp <= 2^47 ->
  img_untouched m -> ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 0x7fff8000)] ->
  ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)] -> mem_inv asegs m ->
  evt asegs (j0_w0_post (bv_unsigned sp) gp t0 t1 t2 sp a6 a7 s2 s6 s7 s8 t3 t4 t5 t6 (j0_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F fc BI PN PH PD PLN fl lo pd m)
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz BI) (wz PN) (wz PH) (wz PD) (wz PLN) (wz fl) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz FZ_PEM_READ_BIO) fc None m (seg_rom asegs)).
Proof.
  intros until pd. intros HP HPM ST HLO HLOS SPH UT SHC UAR MI. unfold FZ_PEM_READ_BIO, g_shadow_memory_dynamic_address, g_detect_stack_use_after_return, TP_A in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn [Z.of_N] in RSP.
  remember (bv_unsigned sp) as SP eqn:ESP. rewrite <- (Z_to_bv_bv_unsigned sp). rewrite <- ESP.
  pose proof (munch_refl [(SP - 352 - pd, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (HWU : ut_fp [(SP - 352 - pd, SP)]) by ut_fp_lia.
  carve_frame 352%nat ST.
  zstep. zstep; lfix. do 13 (zstep; lfix).
  zstep. zstep.
  rewrite (land_m32_pad (SP + -352) pd) by (first [lia | replace (SP + -352) with (SP + (-11) * 32) by lia; rewrite Z.mod_add by lia; exact HPM]).
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep; lfix. zstep; lfix. zstep; lfix. zstep; lfix.
  destruct HP as [-> | ->].
  - replace (SP + -352 - 0) with (SP + -352) in * by lia.
    zstep; lfix. zstep. if_false. zstep. zstep.
    lazymatch type of FR with rw_cells _ ?mm _ (C8 ?z :: CB 208 ?ja :: C8 ?bi :: CB 24 ?jb :: ?sv) =>
      destruct (proj1 (rw_cells_app mm (SP + -352) [C8 z; CB 208 ja; C8 bi; CB 24 jb] sv) FR) as [FRL SAV];
      pose proof (rw_cells_blur mm (SP + -352) [C8 z; CB 208 ja] [C8 bi; CB 24 jb] FRL) as FRB end.
    cbn [cells_size csize Nat.add app] in SAV, FRB. replace (SP + -352 + 248) with (SP + -104) in SAV by lia.
    lazymatch type of FRB with rw_cells _ ?mm _ ?l =>
      assert (FRX : rw_cells asegs mm (SP + -352) (l ++ [CB 0%nat []]));
      [apply (proj2 (rw_cells_app mm (SP + -352) l [CB 0%nat []])); split; [exact FRB|]; cbn [cells_size csize Nat.add]; apply rw_cells_CB0; lia|] end.
    cbn [app] in FRX.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold j0_w0_post, SITE_j0_sm, e_stack_malloc, SHB, j0_saved. apply evt_done. do 6 eexists.
    replace (bv_unsigned sp - 352 - 0) with (bv_unsigned sp + -352) by lia.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRX|]. split; [exact SAV| exact ST].
  - replace (SP + -352 - 16) with (SP + -368) in * by lia.
    carve_frame 16%nat ST.
    zstep; lfix. zstep. if_false. zstep. zstep.
    lazymatch type of FR with rw_cells _ ?mm _ (C8 ?z :: CB 192 ?ja :: C8 ?bi :: CB 40 ?jb :: ?sv) =>
      destruct (proj1 (rw_cells_app mm (SP + -352) [C8 z; CB 192 ja; C8 bi; CB 40 jb] sv) FR) as [FRL SAV];
      pose proof (rw_cells_split_CB asegs mm (SP + -352) [C8 z; CB 192 ja; C8 bi] 40 jb [] [24; 16]%nat FRL eq_refl) as FRS end.
    cbn [cells_size csize Nat.add app mk_CB_cells sum_nat] in SAV, FRS. replace (SP + -352 + 248) with (SP + -104) in SAV by lia.
    lazymatch type of FRS with rw_cells _ ?mm _ ?l =>
      lazymatch type of FR0 with rw_cells _ _ _ [CB 16 ?g0] =>
        assert (FRJ : rw_cells asegs mm (SP + -368) ([CB 16 g0] ++ l));
        [apply (proj2 (rw_cells_app mm (SP + -368) [CB 16 g0] l)); split; [exact FR0|]; cbn [cells_size csize Nat.add]; replace (SP + -368 + 16) with (SP + -352) by lia; exact FRS|] end end.
    lazymatch type of FRJ with rw_cells _ ?mm _ ([CB 16 ?g0] ++ (C8 ?z :: CB 192 ?ja :: ?rest)) =>
      pose proof (rw_cells_blur mm (SP + -368) [CB 16 g0; C8 z; CB 192 ja] rest FRJ) as FRX end.
    cbn [cells_size csize Nat.add app] in FRX.
    subst SP. rewrite ?Z_to_bv_bv_unsigned.
    unfold j0_w0_post, SITE_j0_sm, e_stack_malloc, SHB, j0_saved. apply evt_done. do 6 eexists.
    replace (bv_unsigned sp - 352 - 16) with (bv_unsigned sp + -368) by lia.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FRX|]. split; [exact SAV| exact ST].
Qed.
(* [comment removed for export] *)
Definition j0_hdr (pcw : word) : list cell := [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); C8 pcw].
Definition j0_sh12 : list cell :=
  [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4);
   C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13))].
Definition SITE_j0_c1 : Z := 0x30c1c4.   (* [comment removed for export] *)
Definition j0_w1a_post (sp1 : Z) (gp t0 t1 t2 sp a6 a7 s7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (f PN PH PD PLN fl : Z) (fj sj : list byte) (m : mem)
    : machine_state -> Prop :=
  fun ms => exists (pcw : word) (m' : mem),
    ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (PLN / 8)) (wz 4) pcw (wz (-8)) (wz (-14)) (wz (-15)) a6 a7
                 (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
            F (wz SITE_j0_c1) fc None m' (seg_rom asegs)
    /\ munch [(f, f + 24); (f / 8 + SHB, f / 8 + SHB + 12)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' f (j0_hdr pcw ++ [CB 96 (skipn 24 fj)])
    /\ rw_cells asegs m' (f / 8 + SHB) (j0_sh12 ++ [CB 4 (skipn 12 sj)]).

Lemma j0_w1a : forall sp1 gp t0 t1 t2 sp b1 b2 b3 b4 b5 b6 b7 s2 s6 s7 s8 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem)
    (f PN PH PD PLN fl : Z) (fj sj : list byte),
  0 < f -> f + 128 <= 2^47 -> (f + 120 <= 0x10000 \/ SEGTOP_A <= f) -> (f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) ->
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0x10007fff8000 <= sp1 -> f + 128 <= sp1 -> 0 < PLN -> PLN + 8 <= 2 ^ 47 ->
  img_untouched m -> rw_cells asegs m f [CB 120 fj] -> rw_cells asegs m (shad f) [CB 16 sj] -> mem_inv asegs m ->
  evt asegs (j0_w1a_post sp1 gp t0 t1 t2 sp b6 b7 s7 t3 t4 t5 t6 F fc f PN PH PD PLN fl fj sj m)
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz f) b1 b2 b3 b4 b5 b6 b7 s2 (wz PLN) (wz fl) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_sm) fc None m (seg_rom asegs)).
Proof.
  intros until sj. intros F0 FH FIMG FSH SP0 SPH SPS FSP L0 LH UT FB SB MI.
  unfold SITE_j0_sm, TP_A, shad, SHB in *.
  pose proof (munch_refl [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 12)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts f) as Qf.
  assert (SHR : 0x7fff8000 <= f / 8 + 2147450880 /\ f / 8 + 2147450880 + 16 <= 0x10007fff8000) by (clear - Qf F0 FH; lia).
  assert (HWU : ut_fp [(f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450880 + 12)]) by (clear - F0 FIMG Qf SHR SPS SPH; unfold SEGTOP_A in *; ut_fp_lia).
  assert (EUf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 PLN) = PLN) by (apply unsigned_lit; lia).
  assert (TST : f + 24 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 12 <= f) by (clear - Qf FSH F0 FH; lia).
  zstep. zstep. zstep. zstep. if_true.
  zgo 0x30c170.
  rewrite (shr3_div f) by lia.
  zstep; lfix. zstep; lfix. zstep; lfix.
  zgo 0x30c1b8.
  rewrite (shr3_div PLN) by lia.
  zgo 0x30c1c4.
  repeat rewrite skipn_skipn in FB. repeat rewrite skipn_skipn in SB. cbn [Nat.add] in FB, SB.
  unfold j0_w1a_post, SITE_j0_c1, SITE_j0_sm, j0_hdr, j0_sh12, FF_MAGIC, FF_DESCR, SHB, TP_A. apply evt_done. do 2 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FB| exact SB].
Qed.
Local Ltac zsh := cbv beta; try change (bv_unsigned (Z_to_bv 8 0)) with 0; try change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0).
Definition SITE_j0_c1x : Z := 0x30c1d4.  (* [comment removed for export] *)
Definition SITE_j0_c2x : Z := 0x30c1e8.  (* [comment removed for export] *)
Definition SITE_j0_c3x : Z := 0x30c1fc.  (* [comment removed for export] *)
Definition SITE_j0_c4 : Z := 0x30c210.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma j0_w1b : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (x1 x2 x3 : word),
  0 <= sp1 -> sp1 + 368 <= 2 ^ 47 -> 0x10007fff8000 <= sp1 -> 0 < PLN -> PLN + 8 <= 2 ^ 47 -> PLN mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m (sp1 + 224) [C8 x1; C8 x2; C8 x3] -> ro_cells asegs m (PLN / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (-8)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c1x) fc None m' (seg_rom asegs)
      /\ munch [(sp1 + 240, sp1 + 248)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' (sp1 + 224) [C8 x1; C8 x2; C8 (wz f)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (PLN / 8)) (wz 4) pcw (wz (-8)) (wz (-14)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c1) fc None m (seg_rom asegs)).
Proof.
  intros until x3. intros SP0 SPH SPS L0 LH LAL MI FR RO. unfold SITE_j0_c1, SITE_j0_sm, TP_A, SHB in *.
  pose proof (munch_refl [(sp1 + 240, sp1 + 248)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts PLN) as Ql.
  assert (SHR : 0x7fff8000 <= PLN / 8 + 2147450880 /\ PLN / 8 + 2147450880 + 1 <= 0x10007fff8000) by (clear - Ql L0 LH; lia).
  assert (HWU : ut_fp [(sp1 + 240, sp1 + 248)]) by (clear - SPS SPH; unfold SEGTOP_A in *; ut_fp_lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; lia).
  zstep. zstep. zsh. zstep; lfix. zstep. if_false.
  unfold SITE_j0_c1x. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.
(* [comment removed for export] *)
Lemma j0_w1c : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (ol : word),
  0 < PLN -> PLN + 8 <= 2 ^ 47 -> (PLN + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PLN) -> 0 < PH -> PH + 8 <= 2 ^ 47 -> PH mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PLN [C8 ol] -> ro_cells asegs m (PH / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c2x) fc None m' (seg_rom asegs)
      /\ munch [(PLN, PLN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PLN [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (-8)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c1x) fc None m (seg_rom asegs)).
Proof.
  intros until ol. intros L0 LH LSH H0 HH HAL MI OUT RO. unfold SITE_j0_c1x, SITE_j0_sm, TP_A, SHB in *.
  pose proof (munch_refl [(PLN, PLN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts PLN) as Ql. pose proof (div8_facts PH) as Qh.
  assert (SHR : 0x7fff8000 <= PH / 8 + 2147450880 /\ PH / 8 + 2147450880 + 1 <= 0x10007fff8000) by (clear - Qh H0 HH; lia).
  assert (TST : PLN + 8 <= PH / 8 + 2147450880 \/ PH / 8 + 2147450880 + 1 <= PLN) by (clear - SHR LSH; lia).
  assert (EUl : bv_unsigned (Z_to_bv 64 PLN) = PLN) by (apply unsigned_lit; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  zstep; lfix. zstep. zstep. rewrite (shr3_div PH) by lia. zstep. zsh. zstep. if_false.
  unfold SITE_j0_c2x. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma j0_w1d : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (oh : word),
  0 < PH -> PH + 8 <= 2 ^ 47 -> (PH + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PH) -> 0 < PN -> PN + 8 <= 2 ^ 47 -> PN mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PH [C8 oh] -> ro_cells asegs m (PN / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c3x) fc None m' (seg_rom asegs)
      /\ munch [(PH, PH + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PH [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (-15)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c2x) fc None m (seg_rom asegs)).
Proof.
  intros until oh. intros H0 HH HSH N0 NH NAL MI OUT RO. unfold SITE_j0_c2x, SITE_j0_sm, TP_A, SHB in *.
  pose proof (munch_refl [(PH, PH + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts PH) as Qh. pose proof (div8_facts PN) as Qn.
  assert (SHR : 0x7fff8000 <= PN / 8 + 2147450880 /\ PN / 8 + 2147450880 + 1 <= 0x10007fff8000) by (clear - Qn N0 NH; lia).
  assert (TST : PH + 8 <= PN / 8 + 2147450880 \/ PN / 8 + 2147450880 + 1 <= PH) by (clear - SHR HSH; lia).
  assert (EUh : bv_unsigned (Z_to_bv 64 PH) = PH) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 PN) = PN) by (apply unsigned_lit; lia).
  zstep; lfix. zstep. zstep. rewrite (shr3_div PN) by lia. zstep. zsh. zstep. if_false.
  unfold SITE_j0_c3x. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma j0_w1e : forall sp1 gp t0 t1 t2 sp pcw a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (on : word),
  0 < PN -> PN + 8 <= 2 ^ 47 -> (PN + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= PN) -> 0 < PD -> PD + 8 <= 2 ^ 47 -> PD mod 8 = 0 -> mem_inv asegs m ->
  rw_cells asegs m PN [C8 on] -> ro_cells asegs m (PD / 8 + SHB) [C1 z8] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz SITE_j0_c4) fc None m' (seg_rom asegs)
      /\ munch [(PN, PN + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PN [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) pcw (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c3x) fc None m (seg_rom asegs)).
Proof.
  intros until on. intros N0 NH NSH D0 DH DAL MI OUT RO. unfold SITE_j0_c3x, SITE_j0_sm, TP_A, SHB in *.
  pose proof (munch_refl [(PN, PN + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (div8_facts PN) as Qn. pose proof (div8_facts PD) as Qd.
  assert (SHR : 0x7fff8000 <= PD / 8 + 2147450880 /\ PD / 8 + 2147450880 + 1 <= 0x10007fff8000) by (clear - Qd D0 DH; lia).
  assert (TST : PN + 8 <= PD / 8 + 2147450880 \/ PD / 8 + 2147450880 + 1 <= PN) by (clear - SHR NSH; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 PN) = PN) by (apply unsigned_lit; lia).
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  zstep; lfix. zstep. zstep. rewrite (shr3_div PD) by lia. zstep. zsh. zstep. if_false.
  unfold SITE_j0_c4. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
Lemma j0_w1f : forall sp1 gp t0 t1 t2 sp a6 a7 s7 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem) (f PN PH PD PLN fl : Z) (od : word),
  0 < PD -> PD + 8 <= 2 ^ 47 -> 0 <= fl < 256 -> mem_inv asegs m -> rw_cells asegs m PD [C8 od] ->
  evt asegs (fun ms => exists m',
      ms = MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz (Z.land fl 6)) (wz 6) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
                   (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
              F (wz (if Z.land fl 6 =? 6 then J_RAISE0 else J_J0N)) fc None m' (seg_rom asegs)
      /\ munch [(PD, PD + 8)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ rw_cells asegs m' PD [C8 (wz 0)])
    (MS (mkR (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 0) (wz 4) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PLN / 8 + SHB)) (wz (PN / 8 + SHB)) a6 a7
             (wz f) (wz PLN) (wz fl) (wz PN) (wz f) s7 (wz (f / 8 + SHB)) (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6)
        F (wz SITE_j0_c4) fc None m (seg_rom asegs)).
Proof.
  intros until od. intros D0 DH FL MI OUT. unfold SITE_j0_c4, SITE_j0_sm, TP_A, SHB in *.
  pose proof (munch_refl [(PD, PD + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EUd : bv_unsigned (Z_to_bv 64 PD) = PD) by (apply unsigned_lit; lia).
  assert (EUfl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  pose proof (land_lt_pow2 fl 6 8 ltac:(lia) ltac:(lia)) as AND6. change (2 ^ 8) with 256 in AND6.
  zstep. zstep. zstep; lfix. zstep. if_cases K; zify_cond K.
  - rewrite ?unsigned_lit in K by lia. replace (Z.land fl 6 =? 6) with false by (symmetry; apply Z.eqb_neq; exact K).
    unfold J_J0N. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
  - rewrite ?unsigned_lit in K by lia. replace (Z.land fl 6 =? 6) with true by (symmetry; apply Z.eqb_eq; lia).
    unfold J_RAISE0. apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_le_to_Z_range' : forall bs : list byte, 0 <= bytes_le_to_Z bs < 256 ^ Z.of_nat (length bs).
Proof.
  intros bs. rewrite bytes_le_to_Z_le_val. pose proof (le_val_range (map bv_unsigned bs) (bytes_ok_map bs)) as H. rewrite length_map in H. exact H.
Qed.
Lemma le_bytes_roundtrip' : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2 ^ Z.of_N 8) with 256 in Hb.
  pose proof (bytes_le_to_Z_range' bs) as [Hr _].
  rewrite lor_shiftl8_add by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    rewrite Z.mul_comm, Z_div_plus_full by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l. exact IH.
Qed.
Lemma le8_of_junk' : forall bs : list byte, length bs = 8%nat -> cbytes (C8 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le8, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range' bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 8) with (2 ^ 64) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip'.
Qed.
Lemma le4_of_junk' : forall bs : list byte, length bs = 4%nat -> cbytes (C4 (le_bytes_to_word bs)) = bs.
Proof.
  intros bs L. cbn [cbytes]. unfold le4, word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  pose proof (bytes_le_to_Z_range' bs) as Hr. rewrite L in Hr. change (256 ^ Z.of_nat 4) with (2 ^ 32) in Hr.
  rewrite bv_wrap_small by (unfold bv_modulus; change (2 ^ Z.of_N 64) with (2 ^ 64); lia).
  rewrite <- L. apply le_bytes_roundtrip'.
Qed.
(* [comment removed for export] *)
Lemma junk_C8 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 8 bs :: post) -> rw_cells asegs m A (pre ++ C8 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [L _]]. cbn in L.
  apply (Fz_kit.rw_cells_recast m A _ _ H).
  - pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (le8_of_junk' bs L). reflexivity.
Qed.
Lemma junk_C4 : forall (m : mem) A pre post bs, rw_cells asegs m A (pre ++ CB 4 bs :: post) -> rw_cells asegs m A (pre ++ C4 (le_bytes_to_word bs) :: post).
Proof.
  intros m A pre post bs H. pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [_ [L _]]. cbn in L.
  apply (Fz_kit.rw_cells_recast m A _ _ H).
  - pose proof H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]]. apply cells_wf_app. split; [exact H1|]. split; [exact I| exact H3].
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (le4_of_junk' bs L). reflexivity.
Qed.

(* [comment removed for export] *)
Ltac zofnat H := repeat match type of H with context [Z.of_nat ?n] => let v := eval vm_compute in (Z.of_nat n) in change (Z.of_nat n) with v in H end.
Lemma j0_frame_split : forall (m : mem) sp1 j1 bi j2 gap,
  rw_cells asegs m sp1 (CB 216 j1 :: C8 bi :: CB 24 j2 :: gap) ->
  exists j0 jH jF endv jE x1 x2 x3,
       rw_cells asegs m sp1 [CB 24 j0] /\ rw_cells asegs m (sp1 + 24) [CB 56 jH] /\ rw_cells asegs m (sp1 + 80) [CB 24 jF]
    /\ rw_cells asegs m (sp1 + 104) [C8 endv] /\ rw_cells asegs m (sp1 + 112) [CB 104 jE] /\ rw_cells asegs m (sp1 + 216) [C8 bi]
    /\ rw_cells asegs m (sp1 + 224) [C8 x1; C8 x2; C8 x3] /\ rw_cells asegs m (sp1 + 248) gap.
Proof.
  intros m sp1 j1 bi j2 gap FR.
  pose proof (rw_cells_split_CB asegs m sp1 [] 216 j1 (C8 bi :: CB 24 j2 :: gap) [24; 56; 24; 8; 104]%nat FR eq_refl) as F1. cbn [mk_CB_cells app] in F1.
  lazymatch type of F1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: CB 8 ?b3 :: ?rest) =>
    pose proof (junk_C8 m sp1 [c0; c1; c2] rest b3 F1) as F2 end. cbn [app] in F2. clear F1.
  lazymatch type of F2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 24 ?jb :: ?rest) =>
    pose proof (rw_cells_split_CB asegs m sp1 [c0; c1; c2; c3; c4; c5] 24 jb rest [8; 8; 8]%nat F2 eq_refl) as F3 end. cbn [mk_CB_cells app] in F3. clear F2.
  lazymatch type of F3 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: CB 8 ?b6 :: ?rest) =>
    pose proof (junk_C8 m sp1 [c0; c1; c2; c3; c4; c5] rest b6 F3) as F4 end. cbn [app] in F4. clear F3.
  lazymatch type of F4 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: CB 8 ?b7 :: ?rest) =>
    pose proof (junk_C8 m sp1 [c0; c1; c2; c3; c4; c5; c6] rest b7 F4) as F5 end. cbn [app] in F5. clear F4.
  lazymatch type of F5 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: CB 8 ?b8 :: ?rest) =>
    pose proof (junk_C8 m sp1 [c0; c1; c2; c3; c4; c5; c6; c7] rest b8 F5) as F6 end. cbn [app] in F6. clear F5.
  lazymatch type of F6 with rw_cells _ _ _ (CB 24 ?a0 :: CB 56 ?a1 :: CB 24 ?a2 :: C8 ?a3 :: CB 104 ?a4 :: C8 _ :: C8 ?a6 :: C8 ?a7 :: C8 ?a8 :: _) =>
    exists a0, a1, a2, a3, a4, a6, a7, a8 end.
  lazymatch type of F6 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?rest) =>
    destruct (proj1 (rw_cells_app m sp1 [c0] (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest)) F6) as [G0 R0];
    destruct (proj1 (rw_cells_app m _ [c1] (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest)) R0) as [G1 R1];
    destruct (proj1 (rw_cells_app m _ [c2] (c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: rest)) R1) as [G2 R2];
    destruct (proj1 (rw_cells_app m _ [c3] (c4 :: c5 :: c6 :: c7 :: c8 :: rest)) R2) as [G3 R3];
    destruct (proj1 (rw_cells_app m _ [c4] (c5 :: c6 :: c7 :: c8 :: rest)) R3) as [G4 R4];
    destruct (proj1 (rw_cells_app m _ [c5] (c6 :: c7 :: c8 :: rest)) R4) as [G5 R5];
    destruct (proj1 (rw_cells_app m _ [c6; c7; c8] rest) R5) as [G6 R6] end.
  cbn [cells_size csize Nat.add] in G1, G2, G3, G4, G5, G6, R6. zofnat G1. zofnat G2. zofnat G3. zofnat G4. zofnat G5. zofnat G6. zofnat R6.
  replace (sp1 + 24 + 56) with (sp1 + 80) in G2 by lia. replace (sp1 + 24 + 56 + 24) with (sp1 + 104) in G3 by lia.
  replace (sp1 + 24 + 56 + 24 + 8) with (sp1 + 112) in G4 by lia.
  replace (sp1 + 24 + 56 + 24 + 8 + 104) with (sp1 + 216) in G5 by lia.
  replace (sp1 + 24 + 56 + 24 + 8 + 104 + 8) with (sp1 + 224) in G6 by lia. replace (sp1 + 24 + 56 + 24 + 8 + 104 + 8 + 24) with (sp1 + 248) in R6 by lia.
  exact (conj G0 (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 R6))))))).
Qed.

(* [comment removed for export] *)
Lemma j0_ff_split : forall (m : mem) f pcw r,
  rw_cells asegs m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR); C8 pcw; CB 96 r] ->
  exists hj lenv j1 tav j2 bmv j3, rw_cells asegs m f (ff_cells hj lenv j1 tav j2 bmv j3).
Proof.
  intros m f pcw r FB.
  destruct (proj1 (rw_cells_app m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR)] [C8 pcw; CB 96 r]) FB) as [H1 H2].
  pose proof (rw_cells_blur m _ [C8 pcw; CB 96 r] [] ltac:(rewrite app_nil_r; exact H2)) as H3. cbn [cells_size csize Nat.add cells_bytes app] in H3.
  lazymatch type of H3 with rw_cells _ _ ?a [CB _ ?bs] =>
    pose proof (rw_cells_split_CB asegs m a [] 104 bs [] [16; 4; 12; 4; 12; 8; 48]%nat H3 eq_refl) as H4 end. cbn [mk_CB_cells app] in H4. clear H3.
  lazymatch type of H4 with rw_cells _ _ ?a (?c0 :: CB 4 ?b1 :: ?rest) => pose proof (junk_C4 m a [c0] rest b1 H4) as H5 end. cbn [app] in H5. clear H4.
  lazymatch type of H5 with rw_cells _ _ ?a (?c0 :: ?c1 :: ?c2 :: CB 4 ?b3 :: ?rest) => pose proof (junk_C4 m a [c0; c1; c2] rest b3 H5) as H6 end. cbn [app] in H6. clear H5.
  lazymatch type of H6 with rw_cells _ _ ?a (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: CB 8 ?b5 :: ?rest) => pose proof (junk_C8 m a [c0; c1; c2; c3; c4] rest b5 H6) as H7 end. cbn [app] in H7. clear H6.
  lazymatch type of H7 with rw_cells _ _ _ [CB 16 ?a0; C4 ?a1; CB 12 ?a2; C4 ?a3; CB 12 ?a4; C8 ?a5; CB 48 ?a6] => exists a0, a1, a2, a3, a4, a5, a6 end.
  unfold ff_cells. lazymatch type of H7 with rw_cells _ _ _ ?l =>
    apply (proj2 (rw_cells_app m f [C8 (wz FF_MAGIC); C8 (wz FF_DESCR)] l)); split; [exact H1| exact H7] end.
Qed.

(* [comment removed for export] *)
Lemma mbio_rep_offnd : forall live (m : mem) K BI meth len max off,
  mbio_rep live m K BI meth len max off -> 0 <= off <= len /\ List.NoDup (mbio_blocks K).
Proof.
  intros live m K BI meth len max off (BM & fl & rrw & numw & padw & nr & nw & EBI & EBM & IBI & AL & ND & HM & HD & W1 & FL & TL & INR).
  destruct INR as (rmaxw & _ & _ & _ & _ & _ & _ & _ & OFF & _). split; [exact OFF| exact ND].
Qed.

Section CJ0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AFP : art_facts_pem RT GOBJ.
Variable libenv : mem -> list (Z * Z) -> Z -> Prop.
Variable libenv_fp : list (Z * Z) -> Z -> Prop.
Hypothesis libenv_agree : forall m m' LBL E, libenv m LBL E -> agree_on (libenv_fp LBL) m m' -> libenv m' LBL E.
Hypothesis libenv_fp_where : forall LBL a, libenv_fp LBL a -> (in_ranges LIB_W a /\ client_static a /\ ~ cl_cell a) \/ in_live LBL a.
Variable errst_at_rest : Z -> list (Z * Z) -> mem -> Prop.
Variable errst_live : Z -> Z -> Z -> list (Z * Z) -> mem -> Prop.
Variable errst_fp : Z -> list (Z * Z) -> Z -> Prop.
Hypothesis errst_rest_agree : forall m m' E strs, errst_at_rest E strs m -> agree_on (errst_fp E strs) m m' -> errst_at_rest E strs m'.
Hypothesis errst_fp_where : forall E strs a, errst_fp E strs a -> (E <= a < E + 904) \/ in_live strs a.
Variables FZ_SITES FZ_CALLS : list (Z * Z).
Hypothesis SM1 : stack_malloc_contract RT 1.
Hypothesis HCG : cg_sub PEM_SITES PEM_CALLS FZ_SITES FZ_CALLS.
Hypothesis H_R0 : RAISE0_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Hypothesis H_J0N : J0N_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.

Local Notation pem_entry := (pem_entry RT).
Local Notation pem_com := (pem_com RT libenv FZ_SITES FZ_CALLS).
Local Notation pem_ms := (pem_ms RT).

(* [comment removed for export] *)
Lemma out_loc_facts : forall Σ (m : mem) lo (frames0 : list (Z * nat)) (mm : mem) P,
  ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= lo -> (forall fk, In fk frames0 -> In fk (rt_frames RT Σ)) ->
  P mod 8 = 0 /\ pp_loc frames0 mm USTACK_TOP P ->
  exists f' k', In (f', k') frames0 /\ f' <= P /\ P + 8 <= f' + fs_size k' - 8 /\ bytes_at asegs mm (shad P) [z8]
    /\ 0 < P /\ P + 8 <= lo /\ (P + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= P) /\ P mod 8 = 0
    /\ (forall p n, In (p, n) (rt_live RT Σ) -> P + 8 <= p \/ p + n <= P).
Proof using AF.
  intros Σ m lo frames0 mm P ART0 LOW SUB [AL [[H1 H2]|(f' & k' & HF & F1 & F2 & B0)]]; [exfalso; clear - H1 H2; lia|].
  pose proof (af_frames_range RT AF Σ m f' k' ART0 (SUB _ HF)) as (X0 & X1 & X2 & X3). pose proof (af_frames_hi RT AF Σ m f' k' ART0 (SUB _ HF)) as Y.
  pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN.
  exists f', k'. split; [exact HF|]. split; [exact F1|]. split; [exact F2|]. split; [exact B0|].
  split; [clear - X0 F1; lia|]. split; [clear - X1 F2 LOW KN; unfold fs_size in *; lia|]. split; [clear - Y F1 F2 KN; unfold fs_size in *; lia|]. split; [exact AL|].
  intros p n Hin. destruct (X3 p n Hin) as [Q|Q]; clear - Q F1 F2 KN; unfold fs_size in *; lia.
Qed.

Theorem J0_proof : pem_read_bio_stmt RT libenv errst_at_rest errst_live FZ_SITES FZ_CALLS.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer canary LBL K E BI meth blen bmax boff PN PH PD PL flags
         on oh od ol.
  intros FDO MST -> -> -> -> -> -> -> FLR LE INCL INE NLE NTL ER0 MB BLEN NDO OUTS ON OH OD OL ART0 MI0 CALL HSTK CLE SEC CTX UWC CGH FRN LIV CRE LPOS.
  intros T c HA Hk.
  pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  set (usp := bv_unsigned sp) in *. set (pad := usp mod 32).
  assert (HP : pad = 0 \/ pad = 16) by (unfold pad; clear - SPA; Z.div_mod_to_equations; lia).
  assert (HPM : usp mod 32 = pad) by reflexivity. clearbody pad.
  set (sp1 := usp - 352 - pad).
  unfold PEMR_STACK, PEM_CALLEE_STACK in HSTK.
  assert (NUM : 0x10007fff8000 <= lo /\ usp <= 2 ^ 47 /\ lo <= usp - 1136 /\ rt_sp0 RT Σ - STACK_WIN <= sp1 /\ SEGTOP_A <= lo /\ 0 <= sp1 /\ sp1 + 368 <= 2 ^ 47)
    by (unfold sp1, RT_STACK, STACK_WIN, USTACK_TOP, SEGTOP_A in *; clear - SP0W SP0R LOW LOR SPT HSTK HP; lia).
  destruct NUM as (HLOS & SPH & HLO & LOW1 & HLOI & SP0' & SPH1).
  assert (EU1 : bv_unsigned (wz sp1) = sp1) by (apply unsigned_lit; clear - SP0' SPH1; lia).
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  pose proof (mbio_rep_offnd _ _ _ _ _ _ _ _ MB) as [OFF NDK].
  assert (CR1 : 1 <= rt_credit RT Σ) by (unfold pem_credit in CRE; clear - CRE OFF; lia).
  assert (FRL : (length (rt_frames RT Σ) < FRAMES_MAX)%nat) by (clear - FRN; lia).
  (* [comment removed for export] *)
  assert (OUTF : forall P, In P [PN; PH; PD; PL] ->
    exists f' k', In (f', k') (rt_frames RT Σ) /\ f' <= P /\ P + 8 <= f' + fs_size k' - 8 /\ bytes_at asegs m (shad P) [z8]
      /\ 0 < P /\ P + 8 <= lo /\ (P + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= P) /\ P mod 8 = 0
      /\ (forall p n, In (p, n) (rt_live RT Σ) -> P + 8 <= p \/ p + n <= P)).
  { intros P HPP. exact (out_loc_facts Σ m lo (rt_frames RT Σ) m P ART0 LOW ltac:(intros fk X; exact X) (proj1 (Forall_forall _ _) OUTS P HPP)). }
  destruct (OUTF PL ltac:(cbn; tauto)) as (fL & kL & FkL & FL1 & FL2 & BL & L0 & LLO & LSH & L8 & LLV).
  destruct (OUTF PH ltac:(cbn; tauto)) as (fH & kH & FkH & FH1 & FH2 & BH & H0 & HHLO & HSH & H8 & HLV).
  destruct (OUTF PN ltac:(cbn; tauto)) as (fN & kN & FkN & FN1 & FN2 & BN & N0 & NLO & NSH & N8 & NLV).
  destruct (OUTF PD ltac:(cbn; tauto)) as (fD & kD & FkD & FD1 & FD2 & BD & D0 & DLO & DSH & D8 & DLV).
  (* [comment removed for export] *)
  pose proof (j0_w0 ra sp gp t0 t1 t2 s0 s1 BI PN PH PD PL flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pad
                HP HPM ST HLO HLOS SPH UT SHC UAR MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (a1' & a2' & j1 & j2 & g & m1 & -> & MU1 & WM1 & MI1 & FR1 & SAV1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, FR1, SAV1, ST1, Hc1'. fold sp1 in MU1, FR1, ST1, Hc1'.
  (* [comment removed for export] *)
  assert (MU1' : munch ([] ++ [(usp - (352 + pad), usp)]) m m1) by (cbn [app]; replace (usp - (352 + pad)) with sp1 by (unfold sp1; clear; lia); exact MU1).
  pose proof (cl_seg_ART RT AF Σ m m1 usp (352 + pad) [] ART0 ltac:(clear - LOW1; unfold sp1 in LOW1; lia) ltac:(clear - SPT; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp (352 + pad) [] ART0 ltac:(clear - LOW1; unfold sp1 in LOW1; lia) ltac:(clear - HP; lia) MU1') as PR1. clear MU1'.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  pose proof (cl_env_seg _ m m1 _ canary CLE MU1 ltac:(cl_fp_lia)) as ENV1.
  pose proof (uw_chain_agree outer m m1 sp s0 UWC AG1) as UWF1.
  assert (COK1 : call_ok RT Σ m1 (wz sp1) lo).
  { unfold call_ok. rewrite EU1. split; [exact ST1|]. split; [exact LOW|]. split; [clear - HSTK HP; unfold sp1, RT_STACK in *; lia|].
    split; [clear - SPT HP; unfold sp1 in *; lia|]. clear - SPA HP. unfold sp1. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  apply (SM1 Σ PMc (wz SITE_j0_sm) (wz sp1) gp (wz TP_A) t0 t1 t2 sp (wz sp1) (wz 96) a1' a2' (wz PD) (wz PL) (wz flags) a6 a7
           s2 (wz PL) (wz flags) (wz PN) s6 s7 s8 (wz SHB) (wz PD) (wz PH) t3 t4 t5 t6 F fc m1 lo FDO MST ltac:(right; left; reflexivity) eq_refl FRL CR1 ART1 MI1
           COK1 _ _ Hc1').
  clear Hc1'. intros c2 (Σ1 & f & Hc2 & FRS1 & LV1 & SP1 & CR2 & F0 & F64 & FU & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & WF2 & WS2) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_j0_sm) in Hc2' by (unfold SITE_j0_sm; clear; lia).
  assert (INF : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FLO & _ & FLV).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 INF) as (_ & FSEG).
  pose proof (af_frames_hi RT AF Σ1 m2 f 1%nat ART2 INF) as FSH0.
  pose proof (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 INF) as [FSA1 FSA2].
  rewrite SP1 in FLO. rewrite LV1 in FLV, FSA1. change (fs_size 1) with 128 in FLO, FSH0, FU, WF2, WS2, FLV, FSA1, FSA2. change (128 - 8) with 120 in WF2. change (128 / 8) with 16 in WS2.
  assert (FSH : f + 128 <= 0x7fff8000 \/ 0x10007fff8000 <= f) by (clear - FSH0; lia).
  assert (FTOP : f + 128 < USTACK_TOP) by exact FU.
  assert (FH : f + 128 <= 2 ^ 47) by (clear - FU; unfold USTACK_TOP in FU; lia).
  assert (SHF : shad (f + 128) = shad f + 16) by (unfold shad; clear - F64; Z.div_mod_to_equations; lia).
  pose proof (div8_facts f) as Qf.
  assert (SHR : 0x7fff8000 <= shad f /\ shad f + 16 <= 0x10007fff8000) by (unfold shad, SHB; clear - Qf F0 FH; lia).
  (* [comment removed for export] *)
  assert (AG2 : forall a k, sp1 <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m1 m2).
  { intros a k H1 H2 x Hx. cbv beta in Hx. apply PRES2. left. clear - H1 H2 Hx. lia. }
  cl_keep FR1 AG2 WM2 FR2. unfold j0_saved in SAV1. cl_keep SAV1 AG2 WM2 SAV2.
  destruct (wr_at_rw_CB m2 f 120 WF2 ltac:(clear; lia)) as (fj & FB2). destruct (wr_at_rw_CB m2 (shad f) 16 WS2 ltac:(clear; lia)) as (sj & SB2).
  change (Z.to_nat 120) with 120%nat in FB2. change (Z.to_nat 16) with 16%nat in SB2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & _ & _ & _ & UT2).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct (j0_frame_split m2 sp1 j1 (wz BI) j2 [CB (Z.to_nat pad) g] FR2) as (j0b & jH & jF & endv & jE & x1 & x2 & x3 & FR0_2 & FRH_2 & FRF_2 & FR104_2 & FRE_2 & FBI_2 & FR224_2 & FRG_2).
  assert (SP1S : 0x10007fff8000 <= sp1) by (clear - HLOS HSTK HP; unfold sp1, RT_STACK in *; lia).
  assert (FSP : f + 128 <= sp1) by (clear - FLO LOW HLO HP; unfold sp1, STACK_WIN in *; lia).
  pose proof (j0_w1a sp1 gp u0 u1 u2 sp b1 b2 b3 b4 b5 b6 b7 s2 s6 s7 s8 u3 u4 u5 u6 F2 fc2 m2 f PN PH PD PL flags fj sj
                F0 FH ltac:(right; exact FSEG) FSH SP0' SPH1 SP1S FSP L0 ltac:(clear - LLO HLO SPH; lia) UT2 FB2 SB2 MI2) as W1.
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (pcw & m3 & -> & MU3 & WM3 & MI3 & FB3 & SB3) & Hc3'). clear Hc3 Hc2'.
  (* [comment removed for export] *)
  assert (AG03 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m3 a = m a).
  { intros a Ha. transitivity (m2 a); [| transitivity (m1 a); [apply PRES2; destruct Ha as [S|R]; [left; clear - S HP; unfold sp1; lia| right; exact R] | apply PR1; [exact Ha| exact I]]].
    apply MU3. cbn [outside fst snd]. unfold shad, SHB in *.
    destruct Ha as [S|[CS|[(p & n & Hin & Hp)|[(f' & k' & Hin & Hf')|(f' & k' & Hin & Hf')]]]]; (split; [| split; [| exact I]]); unfold shad, SHB in *.
    - clear - S FLO LOW HLO. unfold USTACK_TOP, STACK_WIN in *. lia.
    - clear - S SHR HLOS LOW HLO. unfold USTACK_TOP, STACK_WIN in *. lia.
    - pose proof (client_static_range _ CS) as R. clear - R FSEG. unfold SEGTOP_A in *. lia.
    - pose proof (client_static_range _ CS) as R. clear - R SHR. unfold SEGTOP_A in *. lia.
    - pose proof (FLV p n Hin) as R1. clear - R1 Hp. lia.
    - pose proof (FSA1 p n Hin) as R2. clear - R2 Hp SHF. lia.
    - pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat f' k' [] (rt_frames RT Σ) ART2 FRS1 Hin) as R1.
      change (fs_size 1) with 128 in R1. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN. clear - R1 Hf' KN. unfold fs_size in *. lia.
    - assert (Hin' : In (f', k') (rt_frames RT Σ1)) by (rewrite FRS1; right; exact Hin).
      pose proof (FSA2 f' k' Hin') as R2. pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN. clear - R2 Hf' SHF KN. unfold fs_size in *. lia.
    - assert (Hin' : In (f', k') (rt_frames RT Σ1)) by (rewrite FRS1; right; exact Hin).
      pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f' k' ART2 Hin') f 1%nat INF) as R2. change (fs_size 1) with 128 in R2. unfold shad, SHB in R2.
      pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN. clear - R2 Hf' KN. unfold fs_size in *. lia.
    - assert (Hin' : In (f', k') (rt_frames RT Σ1)) by (rewrite FRS1; right; exact Hin).
      pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat f' k' [] (rt_frames RT Σ) ART2 FRS1 Hin) as R1. change (fs_size 1) with 128 in R1.
      pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN.
      assert (MN : f + 128 <= f' -> (f + 128) / 8 <= f' / 8) by (intros X; apply Z.div_le_mono; clear - X; lia).
      assert (MN' : f' + fs_size k' <= f -> (f' + fs_size k') / 8 <= f / 8) by (intros X; apply Z.div_le_mono; clear - X; lia).
      clear - R1 Hf' SHF KN MN MN' Qf. unfold fs_size in *. lia. }
  assert (AGQ : forall Q : Z -> Prop, (forall x, Q x -> aclient (rt_live RT Σ) (rt_frames RT Σ) usp x) -> agree_on Q m m3) by (intros Q HQ a Ha; exact (AG03 a (HQ _ Ha))).
  pose proof (wmono_trans asegs _ _ _ WM1 (wmono_trans asegs _ _ _ WM2 WM3)) as WM03.
  assert (PRES3 : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp
            ([(PN, PN + 8); (PH, PH + 8); (PD, PD + 8); (PL, PL + 8); (E, E + 904)] ++ mbio_W K bmax ++ lib_W LBL) m m3) by (intros a Ha _; exact (AG03 a Ha)).
  assert (LE3 : libenv m3 LBL E).
  { eapply libenv_agree; [exact LE|]. apply AGQ. intros x Hx. destruct (libenv_fp_where _ _ Hx) as [(_ & CS & _)|(p & n & Hin & Hp)]; [apply acl_static; exact CS| eapply acl_live; [exact (INCL _ Hin)| exact Hp]]. }
  assert (MB3 : mbio_rep (rt_live RT Σ1) m3 K BI meth blen bmax boff).
  { rewrite LV1. eapply mbio_rep_agree; [exact MB|]. apply AGQ. intros x ([p n] & He & Hx). eapply acl_live; [exact (mbio_rep_ents _ _ _ _ _ _ _ _ _ MB He)| exact Hx]. }
  assert (ER3 : errst_at_rest E [] m3).
  { eapply errst_rest_agree; [exact ER0|]. apply AGQ. intros x Hx. destruct (errst_fp_where _ _ _ Hx) as [HE|(p & n & Hin & _)]; [eapply acl_live; [exact INE| cbn [fst snd]; exact HE]| destruct Hin]. }
  pose proof (cl_env_pres _ _ _ m1 m2 _ canary ENV1 PRES2) as ENV2.
  assert (CFP3 : cl_fp [(f, f + 24); (f / 8 + SHB, f / 8 + SHB + 12)]).
  { intros x Hx. pose proof (client_static_range x (cl_cell_static x Hx)) as R. cbn [outside fst snd]. unfold SHB, SEGTOP_A, shad in *. refine (conj _ (conj _ I)); clear - R FSEG SHR; lia. }
  pose proof (cl_env_seg _ m2 m3 _ canary ENV2 MU3 CFP3) as ENV3.
  assert (SEC3 : sec_off m3).
  { eapply sec_off_agree; [exact SEC|]. intros a Ea. apply AG03. apply acl_static. apply client_static_intro. rewrite Ea. unfold SEC_INIT. clear; lia. }
  pose proof (uw_chain_agree outer m m3 sp s0 UWC ltac:(apply AGQ; intros x Hx; apply acl_stack; exact Hx)) as UWC3.
  assert (AG23s : forall a k, lo <= a -> a + k <= USTACK_TOP -> agree_on (fun x => a <= x < a + k) m2 m3).
  { intros a k H1 H2. apply (agree_of_munch _ m2 m3 _ MU3). intros x Hx. cbv beta in Hx. cbn [outside fst snd]. unfold shad in SHR. clear - Hx H1 H2 FLO LOW SHR HLOS. unfold USTACK_TOP, STACK_WIN in *. lia. }
  assert (SAV3 : rw_cells asegs m3 (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    by (eapply rw_cells_agree; [exact SAV2| apply AG23s; [clear - HLO; lia| cbn [cells_size csize Nat.add]; clear - SPT; lia]| exact WM3]).
  Local Ltac keep23 AG WM X X' := lazymatch type of X with rw_cells _ _ ?a ?cs => lazymatch type of WM with wmono _ _ ?mm3 =>
    assert (X' : rw_cells asegs mm3 a cs); [eapply rw_cells_agree; [exact X| apply AG; cbn [cells_size csize Nat.add] | exact WM] |] end end.
  keep23 AG23s WM3 FR0_2 FR0. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FRH_2 FRH. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FRF_2 FRF. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FR104_2 FR104. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FRE_2 FRE. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FBI_2 FBI. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FR224_2 FR224. 1-2: (clear - HLO HP SPT; unfold sp1 in *; lia).
  keep23 AG23s WM3 FRG_2 FRG. 1-2: (clear - HLO HP SPT; unfold sp1 in *; destruct HP as [-> | ->]; cbn; lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (af_frame RT AF Σ1 m2 m3 sp1 ART2 ltac:(rewrite SP1; exact LOW1)); [| exact WM3].
    intros a Ha. apply MU3. cbn [outside fst snd]. split; [| split; [| exact I]]; intros Hin; apply Ha.
    - apply (acl_frame _ _ _ f 1%nat); [exact INF | change (fs_size 1) with 128; clear - Hin; lia].
    - apply (acl_fshadow _ _ _ f 1%nat); [exact INF | rewrite SHF; unfold shad; clear - Hin; lia]. }
  assert (ST3 : stk asegs m3 lo sp1).
  { apply (stk_munch _ m2 m3 lo sp1 ST2 MU3 WM3). intros x Hx. cbn [outside fst snd]. unfold shad in SHR. refine (conj _ (conj _ I)); clear - Hx FLO LOW HLOS SHR; unfold STACK_WIN, SHB in *; lia. }
  (* [comment removed for export] *)
  assert (OC3 : forall P v f' k', In (f', k') (rt_frames RT Σ) -> f' <= P -> P + 8 <= f' + fs_size k' - 8 -> rw_cells asegs m P [C8 v] -> rw_cells asegs m3 P [C8 v]).
  { intros P v f' k' HF F1 F2' C. eapply rw_cells_agree; [exact C| | exact WM03]. apply AGQ. intros x Hx. cbv beta in Hx. cbn [cells_size csize Nat.add] in Hx.
    eapply acl_frame; [exact HF| clear - Hx F1 F2'; lia]. }
  pose proof (OC3 PN on fN kN FkN FN1 FN2 ON) as ON3. pose proof (OC3 PH oh fH kH FkH FH1 FH2 OH) as OH3.
  pose proof (OC3 PD od fD kD FkD FD1 FD2 OD) as OD3. pose proof (OC3 PL ol fL kL FkL FL1 FL2 OL) as OL3. clear OC3.
  assert (SHIN : forall f' k' P, f' <= P -> P + 8 <= f' + fs_size k' - 8 -> shad f' <= shad P /\ shad P + 1 <= shad (f' + fs_size k')).
  { intros f' k' P F1 F2'. unfold shad. pose proof (Z.div_le_mono f' P 8 ltac:(clear; lia) F1) as DM1. pose proof (Z.div_le_mono (P + 8) (f' + fs_size k' - 8) 8 ltac:(clear; lia) F2') as DM2.
    clear - DM1 DM2. Z.div_mod_to_equations. lia. }
  assert (RO3 : forall P f' k', In (f', k') (rt_frames RT Σ) -> f' <= P -> P + 8 <= f' + fs_size k' - 8 -> bytes_at asegs m (shad P) [z8] -> ro_cells asegs m3 (P / 8 + SHB) [C1 z8]).
  { intros P f' k' HF F1 F2' B0. destruct (SHIN f' k' P F1 F2') as [S1 S2].
    assert (B : bytes_at asegs m3 (shad P) [z8]).
    { apply (bytes_at_agree asegs m m3 _ _ B0). intros a Ha. cbn [length] in Ha. apply AG03. eapply acl_fshadow; [exact HF| clear - Ha S1 S2; lia]. }
    unfold ro_cells, cells_at. cbn [cells_wf cells_bytes cbytes]. rewrite app_nil_r. unfold shad in B. split; [split; [reflexivity | exact I] | exact B]. }
  pose proof (RO3 PN fN kN FkN FN1 FN2 BN) as RON3. pose proof (RO3 PH fH kH FkH FH1 FH2 BH) as ROH3.
  pose proof (RO3 PD fD kD FkD FD1 FD2 BD) as ROD3. pose proof (RO3 PL fL kL FkL FL1 FL2 BL) as ROL3. clear RO3.
  (* [comment removed for export] *)
  set (en := PEMENT RT ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ PMc m lo outer canary LBL E K BI meth blen bmax boff flags PN PH PD PL on oh od ol pad f (skipn 12 sj)).
  set (CREM := pem_credit (blen - boff) - 1).
  assert (COM3 : pem_com en Σ1 m3 boff CREM 21 []).
  { unfold pem_com. unfold e_PL, e_sp1, e_plen, e_live, e_frames, pem_saved, pem_W, e_PL. unfold en.
    cbn [e_ra e_sp e_gp e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_Σ e_PMc e_m e_lo e_outer e_canary e_LBL e_E e_K e_BI e_meth e_blen e_bmax e_boff e_flags
         e_PN e_PH e_PD e_PLN e_on e_oh e_od e_ol e_pd e_f e_fsj]. fold usp. fold sp1.
    split; [exact ART3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exact HP|]. split; [exact HPM|]. split; [exact SPT|].
    split; [rewrite SP1; exact LOW|]. split; [clear - HSTK HP; unfold sp1, PEM_CALLEE_STACK; lia|]. split; [exact HLOS|].
    split; [exact ENV3|]. split; [exact SEC3|]. split; [exact LE3|]. split; [exact INCL|]. split; [exact INE|]. split; [exact NLE|].
    split; [intros e He; rewrite app_nil_r; exact (NTL e He)|].
    split; [exact MB3|]. split; [clear - OFF; lia|]. split; [clear - OFF BLEN; lia|].
    split; [intros e He; exact (mbio_rep_ents _ _ _ _ _ _ _ _ _ MB He)|].
    split; [rewrite LV1; apply Permutation_refl|]. split; [intros e [] |].
    split; [cbn [map app]; constructor; [exact (NTL (E, 904) (or_introl eq_refl))| exact NDK]|].
    split; [rewrite LV1; exact LPOS|].
    split; [exact FRS1|]. split; [exact FRN|]. split; [exact SP1|]. split; [exact CG1|].
    split; [rewrite LV1; exact LIV|]. split; [clear; lia|].
    split; [rewrite CR2; unfold CREM; clear; lia|]. split; [unfold CREM, pem_credit; clear - OFF; lia|]. split; [exact CRE|].
    split; [rewrite CG1; exact CGH|]. split; [exact HCG|]. split; [rewrite CG1; exact CTX|]. split; [exact UWC3|].
    split; [exact F0|]. split; [exact F64|]. split; [exact FTOP|]. split; [exact FSEG|]. split; [exact FSH|].
    split; [unfold ff_shadow; unfold j0_sh12 in SB3; cbn [app] in SB3; exact SB3|].
    split; [exact SAV3|]. split; [exact PRES3|]. split; [exact FLR|]. split; [exact NDO|]. split; [exact OUTS|]. split; [exact FDO| exact MST]. }
  (* [comment removed for export] *)
  unfold j0_hdr in FB3. cbn [app] in FB3. destruct (j0_ff_split m3 f pcw (skipn 24 fj) FB3) as (hj & lenv & jj1 & tav & jj2 & bmv & jj3 & FFC3).
  (* [comment removed for export] *)
  assert (DIS : PN <> PH /\ PN <> PD /\ PN <> PL /\ PH <> PD /\ PH <> PL /\ PD <> PL).
  { pose proof NDO as ND0. apply NoDup_cons_iff in ND0. destruct ND0 as [N1 ND1]. apply NoDup_cons_iff in ND1. destruct ND1 as [N2 ND2]. apply NoDup_cons_iff in ND2. destruct ND2 as [N3 _].
    cbn in N1, N2, N3. split; [intros X; apply N1; rewrite X; left; reflexivity|]. split; [intros X; apply N1; rewrite X; right; left; reflexivity|].
    split; [intros X; apply N1; rewrite X; right; right; left; reflexivity|]. split; [intros X; apply N2; rewrite X; left; reflexivity|].
    split; [intros X; apply N2; rewrite X; right; left; reflexivity|]. intros X; apply N3; rewrite X; left; reflexivity. }
  assert (APART : forall P Q, P <> Q -> P mod 8 = 0 -> Q mod 8 = 0 -> P + 8 <= Q \/ Q + 8 <= P) by (intros P Q NE A B; clear - NE A B; Z.div_mod_to_equations; lia).
  destruct DIS as (D1 & D2 & D3 & D4 & D5 & D6).
  pose proof (APART _ _ D1 N8 H8) as ANH. pose proof (APART _ _ D2 N8 D8) as AND. pose proof (APART _ _ D3 N8 L8) as ANL.
  pose proof (APART _ _ D4 H8 D8) as AHD. pose proof (APART _ _ D5 H8 L8) as AHL. pose proof (APART _ _ D6 D8 L8) as ADL. clear APART D1 D2 D3 D4 D5 D6.
  assert (OUTFR : forall P f' k', In (f', k') (rt_frames RT Σ) -> f' <= P -> P + 8 <= f' + fs_size k' - 8 -> P + 8 <= f \/ f + 128 <= P).
  { intros P f' k' HF F1 F2'. pose proof (af_frames_disj RT AF Σ1 m2 f 1%nat f' k' [] (rt_frames RT Σ) ART2 FRS1 HF) as R1. change (fs_size 1) with 128 in R1.
    pose proof (Z.shiftl_nonneg 64 (Z.of_nat k')) as KN. clear - R1 F1 F2' KN. unfold fs_size in *. lia. }
  pose proof (OUTFR PN fN kN FkN FN1 FN2) as NFF. pose proof (OUTFR PH fH kH FkH FH1 FH2) as HFF. pose proof (OUTFR PD fD kD FkD FD1 FD2) as DFF. pose proof (OUTFR PL fL kL FkL FL1 FL2) as LFF. clear OUTFR.
  pose proof (div8_facts PL) as QL. pose proof (div8_facts PH) as QH. pose proof (div8_facts PN) as QN. pose proof (div8_facts PD) as QD.
  (* [comment removed for export] *)
  pose proof (j0_w1b sp1 gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m3 f PN PH PD PL flags x1 x2 x3 SP0' SPH1 SP1S L0 ltac:(clear - LLO HLO SPH; lia) L8 MI3 FR224 ROL3) as W2.
  cl_lift W2 Hc3' c4 Hc4. destruct (ASTA_unpack RT Σ1 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & FR224') & Hc4'). clear Hc4 Hc3'.
  assert (ST4 : stk asegs m4 lo sp1) by (apply (stk_munch _ m3 m4 lo sp1 ST3 MU4 WM4); intros x Hx; cbn [outside fst snd]; refine (conj _ I); clear - Hx; lia).
  assert (COM4 : pem_com en Σ1 m4 boff CREM 21 []).
  { eapply (com_seg RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m3 m4); [exact COM3| exact MU4| exact WM4| exact MI4| exact ST4|].
    apply Forall_cons; [| apply Forall_nil]. left. unfold e_sp1, e_PL, en. cbn [e_sp e_pd fst snd]. fold usp. clear - HP; unfold sp1; lia. }
  Local Ltac keep8 X MU X' := lazymatch type of X with rw_cells _ ?mm ?a ?cs => lazymatch type of MU with munch _ mm ?mm' =>
    assert (X' : rw_cells asegs mm' a cs); [eapply rw_cells_agree_nw; [exact X| apply (agree_of_munch _ _ _ _ MU); intros xq Hxq; cbv beta in Hxq; cbn [cells_size csize Nat.add outside fst snd] in *; refine (conj _ I)] |] end end.
  Local Ltac keepro X MU X' := lazymatch type of X with ro_cells _ ?mm ?a ?cs => lazymatch type of MU with munch _ mm ?mm' =>
    assert (X' : ro_cells asegs mm' a cs); [eapply ro_cells_agree; [exact X| apply (agree_of_munch _ _ _ _ MU); intros xq Hxq; cbv beta in Hxq; cbn [cells_size csize Nat.add outside fst snd] in *; refine (conj _ I)] |] end end.
  keep8 OL3 MU4 OL4. { clear - Hxq LLO HLO HP. unfold sp1. lia. }
  keepro ROH3 MU4 ROH4. { clear - Hxq SP1S QH H0 HHLO HLOS HLO SPH. unfold SHB in *. lia. }
  (* [comment removed for export] *)
  pose proof (j0_w1c sp1 gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m4 f PN PH PD PL flags ol L0 ltac:(clear - LLO HLO SPH; lia) ltac:(clear - LSH; lia) H0 ltac:(clear - HHLO HLO SPH; lia) H8 MI4 OL4 ROH4) as W3.
  cl_lift W3 Hc4' c5 Hc5. destruct (ASTA_unpack RT Σ1 _ _ c5 Hc5) as (ms5 & (m5 & -> & MU5 & WM5 & MI5 & OL5) & Hc5'). clear Hc5 Hc4'.
  assert (ST5 : stk asegs m5 lo sp1) by (apply (stk_munch _ m4 m5 lo sp1 ST4 MU5 WM5); intros x Hx; cbn [outside fst snd]; refine (conj _ I); clear - Hx LLO; lia).
  assert (COM5 : pem_com en Σ1 m5 boff CREM 21 []).
  { eapply (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m4 m5 boff CREM 21 [] PL fL kL);
      [exact COM4| right; right; right; left; reflexivity| exact FkL| exact FL1| exact FL2| exact MU5| exact WM5| exact MI5| exact ST5]. }
  keep8 OH3 MU4 OH4. { clear - Hxq HHLO HLO HP. unfold sp1. lia. } keep8 OH4 MU5 OH5. { clear - Hxq AHL. lia. }
  keepro RON3 MU4 RON4. { clear - Hxq SP1S QN N0 NLO HLOS HLO SPH. unfold SHB in *. lia. } keepro RON4 MU5 RON5. { clear - Hxq QN N0 NLO HLOS LSH HLO SPH. unfold SHB in *. lia. }
  (* [comment removed for export] *)
  pose proof (j0_w1d sp1 gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m5 f PN PH PD PL flags oh H0 ltac:(clear - HHLO HLO SPH; lia) ltac:(clear - HSH; lia) N0 ltac:(clear - NLO HLO SPH; lia) N8 MI5 OH5 RON5) as W4.
  cl_lift W4 Hc5' c6 Hc6. destruct (ASTA_unpack RT Σ1 _ _ c6 Hc6) as (ms6 & (m6 & -> & MU6 & WM6 & MI6 & OH6) & Hc6'). clear Hc6 Hc5'.
  assert (ST6 : stk asegs m6 lo sp1) by (apply (stk_munch _ m5 m6 lo sp1 ST5 MU6 WM6); intros x Hx; cbn [outside fst snd]; refine (conj _ I); clear - Hx HHLO; lia).
  assert (COM6 : pem_com en Σ1 m6 boff CREM 21 []).
  { eapply (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m5 m6 boff CREM 21 [] PH fH kH);
      [exact COM5| right; left; reflexivity| exact FkH| exact FH1| exact FH2| exact MU6| exact WM6| exact MI6| exact ST6]. }
  keep8 ON3 MU4 ON4. { clear - Hxq NLO HLO HP. unfold sp1. lia. } keep8 ON4 MU5 ON5. { clear - Hxq ANL. lia. } keep8 ON5 MU6 ON6. { clear - Hxq ANH. lia. }
  keepro ROD3 MU4 ROD4. { clear - Hxq SP1S QD D0 DLO HLOS HLO SPH. unfold SHB in *. lia. } keepro ROD4 MU5 ROD5. { clear - Hxq QD D0 DLO HLOS LSH HLO SPH. unfold SHB in *. lia. }
  keepro ROD5 MU6 ROD6. { clear - Hxq QD D0 DLO HLOS HSH HLO SPH. unfold SHB in *. lia. }
  (* [comment removed for export] *)
  pose proof (j0_w1e sp1 gp u0 u1 u2 sp pcw b6 b7 s7 u3 u4 u5 u6 F2 fc2 m6 f PN PH PD PL flags on N0 ltac:(clear - NLO HLO SPH; lia) ltac:(clear - NSH; lia) D0 ltac:(clear - DLO HLO SPH; lia) D8 MI6 ON6 ROD6) as W5.
  cl_lift W5 Hc6' c7 Hc7. destruct (ASTA_unpack RT Σ1 _ _ c7 Hc7) as (ms7 & (m7 & -> & MU7 & WM7 & MI7 & ON7) & Hc7'). clear Hc7 Hc6'.
  assert (ST7 : stk asegs m7 lo sp1) by (apply (stk_munch _ m6 m7 lo sp1 ST6 MU7 WM7); intros x Hx; cbn [outside fst snd]; refine (conj _ I); clear - Hx NLO; lia).
  assert (COM7 : pem_com en Σ1 m7 boff CREM 21 []).
  { eapply (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m6 m7 boff CREM 21 [] PN fN kN);
      [exact COM6| left; reflexivity| exact FkN| exact FN1| exact FN2| exact MU7| exact WM7| exact MI7| exact ST7]. }
  keep8 OD3 MU4 OD4. { clear - Hxq DLO HLO HP. unfold sp1. lia. } keep8 OD4 MU5 OD5. { clear - Hxq ADL. lia. } keep8 OD5 MU6 OD6. { clear - Hxq AHD. lia. }
  keep8 OD6 MU7 OD7. { clear - Hxq AND. lia. }
  (* [comment removed for export] *)
  pose proof (j0_w1f sp1 gp u0 u1 u2 sp b6 b7 s7 u3 u4 u5 u6 F2 fc2 m7 f PN PH PD PL flags od D0 ltac:(clear - DLO HLO SPH; lia) FLR MI7 OD7) as W6.
  cl_lift W6 Hc7' c8 Hc8. destruct (ASTA_unpack RT Σ1 _ _ c8 Hc8) as (ms8 & (m8 & -> & MU8 & WM8 & MI8 & OD8) & Hc8'). clear Hc8 Hc7'.
  assert (ST8 : stk asegs m8 lo sp1) by (apply (stk_munch _ m7 m8 lo sp1 ST7 MU8 WM8); intros x Hx; cbn [outside fst snd]; refine (conj _ I); clear - Hx DLO; lia).
  assert (COM8 : pem_com en Σ1 m8 boff CREM 21 []).
  { eapply (com_out_store RT AF GOBJ AFP libenv libenv_fp libenv_agree libenv_fp_where FZ_SITES FZ_CALLS en Σ1 m7 m8 boff CREM 21 [] PD fD kD);
      [exact COM7| right; right; left; reflexivity| exact FkD| exact FD1| exact FD2| exact MU8| exact WM8| exact MI8| exact ST8]. }
  (* [comment removed for export] *)
  assert (AG38 : forall x : word, outside [(sp1 + 240, sp1 + 248); (PL, PL + 8); (PH, PH + 8); (PN, PN + 8); (PD, PD + 8)] (bv_unsigned x) -> m8 x = m3 x).
  { intros x Ho. cbn [outside fst snd] in Ho. destruct Ho as (O1 & O2 & O3 & O4 & O5 & _).
    transitivity (m7 x); [apply MU8; cbn [outside fst snd]; exact (conj O5 I)|]. transitivity (m6 x); [apply MU7; cbn [outside fst snd]; exact (conj O4 I)|].
    transitivity (m5 x); [apply MU6; cbn [outside fst snd]; exact (conj O3 I)|]. transitivity (m4 x); [apply MU5; cbn [outside fst snd]; exact (conj O2 I)|].
    apply MU4; cbn [outside fst snd]; exact (conj O1 I). }
  pose proof (af_live_range RT AF Σ m E 904 ART0 INE) as (_ & ELO & _).
  assert (ER8 : errst_at_rest E [] m8).
  { eapply errst_rest_agree; [exact ER3|]. intros a Ha. destruct (errst_fp_where _ _ _ Ha) as [HE|(p & n & Hin & _)]; [| destruct Hin]. apply AG38. cbn [outside fst snd].
    pose proof (LLV E 904 INE) as V1. pose proof (HLV E 904 INE) as V2. pose proof (NLV E 904 INE) as V3. pose proof (DLV E 904 INE) as V4.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ I))))); unfold sp1, STACK_WIN in *; clear - HE ELO LOW HLO HP V1 V2 V3 V4; lia. }
  Local Ltac keep38 AG X X' := lazymatch type of AG with forall x, _ -> ?mm8 x = ?mm3 x => lazymatch type of X with rw_cells _ mm3 ?a ?cs =>
    assert (X' : rw_cells asegs mm8 a cs); [eapply rw_cells_agree_nw; [exact X| intros xq Hxq; cbv beta in Hxq; cbn [cells_size csize Nat.add] in Hxq; apply AG; cbn [outside fst snd];
      refine (conj _ (conj _ (conj _ (conj _ (conj _ I)))))] |] end end.
  keep38 AG38 FFC3 FFC8. all: try (unfold ff_cells in Hxq; cbn [cells_size csize Nat.add] in Hxq; unfold sp1, STACK_WIN in *; clear - Hxq FLO LOW HLO HP LFF HFF NFF DFF; lia).
  keep38 AG38 FR0 FR0'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FRH FRH'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FRF FRF'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FR104 FR104'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FRE FRE'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FBI FBI'. all: try (unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep38 AG38 FRG FRG'. all: try (zofnat Hxq; unfold sp1 in *; clear - Hxq LLO HHLO NLO DLO HLO HP; lia).
  keep8 FR224' MU5 FR224_5. { unfold sp1 in *. clear - Hxq LLO HLO HP. lia. } keep8 FR224_5 MU6 FR224_6. { unfold sp1 in *. clear - Hxq HHLO HLO HP. lia. }
  keep8 FR224_6 MU7 FR224_7. { unfold sp1 in *. clear - Hxq NLO HLO HP. lia. } keep8 FR224_7 MU8 FR224_8. { unfold sp1 in *. clear - Hxq DLO HLO HP. lia. }
  keep8 OL5 MU6 OL6. { clear - Hxq AHL. lia. } keep8 OL6 MU7 OL7. { clear - Hxq ANL. lia. } keep8 OL7 MU8 OL8. { clear - Hxq ADL. lia. }
  keep8 OH6 MU7 OH7. { clear - Hxq ANH. lia. } keep8 OH7 MU8 OH8. { clear - Hxq AHD. lia. }
  keep8 ON7 MU8 ON8. { clear - Hxq AND. lia. }
  assert (ONULL : out_null RT en m8) by exact (conj ON8 (conj OH8 (conj OD8 OL8))).
  assert (CRM : gn_need RT en boff + 4 <= CREM).
  { unfold gn_need, C_END, grow_pot, grow_cap, e_plen, CREM, pem_credit, gr_n. unfold en. cbn [e_blen e_boff]. clear - OFF BLEN. Z.div_mod_to_equations. lia. }
  assert (CR6 : C_END + 6 <= CREM) by (unfold C_END, CREM, pem_credit; clear - OFF; lia).
  clear COM3 COM4 COM5 COM6 COM7.
  destruct (Z.land flags 6 =? 6) eqn:E6.
  - (* [comment removed for export] *)
    change (if true then J_RAISE0 else J_J0N) with J_RAISE0 in Hc8'.
    refine (H_R0 en Σ1 m8 CREM 21 j0b [CB 56 jH] [CB 24 jF] endv x1 x2 g hj lenv jj1 tav jj2 bmv jj3 F2 fc2 (wz SITE_j0_sm) u0 u1 u2
              (wz (Z.land flags 6)) (wz 6) (wz (PD / 8 + SHB)) (wz (PH / 8 + SHB)) (wz (PL / 8 + SHB)) (wz (PN / 8 + SHB)) b6 b7 (wz PL) (wz PN) s7 (wz PD) (wz PH) u3 u4 u5 u6 [CB 104 jE]
              COM8 ER8 CR6 ltac:(clear; lia) FR0' FRH' eq_refl FRF' eq_refl FR104' FRE' eq_refl FBI' FR224_8 FRG' FFC8 ONULL T c8 Hc8' Hk).
  - (* [comment removed for export] *)
    change (if false then J_RAISE0 else J_J0N) with J_J0N in Hc8'.
    refine (H_J0N en Σ1 m8 CREM 21 j0b [CB 56 jH] [CB 24 jF] endv x1 x2 g hj lenv jj1 tav jj2 bmv jj3 F2 fc2 (wz SITE_j0_sm) u0 u1 u2
              (wz (Z.land flags 6)) (wz 6) b6 b7 s7 u3 u4 u5 u6 [CB 104 jE]
              COM8 ER8 CRM ltac:(clear; lia) FR0' FRH' eq_refl FRF' eq_refl FR104' FRE' eq_refl FBI' FR224_8 FRG' FFC8 ONULL T c8 Hc8' Hk).
Qed.
End CJ0.
