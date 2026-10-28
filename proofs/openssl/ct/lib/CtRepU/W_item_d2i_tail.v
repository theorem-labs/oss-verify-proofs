(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApPrim ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_get_object W_get_object_walk W_c2i_int W_check_tlen W_item_d2i_stmt W_item_d2i_img W_item_d2i_front ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

(* [comment removed for export] *)
Ltac xport H MU WM :=
  first [ eapply rw_cells_transport in H; [| exact MU| exact WM| cbn [cells_size csize Nat.add disjoint_from fst snd]; cbn; lia]
        | eapply ro_cells_transport in H; [| exact MU| cbn [cells_size csize Nat.add disjoint_from fst snd]; cbn; lia] ].

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Ltac step := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition D2I_OK_TAIL : Z := 0x112590.
Definition D2I_FAIL_TAIL : Z := 0x11255c.
Definition EMBED_FREE : Z := 0x113334.

Lemma sx32_unsigned_ne1 : forall w, 0 <= w < 2^32 -> w <> 1 -> bv_unsigned (sx32 (Z_to_bv 64 w)) <> 1.
Proof.
  intros w Hw H1. unfold sx32. rewrite (unsigned_lit w) by lia.
  destruct (Z.lt_ge_cases w (2^31)) as [L|G].
  - rewrite bk_swrap32_small by lia. rewrite unsigned_lit by lia. exact H1.
  - unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 `div` 2) with 2147483648.
    rewrite <- (Z.mod_add (w + 2147483648) (-1) 4294967296) by lia. rewrite Z.mod_small by lia.
    rewrite unsigned_lit_wrap. rewrite <- (Z.mod_add _ 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma embed_free_null : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo PVAL IT w : Z) (POST : machine_state -> Prop),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> 0 < lo -> lo <= bv_unsigned sp - 112 -> bv_unsigned sp < 2^63 ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^63 -> PVAL mod 8 = 0 -> rw_cells ctusegs m PVAL [C8 (Z_to_bv 64 0)] ->
  0 < IT -> IT + 56 <= lo -> IT mod 8 = 0 ->
  ro_cells ctusegs m IT [C1 (Z_to_bv 8 0)] -> ro_cells ctusegs m (IT + 8) [C4 (Z_to_bv 64 w)] ->
  ro_cells ctusegs m (IT + 16) [C8 (Z_to_bv 64 0)] -> ro_cells ctusegs m (IT + 32) [C8 (Z_to_bv 64 0)] ->
  0 <= w < 2^32 -> w <> 1 ->
  (forall (t0' t1' a0' a1' a2' a3' : word) (m' : mem),
     munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' -> stk ctusegs m' lo (bv_unsigned sp) ->
     evt ctusegs POST
       (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (ret_pc ra) fc None m' (seg_rom ctusegs))) ->
  evt ctusegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 PVAL) (Z_to_bv 64 IT) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 EMBED_FREE) fc None m (seg_rom ctusegs)).
Proof.
  intros until POST. intros ST MI LO0 LO SPB PVS PVB PVA HPV IT0' ITL ITA IT0 IT8 IT16 IT32 WR W1 KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold EMBED_FREE.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 96%nat ST. do 13 step.
  step. step. step. if_cases K0; zc K0; [exfalso; lia|].
  step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. step. if_true.
  step. if_true. step. step. step. if_false. step. step. step. step.
  match goal with H : mem_inv ctusegs ?mx |- evt _ _ (MS _ _ _ _ _ ?mx _) => pose proof (jt_embed_free mx H) as JT end.
  step. clear JT. rewrite (sx32_small 859512) by lia. step. setreg 11 (Z_to_bv 64 1127504) ltac:(reflexivity). step.
  step. step. if_true. step. step. step. do 11 step. step. release_frame FR ST (bv_unsigned sp). step.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 5 step. step.
  step. if_cases K1; zc K1; [exfalso; lia|].
  step. step. if_true. step. if_true.
  step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. step. if_true.
  step. step. step. if_cases K2; zc K2; [exfalso; exact (sx32_unsigned_ne1 w WR W1 K2)|].
  step. step. if_true.
  step. step. step. step. release_frame FR ST (bv_unsigned sp). step.
  name_mem m2. eapply KONT; [exact MU| exact WM| | exact ST]. assumption.
Qed.

(* [comment removed for export] *)
Lemma d2i_tail_ok : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (x1 x18 x19 x20 x21 x22 x23 x24 x25 x26 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo OPP utype D cont plen item pv : Z) (vo cw : word) (j5 j4 j16 j0 jt : list byte) (POST : machine_state -> Prop),
  stk ctusegs m lo (bv_unsigned sp + -320) -> mem_inv ctusegs m -> 0 < lo -> lo <= bv_unsigned sp - 320 -> bv_unsigned sp < 2^63 -> bv_unsigned sp mod 16 = 0 ->
  bv_unsigned sp <= OPP -> OPP + 8 <= 2^63 -> rw_cells ctusegs m OPP [C8 vo] ->
  0 <= pv < 2^64 ->
  rw_cells ctusegs m (bv_unsigned sp + -320) (exprim_frame sp s3 s4 s5 s6 s7 s8 s9 s10 utype D cont plen item cw j5 j4 j16 j0) ->
  rw_cells ctusegs m (bv_unsigned sp + -128) (intern_frame sp s2 s3) ->
  rw_cells ctusegs m (bv_unsigned sp + -64) (d2iex_frame ra s0 s1 pv jt) ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     munch [(OPP, OPP + 8)]%Z m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' -> stk ctusegs m' lo (bv_unsigned sp) ->
     rw_cells ctusegs m' OPP [C8 (Z_to_bv 64 (D + cont + plen))] ->
     evt ctusegs POST
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 pv) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom ctusegs))) ->
  evt ctusegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -320)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -128)) (Z_to_bv 64 OPP)
             a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 D2I_OK_TAIL) fc None m (seg_rom ctusegs)).
Proof.
  intros until POST. intros ST MI LO0 LO SPB SP16 OPS OPB HOPP PVR FX FI FD KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold D2I_OK_TAIL, exprim_frame, intern_frame, d2iex_frame, RA_INTERN, RA_D2IEX in *.
  pose proof (munch_refl [(OPP, OPP + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  step. step. step.
  step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
  step. do 12 step. step. release_frame FX ST (bv_unsigned sp + -128). step.
  (* [comment removed for export] *)
  step. step. if_true. step. do 5 step. step. release_frame FI ST (bv_unsigned sp + -64). step.
  (* [comment removed for export] *)
  change (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008).
  step. if_false. step. step. step. step. step. step. release_frame FD ST (bv_unsigned sp). step.
  name_mem m2. eapply KONT; [exact MU| exact WM| | exact ST|]; assumption.
Qed.

(* [comment removed for export] *)
Lemma d2i_tail_fail : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (x1 x9 x18 x20 x21 x22 x23 x24 x26 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo utype D cont plen item : Z) (cw : word) (j5 j4 j16 j0 jt : list byte) (POST : machine_state -> Prop),
  stk ctusegs m lo (bv_unsigned sp + -320) -> mem_inv ctusegs m -> 3493888 <= lo -> lo <= bv_unsigned sp - 480 -> bv_unsigned sp < 2^63 -> bv_unsigned sp mod 16 = 0 ->
  rw_cells ctusegs m (bv_unsigned sp + -320) (exprim_frame sp s3 s4 s5 s6 s7 s8 s9 s10 utype D cont plen item cw j5 j4 j16 j0) ->
  rw_cells ctusegs m (bv_unsigned sp + -128) (intern_frame sp s2 s3) ->
  rw_cells ctusegs m (bv_unsigned sp + -64) (d2iex_frame ra s0 s1 0 jt) ->
  0 < item -> item + 56 <= lo -> item mod 8 = 0 ->
  ro_cells ctusegs m item [C1 (Z_to_bv 8 0)] -> ro_cells ctusegs m (item + 8) [C4 (Z_to_bv 64 utype)] ->
  ro_cells ctusegs m (item + 16) [C8 (Z_to_bv 64 0)] -> ro_cells ctusegs m (item + 32) [C8 (Z_to_bv 64 0)] -> 0 <= utype < 2^32 -> utype <> 1 ->
  ro_cells ctusegs m ITEM_ANY [C1 (Z_to_bv 8 0)] -> ro_cells ctusegs m (ITEM_ANY + 8) [C4 (Z_to_bv 64 (2^32 - 4))] ->
  ro_cells ctusegs m (ITEM_ANY + 16) [C8 (Z_to_bv 64 0)] -> ro_cells ctusegs m (ITEM_ANY + 32) [C8 (Z_to_bv 64 0)] ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
     munch [(bv_unsigned sp - 480, bv_unsigned sp)]%Z m m' -> wmono ctusegs m m' -> mem_inv ctusegs m' -> stk ctusegs m' lo (bv_unsigned sp) ->
     evt ctusegs POST
       (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F (ret_pc ra) fc None m' (seg_rom ctusegs))) ->
  evt ctusegs POST
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -320)) gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + -128)) x9
             a0 a1 a2 a3 a4 a5 a6 a7 x18 (Z_to_bv 64 0) x20 x21 x22 x23 x24 (Z_to_bv 64 0) x26 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 D2I_FAIL_TAIL) fc None m (seg_rom ctusegs)).
Proof.
  intros until POST. intros ST MI LO0 LO SPB SP16 FX FI FD IT0' ITL ITA IT0 IT8 IT16 IT32 UR U1 AN0 AN8 AN16 AN32 KONT.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold D2I_FAIL_TAIL, exprim_frame, intern_frame, d2iex_frame, RA_INTERN, RA_D2IEX, ITEM_ANY in *.
  pose proof (munch_refl [(bv_unsigned sp - 480, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  step. step. carve_frame 16%nat ST. do 9 step. release_frame FR ST (bv_unsigned sp + -320). step.
  carve_frame 32%nat ST. do 7 step.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0] ++ [c1] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRA FR]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR.
  apply rw_cells_app in FR. destruct FR as [FRV FRB]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FRB.
  replace (bv_unsigned sp + -352 + 8) with (bv_unsigned sp + -344) in FRV by lia.
  replace (bv_unsigned sp + -352 + 8 + 8) with (bv_unsigned sp + -336) in FRB by lia.
  assert (ESP2 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -352)) = bv_unsigned sp + -352) by (apply unsigned_lit; lia).
  step. name_mem m1.
  eapply embed_free_null with (lo := lo) (PVAL := bv_unsigned sp + -344) (IT := 2960664) (w := 2 ^ 32 - 4);
    [rewrite ?ESP2; exact ST| exact MI| lia| rewrite ?ESP2; lia| rewrite ?ESP2; lia| rewrite ?ESP2; lia| lia| clear - SP16; Z.div_mod_to_equations; lia| exact FRV| lia| lia| reflexivity
    | exact AN0| exact AN8| exact AN16| exact AN32| lia| lia|].
  intros t0' t1' a0' a1' a2' a3' m2 MU2 WM2 MI2 ST2. rewrite ?ESP2 in *.
  xport FX MU2 WM2. xport FI MU2 WM2. xport FD MU2 WM2. xport FRA MU2 WM2. xport FRV MU2 WM2. xport FRB MU2 WM2.
  xport IT0 MU2 WM2. xport IT8 MU2 WM2. xport IT16 MU2 WM2. xport IT32 MU2 WM2.
  assert (MU' : munch [(bv_unsigned sp - 480, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. intros x; cbn; lia. }
  pose proof (wmono_trans _ _ _ _ WM WM2) as WM'. clear MU WM MU2 WM2 MI AN0 AN8 AN16 AN32. rename MU' into MU. rename WM' into WM.
  replace (ret_pc (Z_to_bv 64 1127204)) with (Z_to_bv 64 1127204) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step. step. step. release_frame FRA ST2 (bv_unsigned sp + -344). release_frame FRV ST2 (bv_unsigned sp + -336). release_frame FRB ST2 (bv_unsigned sp + -320). step.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 1123684)) with (Z_to_bv 64 1123684) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step. if_true. step. step. step. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0). step. if_true.
  step. do 12 step. step. release_frame FX ST2 (bv_unsigned sp + -128). step.
  (* [comment removed for export] *)
  replace (ret_pc (Z_to_bv 64 1117828)) with (Z_to_bv 64 1117828) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step. step. if_false. step. step. step.
  carve_frame 16%nat ST2. do 8 step. release_frame FR ST2 (bv_unsigned sp + -128). step.
  lazymatch type of FD with rw_cells _ _ _ (?c0 :: ?rest) => change (c0 :: rest) with ([c0] ++ rest) in FD end.
  apply rw_cells_app in FD. destruct FD as [FDV FD]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FD.
  replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) in FD by lia.
  assert (ESP3 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; lia).
  name_mem m3.
  match goal with H : mem_inv ctusegs m3 |- _ => rename H into MI3 end.
  eapply embed_free_null with (lo := lo) (PVAL := bv_unsigned sp + -64) (IT := item) (w := utype);
    [rewrite ?ESP3; exact ST2| exact MI3| lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| rewrite ?ESP3; lia| lia| clear - SP16; Z.div_mod_to_equations; lia| exact FDV| lia| lia| exact ITA
    | exact IT0| exact IT8| exact IT16| exact IT32| lia| exact U1|].
  intros t0'' t1'' a0'' a1'' a2'' a3'' m4 MU4 WM4 MI4 ST4. rewrite ?ESP3 in *.
  xport FI MU4 WM4. xport FD MU4 WM4. xport FDV MU4 WM4.
  assert (MU' : munch [(bv_unsigned sp - 480, bv_unsigned sp)]%Z m m4).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. intros x; cbn; lia. }
  pose proof (wmono_trans _ _ _ _ WM WM4) as WM'. clear MU WM MU4 WM4 MI3 IT0 IT8 IT16 IT32. rename MU' into MU. rename WM' into WM.
  replace (ret_pc (Z_to_bv 64 1117848)) with (Z_to_bv 64 1117848) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  step. step. do 5 step. step. release_frame FI ST4 (bv_unsigned sp + -64). step.
  replace (ret_pc (Z_to_bv 64 1118008)) with (Z_to_bv 64 1118008) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  step. if_true. step. step. step. step. step.
  release_frame FDV ST4 (bv_unsigned sp + -56). release_frame FD ST4 (bv_unsigned sp). step.
  name_mem m5. eapply KONT; [exact MU| exact WM| | exact ST4]; assumption.
Qed.

End WithCeiling0.
