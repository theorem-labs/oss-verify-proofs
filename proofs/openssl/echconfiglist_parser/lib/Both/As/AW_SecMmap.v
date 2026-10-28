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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MmapFixed AllocTacX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition mmap_or_die_seg1_post (ra sp gp tp t0 t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size name : Z) (s0 s1 s2 : word) : machine_state -> Prop :=
  fun ms' => exists m' (j12 : list byte),
    ms' = MS (mkR (wz 0x1d3268) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz name) (wz size) (wz 0) (wz size) (wz 3) (wz 34) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz APAGESZ) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [CB 12 j12; C4 (wz 34); C8 s2; C8 s1; C8 s0; C8 ra].
End HCW.

Section Seg1.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size name : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 320 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz size. Hypothesis Ha1 : a1 = wz name.
  Hypothesis SZ : 0 < size /\ size mod 4096 = 0 /\ size <= 2^47.
  Hypothesis NM : 0 < name < 2^32.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis DPM : rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)].

  Theorem mmap_or_die_seg1 :
    evt asegs (mmap_or_die_seg1_post ra sp gp tp t0 t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size name s0 s1 s2)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d31e0) fc None m (seg_rom asegs)).
  Proof.
    unfold AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS in *. cbn [map] in GOT. change (7586856 + 260) with 7587116 in DPM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a0 a1. unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. do 4 step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709547520)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709547520)) with (Z_to_bv 64 size) end.
    2:{ rewrite (unsigned_lit (size + 4095)) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite StrFun.land_align_down by lia.
        f_equal. clear - SZ; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    match type of FR with context [CB 16 ?j] => remember j as J16 eqn:EJ in FR; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 16 J16 [_;_;_;_] [12;4]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR end.
    repeat match type of FR with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in FR end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    step. st1. step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 272%nat ST.
    match type of FR0 with context [CB 272 ?j] => remember j as J272 eqn:EJ in FR0; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 272 J272 [] [216;8;8;8;8;8;8;8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    repeat match type of FR0 with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR0 end.
    repeat match type of FR0 with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in FR0 end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    do 7 st1. step. step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - NM; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. rewrite zxb_b8 by lia. step. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. do 7 step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    release_frame FR0 ST (bv_unsigned sp + -48).
    replace (sx32 (Z_to_bv 64 34)) with (Z_to_bv 64 34) by (symmetry; apply (sx32_wz 34); lia).
    apply evt_done. unfold mmap_or_die_seg1_post. exists m1, jk.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
  Qed.
End Seg1.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition mmap_or_die_seg2_post (ra0 : word) (spi : Z) (gp tp t0 t1 t2 : word) (s0v s1v : word) (a4 a5 a6 a7 : word) (s2v : word)
    (s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo r : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 : word) m',
    ms' = MS (mkR ra0 (Z_to_bv 64 (spi + 48)) gp tp t0 t1 t2 s0v s1v (wz r) a1 a2 a3 a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m' (seg_rom asegs)
    /\ munch [(spi, spi + 48)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spi + 48).
End HCW.

Section Seg2.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (spi lo r : Z) (ra0 s0v s1v s2v : word) (j12 : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo spi.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo <= spi. Hypothesis SPT : spi + 64 <= 2^47. Hypothesis SPA : spi mod 8 = 0.
  Hypothesis FR : rw_cells asegs m spi [CB 12 j12; C4 (wz 34); C8 s2v; C8 s1v; C8 s0v; C8 ra0].
  Hypothesis RR : 0 < r /\ r + 4096 <= 2^47.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].

  Theorem mmap_or_die_seg2 :
    evt asegs (mmap_or_die_seg2_post ra0 spi gp tp t0 t1 t2 s0v s1v a4 a5 a6 a7 s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r)
      (MS (mkR (wz 0x1d3268) (Z_to_bv 64 spi) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    unfold AGOT_LO, AGOT_VALS, ACFLAGS in *. cbn [map] in GOT. change (7586856 + 144) with 7587000 in MLIM.
    acb.
    pose proof (munch_refl [(spi, spi + 48)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. clear - RR; try acb. intros K. apply K. lia. } clear K.
    step. step.
    replace (v_sltu (Z_to_bv 64 (-4096)) (Z_to_bv 64 r)) with (Z_to_bv 64 0).
    2:{ rewrite v_sltu_b2z. rewrite (unsigned_lit r) by lia.
        match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end.
        rewrite zb_b2z_if. destruct (Z.ltb_spec 18446744073709547520 r); [exfalso; clear - RR H; try acb; lia| reflexivity]. }
    (* [comment removed for export] *)
    match type of FR with context [CB 12 ?j] => remember j as J12 eqn:EJ in FR; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 12 J12 [_;_;_;_;_] [8;4]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR end.
    repeat match type of FR with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in FR end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    step. step. st1. step. step. step.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. clear - RR; try acb. intros K. apply K. lia. } clear K.
    step. step.
    replace (v_sltu (Z_to_bv 64 (-4096)) (Z_to_bv 64 r)) with (Z_to_bv 64 0).
    2:{ rewrite v_sltu_b2z. rewrite (unsigned_lit r) by lia.
        match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end.
        rewrite zb_b2z_if. destruct (Z.ltb_spec 18446744073709547520 r); [exfalso; clear - RR H; try acb; lia| reflexivity]. }
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K. step.
    (* [comment removed for export] *)
    step. do 4 step. step. step. release_frame FR ST (spi + 48). finish.
  Qed.
End Seg2.
Section HCW.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition map_or_die0_seg1_post (ra sp gp tp t0 t1 t2 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo beg size : Z) (s0 s1 s2 s3 s4 : word) : machine_state -> Prop :=
  fun ms' => exists m' (j44 : list byte),
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 (wz size) (wz 0) (wz beg) (wz size) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz beg) (wz 0) (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 368, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -96)
    /\ rw_cells asegs m' (bv_unsigned sp + -96) [C4 (wz 50); CB 44 j44; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End HCW.

Section Seg1z.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo beg size : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 368 <= bv_unsigned sp.
  Hypothesis Ha1 : a1 = wz beg. Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz 0.
  Hypothesis BEG : 0 <= beg /\ beg + size <= 2^47 /\ beg mod 4096 = 0.
  Hypothesis SZ : 0 < size /\ size mod 4096 = 0.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].

  Theorem map_or_die0_seg1 :
    evt asegs (map_or_die0_seg1_post ra sp gp tp t0 t1 t2 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo beg size s0 s1 s2 s3 s4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1dceb8) fc None m (seg_rom asegs)).
  Proof.
    unfold AGOT_LO, AGOT_VALS, APAGESZ in *. cbn [map] in GOT.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 368, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a1 a2 a3.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 96%nat ST. do 6 step.
    (* [comment removed for export] *)
    unfold wz in *.
    step. step. step. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709547520)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709547520)) with (Z_to_bv 64 size) end.
    2:{ rewrite (unsigned_lit (size + 4095)) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite StrFun.land_align_down by lia.
        f_equal. clear - SZ BEG; try acb. Z.div_mod_to_equations. lia. }
    step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    (* [comment removed for export] *)
    step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709547520)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709547520)) with (Z_to_bv 64 beg) end.
    2:{ rewrite (unsigned_lit beg) by lia. change 18446744073709547520 with (2^64 - 2^12)%Z. rewrite StrFun.land_align_down by lia.
        f_equal. clear - BEG; try acb. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    match type of FR with context [CB 48 ?j] => remember j as J48 eqn:EJ in FR; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 48 J48 [_;_;_;_;_;_] [4;40;4]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR end.
    repeat match goal with H : _ = take _ _ |- _ => clear H end.
    step. st1. step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 272%nat ST.
    match type of FR0 with context [CB 272 ?j] => remember j as J272 eqn:EJ in FR0; clear EJ end.
    apply (rw_cells_split_CB asegs _ _ [] 272 J272 [] [216;8;8;8;8;8;8;8]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
    repeat match type of FR0 with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FR0 end.
    repeat match type of FR0 with context [CB ?n (drop ?k ?l)] => let J := fresh "jk" in remember (drop k l) as J in FR0 end.
    repeat match goal with H : _ = take _ _ |- _ => clear H | H : _ = drop _ _ |- _ => clear H end.
    do 7 st1. step. step. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. do 7 step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    release_frame FR0 ST (bv_unsigned sp + -96).
    replace (sx32 (Z_to_bv 64 50)) with (Z_to_bv 64 50) by (symmetry; apply (sx32_wz 50); lia).
    apply (rw_cells_merge asegs _ _ [C4 (Z_to_bv 64 50)] [CB 40 jk0; CB 4 jk1] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in FR. rewrite app_nil_r in FR.
    apply evt_done. unfold map_or_die0_seg1_post. exists m1, (jk0 ++ jk1).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FR.
  Qed.
End Seg1z.

