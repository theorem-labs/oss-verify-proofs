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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N8Store.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


(* [comment removed for export] *)
Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition map_or_die_seg1_post (ra sp gp tp t0 t1 t2 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo beg size name : Z) (s0 s1 s2 s3 s4 : word) : machine_state -> Prop :=
  fun ms' => exists m' (j44 : list byte),
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz size) (wz 1) (wz beg) (wz size) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz beg) (wz name) (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 400, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ rw_cells asegs m' (bv_unsigned sp + -128) [C4 (wz 50); CB 44 j44; C8 s4; C8 s3; C8 s2; C8 (wz beg); C8 (wz size); C8 (wz 0x1dcd98);
                                                  C8 s2; C8 s1; C8 s0; C8 ra].
End HCW2.

Section Seg1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo beg size name : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 400 <= bv_unsigned sp.
  Hypothesis Ha1 : a1 = wz beg. Hypothesis Ha2 : a2 = wz size. Hypothesis Ha3 : a3 = wz name.
  Hypothesis BEG : 0 <= beg /\ beg + size <= 2^47 /\ beg mod 4096 = 0.
  Hypothesis SZ : 0 < size /\ size mod 4096 = 0.
  Hypothesis NM : 0 < name < 2^32.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis DPM : rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)].

  Theorem map_or_die_seg1 :
    evt asegs (map_or_die_seg1_post ra sp gp tp t0 t1 t2 s5 a6 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo beg size name s0 s1 s2 s3 s4)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1dcd6c) fc None m (seg_rom asegs)).
  Proof.
    unfold AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS in *. cbn [map] in GOT. change (7586856 + 260) with 7587116 in DPM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 400, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    subst a1 a2 a3. unfold wz in *.   (* [comment removed for export] *)
    (* [comment removed for export] *)
    step. carve_frame 32%nat ST. rename FR into FRM. do 4 step. step. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    step. carve_frame 96%nat ST. st1. do 5 step.   (* [comment removed for export] *)
    (* [comment removed for export] *)
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
    do 7 st1. step. step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - NM; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. rewrite zxb_b8 by lia. step. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. do 7 step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    release_frame FR0 ST (bv_unsigned sp + -128).
    replace (sx32 (Z_to_bv 64 50)) with (Z_to_bv 64 50) by (symmetry; apply (sx32_wz 50); lia).
    apply (rw_cells_merge asegs _ _ [C4 (Z_to_bv 64 50)] [CB 40 jk0; CB 4 jk1] [_; _; _; _; _; _]) in FR.
    cbn [cells_size csize cells_bytes cbytes app Nat.add] in FR. rewrite app_nil_r in FR.
    (* [comment removed for export] *)
    assert (FRJ : rw_cells asegs m1 (bv_unsigned sp + -128)
                    ([C4 (Z_to_bv 64 50); CB 44 (jk0 ++ jk1); C8 s4; C8 s3; C8 s2; C8 (Z_to_bv 64 beg); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 0x1dcd98)]
                     ++ [C8 s2; C8 s1; C8 s0; C8 ra])).
    { apply rw_cells_app. split; [exact FR|]. cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -128 + Z.of_nat 96) with (bv_unsigned sp + -32) by (clear; lia). exact FRM. }
    cbn [app] in FRJ.
    apply evt_done. unfold map_or_die_seg1_post. exists m1, (jk0 ++ jk1).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. exact FRJ.
  Qed.
End Seg1.
Section HCW2.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition mmap_fixed_seg2_post (ra : word) (spi : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo r : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (spi + 96)) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(spi, spi + 96)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spi + 96).
End HCW2.

Section Seg2.
  Context {HCEIL : HeapCeil}.
  Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (spi lo r size : Z) (s1v s2v s3v : word) (j44 : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo spi.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo <= spi. Hypothesis SPT : spi + 112 <= 2^47. Hypothesis SPA : spi mod 8 = 0.
  Hypothesis FR : rw_cells asegs m spi [C4 (wz 50); CB 44 j44; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RR : 0 < r /\ r + 4096 <= 2^47.
  Hypothesis SZ : 0 < size < 2^47.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].

  Theorem mmap_fixed_seg2 :
    evt asegs (mmap_fixed_seg2_post ra spi gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 spi) gp tp t0 t1 t2 (wz size) s1v (wz r) a1 a2 a3 a4 a5 a6 a7
               s2v s3v (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof using HCEIL ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spi lo r size s1v s2v s3v j44 MI ST LO HI SPT SPA FR RR GOT MLIM.   (* [comment removed for export] *)
    unfold AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS in *. cbn [map] in GOT. change (7586856 + 144) with 7587000 in MLIM.
    acb.
    pose proof (munch_refl [(spi, spi + 96)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. clear - RR; try acb. intros K. apply K. lia. } clear K.
    step. step.
    replace (v_sltu (Z_to_bv 64 (-4096)) (Z_to_bv 64 r)) with (Z_to_bv 64 0).
    2:{ rewrite v_sltu_b2z. rewrite (unsigned_lit r) by lia.
        match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end.
        rewrite zb_b2z_if. destruct (Z.ltb_spec 18446744073709547520 r); [exfalso; clear - RR H; try acb; lia| reflexivity]. }
    (* [comment removed for export] *)
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
    step. do 6 step. step. step. release_frame FR ST (spi + 96). finish.
  Qed.
End Seg2.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW4.
  Context {HCEIL : HeapCeil}.

Definition map_seg2_post (ra : word) (spi : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo r : Z) : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (spi + 128)) gp tp t0 t1 t2 s0 s1 (wz r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(spi, spi + 128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (spi + 128).
End HCW4.

Section MapSeg2.
  Context {HCEIL : HeapCeil}.
  Variables (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (spi lo r size : Z) (s0i s1i s2i s1v s2v s3v : word) (j44 : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo spi.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo <= spi. Hypothesis SPT : spi + 144 <= 2^47. Hypothesis SPA : spi mod 8 = 0.
  Hypothesis FR : rw_cells asegs m spi [C4 (wz 50); CB 44 j44; C8 s4; C8 s3; C8 s2i; C8 s1i; C8 s0i; C8 (wz 0x1dcd98);
                                        C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RR : 0 < r /\ r + 4096 <= 2^47.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].

  Theorem map_seg2 :
    evt asegs (map_seg2_post ra spi gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo r)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 spi) gp tp t0 t1 t2 (wz size) s1v (wz r) a1 a2 a3 a4 a5 a6 a7
               s2v s3v (wz APAGESZ) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    pose proof (munch_refl [(spi, spi + 128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    acb.
    apply (rw_cells_app asegs m spi [C4 (wz 50); CB 44 j44; C8 s4; C8 s3; C8 s2i; C8 s1i; C8 s0i; C8 (wz 0x1dcd98)] [C8 s2; C8 s1; C8 s0; C8 ra]) in FR.
    destruct FR as [FRI FRM]. cbn [cells_size csize Nat.add] in FRM. change (Z.of_nat 96) with 96 in FRM.
    (* [comment removed for export] *)
    eapply evt_cut; [ eapply (mmap_fixed_seg2 (wz 0x1dcd98) gp tp t0 t1 t2 s0i s1i a1 a2 a3 a4 a5 a6 a7 s2i s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m spi lo r size s1v s2v s3v j44)
                    | intros ms' PO; unfold mmap_fixed_seg2_post in PO; revert ms' PO; post_call asegs m ].
    all: try eassumption. all: try (clear - SPT; lia).
    clear ST. rename POST into ST.
    replace (ret_pc (wz 0x1dcd98)) with (Z_to_bv 64 0x1dcd98) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    unfold wz. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - RR; try acb. lia. } clear K.
    do 4 step. step. step. release_frame FRM ST (spi + 128). finish.
  Qed.
End MapSeg2.
