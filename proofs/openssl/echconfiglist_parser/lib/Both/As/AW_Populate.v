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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_PoisonShadow AW_MmapFixed AW_Efs.
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Tactic Notation "callD" uconstr(SPEC) "dropping" ne_hyp_list(HS) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clear HS; post_callD segs m ]
  end.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition size_hi_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c : Z) : machine_state -> Prop :=
  fun ms' => exists (a3 a5 a6 : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (wz (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c23c) fc None m (seg_rom asegs).

End HCW2.


Ltac zcases c lo hi :=
  let b := eval vm_compute in (Z.ltb hi lo) in
  lazymatch b with
  | true => exfalso; lia
  | false => let lo' := eval vm_compute in (lo + 1)%Z in destruct (Z.eq_dec c lo) as [-> | ?]; [| zcases c lo' hi]
  end.

Section HCW3.
  Context {HCEIL : HeapCeil}.

Lemma size_hi_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (c : Z), 17 <= c <= 30 ->
  evt asegs (size_hi_post ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) a4 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m c)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz c) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19c218) fc None m (seg_rom asegs)).
Proof.
  (* [comment removed for export] *)
  intros. unfold wz. do 9 step. apply evt_done. unfold size_hi_post. do 3 eexists.
  zcases c 17 30; (repeat f_equal; apply bv_eq; vm_compute; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_head_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo c R stat sb k au mu : Z) : machine_state -> Prop :=
  fun ms' => exists (a3 a5 a6 : word) m' (j : list byte),
    let csz := class_size c in let total := au + csz * k in
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz stat) a0 (wz (Z.shiftl c 32)) a2 (wz au) a4 a5 a6 a7
                  (wz (sb + c * 2^32)) (wz total) (wz mu) (wz csz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 (if mu <? total then 0x19c254 else 0x19c328)) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End HCW3.

Section Head.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo c R stat sb k nf mfa au mu : Z).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 64 <= bv_unsigned sp.
  Hypothesis Ha0 : a0 = wz AINST. Hypothesis Ha1 : a1 = wz stat. Hypothesis Ha2 : a2 = wz c. Hypothesis Ha3 : a3 = wz R. Hypothesis Ha4 : a4 = wz k.
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize <= aceil.
  Hypothesis KR : 1 <= k <= 128.
  Hypothesis AUR : 0 <= au /\ au + 65536 * 128 <= 2^32 /\ 0 <= mu < 2^32.
  Hypothesis INST1 : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)].
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).

  Theorem pop_head :
    evt asegs (pop_head_post ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c R stat sb k au mu)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c1b4) fc None m (seg_rom asegs)).
  Proof.
    unfold rinfo_cells, AHI_LO, kSpaceSize, AINST, OI_SPACEBEG in *. change (6976152 + 32) with 6976184 in INST1.
    subst a0 a1 a2 a3 a4.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as (CS1 & CS2 & CS3 & _).
    unfold wz in *.
    (* [comment removed for export] *)
    step. carve_frame 64%nat ST. do 8 step. step. step. step. step. step.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - HC; try acb. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit c) by (clear - HC; try acb; lia).
    assert (FIN : forall mq (x3 x5 x6 : word) (jq : list byte) (pcv : Z),
      pcv = (if mu <? au + class_size c * k then 0x19c254 else 0x19c328) ->
      mem_inv asegs mq -> munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m mq -> wmono asegs m mq -> stk asegs mq lo (bv_unsigned sp + -64) ->
      rw_cells asegs mq (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt asegs (pop_head_post ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6976152) (Z_to_bv 64 c) (Z_to_bv 64 k) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo c R stat sb k au mu)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat) (Z_to_bv 64 6976152) (Z_to_bv 64 (c * 2^32)) (Z_to_bv 64 c)
                  (Z_to_bv 64 au) (Z_to_bv 64 k) x5 x6 a7 (Z_to_bv 64 (sb + c * 2^32)) (Z_to_bv 64 (au + class_size c * k)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 pcv) fc None mq (seg_rom asegs))).
    { intros mq x3 x5 x6 jq pcv E MI1 MU1 WM1 ST1 FR1.
      apply evt_done. unfold pop_head_post. exists x3, x5, x6, mq, jq. cbv zeta.
      split; [rewrite E; unfold wz; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1| exact FR1]. }
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      rewrite ?unsigned_lit in K by (clear -HC; lia).
      eapply evt_cut; [eapply size_hi_spec; clear - K HC; try acb; lia|]. intros ms1 PO. destruct PO as (x3 & x5 & x6 & ->). unfold wz.
      (* [comment removed for export] *)
      step. step. step. step. step.
      rewrite (unsigned_lit (class_size c)), (unsigned_lit k) by (clear - CS1 KR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia).
      replace (c * 2 ^ 32 + sb) with (sb + c * 2^32) by (clear; lia).
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - AUR CS1 KR; try acb; nia);
        change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by (clear; lia); rewrite Z.mod_small in K2 by (clear - AUR CS1 KR; try acb; nia).
      + eapply (FIN _ x3 x5 x6 junk); try eassumption. rewrite (proj2 (Z.ltb_ge _ _)) by (clear - K2; try acb; lia). reflexivity.
      + eapply (FIN _ x3 x5 x6 junk); try eassumption. rewrite (proj2 (Z.ltb_lt _ _)) by (clear - K2; try acb; lia). reflexivity.
    - (* [comment removed for export] *)
      step. rewrite (unsigned_lit c) by (clear - HC; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 5) by (clear; lia).
      replace (c * 2^5) with (class_size c) by (unfold class_size; replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; clear - HC; try acb; lia);
                                              replace (c <=? 16) with true by (symmetry; apply Z.leb_le; clear - K; try acb; lia); clear; lia).
      step. step. step. step. step.
      rewrite (unsigned_lit (class_size c)), (unsigned_lit k) by (clear - CS1 KR; try acb; lia). rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia).
      replace (c * 2 ^ 32 + sb) with (sb + c * 2^32) by (clear; lia).
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by (clear - AUR CS1 KR; try acb; nia);
        change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by (clear; lia); rewrite Z.mod_small in K2 by (clear - AUR CS1 KR; try acb; nia).
      + eapply (FIN _ (Z_to_bv 64 16) a5 a6 junk); try eassumption. rewrite (proj2 (Z.ltb_lt _ _)) by (clear - K2; try acb; lia). reflexivity.
      + step. eapply (FIN _ (Z_to_bv 64 16) a5 a6 junk); try eassumption. rewrite (proj2 (Z.ltb_ge _ _)) by (clear - K2; try acb; lia). reflexivity.
  Qed.
End Head.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_ms (total mu : Z) : Z := round_up (total - mu) kUserMapSize.

Definition pop_map_seg1_post (ra sp gp tp t0 t1 t2 s0 s1 a6 s5v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (s2 s3 s4 s5 s6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R stat rbeg mu total : Z) : machine_state -> Prop :=
  fun ms' => exists m' (j44 : list byte),
    let beg := rbeg + mu in let ms := pop_ms total mu in
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (wz ms) (wz 1) (wz beg) (wz ms) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz beg) (wz 0x277c4) (wz APAGESZ) s5v (wz AINST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -192)
    /\ rw_cells asegs m' (bv_unsigned sp + -192) [C4 (wz 50); CB 44 j44; C8 (wz beg); C8 (wz ms); C8 (wz rbeg); C8 (wz beg); C8 (wz ms); C8 (wz 0x1dcd98);
                                                  C8 (wz rbeg); C8 (wz stat); C8 (wz R); C8 (wz 0x19c2d4)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
End HCW3.

Section MapSeg1.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo c R stat sb k nf mfa au mu : Z) (j64 : list byte).
  Let csz := class_size c. Let total := au + csz * k. Let rbeg := sb + c * 2^32.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -64).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 464 <= bv_unsigned sp.
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis HC : 1 <= c <= 30.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis SBR : AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0.
  Hypothesis KR : 1 <= k <= 128.
  Hypothesis AUR : 0 <= au <= mu /\ mu + kUserMapSize <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ mu < total /\ total <= mu + kUserMapSize.
  Hypothesis INST : rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb); C4 (wz 0xffffffff)].
  Hypothesis PMH : rw_cells asegs m (AINST + 56) [C8 (wz 0)].
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis DPM : rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)].

  Theorem pop_map_seg1 :
    evt asegs (pop_map_seg1_post ra sp gp tp t0 t1 t2 s0 s1 a6 (wz csz) s7 s8 s9 s10 s11 t3 t4 t5 t6 s2 s3 s4 s5 s6 F fc m lo R stat rbeg mu total)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz stat) (wz AINST) (wz (Z.shiftl c 32)) a2 (wz au) a4 a5 a6 a7
               (wz rbeg) (wz total) (wz mu) (wz csz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c254) fc None m (seg_rom asegs)).
  Proof.
    apply rw_cells_C8_zero_bytes in PMH.
    unfold rinfo_cells, AHI_LO, kSpaceSize, kUserMapSize, kFreeArrayOffset, AINST, OI_SPACEBEG, AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS in *.
    cbn [map] in GOT. change (6976152 + 32) with 6976184 in INST. change (6976152 + 56) with 6976208 in PMH. change (7586856 + 260) with 7587116 in DPM.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 464, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)) as (CS1 & CS2 & CS3 & _). fold csz in CS1, CS2, CS3.
    assert (MSF : total - mu <= pop_ms total mu < total - mu + 262144 /\ pop_ms total mu mod 262144 = 0 /\ pop_ms total mu = 262144)
      by (unfold pop_ms, round_up, kUserMapSize; clear - AUR; try acb; Z.div_mod_to_equations; lia).
    unfold wz in *. rewrite (Z.shiftl_mul_pow2 c 32) by (clear; lia).
    assert (CONT : forall xa1 : word,
      evt asegs (pop_map_seg1_post ra sp gp tp t0 t1 t2 s0 s1 a6 (Z_to_bv 64 csz) s7 s8 s9 s10 s11 t3 t4 t5 t6 s2 s3 s4 s5 s6 F fc m lo R stat rbeg mu total)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 stat) (Z_to_bv 64 6976152) xa1 a2 (Z_to_bv 64 au) a4 a5 a6 a7
                 (Z_to_bv 64 rbeg) (Z_to_bv 64 total) (Z_to_bv 64 mu) (Z_to_bv 64 csz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x19c258) fc None m (seg_rom asegs))).
    { intros xa1.
      (* [comment removed for export] *)
      step. step. step. step. step. step. step.
      match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709289472 + 262144)] => replace (Z.land x 18446744073709289472 + 262144) with (pop_ms total mu) end.
      2:{ rewrite (unsigned_lit mu) by (clear - AUR; try acb; lia). rewrite lnot_mod64 by (clear - AUR; try acb; lia). unfold Z.lnot.
          rewrite Z_to_bv_unsigned. change (bv_wrap 64 ?y) with (y mod 2^64).
          change 18446744073709289472 with (2^64 - 2^18)%Z. rewrite StrFun.land_align_down by (clear - AUR; try acb; Z.div_mod_to_equations; lia).
          destruct MSF as (M1 & M2 & M3). rewrite M3. clear - AUR M1; try acb. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      step. step. step. step. step. step. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit by (clear - AUR MSF; try acb; lia). clear - AUR MSF; try acb. lia. } clear K2.
      (* [comment removed for export] *)
      step. rewrite zxb_b8 by lia. step. step. if_cases K2; zify_cond K2. 2:{ deadK K2. } clear K2.
      (* [comment removed for export] *)
      step. step. step. step. step. replace (mu + rbeg) with (rbeg + mu) by (clear; lia).
      step. callD (map_or_die_seg1 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo (rbeg + mu) (pop_ms total mu) 161732) dropping ST.
      all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia).
      all: try (subst rbeg; clear - SBR AUR MSF HC; try acb; lia).
      replace (bv_unsigned sp + -64 + -128) with (bv_unsigned sp + -192) in * by lia.
      apply evt_done. unfold pop_map_seg1_post. cbv zeta. exists x, x0. unfold wz, AINST, APAGESZ.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact PC|]. split; [exact POST| exact F64]. }
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    - rewrite ?unsigned_lit in K by (clear - AUR; try acb; lia).
      step. step. if_cases K2; zify_cond K2. 2:{ deadK K2. } clear K2. step. step. rewrite <- K. apply CONT.
    - apply CONT.
  Qed.
End MapSeg1.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_map_seg2_post (ra sp gp tp s7 s8 s9 s10 s11 : word) (fs0 fs1 fs2 fs3 fs4 fs5 fs6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R TH rbeg beg ms csz nf mfa au mu' : Z) (q0 q1 q2 : word) : machine_state -> Prop :=
  fun ms' => exists (rax t0 t1 t2 x1 y1 y2 y4 y5 y6 y7 x3 x6 t3 t4 t5 t6 q3 : word) m',
    ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) x1 (wz AINST) y1 y2 (wz au) y4 y5 y6 y7
                  (wz rbeg) x3 (wz mu') (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c328) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 224, bv_unsigned sp + -64); (sh beg, sh beg + ms / 8); (TH + 2792, TH + 3168); (R + 48, R + 56)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [C8 fs6; C8 fs5; C8 fs4; C8 fs3; C8 fs2; C8 fs1; C8 fs0; C8 ra]
    /\ rw_cells asegs m' R (rinfo_cells nf mfa au mu')
    /\ poisoned m' beg (Z.to_nat (ms / 8)) 0xfa
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
End HCW3.

Section MapSeg2.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R stat TH rbeg mu ms csz nf mfa au TSD CTX : Z) (j44 sbs : list byte) (q0 q1 q2 q3 : word).
  Let beg := rbeg + mu.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -192).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 464 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47. Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis F192 : rw_cells asegs m (bv_unsigned sp + -192) [C4 (wz 50); CB 44 j44; C8 (wz beg); C8 (wz ms); C8 (wz rbeg); C8 (wz beg); C8 (wz ms); C8 (wz 0x1dcd98);
                                                             C8 (wz rbeg); C8 (wz stat); C8 (wz R); C8 (wz 0x19c2d4)].
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis STAT : stat = TH + 2768.
  Hypothesis BEG : AHI_LO <= beg /\ beg + ms <= aceil /\ beg mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ 0 <= mu /\ mu + ms < 2^47.
  Hypothesis TPR : 4096 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0.
  Hypothesis SEP : hidden ((TH + 4096 <= R \/ R + 128 <= TH) /\ (TH + 4096 <= beg \/ beg + ms <= TH) /\ (R + 128 <= beg \/ beg + ms <= R)
                           /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis QST : rw_cells asegs m (TH + 2768) [C8 q0; C8 q1; C8 q2; C8 q3].
  Hypothesis SH : u8arr asegs m (sh beg) sbs. Hypothesis SHL : Z.of_nat (length sbs) = ms / 8.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].
  Hypothesis CTHR : rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)].
  Hypothesis CCAN : rw_cells asegs m ACANPOISON [C1 (b8 1)].
  Hypothesis CSHB : rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
  Hypothesis CHME : rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
  Hypothesis CRMS : rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)].
  Hypothesis CTSDI : rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].
  Hypothesis CTP : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)].
  Hypothesis CTSD : rw_cells asegs m TSD [C8 (wz CTX)].
  Hypothesis CCTX : rw_cells asegs m (CTX + 152) [C8 (wz TH)].

  Theorem pop_map_seg2 :
    evt asegs (pop_map_seg2_post ra sp gp tp s7 s8 s9 s10 s11 s0 s1 s2 s3 s4 s5 s6 F fc m lo R TH rbeg beg ms csz nf mfa au (mu + ms) q0 q1 q2)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -192)) gp tp t0 t1 t2 (wz ms) (wz 1) (wz beg) (wz ms) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
               (wz beg) (wz 0x277c4) (wz APAGESZ) (wz csz) (wz AINST) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    unfold rinfo_cells, AHI_LO, AIMG_TOP, AGOT_LO, AGOT_VALS, APAGESZ, ACFLAGS, ACANPOISON, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, AREALMEMSET, AMEMSET, ATSDINIT, AINST in *.
    cbn [map] in GOT. change (7586856 + 144) with 7587000 in MLIM. change (7586856 + 120) with 7586976 in CTHR.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof SEP as SEPx. destruct SEPx as [SEPx]. subst stat.
    pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp + -64); (sh beg, sh beg + ms / 8); (TH + 2792, TH + 3168); (R + 48, R + 56)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (SHR : 2148314624 <= sh beg /\ sh beg + ms / 8 <= 17594333495296) by (clear - BEG; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    callD (map_seg2 (wz 0x19c2d4) gp tp t0 t1 t2 (wz R) (wz (TH + 2768)) (wz ms) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222) (wz rbeg) (wz ms) (wz beg) (wz csz) (wz 6976152) s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (bv_unsigned sp + -192) lo beg ms) dropping F192.
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia); try (clear - BEG; try acb; lia); try (clear - SPT; try acb; lia); try (clear - SPA; try acb; Z.div_mod_to_equations; lia).
    clear ST. rename POST into ST. replace (bv_unsigned sp + -192 + 128) with (bv_unsigned sp + -64) in * by lia.
    replace (ret_pc (wz 1688276)) with (Z_to_bv 64 1688276) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    unfold wz. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. clear - BEG; try acb. lia. } clear K.
    step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. } clear K.
    step. step. step. step.
    (* [comment removed for export] *)
    pose proof (aapp_lit _ _ (proj1 (proj2 (proj2 RNG)))) as CTXS.
    pose proof (akobj_lit _ _ (proj1 (proj2 (proj2 (proj2 (proj2 RNG)))))) as THS.
    callD (poison_shadow_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo beg ms 250 sbs) dropping SH ST.
    all: rewrite ?unsigned_lit by lia. all: try reflexivity; try eassumption.
    all: try (unfold AHI_LO, ALOWSH_LO; acb; clear - BEG RR; try acb; lia).
    all: try (clear - HI; try acb; lia). all: try (clear; lia).
    all: try (unfold ACANPOISON, AGOT_LO, AGOT_VALS, ASHBASE_CELL, ASHADOW_BASE, AHIGHMEMEND, ACFLAGS, AREALMEMSET, AMEMSET, wz; cbn [map]; eassumption).
    rename PC into ST. destruct POST as (P0 & P8 & PU). remember (poison_bytes (Z.to_nat (ms / 8)) 250) as pb eqn:EPB.
    assert (LPB : Z.of_nat (length pb) = ms / 8) by (subst pb; unfold poison_bytes; rewrite repeat_length; clear - BEG; try acb; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    step. callD (getcurthreadstats_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo TSD CTX TH) dropping ST.
    all: rewrite ?unsigned_lit by lia. all: try eassumption.
    all: try (clear - HI; try acb; lia). all: try (clear - TPR; try acb; unfold AIMG_TOP; lia). all: try (acb; clear - RNG; try acb; aunf; lia).
    all: try (unfold ATSDINIT, wz; eassumption).
    rename POST into ST. unfold wz. clear CTXS.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (TH + 2872) _ TST ltac:(hci; clear; lia)) as [TS1 TS2].
    destruct (stk_split asegs _ _ (TH + 2888) _ TS2 ltac:(hci; clear; lia)) as [TS3 TS4]. clear TS2 TST.
    destruct (stk_cells _ _ _ TS3 ltac:(hci; clear; lia)) as [jst JST]. clear TS3.
    replace (TH + 2888 - (TH + 2872)) with 16 in JST by (clear; lia). change (Z.to_nat 16) with 16%nat in JST.
    apply (rw_cells_split_CB asegs _ _ [] 16 jst [] [8;8]%nat) in JST; [| reflexivity]. cbn [mk_CB_cells app] in JST.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    assert (AL8 : (TH + 2792) mod 8 = 0) by (clear - RNG; try acb; Z.div_mod_to_equations; aunf; lia).
    assert (ALR : 0 <= TH + 2792 < 2^64) by (clear - RNG; try acb; aunf; lia).
    replace (TH + 2768 + 24) with (TH + 2792) by (clear; lia).
    astep.
    (* [comment removed for export] *)
    step. step. step. step.
    pose proof (stk_of_rw_cells asegs _ _ _ JST) as TS2. cbn [cells_size csize Nat.add] in TS2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (TSTn : stk asegs mm (TH + 2800) (TH + 3168))
      by (eapply stk_merge; [exact TS1| |clear; lia]; eapply stk_merge; [| exact TS4| clear; lia];
          replace (TH + 2888) with (TH + 2872 + Z.of_nat 16) by (clear; lia); exact TS2) end.
    apply evt_done. unfold pop_map_seg2_post. do 18 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact F64|].
    split; [exact RI|]. split; [| split; [exact TSTn| exact QST]]. unfold poisoned, SHAD. subst pb. split; [exact P0|]. split; [exact P8|]. exact PU.
  Qed.
End MapSeg2.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_mid_post (sp gp tp s7 s8 s9 s10 s11 : word) (fs : list cell) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R rbeg csz au mu n nf : Z) : machine_state -> Prop :=
  fun ms' => exists (rax t0 t1 t2 y1 y2 y3 y4 y5 y6 y7 x6 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + n)) (wz 1) y1 y2 y3 y4 y5 y6 y7
                  (wz rbeg) (wz n) (wz (mu - au)) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c348) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp + -64)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) fs.
End HCW3.

Section MidFast.
  Context {HCEIL : HeapCeil}.
  Variables (rax sp gp tp t0 t1 t2 x1 a0 a1 a2 a4 a5 a6 a7 x3 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg csz au mu nf mfa : Z) (fs : list cell).
  Let n := (mu - au) / csz.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -64).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 432 <= bv_unsigned sp.
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) fs. Hypothesis FSL : cells_size fs = 64%nat.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis CSZ : 32 <= csz <= 65536. Hypothesis AUR : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ 0 <= nf /\ 4 * (nf + n) <= mfa /\ mfa <= kFreeArraySize.
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).

  Theorem pop_mid_fast :
    evt asegs (pop_mid_post sp gp tp s7 s8 s9 s10 s11 fs F fc m lo R rbeg csz au mu n nf)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) x1 a0 a1 a2 (wz au) a4 a5 a6 a7
               (wz rbeg) x3 (wz mu) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c328) fc None m (seg_rom asegs)).
  Proof.
    unfold rinfo_cells, AHI_LO, kFreeArrayOffset, kFreeArraySize in *.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR. acb.
    pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp + -64)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NR : 0 <= n <= mu - au) by (subst n; clear - CSZ AUR; try acb; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia || (Z.div_mod_to_equations; (first [clear - AUR CSZ; nia | nia]))]).
    unfold wz in *.
    (* [comment removed for export] *)
    step. step. step. (* [comment removed for export] *)
    rewrite (unsigned_lit mu), (unsigned_lit au) by (clear - AUR; try acb; lia).
    replace (mul_div M_DIVU (Z_to_bv 64 (mu - au)) (Z_to_bv 64 csz)) with (Z_to_bv 64 n).
    2:{ unfold mul_div. cbn [bv_unsigned Z_to_bv]. rewrite (unsigned_lit csz) by (clear - CSZ; try acb; lia).
        replace (csz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - CSZ; try acb; lia).
        apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit by (clear - CSZ AUR NR; try acb; lia). reflexivity. }
    (* [comment removed for export] *)
    step. step. step. step. step.
    callD (efs_fast_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo R (nf + n) nf mfa au mu) dropping ST.
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia); try (clear - AUR NR; try acb; lia).
    { unfold kFreeArraySize. clear - AUR NR; try acb. lia. }
    lazymatch goal with H : stk asegs ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STn end.
    apply evt_done. unfold pop_mid_post. do 16 eexists. eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact STn| eassumption].
  Qed.
End MidFast.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_mid_map_post (sp gp tp t0 t1 t2 a6 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fs : list cell) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R rbeg csz au mu n nf mfa : Z) : machine_state -> Prop :=
  fun ms' => exists m' (j8 j44 : list byte),
    let cur := rbeg + kFreeArrayOffset + mfa in let sz := efs_new (nf + n) - mfa in
    ms' = MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0 t1 t2 (wz sz) (wz 1) (wz cur) (wz sz) (wz 3) (wz 50) (Z_to_bv 64 (-1)) (wz 0) a6 (wz 222)
                  (wz cur) (wz 0x2cd48) (wz APAGESZ) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x1d1904) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 512, bv_unsigned sp + -64)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -240)
    /\ rw_cells asegs m' (bv_unsigned sp + -240) [C4 (wz 50); CB 44 j44; C8 (wz (mu - au)); C8 (wz R); C8 (wz sz); C8 (wz cur); C8 (wz sz); C8 (wz 0x1dcd98);
                                                  C8 (wz sz); C8 (wz cur); C8 (wz (efs_new (nf + n))); C8 (wz 0x199f18)]
    /\ rw_cells asegs m' (bv_unsigned sp + -112) [CB 8 j8; C8 (wz n); C8 (wz rbeg); C8 (wz (nf + n)); C8 (wz R); C8 (wz 0x19c348)]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) fs.
End HCW3.

Section MidMap.
  Context {HCEIL : HeapCeil}.
  Variables (rax sp gp tp t0 t1 t2 x1 a1 a2 a4 a5 a6 a7 x3 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg csz au mu nf mfa : Z) (fs : list cell).
  Let n := (mu - au) / csz.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -64).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 512 <= bv_unsigned sp.
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) fs. Hypothesis FSL : cells_size fs = 64%nat.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis RB : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0.
  Hypothesis CSZ : 32 <= csz <= 65536.
  Hypothesis AUR : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ 0 <= nf /\ mfa < 4 * (nf + n) /\ 4 * (nf + n) <= kFreeArraySize /\ 0 <= mfa /\ mfa mod kFreeArrayMapSize = 0.
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis PMH : rw_cells asegs m (AINST + 56) [C8 (wz 0)].
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis PSC : rw_cells asegs m APAGESZ [C8 (wz 4096)].
  Hypothesis DPM : rw_cells asegs m (ACFLAGS + 260) [C1 (b8 0)].

  Theorem pop_mid_map :
    evt asegs (pop_mid_map_post sp gp tp t0 t1 t2 a6 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 fs F fc m lo R rbeg csz au mu n nf mfa)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) x1 (wz AINST) a1 a2 (wz au) a4 a5 a6 a7
               (wz rbeg) x3 (wz mu) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c328) fc None m (seg_rom asegs)).
  Proof.
    unfold kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in AUR.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RR as RRx. pose proof RB as RBx. unfold AHI_LO in RRx, RBx. acb.
    pose proof (munch_refl [(bv_unsigned sp - 512, bv_unsigned sp + -64)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NR : 0 <= n <= mu - au) by (subst n; clear - CSZ AUR; try acb; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia || (Z.div_mod_to_equations; (first [clear - AUR CSZ; nia | nia]))]).
    unfold wz in *.
    (* [comment removed for export] *)
    pose proof RI as RIx. unfold rinfo_cells in RIx.
    step. step. step.
    rewrite (unsigned_lit mu), (unsigned_lit au) by (clear - AUR; try acb; lia).
    replace (mul_div M_DIVU (Z_to_bv 64 (mu - au)) (Z_to_bv 64 csz)) with (Z_to_bv 64 n).
    2:{ unfold mul_div. cbn [bv_unsigned Z_to_bv]. rewrite (unsigned_lit csz) by (clear - CSZ; try acb; lia).
        replace (csz =? 0) with false by (symmetry; apply Z.eqb_neq; clear - CSZ; try acb; lia).
        apply bv_eq. rewrite bv_divu_unsigned, !unsigned_lit by (clear - CSZ AUR NR; try acb; lia). reflexivity. }
    (* [comment removed for export] *)
    step. step. step. step. step.
    callD (efs_seg1 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo R rbeg (nf + n) nf mfa au mu) dropping DPM PSC GOT PMH RI ST.
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity; try (clear - HI; try acb; lia).
    { unfold kFreeArraySize, kFreeArrayMapSize. clear - AUR NR; try acb. lia. }
    replace (bv_unsigned sp + -64 + -176) with (bv_unsigned sp + -240) in * by lia.
    replace (bv_unsigned sp + -64 + -48) with (bv_unsigned sp + -112) in * by lia.
    replace (bv_unsigned sp + -64 - 448) with (bv_unsigned sp - 512) in * by lia.
    lazymatch goal with H : stk asegs ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STn end.
    apply evt_done. unfold pop_mid_map_post. cbv zeta. do 3 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STn|].
    split; [eassumption|]. split; [eassumption| exact F64].
  Qed.
End MidMap.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_mid_map2_post (sp gp tp x6 s7 s8 s9 s10 s11 : word) (fs : list cell) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R TH rbeg csz au mu n nf cur sz newfa : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x19c348) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + n)) (wz 1) a1 a2 a3 a4 a5 a6 a7
                  (wz rbeg) (wz n) (wz (mu - au)) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c348) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 272, bv_unsigned sp + -64); (sh cur, sh cur + sz / 8); (TH + 2800, TH + 3168); (R + 24, R + 32)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -64)
    /\ rw_cells asegs m' R (rinfo_cells nf newfa au mu)
    /\ poisoned m' cur (Z.to_nat (sz / 8)) 0xfa
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ rw_cells asegs m' (bv_unsigned sp + -64) fs.
End HCW3.

Section MidMap2.
  Context {HCEIL : HeapCeil}.
  Variables (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg csz au mu n nf mfa cur sz newfa TSD CTX TH : Z) (j8 j44 sbs : list byte) (fs : list cell).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -240).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 512 <= bv_unsigned sp. Hypothesis SPT : bv_unsigned sp + 16 <= 2^47. Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis F176 : rw_cells asegs m (bv_unsigned sp + -240) [C4 (wz 50); CB 44 j44; C8 (wz (mu - au)); C8 (wz R); C8 (wz sz); C8 (wz cur); C8 (wz sz); C8 (wz 0x1dcd98);
                                                             C8 (wz sz); C8 (wz cur); C8 (wz newfa); C8 (wz 0x199f18)].
  Hypothesis F48 : rw_cells asegs m (bv_unsigned sp + -112) [CB 8 j8; C8 (wz n); C8 (wz rbeg); C8 (wz (nf + n)); C8 (wz R); C8 (wz 0x19c348)].
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) fs. Hypothesis FSL : cells_size fs = 64%nat.
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis CUR : AHI_LO <= cur /\ cur + sz <= aceil /\ cur mod 4096 = 0 /\ sz mod 4096 = 0 /\ 0 < sz /\ 0 <= newfa < 2^64.
  Hypothesis TPR : 4096 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP.
  Hypothesis RNG : 12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil.
  Hypothesis SEP : hidden ((TH + 4096 <= R \/ R + 128 <= TH) /\ (TH + 4096 <= cur \/ cur + sz <= TH) /\ (R + 128 <= cur \/ cur + sz <= R)).
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis TST : stk asegs m (TH + 2800) (TH + 3168).
  Hypothesis SH : u8arr asegs m (sh cur) sbs. Hypothesis SHL : Z.of_nat (length sbs) = sz / 8.
  Hypothesis GOT : rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS).
  Hypothesis MLIM : rw_cells asegs m (ACFLAGS + 144) [C8 (wz 0)].
  Hypothesis CTHR : rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)].
  Hypothesis CCAN : rw_cells asegs m ACANPOISON [C1 (b8 1)].
  Hypothesis CSHB : rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)].
  Hypothesis CHME : rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)].
  Hypothesis CRMS : rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)].
  Hypothesis CTSDI : rw_cells asegs m ATSDINIT [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)].
  Hypothesis CTP : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)].
  Hypothesis CTSD : rw_cells asegs m TSD [C8 (wz CTX)].
  Hypothesis CCTX : rw_cells asegs m (CTX + 152) [C8 (wz TH)].

  Theorem pop_mid_map2 :
    evt asegs (pop_mid_map2_post sp gp tp x6 s7 s8 s9 s10 s11 fs F fc m lo R TH rbeg csz au mu n nf cur sz newfa)
      (MS (mkR (wz 0x1d36d8) (Z_to_bv 64 (bv_unsigned sp + -240)) gp tp t0 t1 t2 (wz sz) (wz 1) (wz cur) a1 a2 a3 a4 a5 a6 a7
               (wz cur) (wz 0x2cd48) (wz APAGESZ) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1d1908) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RR as RRx. pose proof CUR as CURx. pose proof RNG as RNGx. unfold AHI_LO, AIMG_TOP in RRx, CURx, RNGx.
    acb.
    assert (SHR : 2148314624 <= sh cur /\ sh cur + sz / 8 <= 17594333495296) by (clear - CURx; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp - 64) by (apply unsigned_lit; clear - SPR HI LO; try acb; lia).
    remember (Z_to_bv 64 (bv_unsigned sp + -64)) as sp' eqn:Esp'.
    replace (bv_unsigned sp + -240) with (bv_unsigned sp' + -176) in * by (clear - ESP; try acb; lia).
    replace (bv_unsigned sp + -112) with (bv_unsigned sp' + -48) in * by (clear - ESP; try acb; lia).
    replace (bv_unsigned sp + -64) with (bv_unsigned sp') in F64 by (clear - ESP; try acb; lia).
    assert (HI' : lo + 448 <= bv_unsigned sp') by (clear - HI ESP; try acb; lia).
    assert (SPT' : bv_unsigned sp' + 16 <= 2^47) by (clear - SPT ESP; try acb; lia).
    assert (SPA' : bv_unsigned sp' mod 16 = 0) by (clear - SPA ESP SPR HI LO; try acb; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp' - 208, bv_unsigned sp'); (sh cur, sh cur + sz / 8); (TH + 2800, TH + 3168); (R + 24, R + 32)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    clear HI SPT SPA. unfold wz in *.
    callD (efs_seg2 (Z_to_bv 64 0x19c348) sp' gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 (nf + n)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 rbeg) (Z_to_bv 64 n) (Z_to_bv 64 (mu - au)) (Z_to_bv 64 csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6
                    F fc m lo R cur sz newfa nf mfa au mu TSD CTX TH j8 j44 sbs) dropping CCTX CTSD CTP CTSDI CRMS CHME CSHB CCAN CTHR MLIM GOT RI F48 F176 SH TST ST.
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try reflexivity.
    all: try (unfold wz in *; eassumption).
    lazymatch goal with H : stk asegs ?mm lo _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into STn end.
    apply evt_done. unfold pop_mid_map2_post. do 14 eexists. eexists.
    rewrite <- Esp'. replace (bv_unsigned sp + -64) with (bv_unsigned sp') by (clear - ESP; try acb; lia).
    replace (bv_unsigned sp - 272) with (bv_unsigned sp' - 208) by (clear - ESP; try acb; lia).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STn|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. exact F64.
  Qed.
End MidMap2.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_cons : forall m A w ws,
  u32arr asegs m A (w :: ws) <-> rw_cells asegs m A [C4 w] /\ u32arr asegs m (A + 4) ws.
Proof.
  intros m A w ws. unfold u32arr, rw_cells, cells_at. cbn [u32s map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app length].
  rewrite app_nil_r. change (le4 w ++ u32s ws) with (le4 w ++ u32s ws). rewrite bytes_at_app, length_le4.
  change (Z.of_nat 4) with 4. change (Z.of_nat (4 + 0)) with 4.
  replace (4 * Z.of_nat (S (length ws))) with (4 + 4 * Z.of_nat (length ws)) by lia.
  rewrite wr_at_app by lia. tauto.
Qed.

Lemma u32arr_nil : forall m A, 0 <= A <= 2^64 -> u32arr asegs m A [].
Proof.
  intros mq A HA. split; [apply bytes_at_nil; exact HA|]. cbn [length Z.of_nat Z.mul u32s]. unfold wr_at.
  split; [lia|]. split; [lia|]. intros i Hi. exfalso. lia.
Qed.

Lemma carve_asc_snoc : forall b s k j,
  carve_asc b s j (S k) = carve_asc b s j k ++ [Z.shiftr (b + (j + Z.of_nat k) * s) kCompactPtrScale].
Proof.
  intros b s k. induction k as [|k IH]; intros j.
  - cbn. rewrite Z.add_0_r. reflexivity.
  - change (carve_asc b s j (S (S k))) with (Z.shiftr (b + j * s) kCompactPtrScale :: carve_asc b s (j + 1) (S k)).
    rewrite (IH (j + 1)). cbn [carve_asc app]. replace (j + 1 + Z.of_nat k) with (j + Z.of_nat (S k)) by lia. reflexivity.
Qed.

Lemma carve_asc_length : forall b s k j, length (carve_asc b s j k) = k.
Proof. intros b s k. induction k as [|k IH]; intros j; cbn; [reflexivity| now rewrite IH]. Qed.

Definition carve_post (rax sp gp tp t0 t1 t2 s0 s1 a1 a3 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (E au csz n : Z) : machine_state -> Prop :=
  fun ms' => exists (a4 a5 : word) m',
    ms' = MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (wz n) a1 (wz (au + n * csz)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19c390) fc None m' (seg_rom asegs)
    /\ munch [(E - 4 * n, E)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ u32arr asegs m' (E - 4 * n) (wlist (rev (carve_asc au csz 0 (Z.to_nat n)))).
End HCW3.

Section CarveLoop.
  Context {HCEIL : HeapCeil}.
  Variables (rax sp gp tp t0 t1 t2 s0 s1 a3 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (E au csz n : Z).
  Hypothesis ER : AHI_LO <= E - 4 * n /\ E <= aceil /\ E mod 4 = 0.
  Hypothesis NR : 0 < n. Hypothesis CSZ : 32 <= csz <= 65536. Hypothesis AUR : 0 <= au /\ au + n * csz <= kFreeArrayOffset.

  Lemma carve_loop : forall (k : nat) (i ca : Z) (a4 a5 : word) (m1 : mem),
    Z.to_nat (n - i) = k -> 0 <= i < n -> ca = au + i * csz ->
    mem_inv asegs m1 -> munch [(E - 4 * n, E)]%Z m m1 -> wmono asegs m m1 ->
    stk asegs m1 (E - 4 * n) (E - 4 * i) ->
    u32arr asegs m1 (E - 4 * i) (wlist (rev (carve_asc au csz 0 (Z.to_nat i)))) ->
    evt asegs (carve_post rax sp gp tp t0 t1 t2 s0 s1 (wz E) a3 a6 a7 s2 (wz n) s4 (wz csz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m E au csz n)
      (MS (mkR rax sp gp tp t0 t1 t2 s0 s1 (wz i) (wz E) (wz ca) a3 a4 a5 a6 a7 s2 (wz n) s4 (wz csz) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c370) fc None m1 (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kFreeArrayOffset in *. acb.
    induction k as [|k IH]; intros i ca a4 a5 m1 HK HI Hca MI1 MU1 WM1 JK ARR. { exfalso. clear - HK HI; try acb. lia. } subst ca.
    assert (IR : 0 <= au + i * csz /\ au + i * csz + csz <= 3758096384) by (clear - HI CSZ AUR; try acb; nia).
    unfold wz.
    (* [comment removed for export] *)
    step. step. step. step. step.
    rewrite (unsigned_lit i) by (clear - HI ER NR; try acb; lia). rewrite zb_lxor_ones by (clear - HI ER NR; try acb; lia).
    rewrite (unsigned_lit (18446744073709551615 - i)) by (clear - HI ER NR; try acb; lia).
    rewrite (unsigned_lit (au + i * csz)) by (clear - IR CSZ; try acb; lia).
    replace (Z_to_bv 64 (E + Z.shiftl (18446744073709551615 - i) 2)) with (Z_to_bv 64 (E - 4 * i - 4)).
    2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.shiftl_mul_pow2 by lia.
        replace (E + (18446744073709551615 - i) * 2^2) with (E - 4 * i - 4 + 4 * 2^64) by lia. rewrite Z_mod_plus_full. reflexivity. }
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (E - 4 * i - 4) _ JK ltac:(hci; clear -HI; lia)) as [SK1 SK2]. clear JK.
    destruct (stk_cells _ _ _ SK2 ltac:(hci; clear; lia)) as [jw JW]. clear SK2.
    replace (E - 4 * i - (E - 4 * i - 4)) with 4 in JW by lia. change (Z.to_nat 4) with 4%nat in JW.
    (* [comment removed for export] *)
    step. step. step.
    (* [comment removed for export] *)
    assert (ARR' : u32arr asegs m0 (E - 4 * (i + 1)) (wlist (rev (carve_asc au csz 0 (Z.to_nat (i + 1)))))).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HI; try acb; lia). rewrite carve_asc_snoc, rev_app_distr. cbn [rev app wlist map].
      apply u32arr_cons. replace (E - 4 * (i + 1) + 4) with (E - 4 * i) by lia. split; [| exact ARR].
      replace (E - 4 * (i + 1)) with (E - 4 * i - 4) by lia. unfold wz, kCompactPtrScale.
      replace (0 + Z.of_nat (Z.to_nat i)) with i by (clear - HI; try acb; lia). exact JW. }
    clear ARR JW.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (au + i * csz + csz) with (au + (i + 1) * csz) by (clear; lia).
      eapply (IH (i + 1)); try eassumption. { clear - HK HI K; try acb; lia. } { revert K. rewrite ?unsigned_lit by (clear - HI NR ER; try acb; lia). clear - HI; try acb. intros K. lia. } { reflexivity. }
      replace (E - 4 * (i + 1)) with (E - 4 * i - 4) by lia. exact SK1.
    - (* [comment removed for export] *)
      assert (i + 1 = n) as EQ by (revert K; rewrite ?unsigned_lit by (clear - HI NR ER; try acb; lia); clear - HI; try acb; intros K; lia).
      replace (au + i * csz + csz) with (au + (i + 1) * csz) by (clear; lia). rewrite EQ in ARR' |- *.
      apply evt_done. unfold carve_post. do 3 eexists.
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. exact ARR'.
  Qed.
End CarveLoop.
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pop_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo R FAnf au csz mu n nf mfa : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (FAnf, FAnf + 4 * n); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' R (rinfo_cells (nf + n) mfa (au + n * csz) mu)
    /\ rw_cells asegs m' (R + 68) [C1 (b8 0)]
    /\ u32arr asegs m' FAnf (wlist (rev (carve_asc au csz 0 (Z.to_nat n)))).
End HCW3.

Section Tail.
  Context {HCEIL : HeapCeil}.
  Variables (rax ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (ex : byte)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo R rbeg csz au mu nf mfa : Z).
  Let n := (mu - au) / csz.
  Let FAnf := rbeg + kFreeArrayOffset + 4 * nf.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp + -64).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 64 <= bv_unsigned sp.
  Hypothesis F64 : rw_cells asegs m (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RR : AHI_LO <= R /\ R + 128 <= aceil.
  Hypothesis RB : AHI_LO <= rbeg /\ rbeg + 2^32 <= aceil /\ rbeg mod 65536 = 0.
  Hypothesis CSZ : 32 <= csz <= 65536.
  Hypothesis AUR : 0 <= au /\ au + csz <= mu /\ mu <= kFreeArrayOffset /\ 0 <= nf /\ 4 * (nf + n) <= mfa /\ mfa <= kFreeArraySize.
  Hypothesis SEP : hidden (R + 128 <= rbeg \/ rbeg + 2^32 <= R).
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis EXH : rw_cells asegs m (R + 68) [C1 ex].
  Hypothesis JK : stk asegs m FAnf (FAnf + 4 * n).

  Theorem pop_tail :
    evt asegs (pop_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo R FAnf au csz mu n nf mfa)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz R) (wz (nf + n)) (wz 1) a1 a2 a3 a4 a5 a6 a7
               (wz rbeg) (wz n) (wz (mu - au)) (wz csz) x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19c348) fc None m (seg_rom asegs)).
  Proof.
    unfold kFreeArrayOffset, kFreeArraySize in AUR. subst FAnf. unfold kFreeArrayOffset.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    pose proof RR as RRx. pose proof RB as RBx. unfold AHI_LO in RRx, RBx. acb.
    pose proof SEP as SEPx. destruct SEPx as [SEPx].
    assert (NR : 1 <= n <= mu - au /\ n * csz <= mu - au)
      by (subst n; clear - CSZ AUR; try acb; split; [split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; [lia| nia]]| Z.div_mod_to_equations; nia]).
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (rbeg + 3758096384 + 4 * nf, rbeg + 3758096384 + 4 * nf + 4 * n); (R + 16, R + 24); (R + 32, R + 40); (R + 68, R + 69)]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    pose proof RI as RIx. unfold rinfo_cells in RIx. clear RI.
    unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - AUR; try acb; lia). clear - NR CSZ AUR; try acb. nia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    rewrite (unsigned_lit (nf + n)) by (clear - AUR NR; try acb; lia). rewrite (Z.shiftl_mul_pow2 (nf + n) 2) by (clear; lia). change (2^2) with 4.
    unfold kFreeArrayOffset in JK. set (E := rbeg + 3758096384 + 4 * nf + 4 * n) in *.
    replace (rbeg + 3758096384 + (nf + n) * 4) with E by (subst E; clear; lia).
    replace (rbeg + 3758096384 + 4 * nf) with (E - 4 * n) in MU by (subst E; clear; lia).
    replace (rbeg + 3758096384 + 4 * nf) with (E - 4 * n) in JK by (subst E; clear; lia).
    (* [comment removed for export] *)
    assert (ERf : AHI_LO <= E - 4 * n /\ E <= aceil /\ E mod 4 = 0)
      by (subst E; unfold AHI_LO; acb; clear - RBx AUR NR; try acb; Z.div_mod_to_equations; lia).
    assert (NRf : 0 < n) by (clear - NR; try acb; lia).
    assert (AURf : 0 <= au /\ au + n * csz <= kFreeArrayOffset) by (unfold kFreeArrayOffset; clear - AUR NR; try acb; lia).
    assert (ARR0 : u32arr asegs m (E - 4 * 0) (wlist (rev (carve_asc au csz 0 (Z.to_nat 0)))))
      by (replace (E - 4 * 0) with E by (clear; lia); apply u32arr_nil; destruct JK as (J0 & J1 & _); clear - J0 J1 NR; try acb; lia).
    pose proof (munch_refl [(E - 4 * n, E)]%Z m) as MU0.
    replace E with (E - 4 * 0) in JK at 2 by (clear; lia).
    callD (carve_loop rax _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m E au csz n ERf NRf CSZ AURf (Z.to_nat n) 0 au _ _ m ltac:(hci; rewrite Z.sub_0_r; reflexivity) ltac:(hci; clear - NR; try acb; lia) ltac:(hci; clear; lia) MI MU0 WM JK ARR0) dropping JK.
    clear ARR0 MU0. rename POST into ARR. unfold wz in *.
    assert (EE : E = rbeg + 3758096384 + 4 * nf + 4 * n) by reflexivity. clearbody E.
    assert (NE : n = (mu - au) / csz) by reflexivity. clearbody n.
    assert (PR : csz <= n * csz <= mu - au) by (clear - NR AUR CSZ; try acb; (first [clear - NR CSZ; nia | nia])).
    remember (wlist (rev (carve_asc au csz 0 (Z.to_nat n)))) as ws eqn:Ews.
    assert (LWS : length ws = Z.to_nat n) by (subst ws; unfold wlist; rewrite length_map, length_rev, carve_asc_length; reflexivity).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step.
    rewrite ?unsigned_lit by (clear - AUR PR NR; try acb; aunf; lia).
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    { exfalso. revert K. rewrite <- ?unsigned_lit_land. rewrite ?unsigned_lit by (clear - AUR PR CSZ; try acb; aunf; lia). clear - PR AUR CSZ; try acb. intros K. lia. }
    clear K.
    (* [comment removed for export] *)
    step. step. step. if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    st1. step. step.
    (* [comment removed for export] *)
    do 8 step. step. step.
    rewrite ?unsigned_lit in RIx by (clear - NR CSZ AUR; try acb; lia).
    release_frame F64 ST (bv_unsigned sp).
    apply evt_done. unfold pop_tail_post. do 14 eexists. eexists.
    split; [reflexivity|]. replace (rbeg + 3758096384 + 4 * nf) with (E - 4 * n) by (clear - EE; try acb; lia).
    replace (E - 4 * n + 4 * n) with E by (clear; lia).
    split; [exact MU|]. split; [exact WM|]. split; [exact MI0|]. split; [exact ST|].
    split; [exact RIx|]. split; [exact EXH|]. subst ws. exact ARR.
  Qed.
End Tail.

