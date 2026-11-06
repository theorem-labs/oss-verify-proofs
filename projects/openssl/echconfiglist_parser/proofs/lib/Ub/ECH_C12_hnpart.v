(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_SR ECH_Kit ECH_Rep ECH_LibState ECH_C1_stmt ECH_C1_dup ECH_C5_stmt ECH_C12_stmt ECH_C12_ctype ECH_UbKit.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Lemma mod_small_neg : forall z M, 0 < M -> - M <= z < 0 -> z mod M = z + M.
  Proof. intros z M HM Hz. symmetry. apply (Z.mod_unique_pos z M (-1)); lia. Qed.

  Lemma hn_loop_at : forall (ns : list byte) i (b : byte) part prev,
    nth_error ns (Z.to_nat i) = Some b ->
    hn_loop (skipn (Z.to_nat i) (map bv_unsigned ns)) i part prev =
      (let c := bv_unsigned b in let cs' := skipn (S (Z.to_nat i)) (map bv_unsigned ns) in
       if c =? 46 then
         if ((part =? 0) && negb (i =? 0)) || (prev =? 45) then false else hn_loop cs' (i + 1) 0 c
       else if (part =? 0) && (c =? 45) then false
       else if negb (label_charZ c || (c =? 45)) then false
       else if 63 <? part + 1 then false
       else hn_loop cs' (i + 1) (part + 1) c).
  Proof.
    intros ns i b part prev NTH.
    rewrite (skipn_nth_cons (map bv_unsigned ns) (Z.to_nat i) (bv_unsigned b)) by (rewrite (nth_error_map bv_unsigned), NTH; reflexivity).
    reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition hn_cond (c al : Z) : Z :=
    Z.land (Z.b2z (0 <? (c + -45) mod 18446744073709551616))
      (Z.lor (Z.b2z ((c + -45) mod 18446744073709551616 <? 2))
         (Z.land (Z.b2z (0 <? (c + -95) mod 18446744073709551616))
            (Z.land (Z.b2z (al mod 18446744073709551616 <? 1)) 1))).
  Definition hn_al (c : Z) : Z := if is_alnumZ c then 1 else 0.
  Lemma hn_cond_ok : forall c, 0 <= c < 256 -> c <> 46 ->
    (hn_cond c (hn_al c) =? 0) = (label_charZ c || (c =? 45)).
  Proof.
    intros c Hc N46.
    assert (ALL : forallb (fun n => let c := Z.of_nat n in implb (negb (c =? 46)) (Bool.eqb (hn_cond c (hn_al c) =? 0) (label_charZ c || (c =? 45)))) (seq 0 256) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat c)).
    rewrite in_seq, Z2Nat.id in ALL by lia. cbv zeta in ALL.
    specialize (ALL ltac:(lia)). rewrite (proj2 (Z.eqb_neq c 46) N46) in ALL. cbn [negb implb] in ALL.
    apply Bool.eqb_prop in ALL. exact ALL.
  Qed.


  (* [comment removed for export] *)
  Lemma hn_flags_seg : forall (ra gp tp t0 t1 t2 s0 a1x a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 spw s4w s8w : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (c len name al : Z),
      0 <= c < 256 ->
      evt usegs (fun ms' => exists a2',
          ms' = MS (mkR ra spw gp tp t0 t1 t2 s0 (Z_to_bv 64 len) (Z_to_bv 64 al) (Z_to_bv 64 1) a2' a3 a4 a5 a6 a7
                       (Z_to_bv 64 name) (Z_to_bv 64 c) s4w (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45) s8w
                       (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x216930) fc None m (seg_rom usegs))
        (MS (mkR ra spw gp tp t0 t1 t2 s0 (Z_to_bv 64 len) (Z_to_bv 64 al) a1x a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 name) (Z_to_bv 64 c) s4w (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45) s8w
                 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3 t4 t5 t6)
            F (Z_to_bv 64 0x216920) fc None m (seg_rom usegs)).
  Proof.
    intros until al. intros CR.
    zstep. step. step. if_cases K0; zify_cond K0; [| step]; clear K0.
    all: apply evt_done; eexists; reflexivity.
  Qed.

  Definition HN_HEAD : Z := 0x2168dc.  Definition HN_EXIT : Z := 0x21697c.  Definition HN_EXIT0 : Z := 0x2168a8.  Definition HN_CT_RA : Z := 0x216920.

  (* [comment removed for export] *)
  Lemma hn_exit0 : forall (ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
      evt usegs (fun ms' => ms' = MS (mkR ra spw gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 HN_EXIT) fc None m (seg_rom usegs))
        (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 HN_EXIT0) fc None m (seg_rom usegs)).
  Proof. intros. unfold HN_EXIT0, HN_EXIT. step. step. apply evt_done. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma hn_loop_walk : forall (k : nat) (i part prev : Z)
      (ra sp gp tp t0 t1 t2 s0 a0 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lo : Z) (ns rest : list byte),
      Z.to_nat (Z.of_nat (length ns) - i) = k -> 0 <= i < Z.of_nat (length ns) -> Z.of_nat (length ns) <= 256 ->
      0 <= part <= 63 -> 0 <= prev < 256 ->
      bytes_at usegs m name (ns ++ rest) -> (name + Z.of_nat (length ns) + Z.of_nat (length rest) <= lo \/ bv_unsigned sp <= name) ->
      stk usegs m lo (bv_unsigned sp + -112) -> lo <= bv_unsigned sp + -128 -> 0 <= lo -> mem_inv usegs m ->
      evt usegs (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s8' t3' t4' t5' t6' : word) m',
                   ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' s0 (Z_to_bv 64 (Z.of_nat (length ns)))
                                 (Z_to_bv 64 (if hn_loop (skipn (Z.to_nat i) (map bv_unsigned ns)) i part prev then 1 else 0))
                                 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 name) s3' s4' (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45)
                                 s8' (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3' t4' t5' t6')
                            F (Z_to_bv 64 HN_EXIT) fc None m' (seg_rom usegs)
                   /\ munch [(lo, bv_unsigned sp + -112)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -112))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ns))) a0 (Z_to_bv 64 prev) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 name) s3 (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45) (Z_to_bv 64 part)
                 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3 t4 t5 t6)
            F (Z_to_bv 64 HN_HEAD) fc None m (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros until rest; intros HK HI L256 PR PV BS NLO ST LO LO0 MI; [lia|].
    unfold HN_HEAD, HN_EXIT.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB.
    pose proof (word_range sp) as SPR.
    pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    destruct (nth_error ns (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    assert (NTH' : nth_error (ns ++ rest) (Z.to_nat i) = Some b) by (rewrite nth_error_app1 by lia; exact NTH).
    pose proof (byte_range b) as BR.
    pose proof (u8ro_read usegs m name (ns ++ rest) i b _ BS NTH' ltac:(lia) eq_refl) as RD.
    (* [comment removed for export] *)
    step. ub_dead_by (clear - HI BB).
    zstep.
    step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)).
    rewrite (hn_loop_at ns i b part prev NTH). cbv zeta. set (c := bv_unsigned b) in *.
    destruct (Z.eq_dec c 46) as [E46|N46].
    { (* [comment removed for export] *) rewrite E46. step. try if_false; try if_true.
      zstep. zstep. zstep. step. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        assert (C1 : part = 0 /\ i <> 0).
        { destruct (Z.eq_dec part 0) as [->|NP]; [| exfalso; apply K0; replace (part <? 1) with false by (symmetry; apply Z.ltb_ge; lia); cbn [Z.b2z]; rewrite Z.land_0_r; reflexivity].
          destruct (Z.eq_dec i 0) as [->|NI]; [| split; [reflexivity| exact NI]].
          exfalso. apply K0. vm_compute. reflexivity. }
        destruct C1 as [-> NI].
        eapply evt_cut; [apply hn_exit0|]. intros ms' ->. unfold HN_EXIT.
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m.
        rewrite (proj2 (Z.eqb_neq i 0) NI). cbn [Z.eqb Pos.eqb andb negb orb].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
      (* [comment removed for export] *)
      assert (NC1 : (part =? 0) && negb (i =? 0) = false).
      { destruct (Z.eqb_spec part 0) as [->|NP]; [|reflexivity]. destruct (Z.eqb_spec i 0) as [->|NI]; [reflexivity|].
        exfalso. revert K0. replace (0 <? i mod 18446744073709551616) with true by (symmetry; apply Z.ltb_lt; rewrite Z.mod_small by lia; lia).
        replace (0 <? i) with true by (symmetry; apply Z.ltb_lt; lia).
        intros K; vm_compute in K; lia. }
      rewrite K0. clear K0. step.
      destruct (Z.eq_dec prev 45) as [E45|N45].
      { rewrite E45. step. try if_true; try if_false.
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m.
        rewrite NC1. cbn [Z.eqb Pos.eqb andb negb orb].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
      step. if_cases K1; zify_cond K1; [kill K1|]; clear K1. step.
      (* [comment removed for export] *)
      rewrite NC1, (proj2 (Z.eqb_neq prev 45) N45). cbn [Z.eqb Pos.eqb andb negb orb].
      zstep. step. step. if_cases K2; zify_cond K2; rewrite ?Z.mod_small in K2 by lia.
      + (* [comment removed for export] *)
        replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
        eapply (IH (i + 1) 0 46); try eassumption; try lia.
      + (* [comment removed for export] *)
        zstep. zstep.
        rewrite skipn_all2 by (rewrite length_map; lia). cbn [hn_loop Z.eqb Pos.eqb orb negb].
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m.
        split; [| split; [exact MU| split; [exact WM| split; [exact MI| exact ST]]]].
        reflexivity. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_neq c 46) N46). cbv beta iota.
    step. if_cases KB; zify_cond KB. 2:{ kill KB. } clear KB.
    (* [comment removed for export] *)
    assert (JOIN : forall a0x a2x,
      (part =? 0) && (c =? 45) = false ->
      evt usegs (fun ms' => exists (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s3' s4' s8' t3' t4' t5' t6' : word) m',
                   ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' s0 (Z_to_bv 64 (Z.of_nat (length ns)))
                                 (Z_to_bv 64 (if (if (part =? 0) && (c =? 45) then false
                                                  else if negb (label_charZ c || (c =? 45)) then false
                                                  else if 63 <? part + 1 then false
                                                  else hn_loop (skipn (S (Z.to_nat i)) (map bv_unsigned ns)) (i + 1) (part + 1) c) then 1 else 0))
                                 a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 name) s3' s4' (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45)
                                 s8' (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3' t4' t5' t6')
                            F (Z_to_bv 64 0x21697c) fc None m' (seg_rom usegs)
                   /\ munch [(lo, bv_unsigned sp + -112)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp + -112))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (Z.of_nat (length ns))) a0x (Z_to_bv 64 prev) a2x a3 a4 a5 a6 a7
                 (Z_to_bv 64 name) (Z_to_bv 64 c) (Z_to_bv 64 i) (Z_to_bv 64 (18446744073709551615 - name)) (Z_to_bv 64 46) (Z_to_bv 64 45) (Z_to_bv 64 part)
                 (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 63) t3 t4 t5 t6)
            F (Z_to_bv 64 0x216910) fc None m (seg_rom usegs))).
    { intros a0x a2x NPC. rewrite NPC. cbv beta iota.
      (* [comment removed for export] *)
      step. step. step. step.
      eapply evt_cut.
      { eapply ctype_alnum_spec with (lo := lo); try reflexivity; try lia;
          rewrite ?unsigned_lit by lia; unfold CTYPE_STACK, FR_ossl_ctype_check in *;
          first [exact ST | exact MI | lia | (vm_compute; reflexivity)]. }
      pose proof (length_app ns rest) as LA.
      unfold ctype_post. land MU WM.
      change (Z_to_bv 64 (if is_alnumZ c then 1 else 0)) with (Z_to_bv 64 (hn_al c)).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
      rename PC2 into MI.
      eapply evt_cut; [eapply hn_flags_seg; lia|]. intros ms' [a2' ->].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. step. step.
      if_cases K1; zify_cond K1; change (Z.land _ _) with (hn_cond c (hn_al c)) in K1.
      - (* [comment removed for export] *)
        apply Z.eqb_neq in K1. rewrite hn_cond_ok in K1 by lia. rewrite K1. cbn [negb].
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mc.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      - apply Z.eqb_eq in K1. rewrite hn_cond_ok in K1 by lia. rewrite K1. cbn [negb].
        (* [comment removed for export] *)
        zstep. step. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *) replace (63 <? part + 1) with true by (symmetry; apply Z.ltb_lt; lia).
          apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mc.
          split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
        + replace (63 <? part + 1) with false by (symmetry; apply Z.ltb_ge; lia).
          (* [comment removed for export] *)
          zstep. step. step. if_cases K3; zify_cond K3; rewrite ?Z.mod_small in K3 by lia.
          * (* [comment removed for export] *)
            replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
            eapply evt_cut.
            { eapply (IH (i + 1) (part + 1) c); try eassumption; try lia. }
            clear ST. land MU WM.
            apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _.
            split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact ST].
          * (* [comment removed for export] *)
            zstep. zstep.
            rewrite skipn_all2 by (rewrite length_map; lia). cbn [hn_loop].
            rewrite (proj2 (Z.eqb_neq c 46) N46). cbn [orb].
            replace (Z.b2z ((c + -47) mod 18446744073709551616 <? 18446744073709551614)) with (if negb (c =? 45) then 1 else 0).
            2:{ destruct (Z.eqb_spec c 45) as [->|N45]; cbn [negb]; [vm_compute; reflexivity|].
                destruct (Z_lt_le_dec c 47).
                - rewrite mod_small_neg by lia. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
                - rewrite Z.mod_small by lia. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
            apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, mc.
            split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST]. }
    (* [comment removed for export] *)
    step. if_cases KP; zify_cond KP.
    - (* [comment removed for export] *) apply (JOIN _ _). destruct (Z.eqb_spec part 0) as [->|NP]; [exfalso; revert KP; rewrite ?Z.mod_small by lia; lia| reflexivity].
    - (* [comment removed for export] *)
      step. if_cases K45; zify_cond K45.
      + (* [comment removed for export] *)
        replace ((part =? 0) && (c =? 45)) with true by (symmetry; apply andb_true_iff; split; apply Z.eqb_eq; first [lia | rewrite <- (Z.mod_small c 18446744073709551616) by lia; lia]).
        eapply evt_cut; [apply hn_exit0|]. intros ms' ->. unfold HN_EXIT.
        apply evt_done. eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact ST].
      + apply (JOIN _ _). destruct (Z.eqb_spec c 45) as [->|N45]; [exfalso; revert K45; rewrite ?Z.mod_small by lia; lia|]. apply andb_false_r.
  Qed.

  Lemma hnpart_spec : hnpart_stmt.
  Proof.
    unfold hnpart_stmt. intros until rest. intros A0 A1 A2 BS NLO ST CEIL LO MI RAE. subst a0 a1 a2.
    unfold P_validate_hostname_part, HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check in *.
    pose proof (word_range sp) as SPR. pose proof (word_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold zlength in *.
    (* [comment removed for export] *)
    carve_frame 112%nat ST.
    do 14 st1. step. step. step. step. step.
    destruct (Z_le_dec 2 (Z.of_nat (length ns))) as [L2|L2]; [destruct (Z_le_dec (Z.of_nat (length ns)) 256) as [L256|L256]|].
    2:{ (* [comment removed for export] *) if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step.
        replace (hostname_ok ns) with false by (unfold hostname_ok, zlength; destruct (2 <=? Z.of_nat (length ns)) eqn:?; destruct (Z.of_nat (length ns) <=? 256) eqn:?; cbn; try reflexivity; exfalso; lia).
        do 13 st1. step. step. release_frame FR ST (bv_unsigned sp). finish. }
    2:{ (* [comment removed for export] *) if_cases K0; zify_cond K0; rewrite mod_small_neg in K0 by lia; [exfalso; lia|]. clear K0. step. step.
        replace (hostname_ok ns) with false by (unfold hostname_ok, zlength; destruct (2 <=? Z.of_nat (length ns)) eqn:?; destruct (Z.of_nat (length ns) <=? 256) eqn:?; cbn; try reflexivity; exfalso; lia).
        do 13 st1. step. step. release_frame FR ST (bv_unsigned sp). finish. }
    if_cases K0; zify_cond K0; rewrite mod_small_neg in K0 by lia; [| exfalso; lia]. clear K0.
    (* [comment removed for export] *)
    step. step. step. step. step. ubnot. step. step. zstep. step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    replace (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 2)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    replace (Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (Z_to_bv 64 2) 2)) 1)) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
    eapply evt_cut.
    { eapply (hn_loop_walk (Z.to_nat (Z.of_nat (length ns))) 0 0 0) with (lo := lo) (rest := rest); try eassumption; try lia. }
    clear ST. land MU WM.
    cbn [Z.to_nat skipn].
    replace (hostname_ok ns) with (hn_loop (map bv_unsigned ns) 0 0 0)
      by (unfold hostname_ok, zlength; replace (2 <=? Z.of_nat (length ns)) with true by (symmetry; apply Z.leb_le; lia);
          replace (Z.of_nat (length ns) <=? 256) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    (* [comment removed for export] *)
    do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.
End S.
