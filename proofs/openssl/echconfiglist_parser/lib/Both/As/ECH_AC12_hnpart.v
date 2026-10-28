(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX Frame.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AStmt_C13 ECH_AStmt_C12 ECH_AKit ECH_AsKit ECH_AsKitK ECH_AC1_dup ECH_AC13_small ECH_AC12_ctype.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac retpc := match goal with |- context [ret_pc (Z_to_bv 64 ?v)] => replace (ret_pc (Z_to_bv 64 v)) with (Z_to_bv 64 v) by (symmetry; apply ret_pc_even; [lia| reflexivity]) end.
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

  Definition hn_al (c : Z) : Z := if is_alnumZ c then 1 else 0.

  (* [comment removed for export] *)
  Lemma ahn_flags_seg : forall (ra gp tp t0 t1 t2 s0 a1x a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 spw s1w s2w s3w s5w s6w s7w s9w : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (c al : Z),
      0 <= c < 256 -> rw_cells asegs m (bv_unsigned s0 + -112) [C8 (Z_to_bv 64 0)] ->
      evt asegs (fun ms' => exists a2',
          ms' = MS (mkR ra spw gp tp t0 t1 t2 s0 s1w (Z_to_bv 64 al) (Z_to_bv 64 0) a2' a3 a4 a5 a6 a7
                       s2w s3w (Z_to_bv 64 c) s5w s6w s7w (Z_to_bv 64 46) s9w (Z_to_bv 64 45)
                       (Z_to_bv 64 0) t3 t4 t5 t6)
                   F (Z_to_bv 64 0x432854) fc None m (seg_rom asegs))
        (MS (mkR ra spw gp tp t0 t1 t2 s0 s1w (Z_to_bv 64 al) a1x a2 a3 a4 a5 a6 a7
                 s2w s3w (Z_to_bv 64 c) s5w s6w s7w (Z_to_bv 64 46) s9w (Z_to_bv 64 45)
                 (Z_to_bv 64 0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x432844) fc None m (seg_rom asegs)).
  Proof.
    intros until al. intros CR FR0.
    zstep. step. step. if_cases K0; zify_cond K0; [| step]; clear K0.
    all: apply evt_done; eexists; reflexivity.
  Qed.

  Definition ASHB12 : Z := 0x7fff8000.  Definition AHN_HEAD : Z := 0x4327f4.  Definition AHN_EXIT : Z := 0x4328d4.  Definition AHN_CT_RA : Z := 0x432844.  Definition AHN_K : Z := 0x432808.

  (* [comment removed for export] *)
  Definition ahn_cond (c al : Z) : Z :=
    Z.land (Z.b2z (0 <? Z.land (c + -45) 18446744073709551615))
      (Z.lor
         (Z.land (Z.land (Z.b2z (0 <? Z.land (c + -95) 18446744073709551615)) 1) (Z.b2z (al <? 1)))
         (Z.lxor (Z.b2z (Z.land (bv_swrap 32 (c + -47)) 18446744073709551615 <? 18446744073709551614)) 1)).
  Lemma ahn_cond_ok : forall c, 0 <= c < 256 -> c <> 46 ->
    (ahn_cond c (hn_al c) =? 0) = (label_charZ c || (c =? 45)).
  Proof.
    intros c Hc N46.
    assert (ALL : forallb (fun n => let c := Z.of_nat n in implb (negb (c =? 46)) (Bool.eqb (ahn_cond c (hn_al c) =? 0) (label_charZ c || (c =? 45)))) (seq 0 256) = true)
      by (vm_compute; reflexivity).
    rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat c)).
    rewrite in_seq, Z2Nat.id in ALL by lia. cbv zeta in ALL.
    specialize (ALL ltac:(lia)). rewrite (proj2 (Z.eqb_neq c 46) N46) in ALL. cbn [negb implb] in ALL.
    apply Bool.eqb_prop in ALL. exact ALL.
  Qed.
  Lemma land_M1 : forall x, Z.land x 18446744073709551615 = x mod 2^64.
  Proof. intros x. change 18446744073709551615 with (Z.ones 64). apply Z.land_ones. lia. Qed.

  (* [comment removed for export] *)
  Lemma ahn_loop_walk : forall (k : nat) (i part prev : Z)
      (ra sp gp tp t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (name lo : Z) (ns rest : list byte),
      Z.to_nat (Z.of_nat (length ns) - i) = k -> 0 <= i < Z.of_nat (length ns) -> Z.of_nat (length ns) <= 256 ->
      0 <= part <= 63 -> 0 <= prev < 256 ->
      bytes_at asegs m name (ns ++ rest) -> (name + Z.of_nat (length ns) + Z.of_nat (length rest) <= lo \/ bv_unsigned sp <= name) ->
      accessible m name (Z.of_nat (length ns)) -> (name + Z.of_nat (length ns) <= ALOWSH_LO \/ AHI_LO <= name) -> rw_cells asegs m (bv_unsigned sp + -112) [C8 (Z_to_bv 64 0)] ->
      stk asegs m lo (bv_unsigned sp + -112) -> aceil <= lo -> lo <= bv_unsigned sp + -128 -> mem_inv asegs m -> ACONST m ->
      evt asegs (fun ms' => exists (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word) m',
                   ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' sp s1'
                                 (Z_to_bv 64 (if hn_loop (skipn (Z.to_nat i) (map bv_unsigned ns)) i part prev then 1 else 0))
                                 a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' (Z_to_bv 64 46) (Z_to_bv 64 ASHB12) (Z_to_bv 64 45)
                                 (Z_to_bv 64 0) t3' t4' t5' t6')
                            F (Z_to_bv 64 AHN_EXIT) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp + -112)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp + -112))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.of_nat (length ns) - i)) a0 (Z_to_bv 64 prev) a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (name + i)) (Z_to_bv 64 (name + i)) s4 (Z_to_bv 64 i) (Z_to_bv 64 (2 ^ 64 - 1 - name)) (Z_to_bv 64 part) (Z_to_bv 64 46) (Z_to_bv 64 ASHB12) (Z_to_bv 64 45)
                 (Z_to_bv 64 0) t3 t4 t5 t6)
            F (Z_to_bv 64 AHN_HEAD) fc None m (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until rest; intros HK HI L256 PR PV BS NLO ACC0 NSH FR0 ST CEIL LO MI AC; [lia|].
    unfold AHN_HEAD, AHN_EXIT, ASHB12.
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (munch_refl [(lo, bv_unsigned sp + -112)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct (nth_error ns (Z.to_nat i)) as [b|] eqn:NTH; [| apply nth_error_None in NTH; lia].
    assert (NTH' : nth_error (ns ++ rest) (Z.to_nat i) = Some b) by (rewrite nth_error_app1 by lia; exact NTH).
    pose proof (abyte_range b) as BR.
    pose proof (u8ro_read asegs m name (ns ++ rest) i b _ BS NTH' ltac:(lia) eq_refl) as RD.
    rewrite (hn_loop_at ns i b part prev NTH). cbv zeta. set (c := bv_unsigned b) in *.
    (* [comment removed for export] *)
    step. ub_dead. zstep. zstep. ck1_load ACC0 (name + i) v V1 V2 Ha.
    ck_K 12 0x432808 K.
    2:{ ck1_branch_blt (name + i) v V1 V2 Ha K. }
    intros tv. red_tset.
    (* [comment removed for export] *)
    step. change (zxb b) with (Z_to_bv 64 (bv_unsigned b)). fold c.
    (* [comment removed for export] *)
    destruct (Z.eq_dec c 46) as [E46|N46].
    { (* [comment removed for export] *) rewrite E46. step. try if_false; try if_true.
      (* [comment removed for export] *)
      zstep. zstep. zstep. step. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        rewrite ?land_M1 in K0.
        assert (C1 : part = 0 /\ i <> 0).
        { destruct (Z.eq_dec part 0) as [->|NP]; [| exfalso; apply K0; replace (part <? 1) with false by (symmetry; apply Z.ltb_ge; lia); rewrite ?Z.land_0_r, ?Z.land_0_l; reflexivity].
          destruct (Z.eq_dec i 0) as [->|NI]; [| split; [reflexivity| exact NI]].
          exfalso. apply K0. vm_compute. reflexivity. }
        destruct C1 as [-> NI].
        step. step. apply evt_done. do 22 eexists. exists m.
        rewrite (proj2 (Z.eqb_neq i 0) NI). cbn [Z.eqb Pos.eqb andb negb orb].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC| exact ST]. }
      (* [comment removed for export] *)
      assert (NC1 : (part =? 0) && negb (i =? 0) = false).
      { destruct (Z.eqb_spec part 0) as [->|NP]; [|reflexivity]. destruct (Z.eqb_spec i 0) as [->|NI]; [reflexivity|].
        exfalso. revert K0. replace (0 <? i) with true by (symmetry; apply Z.ltb_lt; lia).
        intros K; vm_compute in K; lia. }
      rewrite K0. clear K0. step.
      destruct (Z.eq_dec prev 45) as [E45|N45].
      { rewrite E45. step. try if_true; try if_false.
        apply evt_done. do 22 eexists. exists m.
        rewrite NC1. cbn [Z.eqb Pos.eqb andb negb orb].
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC| exact ST]. }
      step. if_cases K1; zify_cond K1; [kill K1|]; clear K1. step.
      (* [comment removed for export] *)
      rewrite NC1, (proj2 (Z.eqb_neq prev 45) N45). cbn [Z.eqb Pos.eqb andb negb orb].
      zstep. zstep. zstep. zstep. zstep. step. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        replace (name + i + 1) with (name + (i + 1)) by lia. replace (Z.of_nat (length ns) - i + -1) with (Z.of_nat (length ns) - (i + 1)) by lia.
        replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
        eapply (IH (i + 1) 0 46); try eassumption; try lia.
      + (* [comment removed for export] *)
        step. zstep. zstep.
        rewrite skipn_all2 by (rewrite length_map; lia). cbn [hn_loop Z.eqb Pos.eqb orb negb].
        apply evt_done. do 22 eexists. exists m.
        split; [| split; [exact MU| split; [exact WM| split; [exact MI| split; [exact AC| exact ST]]]]].
        reflexivity. }
    (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_neq c 46) N46). cbv beta iota.
    step. if_cases KB; zify_cond KB. 2:{ kill KB. } clear KB.
    (* [comment removed for export] *)
    assert (JOIN :
      (part =? 0) && (c =? 45) = false ->
      evt asegs (fun ms' => exists (ra' t0' t1' t2' s1' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' t3' t4' t5' t6' : word) m',
                   ms' = MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0' t1' t2' sp s1'
                                 (Z_to_bv 64 (if (if (part =? 0) && (c =? 45) then false
                                                  else if negb (label_charZ c || (c =? 45)) then false
                                                  else if 63 <? part + 1 then false
                                                  else hn_loop (skipn (S (Z.to_nat i)) (map bv_unsigned ns)) (i + 1) (part + 1) c) then 1 else 0))
                                 a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' (Z_to_bv 64 46) (Z_to_bv 64 2147450880) (Z_to_bv 64 45)
                                 (Z_to_bv 64 0) t3' t4' t5' t6')
                            F (Z_to_bv 64 0x4328d4) fc None m' (seg_rom asegs)
                   /\ munch [(lo, bv_unsigned sp + -112)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp + -112))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 (Z.of_nat (length ns) - i)) (Z_to_bv 64 v) (Z_to_bv 64 prev) tv a3 a4 a5 a6 a7
                 (Z_to_bv 64 (name + i)) (Z_to_bv 64 (name + i)) (Z_to_bv 64 c) (Z_to_bv 64 i) (Z_to_bv 64 (2 ^ 64 - 1 - name)) (Z_to_bv 64 part) (Z_to_bv 64 46) (Z_to_bv 64 2147450880) (Z_to_bv 64 45)
                 (Z_to_bv 64 0) t3 t4 t5 t6)
            F (Z_to_bv 64 0x432834) fc None m (seg_rom asegs))).
    { intros NPC. rewrite NPC. cbv beta iota.
      (* [comment removed for export] *)
      step. step. step. step.
      eapply evt_cut.
      { eapply actype_alnum_spec with (lo := lo); try reflexivity; try lia;
          rewrite ?unsigned_lit by lia; unfold CTYPE_STACK, FR_ossl_ctype_check in *;
          first [exact ST | exact MI | exact AC | lia | (vm_compute; reflexivity)]. }
      pose proof (length_app ns rest) as LA.
      unfold ctype_post.
      intros ms' PO. destruct PO as (u0 & u1 & u2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & u3 & u4 & u5 & u6 & mc & -> & MU' & WM' & MI' & AC' & ST').
      retpc. rewrite ?unsigned_lit in MU', ST' by lia. clear ST. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI. rename ST' into ST.
      change (Z_to_bv 64 (if is_alnumZ c then 1 else 0)) with (Z_to_bv 64 (hn_al c)).
      assert (ALR : 0 <= hn_al c <= 1) by (unfold hn_al; destruct (is_alnumZ c); lia).
      eapply evt_cut; [eapply ahn_flags_seg; first [lia | eassumption]|]. intros ms' [a2' ->].
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. step. step.
      if_cases K1; zify_cond K1; lazymatch type of K1 with (?X <> 0) => change X with (ahn_cond c (hn_al c)) in K1 | (?X = 0) => change X with (ahn_cond c (hn_al c)) in K1 end.
      - (* [comment removed for export] *)
        apply Z.eqb_neq in K1. rewrite ahn_cond_ok in K1 by lia. rewrite K1. cbn [negb].
        apply evt_done. do 22 eexists. exists mc.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC'| exact ST].
      - apply Z.eqb_eq in K1. rewrite ahn_cond_ok in K1 by lia. rewrite K1. cbn [negb].
        (* [comment removed for export] *)
        zstep. step. step. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *) replace (63 <? part + 1) with true by (symmetry; apply Z.ltb_lt; lia).
          apply evt_done. do 22 eexists. exists mc.
          split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC'| exact ST].
        + replace (63 <? part + 1) with false by (symmetry; apply Z.ltb_ge; lia).
          (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. zstep. step. if_cases K3; zify_cond K3.
          * (* [comment removed for export] *)
            replace (name + i + 1) with (name + (i + 1)) by lia. replace (Z.of_nat (length ns) - i + -1) with (Z.of_nat (length ns) - (i + 1)) by lia.
            replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) by lia.
            assert (ACC1 : accessible mc name (Z.of_nat (length ns))).
            { eapply accessible_across; [exact ACC0| exact MU|]. constructor; [cbn; unfold AHI_LO; lia| constructor]. }
            eapply evt_cut.
            { eapply (IH (i + 1) (part + 1) c); try eassumption; try lia. }
            clear ST.
            intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & h1 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & g1 & g2 & g3 & g5 & g6 & g7 & w4 & w5 & w6 & w7 & m'' & -> & MU'' & WM'' & MI'' & AC'' & ST'').
            apply evt_done. do 22 eexists. exists m''.
            split; [reflexivity|]. split; [| split; [eapply wmono_trans; [exact WM| exact WM'']| split; [exact MI''| split; [exact AC''| exact ST'']]]].
            eapply munch_trans; [exact MU| exact MU''].
          * (* [comment removed for export] *)
            step. zstep. zstep.
            rewrite skipn_all2 by (rewrite length_map; lia). cbn [hn_loop].
            rewrite (proj2 (Z.eqb_neq c 46) N46). cbn [orb].
            replace (Z.b2z (Z.land (c + -47) 18446744073709551615 <? 18446744073709551614)) with (if negb (c =? 45) then 1 else 0).
            2:{ rewrite land_M1. destruct (Z.eqb_spec c 45) as [->|N45]; cbn [negb]; [vm_compute; reflexivity|].
                destruct (Z_lt_le_dec c 47).
                - rewrite mod_small_neg by lia. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
                - rewrite Z.mod_small by lia. replace (_ <? _) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
            apply evt_done. do 22 eexists. exists mc.
            split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC'| exact ST]. }
    (* [comment removed for export] *)
    step. if_cases KP; zify_cond KP; rewrite ?land_M1 in KP.
    - (* [comment removed for export] *) apply JOIN. destruct (Z.eqb_spec part 0) as [->|NP]; [exfalso; revert KP; rewrite ?Z.mod_small by lia; lia| reflexivity].
    - (* [comment removed for export] *)
      step. if_cases K45; zify_cond K45; rewrite ?land_M1 in K45.
      + (* [comment removed for export] *)
        step. step. replace ((part =? 0) && (c =? 45)) with true by (symmetry; apply andb_true_iff; split; apply Z.eqb_eq; first [lia | rewrite <- (Z.mod_small c (2^64)) by lia; lia]).
        apply evt_done. do 22 eexists. exists m.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact AC| exact ST].
      + apply JOIN. destruct (Z.eqb_spec c 45) as [->|N45]; [exfalso; revert K45; rewrite ?Z.mod_small by lia; lia|]. apply andb_false_r.
  Qed.

  Lemma ahnpart_spec : hnpart_stmt.
  Proof.
    unfold hnpart_stmt. intros until rest. intros A0 A1 A2 BS NLO ACC0 NSH ST CEIL LO MI AC RAE. subst a0 a1 a2.
    unfold P_validate_hostname_part, HNPART_STACK, FR_validate_hostname_part, CTYPE_STACK, FR_ossl_ctype_check in *.
    pose proof (ACONST_shbase m AC) as [GSB SHB0]. unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (bytes_at_bound _ _ _ _ BS) as BB. rewrite length_app in BB.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (constructor; [cbn; unfold AHI_LO; lia| constructor]).
    unfold zlength in *.
    change (id (accessible m name (Z.of_nat (length ns)))) in ACC0.
    (* [comment removed for export] *)
    carve_frame 112%nat ST.
    do 14 st1. step.
    Local Ltac hn_exit0 :=
      do 13 st1; step; step;
      let FR := match goal with H : rw_cells _ _ (bv_unsigned _ + -112) _ |- _ => H end in
      let ST1 := match goal with H : stk _ _ _ (bv_unsigned ?spv + _) |- _ => H end in
      lazymatch type of ST1 with stk _ _ _ (bv_unsigned ?spv + _) => release_frame FR ST1 (bv_unsigned spv) end;
      unfold ctype_post; finish;
      lazymatch goal with AC : ACONST ?m0, MU : munch _ ?m0 _, WM : wmono _ ?m0 _, CEIL : aceil <= _ |- ACONST _ =>
        eapply ACONST_stack_frame13; [exact AC| exact MU| exact WM| exact CEIL] end.
    destruct (Z_le_dec 2 (Z.of_nat (length ns))) as [L2|L2]; [destruct (Z_le_dec (Z.of_nat (length ns)) 256) as [L256|L256]|].
    2:{ (* [comment removed for export] *) step. step. step. step. if_cases K0; zify_cond K0; [kill K0|]. clear K0. step. step.
        replace (hostname_ok ns) with false by (unfold hostname_ok, zlength; destruct (2 <=? Z.of_nat (length ns)) eqn:?; destruct (Z.of_nat (length ns) <=? 256) eqn:?; cbn; try reflexivity; exfalso; lia).
        hn_exit0. }
    2:{ (* [comment removed for export] *) step. step. step. step. if_cases K0; zify_cond K0; rewrite ?land_M1 in K0; rewrite ?mod_small_neg in K0 by lia; [exfalso; lia|]. clear K0. step. step.
        replace (hostname_ok ns) with false by (unfold hostname_ok, zlength; destruct (2 <=? Z.of_nat (length ns)) eqn:?; destruct (Z.of_nat (length ns) <=? 256) eqn:?; cbn; try reflexivity; exfalso; lia).
        hn_exit0. }
    step. step. step. step. if_cases K0; zify_cond K0; rewrite ?land_M1 in K0; rewrite ?mod_small_neg in K0 by lia; [| exfalso; lia]. clear K0.
    (* [comment removed for export] *)
    do 14 step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    replace (v_sltiu (Z_to_bv 64 2) 2) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
    replace (v_sltiu (Z_to_bv 64 2) 1) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
    rewrite (unsigned_lit name), zb_lxor_ones by lia.
    replace (Z_to_bv 64 name) with (Z_to_bv 64 (name + 0)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat (length ns))) with (Z_to_bv 64 (Z.of_nat (length ns) - 0)) by (f_equal; lia).
    replace (v_sltiu (Z_to_bv 64 2) 2) with (Z_to_bv 64 0) in FR by (vm_compute; reflexivity).
    pose proof (proj1 (proj1 (rw_cells_app asegs m1 (bv_unsigned sp + -112) [C8 (Z_to_bv 64 0)] _) FR)) as FR0.
    assert (AC1 : ACONST m1) by (eapply ACONST_stack_frame13; [exact AC| exact MU| exact WM| exact CEIL]).
    assert (ACC1 : accessible m1 name (Z.of_nat (length ns))) by (unfold id in ACC0; eapply accessible_across; [exact ACC0| exact MU| exact NSW]).
    eapply evt_cut.
    { eapply (ahn_loop_walk (Z.to_nat (Z.of_nat (length ns))) 0 0 0) with (lo := lo) (rest := rest); try eassumption; try lia. }
    clear ST AC1 ACC1 FR0.
    intros ms' PO. destruct PO as (w0 & w1 & w2 & w3 & h1 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & g1 & g2 & g3 & g5 & g6 & g7 & w4 & w5 & w6 & w7 & m2 & -> & MU' & WM' & MI' & AC' & ST).
    rewrite ?unsigned_lit in MU', ST by lia. carry MU' WM'. extend_munch MU WM MU' WM'. clear MI. rename MI' into MI.
    cbn [Z.to_nat skipn].
    replace (hostname_ok ns) with (hn_loop (map bv_unsigned ns) 0 0 0)
      by (unfold hostname_ok, zlength; replace (2 <=? Z.of_nat (length ns)) with true by (symmetry; apply Z.leb_le; lia);
          replace (Z.of_nat (length ns) <=? 256) with true by (symmetry; apply Z.leb_le; lia); reflexivity).
    unfold AHN_EXIT.
    (* [comment removed for export] *)
    do 13 st1. step. step.
    release_frame FR ST (bv_unsigned sp). unfold ctype_post. finish. all: try exact AC'.
  Qed.
End S.
