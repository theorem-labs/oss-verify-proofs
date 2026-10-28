(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset N6_strlen N6_strncmp_spec.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.As Require Import N8Store. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Section STRNCMP.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (e t rest1 rest2 : list Z) (n lo : Z).
  Hypothesis A2 : a2 = Z_to_bv 64 n.
  Hypothesis N0 : 0 <= n.
  Hypothesis LEN : Z.of_nat (length e) <= n.
  Hypothesis E1 : bytes_at asegs m (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)).
  Hypothesis FE : Forall (fun c => 0 < c < 256) e.
  Hypothesis E2 : bytes_at asegs m (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)).
  Hypothesis FT : Forall (fun c => 0 < c < 256) t.
  Hypothesis ACC1 : accessible m (bv_unsigned a0) (Z.min n (Z.of_nat (length e) + 1)).
  Hypothesis ACC2 : accessible m (bv_unsigned a1) (Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis SV1 : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length e) + 1).
  Hypothesis SV2 : shvis m (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : n <= 2^40.
  Hypothesis INM1 : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.min n (Z.of_nat (length e) + 1)).
  Hypothesis INM2 : in_app_mem (bv_unsigned a1) (bv_unsigned a1 + Z.min n (Z.of_nat (length t) + 1)).
  Hypothesis DJ1 : bv_unsigned a0 + Z.of_nat (length (e ++ 0 :: rest1)) <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis DJ2 : bv_unsigned a1 + Z.of_nat (length (t ++ 0 :: rest2)) <= lo \/ bv_unsigned sp <= bv_unsigned a1.
  Hypothesis CFS : rw_cells asegs m ACF_STRICT_CELL [C1 (Z_to_bv 8 0)].

  Notation p1 := (bv_unsigned a0).
  Notation p2 := (bv_unsigned a1).
  Notation lne := (Z.of_nat (length e)).
  Notation lnt := (Z.of_nat (length t)).
  Notation POST := (astrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (zstrncmp e t (Z.to_nat n)) lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2176)).
  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 mm :=
    (MS (mkR x1 SP2 gp tp x5 t1 t2 sp a2 x10 x11 x12 x13 x14 x15 x16 x17 a1 a0 ra x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -104)
                         [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold AINTRIN_STACK, ACF_STRICT_CELL in *;
    pose proof INM1 as INM1'; unfold in_app_mem, AHI_LO, AAPP_HI in INM1'; rewrite ASHADOW_BASE_val in INM1';
    pose proof INM2 as INM2'; unfold in_app_mem, AHI_LO, AAPP_HI in INM2'; rewrite ASHADOW_BASE_val in INM2';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R;
    pose proof (bv_unsigned_in_range 64 a1) as A1R; unfold bv_modulus in A1R; change (2 ^ Z.of_N 64) with (2^64) in A1R.

  Lemma len1 : Z.of_nat (length (e ++ 0 :: rest1)) = lne + 1 + Z.of_nat (length rest1).
  Proof. rewrite length_app. cbn [length]. lia. Qed.
  Lemma len2 : Z.of_nat (length (t ++ 0 :: rest2)) = lnt + 1 + Z.of_nat (length rest2).
  Proof. rewrite length_app. cbn [length]. lia. Qed.

  (* [comment removed for export] *)
  Section K.
    Variables (i C1 C2 : Z).
    Hypothesis HC : 0 <= C1 < 256 /\ 0 <= C2 < 256.
    Hypothesis HI : 0 <= i <= n /\ i <= lne /\ i <= lnt.
    Hypothesis SIGN : (zstrncmp e t (Z.to_nat n) = 0 <-> C1 = C2) /\ (zstrncmp e t (Z.to_nat n) < 0 <-> C1 < C2).

    (* [comment removed for export] *)
    Section JF.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis E1m : bytes_at asegs mm (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)).
      Hypothesis E2m : bytes_at asegs mm (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)).
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2176) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2176).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 5957272 [C8 (Z_to_bv 64 6779576)].
      Hypothesis CB1 : rw_cells asegs mm 6779576 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis G2 : rw_cells asegs mm 5957280 [C8 (Z_to_bv 64 6782888)].
      Hypothesis G3 : rw_cells asegs mm 5957288 [C8 (Z_to_bv 64 6782896)].
      Hypothesis G4 : rw_cells asegs mm 5957296 [C8 (Z_to_bv 64 6782880)].
      Hypothesis CB4 : rw_cells asegs mm 6782880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

      (* [comment removed for export] *)
      Lemma asn_jf : forall x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x26 x27,
        evt asegs POST (RST 0x1ae580 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 x27 mm).
      Proof.
        prep.
        do 3 zstep.
        match goal with |- context [Z_to_bv 64 ?d] =>
          lazymatch d with context [Z.b2z _] =>
            set (dd := d);
            assert (DD : dd = (if C2 <? C1 then 1 else 0) - (if C1 <? C2 then 1 else 0)) by
              (subst dd; destruct (Z.ltb_spec C2 C1); destruct (Z.ltb_spec C1 C2); cbn; (lia_guard; (lia_guard; (lia_guard; (lia_guard; first [clear - SIGN H H0; lia | lia])))));
            clearbody dd
          end end.
        do 24 zstep.
        release_frame FR STm (bv_unsigned sp + -104).
        release_frame FR1 STm (bv_unsigned sp).
        assert (AC' : ACONST mm)
          by (eapply ACONST_frame; [exact AC | exact MU | exact WM |];
              constructor; [|constructor];
              apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; (first [clear - ACEILB LO CEIL; lia | lia])).
        assert (CASES : (dd = 0 /\ C1 = C2) \/ (dd = 1 /\ C2 < C1) \/ (dd = -1 /\ C1 < C2)).
        { destruct (Z.ltb_spec C2 C1); destruct (Z.ltb_spec C1 C2); (first [clear - H0 H DD; lia | lia]). }
        apply evt_done. unfold astrncmp_post, AINTRIN_STACK. do 16 eexists. split; [reflexivity|].
        destruct SIGN as [SG1 SG2].
        destruct CASES as [[-> E]|[[-> E]|[-> E]]].
        - split; [reflexivity|]. change (bv_signed (sx32 (Z_to_bv 64 0))) with 0.
          split; [(first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | (first [clear; solve [repeat split; exact I] | clear; tauto | (lazymatch goal with H1 : _ |- _ => revert H1; clear; tauto end) | tauto])])])])|]. split; [split; intros; lia|]. auto 10.
        - split; [reflexivity|]. change (bv_signed (sx32 (Z_to_bv 64 1))) with 1.
          split; [split; intros; lia|]. split; [split; intros; lia|]. auto 10.
        - split; [apply bv_eq; vm_compute; reflexivity|].
          replace (bv_signed (sx32 (Z_to_bv 64 (-1)))) with (-1) by (vm_compute; reflexivity).
          split; [split; intros; lia|]. split; [split; intros; lia|]. auto 10.
      Qed.
    End JF.

    Notation NN := (Z.min (i + 1) n).

    (* [comment removed for export] *)
    Lemma NN_facts : 0 <= NN <= n /\ NN <= Z.min n (lne + 1) /\ NN <= Z.min n (lnt + 1) /\ NN <= 2^40 /\ NN <= i + 1.
    Proof using e t rest1 rest2 n N0 N40 i C1 C2 HI SIGN. pose proof HI. pose proof N40. (first [clear - H0 H; lia | lia]). Qed.

    (* [comment removed for export] *)
    Section CHK2.
      Variables (mm : word -> option byte) (fjunk : list byte).
      Hypothesis MIm : mem_inv asegs mm.
      Hypothesis E1m : bytes_at asegs mm (bv_unsigned a0) (map b8 (e ++ 0 :: rest1)).
      Hypothesis E2m : bytes_at asegs mm (bv_unsigned a1) (map b8 (t ++ 0 :: rest2)).
      Hypothesis FR1 : FRAME mm.
      Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2176) [CB 2072 fjunk].
      Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2176).
      Hypothesis MU : munch W m mm.
      Hypothesis WM : wmono asegs m mm.
      Hypothesis G1 : rw_cells asegs mm 5957272 [C8 (Z_to_bv 64 6779576)].
      Hypothesis CB1 : rw_cells asegs mm 6779576 [C8 (Z_to_bv 64 2147450880)].
      Hypothesis G2 : rw_cells asegs mm 5957280 [C8 (Z_to_bv 64 6782888)].
      Hypothesis G3 : rw_cells asegs mm 5957288 [C8 (Z_to_bv 64 6782896)].
      Hypothesis G4 : rw_cells asegs mm 5957296 [C8 (Z_to_bv 64 6782880)].
      Hypothesis CB4 : rw_cells asegs mm 6782880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

      Lemma chk2_consts : ACONST mm /\ accessible mm p2 NN /\ accessible mm p1 NN.
      Proof using HCEIL sp a0 a1 m e t rest1 rest2 n lo N0 ACC1 ACC2 CEIL LO AC N40 INM1 INM2 i C1 C2 HI SIGN mm MU WM.
        prep. pose proof NN_facts as NF. split; [|split].
        - eapply ACONST_frame; [exact AC | exact MU | exact WM |].
          constructor; [|constructor].
          apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; (first [clear - ACEILB LO CEIL; lia | lia]).
        - eapply accessible_transport; [eapply accessible_sub; [exact ACC2| lia | lia | lia] | exact MU |].
          intros x Hx. destruct ACC2 as (? & ? & _). pose proof (sh_range_app x ltac:((first [clear - H0 H Hx NF; lia | lia]))) as SR.
          unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. (first [clear - SR ACEILB LO CEIL; lia | lia]).
        - eapply accessible_transport; [eapply accessible_sub; [exact ACC1| lia | lia | lia] | exact MU |].
          intros x Hx. destruct ACC1 as (? & ? & _). pose proof (sh_range_app x ltac:((first [clear - H0 H Hx NF; lia | lia]))) as SR.
          unfold AHI_LO in SR. rewrite ASHADOW_BASE_val in SR. cbn. (first [clear - SR ACEILB LO CEIL; lia | lia]).
      Qed.

      (* [comment removed for export] *)
      Lemma asn_jr2 : forall x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27,
        evt asegs POST (RST 0x1ae7fc x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 NN) x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 x27 mm).
      Proof using HCEIL ra sp gp tp t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e t rest1 rest2 n lo N0 ACC1 ACC2 CEIL LO AC N40 INM1 INM2 DJ1 DJ2 i C1 C2 HC HI SIGN mm fjunk MIm FR1 FR STm MU WM G1 CB1 G2 G3 G4 CB4.
        prep. pose proof NN_facts as NF. destruct chk2_consts as (ACm & ACC2m & ACC1m).
        do 2 zstep.
        zstep. call2 rip_body_w; try eassumption; rewrite ?unsigned_lit by (first [clear - NF SPR ACEILB LO CEIL; lia | lia]);
          [ exact ACC2m
          | lia
          | unfold in_app_mem, AHI_LO, AAPP_HI; rewrite ASHADOW_BASE_val; (first [clear - NF INM2'; lia | lia])
          | exact STm
          | unfold RIP_STACK; lia
          | unfold AHI_LO; (first [clear - ACEILB CEIL; lia | lia])
          | ].
        try rewrite unsigned_lit in * by lia.
        zstep. if_cases K; zify_cond K; [| exfalso; (first [clear - K; lia | lia])].
        eapply asn_jf; [exact MI0 | exact FR1 | exact FR | exact PC | exact MU | exact WM].
      Qed.

      Hypothesis N64 : 1 <= NN <= 64.

      (* [comment removed for export] *)
      Lemma asn_j5b : forall x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27,
        evt asegs POST (RST 0x1ae7f4 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 NN) x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 x27 mm).
      Proof using HCEIL ra sp gp tp t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e t rest1 rest2 n lo N0 ACC1 ACC2 CEIL LO AC N40 INM1 INM2 DJ1 DJ2 i C1 C2 HC HI SIGN mm fjunk MIm FR1 FR STm MU WM G1 CB1 G2 G3 G4 CB4.
        intros. zstep. zstep. if_cases K.
        - eapply asn_jf; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
        - eapply asn_jr2; eassumption.
      Qed.

      Section Loop2.
        Variables (q1 : Z) (qj : list byte).
        Hypothesis QA : u8arr asegs mm (8 * q1) qj.
        Hypothesis QB : 8 * q1 <= sh p2 /\ sh (p2 + NN - 1) < 8 * q1 + Z.of_nat (length qj).
        Hypothesis SR12 : 2147450880 <= sh p2 /\ sh (p2 + NN - 1) < 17594333495296.
        Lemma asn_loop2 : forall (k : nat) (j : Z) x1 x5 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27,
          Z.to_nat (sh (p2 + NN - 1) - (sh p2 + j)) = k -> 0 <= j -> sh p2 + j < sh (p2 + NN - 1) ->
          evt asegs POST (RST 0x1ae7e4 x1 x5 (Z_to_bv 64 (sh p2 + j)) (Z_to_bv 64 (sh (p2 + NN - 1))) x12 x13 x14 x15 x16 x17
                              (Z_to_bv 64 NN) x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 x27 mm).
        Proof using HCEIL ra sp gp tp t1 t2 s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e t rest1 rest2 n lo N0 ACC1 ACC2 CEIL LO AC N40 INM1 INM2 DJ1 DJ2 i C1 C2 HC HI SIGN mm fjunk MIm FR1 FR STm MU WM G1 CB1 G2 G3 G4 CB4 q1 qj QA QB SR12.
          induction k as [k IH] using lt_wf_ind; intros j x1 x5 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 Hk Hj Hlt.
          pose proof (q_read mm q1 qj QA (sh p2 + j) ltac:((first [clear - Hlt Hj QB; lia | lia]))) as RD.
          do 3 zstep.
          zstep. if_cases K; zify_cond K.
          - replace (sh p2 + j + 1) with (sh p2 + (j + 1)) by lia.
            eapply (IH (Z.to_nat (sh (p2 + NN - 1) - (sh p2 + (j + 1))))); (first [clear - Hlt Hk Hj K; lia | lia]).
          - apply asn_j5b.
        Qed.
      End Loop2.

      Hypothesis SV2m : stk asegs mm (sh (hull_lo p2)) (sh (hull_hi (p2 + Z.min n (lnt + 1)))).

      (* [comment removed for export] *)
      Lemma asn_jq2 : forall x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27,
        evt asegs POST (RST 0x1ae544 x1 x5 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 NN) x22 x23 (Z_to_bv 64 C1) (Z_to_bv 64 C2) x26 x27 mm).
      Proof.
        prep. pose proof NN_facts as NF.
        assert (SVq : stk asegs mm (sh (hull_lo p2)) (sh (hull_hi (p2 + NN)))).
        { change (shvis mm p2 (p2 + NN)). eapply shvis_sub; [exact SV2m | lia | lia | lia | lia | (first [clear - NF A1R; lia | lia])]. }
        (* [comment removed for export] *)
        pose proof (sh_range_app p2 ltac:(unfold AAPP_HI; (first [clear - INM2' N40 LO CEIL SV1 ACC2 E2 FE LEN N0 A2; lia | lia]))) as SR1.
        pose proof (sh_range_app (p2 + NN - 1) ltac:(unfold AAPP_HI; (first [clear - NF INM2' N64; lia | lia]))) as SR2.
        unfold AHI_LO in SR1, SR2. rewrite ASHADOW_BASE_val in SR1, SR2.
        (* [comment removed for export] *)
        do 9 zstep.
        destruct (hull_words p2 NN ltac:(lia) N64) as (HLO & HHI & HQ2 & HB1 & HB2 & HB3).
        destruct (hull_chunk mm p2 NN ltac:(lia) N64 ltac:((first [clear - NF INM2' E1; lia | lia])) SVq) as (qj & QW & QL & QL2).
        pose proof (u8arr_of_rw_cells asegs mm _ _ _ QW) as QA.
        set (q1 := sh p2 / 8) in *. set (q2 := sh (p2 + NN - 1) / 8) in *.
        assert (QB : 8 * q1 <= sh p2 /\ sh (p2 + NN - 1) < 8 * q1 + Z.of_nat (length qj)) by (first [clear - QL; lia | lia]).
        assert (SR12 : 2147450880 <= sh p2 /\ sh (p2 + NN - 1) < 17594333495296) by lia.
        replace (p2 + NN + -1) with (p2 + NN - 1) by lia. rewrite !shr3_sh by (first [clear - A1R N64; lia | lia]).
        clear HLO HHI HQ2 HB1 HB2 HB3.   (* [comment removed for export] *)
        do 2 zstep. rewrite !land_m8 by lia. fold q1. fold q2.
        destruct QL2 as [[E L]|[E L]]; rewrite E in QL |- *; rewrite L in QW, QL.
        - do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (p2 + NN - 1)) ltac:((first [clear - QB E; lia | lia]))) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply asn_j5b.
            * replace (Z_to_bv 64 (sh p2)) with (Z_to_bv 64 (sh p2 + 0)) by (f_equal; lia).
              eapply (asn_loop2 q1 qj); first [eassumption | reflexivity | lia].
          + eapply asn_jf; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
        - replace (8 * (q1 + 1)) with (8 * q1 + 8) by lia.
          do 3 zstep. zstep. if_cases K0.
          + pose proof (q_read mm q1 qj QA (sh (p2 + NN - 1)) ltac:((first [clear - QB E; lia | lia]))) as RD.
            do 6 zstep.
            zstep. if_cases K1; zify_cond K1.
            * apply asn_j5b.
            * replace (Z_to_bv 64 (sh p2)) with (Z_to_bv 64 (sh p2 + 0)) by (f_equal; lia).
              eapply (asn_loop2 q1 qj); first [eassumption | reflexivity | lia].
          + eapply asn_jf; [exact MIm | exact FR1 | exact FR | exact STm | exact MU | exact WM].
      Qed.
    End CHK2.

  End K.
End STRNCMP.
