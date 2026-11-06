(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Prelim Malloc Stdio Prog BnBase BnModel BnTree BnInv BgState BgInv BgLib BgExp BgTree.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgB Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs D_libiface.
From OSSVerify.Proofs.openssl.bignum.lib.BnBoth Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require Import LibKitA ARun BnHeapA ImplA UnwindA EdgesA EdgesInstA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnBoth Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepB Require Import BgRepDefs BgRep BgLayer BgIface BgPlace LibaBg.
From OSSVerify.Proofs.openssl.bignum.lib.BgHXB Require HxbEceIface HxbEceMain.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRB Require Import ExpKitA W_fuzzA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import FuzzModelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma fresh_blocks : forall (CL : list (Z * Z)) (avoid : list bptr),
  exists LB : list block, map blk_an LB = CL /\ List.NoDup (map blk_id LB) /\ (forall b, In b LB -> ~ In (blk_id b) avoid).
Proof.
  induction CL as [|[p n] CL IH]; intros avoid.
  - exists []. split; [reflexivity|]. split; [constructor | intros b []].
  - destruct (IH avoid) as (LB & E & ND & HA).
    destruct (bptr_fresh (avoid ++ map blk_id LB)) as [q Hq].
    exists ((q, p, n) :: LB). split; [cbn [map]; unfold blk_an at 1; cbn [blk_addr blk_size fst snd]; rewrite E; reflexivity|].
    split.
    + cbn [map]. constructor; [|exact ND]. cbn [blk_id fst]. intros Hin. apply Hq. apply in_or_app. right. exact Hin.
    + intros b [<-|Hb]; [cbn [blk_id fst]; intros Hin; apply Hq; apply in_or_app; left; exact Hin | exact (HA b Hb)].
Qed.

Lemma nodup_app_intro : forall {A} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) -> List.NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [|a l1 IH]; intros l2 H1 H2 HD; [exact H2|]. cbn [app]. inversion H1 as [|? ? Ha H1']. subst.
  constructor.
  - intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Ha Hin) | exact (HD a (or_introl eq_refl) Hin)].
  - apply IH; [exact H1' | exact H2 | intros x Hx1 Hx2; exact (HD x (or_intror Hx1) Hx2)].
Qed.

Lemma to_bytes_unsigned : forall bs : list byte, to_bytes (map bv_unsigned bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. unfold to_bytes in *. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma LIBW_A_client_static : forall x, rin_ivs LIBW_A x -> client_static x.
Proof.
  intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold client_static, in_ranges, CLIENT_STATIC, RT_STATIC. split.
  - destruct H as [H|[H|[H|[]]]]; eexists _, _.
    + split; [left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
  - intros (l & h & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Lemma libw_extra_not_static : forall x, CONST_ONE <= x < CONST_ONE + BN_STRUCT_SZ \/ GOT_BN_ADD <= x < GOT_BN_ADD + 16 -> ~ client_static x.
Proof.
  intros x H (HC & _). unfold in_ranges, CLIENT_STATIC in HC. destruct HC as (l & h & Hin & Hr). cbn [In] in Hin.
  unfold CONST_ONE, BN_STRUCT_SZ, GOT_BN_ADD in H.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

Section Fuzz.
  Variable RT : rt_sig.
  Variable RC : rt_contracts RT.
  Variable RC2 : rt_contracts2 RT.

  Definition ar_of (SP0 : Z) (PMc : Model -> Prop) (FD : fdfs_only PMc) (MST : mat_stable PMc) : ARun :=
    mkARun RT RC SP0 PMc FD MST LIBW_A_client_static [] RC2.

  Variables (EXP_COST SIMPLE_COST : Z).
  Hypothesis COST_TOTAL : FUZZ_TOTAL EXP_COST SIMPLE_COST <= FUZZ_COST.

  Hypothesis WALK : forall SP0 PMc FD MST,
    let AR := ar_of SP0 PMc FD MST in
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (EA : BnRepDefs.err_addrs)
      (lo : Z) (D : Z) (d : list Z),
    @bn_preA AR Σ st_init m OW LB pl_empty EA sp lo FUZZ_STACK_A (FUZZ_TOTAL EXP_COST SIMPLE_COST) -> tp = wz TP_A ->
    cnt_bal st_init OW + Z.of_nat (length LB) + 80 <= LIVE_MAX ->
    (bv_unsigned s0 <= lo \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
    payload_okA m LB D d -> D <= lo -> a0 = wz D -> a1 = wz (zlength d) ->
    @implA AR _ (fuzz_one_gA (tree_ops bptr) d st_init) Σ
      (@bn_postA AR _ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st_init OW LB lo m pl_empty EA (FUZZ_TOTAL EXP_COST SIMPLE_COST)
                (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom bgbsegs)).

  Theorem fuzz_one_cpsA_of_walk : fuzz_one_cps' RT (LIBA RT).
  Proof.
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo LW CL
           FD MST -> -> -> Hd Hdlo Hlen BY HCL PERM HLIBA FR0 CLpos LIVE COST S0 HART MI ST SP0W LOSTK SPT SP16 SPSP0.
    set (AR := ar_of (rt_sp0 RT Σ) PMc FD MST).
    assert (FRN : @ar_FR AR = []) by reflexivity.
    destruct HLIBA as (OW & EA & -> & ND & OKB & LS & NDE).
    destruct (fresh_blocks CL (map blk_id OW)) as (LB & ELB & NDLB & FRESH).
    set (dz := map bv_unsigned bs).
    assert (EDZ : to_bytes dz = bs) by (apply to_bytes_unsigned).
    assert (LDZ : zlength dz = Z.of_nat (length bs)) by (unfold zlength, dz; rewrite length_map; reflexivity).
    assert (HEAP : @AHEAP AR Σ OW LB m).
    { apply (@AH_intro_nofr AR); [exact FRN | exact HART | reflexivity | exact FR0 | rewrite map_app, ELB; exact PERM | | exact OKB |].
      - rewrite map_app. apply nodup_app_intro; [exact ND | exact NDLB|].
        intros q Hq1 Hq2. apply in_map_iff in Hq2 as (b & <- & Hb). exact (FRESH b Hb Hq1).
      - apply Forall_forall. intros b Hb. apply (CLpos (blk_addr b)). rewrite <- ELB. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
    assert (LENL : Z.of_nat (length (rt_live RT Σ)) = Z.of_nat (length OW) + Z.of_nat (length LB)).
    { rewrite (Permutation_length PERM), length_app, length_map, <- ELB, length_map. lia. }
    assert (B0 : blocks_of (st_init : bstate bptr) = []) by reflexivity.
    assert (CNT80 : cnt_bal st_init OW + Z.of_nat (length LB) + 80 <= LIVE_MAX).
    { unfold cnt_bal. rewrite B0. cbn [length]. unfold FUZZ_LIVE in LIVE. clear - LIVE LENL. lia. }
    assert (PRE : @bn_preA AR Σ st_init m OW LB pl_empty EA sp lo FUZZ_STACK_A (FUZZ_TOTAL EXP_COST SIMPLE_COST)).
    { unfold bn_preA. split; [exact HEAP|]. split; [exact LS|].
      split. { apply frames_ok_empty; [unfold BnHeapA.ACEIL; cbn [ar_SP0 AR ar_of]; unfold FUZZ_STACK in LOSTK; clear - SP0W LOSTK; lia | unfold USTACK_TOP; clear; lia]. }
      split; [exact ST|].
      split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 AR ar_of]; exact SP0W|].
      split; [unfold FUZZ_STACK_A, FUZZ_CALLEE_MAX; unfold FUZZ_STACK in LOSTK; clear - LOSTK; lia|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact MI|].
      split; [unfold cnt_ok; clear - CNT80; lia|].
      split; [exact (Z.le_trans _ _ _ COST_TOTAL COST)|].
      split; [intros iv Hiv; rewrite pl_frames_empty in Hiv; destruct Hiv | apply pl_frames_empty]. }
    assert (PL : payload_okA m LB d dz).
    { unfold payload_okA. rewrite EDZ, LDZ. split; [exact BY|].
      split. { unfold dz. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _).
               pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
      split; [clear - Hd; lia|]. split; [clear - Hlen; lia|].
      destruct HCL as [(p & n & Hin & H1 & H2)|E]; [right | left; unfold dz; rewrite E; reflexivity].
      rewrite <- ELB in Hin. apply in_map_iff in Hin as (b & Eb & Hb). unfold blk_an in Eb. injection Eb as <- <-.
      exists b. split; [exact Hb|]. clear - H1 H2. lia. }

    assert (IMP : @implA AR _ (bg_oneA dz) Σ
              (fun rc Σ' ms' => exists ls' : bstate bptr,
                                 @bn_postA AR _ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ st_init OW LB lo m pl_empty EA (FUZZ_TOTAL EXP_COST SIMPLE_COST)
                                   (fun (rc : Z) (_ : bstate bptr) (_ : list block) (_ : placement) (a0' : word) => rc = 0 /\ a0' = wz 0) (rc, ls') Σ' ms')
              (entry_st ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length bs))) a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)).
    { unfold bg_oneA. eapply implA_bind.
      - eapply (WALK (rt_sp0 RT Σ) PMc FD MST) with (lo := lo) (D := d) (d := dz);
          [exact PRE | reflexivity | exact CNT80 | exact S0 | exact PL | exact Hdlo | reflexivity | rewrite LDZ; reflexivity].
      - cbv beta. intros [rc ls'] Σ' ms' PO. apply implA_ret. cbn [fst snd]. exists ls'. exact PO. }
    eapply cps_conseq; [exact (@implA_run AR _ (bg_oneA dz) Σ _ _ [] _ IMP (fuzz_one_gwpA dz)) | intros c Hc; exact Hc |].
    intros c (rc & X' & Σ' & (_ & ERC) & Hc). cbn [fst snd] in *.
    destruct (ASTA_unpack RT Σ' PMc _ c Hc) as (ms' & (ls' & PO) & Hc').
    unfold bn_postA in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & PL' & -> & HEAP' & LS' & ST' & MI'
                    & AXP & CR & CNT & RST & (_ & ->)).
    destruct (@AH_nofr AR _ _ _ _ FRN HEAP') as (HFR' & PERM').
    pose proof (AH_art _ _ _ _ HEAP') as HART'. pose proof (AH_sp0 _ _ _ _ HEAP') as HSP0'. pose proof (AH_nodup _ _ _ _ HEAP') as ND'.
    pose proof HEAP' as (_ & _ & _ & _ & _ & OKB' & _).
    pose proof (lib_state_h_parts _ _ _ _ _ _ LS') as (WFS' & _).
    destruct (lib_state_init m' OW' (lib_state_fini_any ls' m' OW' PL' EA LS' NDE)) as (EA' & LS0' & NDE').
    exists Σ', (map blk_an OW').
    split.
    { eapply ASTA_conseq; [exact Hc'|]. intros ms0 <-. exists m'.
      split. { unfold ret_st. exists y0, y1, y2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc'. reflexivity. }
      split. { unfold rt_after_f. split; [exact HART'|]. split; [exact MI' | exact ST']. }
      split.
      {
        intros a Ha Ho. apply (agree_on_D _ _ _ AXP). unfold ax_client.
        assert (O : outside LIB_FP (bv_unsigned a)) by (unfold LIB_FPE in Ho; cbn [outside] in Ho; exact (proj2 Ho)).
        assert (CA : aclient_addr LB (bv_unsigned sp) (bv_unsigned a)).
        { destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
          - left. exact Ha.
          - right. left. exact Ha.
          - right. right. apply in_live_blocks. rewrite ELB. exact Ha.
          - destruct Ha as (f & k & [] & _).
          - destruct Ha as (f & k & [] & _). }
        split; [|exact CA].
        unfold XW. rewrite pl_frames_empty, app_nil_r. intros HL. apply (proj1 (libw_cases _)) in HL. destruct HL as [HL|HX].
        - apply libw_in_LIB_FP in HL. destruct HL as (l & h & Hin & Hr).
          clear - O Hin Hr. unfold LIB_FP in *. cbn [In] in Hin. cbn [outside] in O.
          repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
        -
          pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3.
          destruct CA as [CA|[CA|(b & Hb & Hr)]].
          + unfold BnHeapA.ACEIL in *. cbn [ar_SP0 AR ar_of] in *. unfold FUZZ_STACK in LOSTK. unfold CONST_ONE, BN_STRUCT_SZ, GOT_BN_ADD in HX. clear - CA HX SP0W LOSTK CL1 CL2 CL3. lia.
          + exact (libw_extra_not_static _ HX CA).
          + pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (R1 & _ & R3 & R4 & R5).
            unfold CONST_ONE, BN_STRUCT_SZ, GOT_BN_ADD in HX. clear - HX Hr R1 R3 R5. lia. }
      exists OW', EA'. split; [reflexivity|]. split; [rewrite map_app in ND'; exact (nodup_app_l _ _ ND')|]. split; [exact OKB'|]. split; [exact LS0' | exact NDE']. }
    split; [rewrite map_app, ELB in PERM'; exact PERM'|].
    split; [exact HFR'|]. split; [exact HSP0'|].
    split. { change (@ar_RT AR) with RT in CR. clear - CR COST_TOTAL. lia. }
    pose proof (proj1 (st_wf_blocks ls' WFS')) as B63. unfold NFIX, BG_POOL in B63.
    change (@ar_RT AR) with RT in PERM'.
    rewrite (Permutation_length PERM'), length_map, length_app, LENL. unfold cnt_eq, cnt_bal in CNT. rewrite B0 in CNT. cbn [length] in CNT. unfold FUZZ_LIVE.
    clear - CNT B63. lia.
  Qed.
End Fuzz.

Theorem fuzz_one_cpsA : forall (RT : rt_sig) (RC : rt_contracts RT) (RC2 : rt_contracts2 RT)
    (EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST : Z) (EXP_DEPTH SIMPLE_DEPTH : nat),
  0 <= EXP_STACK <= FUZZ_CALLEE_MAX -> 0 <= SIMPLE_STACK <= FUZZ_CALLEE_MAX -> 0 <= EXP_COST -> 0 <= SIMPLE_COST ->
  (EXP_DEPTH <= 4)%nat -> (SIMPLE_DEPTH <= 4)%nat ->
  FUZZ_TOTAL EXP_COST SIMPLE_COST <= FUZZ_COST ->
  (forall AR : ARun, @ar_FR AR = [] -> @exp_stmtA_f AR UK_A BN_MOD_EXP EXP_STACK EXP_COST EXP_DEPTH (BN_mod_exp (tree_ops bptr)) None) ->
  (forall AR : ARun, @ar_FR AR = [] -> @exp_stmtA AR UK_A BN_MOD_EXP_SIMPLE SIMPLE_STACK SIMPLE_COST SIMPLE_DEPTH (BN_mod_exp_simple (tree_ops bptr)) None) ->
  fuzz_one_cps' RT (LIBA RT).
Proof.
  intros RT RC RC2 EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST EXP_DEPTH SIMPLE_DEPTH S1 S2 C1 C2 D1 D2 CT HEXP HSIM.
  eapply (fuzz_one_cpsA_of_walk RT RC RC2 EXP_COST SIMPLE_COST CT).
  intros SP0 PMc FD MST AR.
  exact (@fuzz_one_walkA AR UK_A BE_A EXP_STACK EXP_COST SIMPLE_STACK SIMPLE_COST EXP_DEPTH SIMPLE_DEPTH S1 S2 C1 C2 eq_refl D1 D2
           (HEXP AR eq_refl) (HSIM AR eq_refl) (HxbEceMain.ece_cps_proved AR eq_refl)).
Qed.
