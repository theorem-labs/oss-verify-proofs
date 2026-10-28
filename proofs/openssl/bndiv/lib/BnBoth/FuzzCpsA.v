(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA ZBridge RzCPS.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import Prelim Malloc Stdio Prog BnBase BnModel BnTree BnInv BnSpecs BnMInv BnCorrect.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_unwind_chain RT_iface RT_client_kit D_defs D_libiface.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnAsan Require Import AsKit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.BnBoth Require Import LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA EdgesA EdgesInstA LibaA W_fuzzA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
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

Section Fuzz.
  Variable RT : rt_sig.
  Variable RC : rt_contracts RT.
  Hypothesis LIBW_cs : forall x, rin_ivs LIBW_A x -> client_static x.

  (* [comment removed for export] *)
  Definition ar_of (SP0 : Z) (PMc : Model -> Prop) (FD : fdfs_only PMc) (MST : mat_stable PMc) : ARun := mkARun RT RC SP0 PMc FD MST LIBW_cs.

  Variables (BN_MUL_STACK BN_DIV_STACK ECE_STACK BN_MUL_COST BN_DIV_COST ECE_COST : Z).
  Hypothesis STK_MUL : 0 <= BN_MUL_STACK <= 0x18000.
  Hypothesis STK_DIV : 0 <= BN_DIV_STACK <= 0x18000.
  Hypothesis STK_ECE : 0 <= ECE_STACK <= 0x18000.
  Hypothesis COST_MUL : 0 <= BN_MUL_COST.
  Hypothesis COST_DIV : 0 <= BN_DIV_COST.
  Hypothesis COST_ECE : 0 <= ECE_COST.
  Hypothesis COST_TOTAL : 3 * MC + BN_DIV_COST + BN_MUL_COST + ECE_COST <= FUZZ_COST.

  (* [comment removed for export] *)
  Hypothesis WALK : forall SP0 PMc FD MST,
    let AR := ar_of SP0 PMc FD MST in
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (ls : lstate bptr) (OW LB : list block) (AD : bn_addrs) (EA : err_addrs)
      (lo : Z) (D : Z) (d : list Z),
    @bn_preA AR Σ ls m OW LB AD EA sp lo FUZZ_STACK_A (FUZZ_TOTAL BN_MUL_COST BN_DIV_COST ECE_COST) -> tp = wz TP_A ->
    payload_okA m LB D d -> D <= lo -> a0 = wz D -> a1 = wz (zlength d) ->
    @implA AR _ (fuzz_one (tree_ops bptr) d ls) Σ
      (@bn_postA AR _ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA (FUZZ_TOTAL BN_MUL_COST BN_DIV_COST ECE_COST)
                (fun rc _ _ a0' => rc = 0 /\ a0' = wz 0))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz LX_FUZZ_ENTRY) fc None m (seg_rom bsegs)).

  Theorem fuzz_one_cpsA_of_walk : fuzz_one_cps' RT (LIBA RT).
  Proof.
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo LW CL
           FD MST -> -> -> Hd Hdlo Hlen BY HCL PERM HLIBA FR0 CLpos LIVE COST S0 HART MI ST SP0W LOSTK SPT SP16 SPSP0.
    set (AR := ar_of (rt_sp0 RT Σ) PMc FD MST).
    destruct HLIBA as (ls & OW & AD & EA & -> & ND & OKB & LS & INV & BAL).
    destruct (fresh_blocks CL (map blk_id OW)) as (LB & ELB & NDLB & FRESH).
    set (dz := map bv_unsigned bs).
    assert (EDZ : to_bytes dz = bs) by (apply to_bytes_unsigned).
    assert (LDZ : zlength dz = Z.of_nat (length bs)) by (unfold zlength, dz; rewrite length_map; reflexivity).
    assert (HEAP : @AHEAP AR Σ OW LB m).
    { unfold AHEAP. split; [exact HART|]. split; [reflexivity|]. split; [exact FR0|].
      split; [rewrite map_app, ELB; exact PERM|].
      split. { rewrite map_app. apply nodup_app_intro; [exact ND | exact NDLB|].
               intros q Hq1 Hq2. apply in_map_iff in Hq2 as (b & <- & Hb). exact (FRESH b Hb Hq1). }
      split; [exact OKB|]. apply Forall_forall. intros b Hb. apply (CLpos (blk_addr b)). rewrite <- ELB. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
    pose proof LS as LS0. destruct (lib_state_h_parts _ _ _ _ _ _ LS) as (_ & _ & _ & SOK).
    assert (LENL : Z.of_nat (length (rt_live RT Σ)) = Z.of_nat (length OW) + Z.of_nat (length LB)).
    { rewrite (Permutation_length PERM), length_app, length_map, <- ELB, length_map. lia. }
    assert (PRE : @bn_preA AR Σ ls m OW LB AD EA sp lo FUZZ_STACK_A (FUZZ_TOTAL BN_MUL_COST BN_DIV_COST ECE_COST)).
    { unfold bn_preA. split; [exact HEAP|]. split; [exact LS|]. split; [exact ST|].
      split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 AR ar_of]; exact SP0W|].
      split; [unfold FUZZ_STACK_A; unfold FUZZ_STACK in LOSTK; lia|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact MI|].
      split; [unfold cnt_ok, cnt_bal; unfold FUZZ_LIVE in LIVE; lia|].
      unfold FUZZ_TOTAL. exact (Z.le_trans _ _ _ COST_TOTAL COST). }
    assert (PL : payload_okA m LB d dz).
    { unfold payload_okA. rewrite EDZ, LDZ. split; [exact BY|].
      split. { unfold dz. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _).
               pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
      split; [lia|]. split; [lia|].
      destruct HCL as [(p & n & Hin & H1 & H2)|E]; [right | left; unfold dz; rewrite E; reflexivity].
      rewrite <- ELB in Hin. apply in_map_iff in Hin as (b & Eb & Hb). unfold blk_an in Eb. injection Eb as <- <-.
      exists b. split; [exact Hb|]. lia. }
    (* [comment removed for export] *)
    assert (IMP : @implA AR _ (bn_one ls dz) Σ
              (fun r Σ' ms' => @bn_postA AR _ ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ ls OW LB lo m AD EA (FUZZ_TOTAL BN_MUL_COST BN_DIV_COST ECE_COST)
                                 (fun rc _ _ a0' => rc = 0 /\ a0' = wz 0) (snd r, fst r) Σ' ms')
              (entry_st ra sp gp (Z_to_bv 64 12430928) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length bs))) a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)).
    { unfold bn_one. eapply implA_bind.
      - eapply (WALK (rt_sp0 RT Σ) PMc FD MST) with (lo := lo) (D := d) (d := dz); [exact PRE | reflexivity | exact PL | exact Hdlo | reflexivity | rewrite LDZ; reflexivity].
      - cbv beta. intros [rc ls'] Σ' ms' PO. apply implA_ret. cbn [fst snd]. exact PO. }
    eapply cps_conseq; [exact (@implA_run AR _ (bn_one ls dz) Σ _ _ (blocks_of ls) _ IMP (fuzz_one_wp ls dz (blocks_of ls) INV)) | intros c Hc; exact Hc |].
    intros c ([ls' rc] & X' & Σ' & (INV' & ERC) & Hc). cbn [fst snd] in *.
    destruct (ASTA_unpack RT Σ' PMc _ c Hc) as (ms' & PO & Hc').
    unfold bn_postA in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & F' & fc' & m' & OW' & -> & HEAP' & LS' & ST' & MI'
                    & AXP & CR & CNT & RST & (_ & ->)).
    destruct (lib_state_h_parts _ _ _ _ _ _ LS') as (_ & _ & _ & SOK').
    pose proof HEAP' as (HART' & HSP0' & HFR' & PERM' & ND' & OKB' & _).
    exists Σ', (map blk_an OW').
    split.
    { eapply ASTA_conseq; [exact Hc'|]. intros ms0 <-. exists m'.
      split. { unfold ret_st. exists y0, y1, y2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, F', fc'. reflexivity. }
      split. { unfold rt_after_f. split; [exact HART'|]. split; [exact MI' | exact ST']. }
      split.
      { (* [comment removed for export] *)
        intros a Ha Ho. apply (agree_on_D _ _ _ AXP). unfold ax_client. split.
        - intros HL. apply libw_in_LIB_FP in HL. destruct HL as (l & h & Hin & Hr).
          assert (O : outside LIB_FP (bv_unsigned a)) by (unfold LIB_FPE in Ho; cbn [outside] in Ho; exact (proj2 Ho)).
          clear - O Hin Hr. unfold LIB_FP in *. cbn [In] in Hin. cbn [outside] in O.
          repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
        - destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
          + left. exact Ha.
          + right. left. exact Ha.
          + right. right. apply in_live_blocks. rewrite ELB. exact Ha.
          + destruct Ha as (f & k & [] & _).
          + destruct Ha as (f & k & [] & _). }
      exists ls', OW', AD, EA. split; [reflexivity|]. split; [rewrite map_app in ND'; exact (nodup_app_l _ _ ND')|]. split; [exact OKB'|]. split; [exact LS'|].
      split. { destruct INV' as (I1 & I2 & I3). split; [exact I1|]. split; [unfold own; reflexivity | exact I3]. }
      unfold cnt_eq in CNT. lia. }
    split; [rewrite map_app, ELB in PERM'; exact PERM'|].
    split; [exact HFR'|]. split; [exact HSP0'|].
    split. { unfold FUZZ_TOTAL in CR. change (@ar_RT AR) with RT in CR. lia. }
    pose proof (blocks_of_le23 ls' SOK') as B23.
    change (@ar_RT AR) with RT in PERM'.
    rewrite (Permutation_length PERM'), length_map, length_app, LENL. unfold cnt_eq, cnt_bal in CNT. unfold FUZZ_LIVE. lia.
  Qed.
End Fuzz.

(* [comment removed for export] *)
Lemma LIBW_A_client_static : forall x, rin_ivs LIBW_A x -> client_static x.
Proof.
  intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold client_static, in_ranges, CLIENT_STATIC, RT_STATIC. split.
  - destruct H as [H|[H|[H|[]]]].
    + exists 0x5e6630, 0x6a0398. split; [cbn; tauto | lia].
    + exists 0xbd6050, 0xbfc730. split; [cbn; tauto | lia].
    + exists 0xbd6050, 0xbfc730. split; [cbn; tauto | lia].
  - intros (l & h & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Theorem fuzz_one_cpsA : forall (RT : rt_sig) (RC : rt_contracts RT)
    (BN_MUL_STACK BN_DIV_STACK ECE_STACK BN_MUL_COST BN_DIV_COST ECE_COST : Z),
  0 <= BN_MUL_STACK <= 0x18000 -> 0 <= BN_DIV_STACK <= 0x18000 -> 0 <= ECE_STACK <= 0x18000 ->
  0 <= BN_MUL_COST -> 0 <= BN_DIV_COST -> 0 <= ECE_COST -> 3 * MC + BN_DIV_COST + BN_MUL_COST + ECE_COST <= FUZZ_COST ->
  (forall AR : ARun, @BN_mul_walkA_stmt AR UK_A BN_MUL_STACK BN_MUL_COST) ->
  (forall AR : ARun, @BN_div_walkA_stmt AR UK_A BN_DIV_STACK BN_DIV_COST) ->
  (forall AR : ARun, @ERR_clear_error_cpsA_stmt AR ECE_STACK ECE_COST) ->
  fuzz_one_cps' RT (LIBA RT).
Proof.
  intros RT RC BN_MUL_STACK BN_DIV_STACK ECE_STACK BN_MUL_COST BN_DIV_COST ECE_COST S1 S2 S3 C1 C2 C3 CT HMUL HDIV HECE.
  eapply (fuzz_one_cpsA_of_walk RT RC LIBW_A_client_static BN_MUL_COST BN_DIV_COST ECE_COST CT).
  intros SP0 PMc FD MST AR.
  exact (@fuzz_one_walkA AR UK_A BE_A BN_MUL_STACK BN_DIV_STACK ECE_STACK BN_MUL_COST BN_DIV_COST ECE_COST S1 S2 S3 C1 C2 C3 (HMUL AR) (HDIV AR) (HECE AR)).
Qed.
