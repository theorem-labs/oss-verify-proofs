(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac MState ZBridge RzCPS Nodes. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Stdio Prog LibProg LibSafe ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApLogic ApInv ApErr ApParse ApPrim ApBridge ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import CtSizes CtWire CtTime CtModel CtLogic CtSpecs4 CtOwner CtBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_libiface R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA ImplA RT_iface2 UnwindA EdgesInstA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require BnRepDefs BnRepA BnIfaceA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface LibaAp W_get_objectA CtFuzzStmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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

Lemma to_bytes_unsigned : forall bs : list (bv 8), to_bytes (map bv_unsigned bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. unfold to_bytes in *. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma LIBW_A_client_static : forall x, rin_ivs LIBW_A x -> client_static x.
Proof.
  intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold client_static, in_ranges, CLIENT_STATIC, RT_STATIC. split.
  - destruct H as [H|[H|[H|[H|[H|[H|[]]]]]]]; eexists _, _.
    + split; [left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
    + split; [right; right; left; reflexivity | lia].
  - intros (l & h & Hin & Hr). cbn [In] in Hin.
    repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin.
Qed.

(* [comment removed for export] *)
Lemma LIBW_A_FPE : forall x, rin_ivs LIBW_A x -> ~ outside LIB_FPE x.
Proof. intros x H. unfold LIBW_A in H. cbn [rin_ivs fst snd] in H. unfold LIB_FPE, LIB_FP. cbn [outside]. lia. Qed.

(* [comment removed for export] *)
Lemma ap_state_bo : forall st m OW E bo bo', ap_state st m OW E bo -> ap_state st m OW E bo'.
Proof.
  intros st m OW E bo bo' (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact I| exact A7].
Qed.

(* [comment removed for export] *)
Lemma room0_of_fuzz : forall L, lroom3 L FUZZ_LIVE FUZZ_PB FUZZ_NB -> room0 (map snd L).
Proof.
  intros L H. apply (room0_of_lroom3 L FUZZ_LIVE FUZZ_PB FUZZ_NB H); unfold FUZZ_LIVE, FUZZ_PB, FUZZ_NB, CT_NBT, CT_SMB, CT_NSEC; clear; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Fuzz.
  Variable RT : rt_sig.
  Variable RC : rt_contracts RT.

  (* [comment removed for export] *)
  Definition ar_of (SP0 : Z) (PMc : Model -> Prop) (FD : fdfs_only PMc) (MST : mat_stable PMc) : ARun :=
    mkARun RT RC SP0 PMc FD MST LIBW_A_client_static [] (rt_contracts2_of RT RC).

  (* [comment removed for export] *)
  Hypothesis WALK : forall SP0 PMc FD MST, @ct_fuzz_stmtA (ar_of SP0 PMc FD MST) UK_A.

  Theorem fuzz_one_cpsA_of_walk : fuzz_one_cps' RT (LIBA RT).
  Proof using WALK RC.
    intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo LW CL
           FD MST -> -> -> ERA Hd Hdlo Hlen BY HCL PERM HLIBA FR0 CLpos LROOM COST S0 HART MI ST SP0W LOSTK SPT SP16 SPSP0.
    set (AR := ar_of (rt_sp0 RT Σ) PMc FD MST).
    assert (FRN : @ar_FR AR = []) by reflexivity.
    destruct HLIBA as (ls & OW & -> & ND & OKB & (E & (WF & ECNF & nw & AS) & IDS & DC) & LINV).
    destruct (ct_linv_nil ls (ls_blocks ls) LINV) as (_ & LSB & _). rewrite LSB in LINV.
    destruct (fresh_blocks CL (map blk_id OW)) as (LB & ELB & NDLB & FRESH).
    set (dz := map bv_unsigned bs).
    assert (EDZ : to_bytes dz = bs) by (apply to_bytes_unsigned).
    assert (LDZ : zlength dz = Z.of_nat (length bs)) by (unfold zlength, dz; rewrite length_map; reflexivity).
    assert (PF : Forall (fun c => 0 <= c < 256) dz).
    { unfold dz. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (b & <- & _).
      pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
    assert (HEAP : @AHEAP AR Σ OW LB m).
    { apply (@AH_intro_nofr AR); [exact FRN | exact HART | reflexivity | exact FR0 | rewrite map_app, ELB; exact PERM | | exact OKB |].
      - rewrite map_app. apply nodup_app_intro; [exact ND | exact NDLB|].
        intros q Hq1 Hq2. apply in_map_iff in Hq2 as (b & <- & Hb). exact (FRESH b Hb Hq1).
      - apply Forall_forall. intros b Hb. apply (CLpos (blk_addr b)). rewrite <- ELB. apply in_map_iff. exists b. split; [reflexivity | exact Hb]. }
    assert (PRE : @ap_preA AR Σ (st_of_ls ls) m OW LB E (0, nw) sp lo CT_FUZZ_STACK_A (CT_FUZZ_COST_A (zlength dz)) CT_FUZZ_FRAMES_A).
    { unfold ap_preA. split; [exact HEAP|]. split; [exact AS|]. split; [exact IDS|]. split; [exact DC|]. split; [exact ST|].
      split; [unfold BnHeapA.ACEIL; cbn [ar_SP0 AR ar_of]; exact SP0W|].
      split; [unfold CT_FUZZ_STACK_A; unfold FUZZ_STACK in *; clear - LOSTK; lia|].
      split; [exact SPT|]. split; [exact SP16|]. split; [exact MI|].
      split; [cbn [ar_RT AR ar_of]; unfold CT_FUZZ_COST_A; unfold FUZZ_COST in *; clear - COST; lia|].
      unfold CT_FUZZ_FRAMES_A. cbn [ar_FR AR ar_of length Z.of_nat]. unfold FRAMES_MAX. clear. cbn. lia. }
    assert (PL : payload_okA m LB d dz).
    { unfold payload_okA. rewrite EDZ, LDZ. split; [exact BY|]. split; [exact PF|].
      split; [clear - Hd; lia|]. split; [clear - Hd Hdlo LOSTK SPT Hlen; unfold USTACK_TOP, FUZZ_STACK in *; lia|]. split; [clear - Hlen; lia|].
      destruct HCL as [(p & n & Hin & H1 & H2)|E0]; [right | left; unfold dz; rewrite E0; reflexivity].
      rewrite <- ELB in Hin. apply in_map_iff in Hin as (b & Eb & Hb). unfold blk_an in Eb. injection Eb as <- <-.
      exists b. split; [exact Hb|]. clear - H1 H2. lia. }
    (* [comment removed for export] *)
    assert (UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) nil).
    { cbn [uw_chain]. unfold fp_stop. unfold FUZZ_STACK in LOSTK. clear - S0 Hdlo LOSTK. lia. }
    assert (CTX : @uk_ctx UK_A CT_FUZZ_ENTRY_A [bv_unsigned ra]).
    { rewrite ERA. unfold FUZZ_RA. rewrite unsigned_lit by (clear; lia). exact I_R_LLVMFuzzerTestOneInput_1eef54. }
    (* [comment removed for export] *)
    assert (IMP : @implAp AR _ (ct_one ls dz) Σ
              (fun r Σ' ms' => @ct_top_postA AR ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ LB E (0, nw) lo m d dz (snd r, st_of_ls (fst r)) Σ' ms')
              (entry_st ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 d) (Z_to_bv 64 (Z.of_nat (length bs))) a2 a3 a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m)).
    { unfold ct_one. rewrite (ct_bytes_id dz PF). eapply implAp_bind.
      - eapply (WALK (rt_sp0 RT Σ) PMc FD MST) with (lo := lo) (D := d) (d := dz);
          [exact PRE | reflexivity | exact UW | exact CTX | exact PL | reflexivity | rewrite LDZ; reflexivity].
      - cbv beta. intros [rc st'] Σ' ms' PO. apply implAp_ret. cbn [fst snd].
        pose proof PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F' & fc' & m' & OW' & bo' & E0 & PRE' & NF & _).
        cbn [fst snd] in NF. rewrite <- NF. exact PO. }
    pose proof (ct_one_awp realloc_crit shrink_crit inplace_crit ap_spre ct_grow ct_inI ls dz [] LINV
                  ltac:(unfold CT_MAX_INPUT; rewrite LDZ; clear - Hlen; lia)) as AWP.
    assert (LINK : @linked AR (map snd (rt_live RT Σ)) Σ []).
    { apply (@linked_intro0 AR). cbn [ar_RT AR ar_of]. exact (room0_of_fuzz _ LROOM). }
    eapply cps_conseq; [exact (@implAp_run AR _ _ _ _ _ (ct_one ls dz) Σ _ _ [] _ _ IMP AWP LINK) | intros c Hc; exact Hc |].
    intros c ([ls' rc] & X' & Σ' & LINV' & LINK' & Hc). cbn [fst snd] in *.
    destruct (ct_linv_nil ls' X' LINV') as (EX' & LSB' & _). subst X'.
    destruct (ASTA_unpack RT Σ' PMc _ c Hc) as (ms' & PO & Hc').
    unfold ct_top_postA in PO. cbn [fst snd] in PO.
    destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F' & fc' & m' & OW' & bo' & -> & PRE' & NF & AXP & CR & PAY' & ->).
    pose proof PRE' as (HEAP' & AS' & IDS' & DC' & ST' & _ & _ & _ & _ & MI' & _).
    destruct (@AH_nofr AR _ _ _ _ FRN HEAP') as (HFR' & PERM').
    pose proof (AH_art _ _ _ _ HEAP') as HART'. pose proof (AH_sp0 _ _ _ _ HEAP') as HSP0'. pose proof (AH_nodup _ _ _ _ HEAP') as ND'.
    pose proof HEAP' as (_ & _ & _ & _ & _ & OKB' & _).
    pose proof LINV' as ([WF' _] & _).
    exists Σ', (map blk_an OW').
    split.
    { eapply ASTA_conseq; [exact Hc'|]. intros ms0 <-. exists m'.
      split. { unfold ret_st, MallocRep.wz. exists y0, y1, y2, z1, z2, z3, z4, z5, z6, z7, y3, y4, y5, y6, F', fc'. reflexivity. }
      split. { unfold rt_after_f. split; [exact HART'|]. split; [exact MI' | exact ST']. }
      split.
      { (* [comment removed for export] *)
        intros a Ha Ho. apply (agree_on_D _ _ _ AXP). split; [intros HX; exact (LIBW_A_FPE _ HX Ho)|].
        destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
        - left. exact Ha.
        - right. left. exact Ha.
        - right. right. apply in_live_blocks. rewrite ELB. exact Ha.
        - destruct Ha as (f & k & [] & _).
        - destruct Ha as (f & k & [] & _). }
      exists ls', OW'. split; [reflexivity|]. split; [rewrite map_app in ND'; exact (nodup_app_l _ _ ND')|]. split; [exact OKB'|].
      split.
      - exists E. split; [split; [exact WF'| split; [exact ECNF| exists (snd bo'); exact (ap_state_bo _ _ _ _ _ _ AS')]]|].
        split; [exact IDS'| exact DC'].
      - rewrite LSB'. exact LINV'. }
    split; [rewrite map_app, ELB in PERM'; exact PERM'|].
    split; [exact HFR'|]. split; [exact HSP0'|].
    split. { change (@ar_RT AR) with RT in CR. unfold CT_FUZZ_COST_A in CR. clear - CR. lia. }
    (* [comment removed for export] *)
    change (@ar_RT AR) with RT in PERM', LINK'. destruct LINK' as (LK & _ & _). cbn [map] in LK. rewrite app_nil_r in LK.
    pose proof (Permutation_length LK) as LL. rewrite !length_map in LL.
    pose proof (lwsum_perm _ _ LK) as LP. rewrite <- !psum_sizes in LP.
    pose proof (bigcnt_perm _ _ LK) as LB2. rewrite <- !nbig_sizes in LB2.
    unfold KEEP_LIVE, KEEP_PB, KEEP_NB, LW_MAX. rewrite LL, LP, LB2. clear. repeat split; try lia.
    all: unfold lw; cbn; lia.
  Qed.
End Fuzz.
