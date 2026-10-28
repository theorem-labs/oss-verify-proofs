(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HFpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpK LbB_HEmpD LbB_HEmpI LbB_HEmpI2
  LbB_HEmpI3 LbB_HEmpI4 LbB_HEmpX LbB_HEmpR LbB_HEmpN LbB_HEmpF.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma w_sltuE : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_SLTU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (if a <? b then 1 else 0).
Proof.
  intros a b Ha Hb. apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
  destruct (a <? b); rewrite u64_of_Z by lia; reflexivity.
Qed.

Lemma land_odd_even : forall x, 0 <= x -> Z.land (2 * x + 1) (2 * x) = 2 * x.
Proof.
  intros x Hx. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
  destruct (Z.eq_dec n 0) as [->|Hne].
  - rewrite Z.testbit_even_0. apply Bool.andb_false_r.
  - replace n with (Z.succ (n - 1)) by lia. rewrite Z.testbit_odd_succ, Z.testbit_even_succ by lia. apply Bool.andb_diag.
Qed.

Lemma bseq_lt24 : forall bc, In bc BSEQ -> bc <> BSEQ_LAST -> 0 <= bc < 2 ^ 24.
Proof.
  intros bc Hin Hl. unfold BSEQ in Hin. unfold BSEQ_LAST in Hl.
  repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin.
Qed.

Lemma grq_nreq : forall bc sz, In bc BSEQ -> 0 <= sz -> sz <= bc -> (bc = 0 \/ sz = bc) -> grq bc (sz + 1) = nreq bc.
Proof.
  intros bc sz Hin Hsz Hle G.
  assert (Hs : sz = bc) by lia. subst sz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin]; [vm_compute; reflexivity|]). destruct Hin.
Qed.

Definition E_LF : Z := 0xfa68c.
Definition E_FLW : Z := 0xfa6b8.
Definition E_GR : Z := 0xfa6d8.

Section EmpL.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis REH : reh_stmt H EMP_U32.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc key : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).

  Abbreviation GPREx := (GPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation IPREx := (IPRE H ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).
  Abbreviation QIx := (QI H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0).

  Definition LPRE (s : as_St H) (mo : Model) (m : mem) (errv' : word) (LB' LBm : list block) (p : Z) : Prop :=
    as_MPRES H mo0 mo
    /\ FRAME ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 spz m /\ spz mod 16 = 0 /\ 2 ^ 45 <= spf spz /\ spz <= 2 ^ 47
    /\ bv_unsigned ra mod 2 = 0
    /\ mem_inv asegs m /\ stk asegs m lo spz /\ rw_cells asegs m (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m B
    /\ tp = Z_to_bv 64 ATP /\ aceil <= spf spz /\ aceil <= lo /\ lo <= spf spz - AREH_STACK /\ spz <= shi /\ spz <= B /\ B < 2 ^ 64
    /\ map_live_frame LF obj /\ obj + 40 <= aceil
    /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') m obj bl bc ents /\ umap_sh m 24 (bl, bc, ents)
    /\ bc <> BSEQ_LAST /\ Zlength ents + 1 < 2 ^ 24 /\ 0 <= key < 2 ^ 32
    /\ addressable m obj 40 /\ wr_at asegs m obj 40
    /\ (forall b, In b LB' -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj)
    /\ 0 < p /\ p + 24 <= 2 ^ 47 /\ p mod 16 = 0 /\ apart p 24 obj 40
    /\ (forall q n, In (q, n) (umap_blocks 24 bl bc ents) -> apart p 24 q n)
    /\ rw_cells asegs m p [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0)] /\ addressable m p 24
    /\ as_RHEAP H s LB' m /\ Permutation LB' (LB0 ++ LBm)
    /\ Permutation (lbl LBm) ((p, 24) :: umap_blocks 24 bl bc ents)
    /\ lb_own LBm m
    /\ xpres H LB0 spz [(obj, obj + 40)] m0 m
    /\ as_RFS H LF m /\ ACONST m /\ stack0 m lo shi
    /\ as_AL H s >= as_AL H sk0 /\ 0 <= as_AL H s
    /\ lb_small LB' + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX /\ Z.of_nat (length LB') + 1 <= RT_CNT_MAX
    /\ nlarge LB' + nlg (8 * bseq_next bc) <= RT_LARGE_MAX /\ ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s)
    /\ trace_ok (as_TR H) APC0_FREE [emp_del_ra EMP_U32].

  Lemma lpre_gpre : forall s mo m errv' LB' LBm p, LPRE s mo m errv' LB' LBm p -> (bc = 0 \/ Zlength ents = bc) ->
    GPREx s mo m errv' LB' LBm p.
  Proof.
    intros s mo m errv' LB' LBm p LP GROW.
    destruct LP as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                    & U & SH & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & P16 & PO & PA & NC & ADP
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RS & RC & RL & RICM & TRK).
    unfold GPRE. repeat (split; [first [assumption | exact (RICM GROW)]|]). exact TRK.
  Qed.

  Lemma lpre_ipre : forall s mo m errv' LB' LBm p, LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    IPREx s mo m errv' LB' LBm p bl bc ents false.
  Proof.
    intros s mo m errv' LB' LBm p LP Hbc LOAD.
    destruct LP as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                    & U & SH & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & P16 & PO & PA & NC & ADP
                    & RH & PE & PM & OWN & XP & RF & AC & S0 & AL & AL0 & RS & RC & RL & RICM & TRK).
    unfold IPRE.
    split; [exact MP|]. split; [exact FR|]. split; [exact SP16|]. split; [exact SPL|]. split; [exact SPH|]. split; [exact RAE|].
    split; [exact MI|]. split; [exact ST|]. split; [exact ERR|]. split; [exact RA|]. split; [exact TPV|]. split; [exact ACS|].
    split; [exact LFO|]. split; [exact U|]. split; [exact SH|]. split; [apply Permutation_refl|]. split; [exact Hbc|].
    split; [exact LOAD|]. split; [exact KR32|]. split; [exact AD|]. split; [exact WR|].
    split; [exact P0|]. split; [exact P1|]. split; [exact P16|]. split; [exact PO|]. split; [exact PA|]. split; [exact NC|].
    split; [exact ADP|]. split; [intros _; split; reflexivity|]. split; [intros X; discriminate X|].
    split; [exact RH|]. split; [exact PE|]. split; [exact PM|]. split; [exact OWN|]. split; [exact XP|].
    split; [exact RF|]. split; [exact AC|]. split; [exact S0|]. lia.
  Qed.

  Lemma lf_nogrow : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                             y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc)
                             (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) (Z_to_bv 64 (hmod key bc))
                             (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_INS) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> bc <> 0 -> Zlength ents + 1 <= bc ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Hbc LOAD.
    eapply (stage_ins H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s msF mo m F fc); [unfold ISTATE; exact VIS | exact FRZ | exact KR | exact (lpre_ipre s mo m errv' LB' LBm p LP Hbc LOAD)].
  Qed.

  Lemma lf_grow : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                             y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc)
                             (Z_to_bv 64 (obj / 8)) (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) y24
                             (rShe (Z_to_bv 64 p)) (rShe (Z_to_bv 64 (obj + 24))) s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_GR) fc None m (seg_rom asegs) ->
    frm_zero fc -> fholds (PropExec.mkFP F fc) 15 one32 -> fholds (PropExec.mkFP F fc) 14 (ieee (Zlength ents + 1)) ->
    as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ H15 H14 KR LP GROW.
    pose proof LP as LP0.
    destruct LP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                     & U & SH & BCL & SZR & KR32 & AD & WR & OBL & P0 & P1 & _).
    pose proof (bseq_lt24 bc (u_bseq U) BCL) as BC24. pose proof (u_load U) as ULD.
    assert (SZ0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS
              (gr_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) p bc (Zlength ents + 1)
                 ltac:(lia) ltac:(lia) ltac:(lia) FRZ H15 H14)).
    intros msF1 mo1 KR1 MP1 (F1 & fc1 & v10 & v12 & v20 & VIS1 & FZ1).
    rewrite (grq_nreq bc (Zlength ents) (u_bseq U) SZ0 ULD ltac:(lia)) in VIS1.
    eapply (stage_np H HH REH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bl bc key ents lo B shi m0 mo0
              s msF1 mo1 m F1 fc1); [exact VIS1 | exact FZ1 | exact KR1 |].
    destruct (lpre_gpre s mo m errv' LB' LBm p LP GROW) as (MPx & GPr).
    split; [eapply (ah_mpres_trans H HH); [exact MPx | exact MP1] | exact GPr].
  Qed.

  Definition srLF : list expr := srs sr_id [(8%bv, EVar 32); (19%bv, ELit SHBASE)].
  Definition SCR_LF := SCR [false; false] [EVar 33] [].

  Lemma stage_lf : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y24 y26 y28 y29 y30 y31 : word) (errv' : word) (LB' LBm : list block) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spf spz)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                             y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc) (Z_to_bv 64 (obj / 8))
                             (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) y24 (rShe (Z_to_bv 64 p)) y26
                             s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 E_LF) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> LPRE s mo m errv' LB' LBm p ->
    (bc <> 0 -> y24 = Z_to_bv 64 (hmod key bc)) ->
    as_SR H QIx (mkCfg msF mo).
  Proof using All.
    intros s msF mo m F fc y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y24 y26 y28 y29 y30 y31 errv' LB' LBm p VIS FRZ KR LP Y24.
    pose proof LP as LP0.
    destruct LP0 as (MP & FR & SP16 & SPL & SPH & RAE & MI & ST & ERR & RA & TPV & ACS & ACL & LOR & SHI & SPB & BR & LFO & OCE
                     & U & SH & BCL & SZR & KR32 & AD & _).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR. pose proof (u_load U) as ULD.
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (intros i Hi; eapply sh0_of_addressable; [exact AD | change (8 * (40 / 8)) with 40; lia]).
    assert (SZ0 : 0 <= Zlength ents) by (unfold Zlength; lia).
    unfold spf in *.
    remember (mkR y1 (Z_to_bv 64 (spz - 96)) gp tp y5 y6 y7 (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 p)
                  y11 y12 y13 y14 y15 y16 y17 y18 (Z_to_bv 64 SHBASE) (Z_to_bv 64 bc) (Z_to_bv 64 (obj / 8))
                  (Z_to_bv 64 key) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE)) y24 (rShe (Z_to_bv 64 p)) y26
                  s11 y28 y29 y30 y31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 (Zlength ents)]).
    assert (HR : regs_ok E srLF R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    assert (Hrd_sz : sc_denot asegs m E (SCReadBase (SA (EVar 32) 24) 8 false (EVar 33))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Csz); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_FLW] SCR_LF E_LF srLF [] 50)) by (kn_eval; know_tac).
    xrun_at (PropExec.mkFP F fc) asegs R E_LF m (seg_rom asegs) HR HK 20%nat [E_FLW] SCR_LF 50%N.
    { clear - E Hrd_sz GZO Ho0 Ho1 BCR KR32 SZR SZ0.
      split_scs; first [exact Hrd_sz | try sc_auto1; try sc_shdj; try sc_dj]. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 8%bv G8. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 18%bv G18.
    rreg HR' 19%bv G19. rreg HR' 26%bv G26.
    rewrite (w_add obj 24) in G18 by lia. rewrite (w_add obj 32) in G11 by lia. rewrite (w_add obj 24) in G26 by lia.
    change (getr R' 26 = rShe (Z_to_bv 64 (obj + 24))) in G26.
    change (Z_to_bv 64 2147450880) with (Z_to_bv 64 SHBASE) in G19.
    rewrite G8, G11, G12, G13, G18, G19, G26 in HRe. clear G8 G11 G12 G13 G18 G19 G26.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.

    pose proof (bseq_lt24 bc (u_bseq U) BCL) as BC24.
    unfold cell4, cellw in Cmlf.
    assert (Ho0' : 0 <= obj) by (clear - Ho0; lia).
    eapply (ahh_evt_then H HH _ _ s msF1 _ mo1 KR1 VIS1
              (lf_fp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (seg_rom asegs) obj (Zlength ents) bc
                 SZ0 SZR BC24 Ho0' Ho1 (proj2 Cmlf) FRZ)).
    intros msF2 mo2 KR2 MP2 (F2 & fc2 & a1 & VIS2 & FZ2 & H15 & H14).
    assert (LP2 : LPRE s mo2 m errv' LB' LBm p).
    { destruct LP as (MPx & REST). split; [|exact REST].
      eapply (ah_mpres_trans H HH); [exact MPx | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2]]. }
    destruct ((bc =? 0) || (bc <? Zlength ents + 1)) eqn:GR.
    -
      assert (GROW : bc = 0 \/ Zlength ents = bc).
      { apply orb_true_iff in GR. destruct GR as [G|G]; [left; apply Z.eqb_eq; exact G | right; apply Z.ltb_lt in G; clear - G ULD; lia]. }
      eapply (lf_grow s msF2 mo2 m F2 fc2); [unfold spf; exact VIS2 | exact FZ2 | exact H15 | exact H14 | exact KR2 | exact LP2 | exact GROW].
    -
      apply orb_false_iff in GR. destruct GR as [G0 G1]. apply Z.eqb_neq in G0. apply Z.ltb_ge in G1.
      rewrite (Y24 G0) in VIS2.
      eapply (lf_nogrow s msF2 mo2 m F2 fc2); [unfold spf; exact VIS2 | exact FZ2 | exact KR2 | exact LP2 | exact G0 | clear - G1; lia].
  Qed.
End EmpL.
