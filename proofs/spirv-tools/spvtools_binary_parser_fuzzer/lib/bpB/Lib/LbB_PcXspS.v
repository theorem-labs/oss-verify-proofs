(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3 LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PcSrc LbB_PcLem LbB_PcXsp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtor LbB_DCtorK LbB_DPdK LbB_PcOvf LbB_PcOvfS LbB_HKit LbB_SegKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section XS.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m : mem) (mo : Model) (s : as_St H) (LB LBk DB : list block) (LF : list fframe) (lo B shi : Z) (errv : word)
            (ds err len p n : Z) (ms : sbuf) (pp hm fl fill : Z).
  Hypothesis RH : as_RHEAP H s LB m.
  Hypothesis RAUX : as_rauxv_ok H m B.
  Hypothesis SPB : bv_unsigned sp <= B.
  Hypothesis BB64 : B < 2 ^ 64.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis STK : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - XSP_STACK.
  Hypothesis ERRN : rw_cells asegs m (errno_addr tp) [C4 errv].
  Hypothesis MI : mem_inv asegs m.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis LV : LINV_P5 m.
  Hypothesis AC : ACONST m.
  Hypothesis RFS : as_RFS H LF m.
  Hypothesis S0 : stack0 m lo shi.
  Hypothesis SPS : bv_unsigned sp <= shi.
  Hypothesis N0 : 0 < n.
  Hypothesis REP : ds_rep_w LB m ds err len DB ms pp hm fl fill.
  Hypothesis PERM : Permutation LB (DB ++ LBk).
  Hypothesis OWN : lb_own DB m.
  Hypothesis DSIN : ds_in LF ds.
  Hypothesis SRC : xsp_src H LBk LF DB m (bv_unsigned sp) XSP_STACK ds p n.
  Hypothesis LEN : len + n <= DS_MAXLEN.
  Hypothesis BS : lb_small LB + 2 * 64512 <= RT_SMALL_MAX.
  Hypothesis BC : Z.of_nat (length LB) + 2 <= RT_CNT_MAX.
  Hypothesis BL : nlarge LB + 2 <= RT_LARGE_MAX.
  Hypothesis COST : ds_cost (len + n) <= as_AL H s.
  Hypothesis TRO : trace_ok (as_TR H) APC0_FREE [0x1200e8].

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.
  Notation spz := (bv_unsigned sp) (only parsing).

  Definition Qxs : as_St H -> list block -> mem -> Prop :=
    fun s' LB' m' => exists DB' ms' pp' hm',
        Permutation LB' (DB' ++ LBk)
     /\ ds_rep_w LB' m' ds err (len + n) DB' ms' pp' hm' fl fill
     /\ pp' - dsdata ds ms' = pp - dsdata ds ms + n
     /\ lb_own DB' m'
     /\ xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m'
     /\ as_AL H s' >= as_AL H s - 8 * (blkof ms' - blkof ms).
  Definition POSTxs : config -> Prop :=
    pc_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LF lo B shi mo (Z_to_bv 64 n) Qxs.

  Definition XW (i ppi epi c k : Z) : list word := Wx ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n i ppi epi c k.

  Definition epof (msi : sbuf) : Z := dsdata ds msi + str_cap msi.

  Lemma xs_nums : AIMG_TOP <= ds /\ ds + DS_SIZE <= lo /\ ds mod 8 = 0 /\ as_FSB H <= ds /\ ds + DS_SIZE <= as_FSB H + AFS_SIZE
                  /\ aceil + XSP_STACK <= spz /\ spz <= 2 ^ 47 /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000
                  /\ AIMG_TOP <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ (ds + DS_SIZE <= ALOWSH_LO \/ AHI_LO <= ds)
                  /\ 0 < ds /\ 0 < n <= 2 ^ 24 /\ 0 <= p /\ p + n + 8 <= 2 ^ 47 /\ 0 <= len.
  Proof.
    pose proof DSIN as (IN & DSO & D8 & D0). pose proof DSO as (O1 & O2 & O3).
    destruct (LbB_DCtor.inframe_facts H HH LF m ds DS_SIZE RFS IN ltac:(unfold DS_SIZE; lia) O1) as (F1 & _ & F3 & F4).
    destruct (ah_RFS_range H HH LF m RFS) as [(B1 & B2 & B3 & B4) _].
    pose proof aceil_facts as ((A1 & A2) & _ & _). pose proof (stack0_bounds m lo shi S0) as (K1 & K2 & K3).
    pose proof SRC as (P0 & Pn & _ & IAM & _).
    pose proof REP as (DI & _). pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI) as L0.
    clear - O1 O2 O3 D8 D0 F1 F3 F4 B1 B2 A1 A2 K1 K2 K3 LO CEIL SPS N0 LEN P0 Pn IAM L0.
    unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, DS_MAXLEN in *. repeat split; lia.
  Qed.

  Lemma rep_facts : forall LBi mi leni DBi msi ppi hmi,
    ds_rep_w LBi mi ds err leni DBi msi ppi hmi fl fill ->
    0 <= dsdata ds msi /\ dsdata ds msi <= ppi <= epof msi /\ epof msi + 1 <= 2 ^ 47 /\ ppi - dsdata ds msi <= leni /\ 0 <= leni
    /\ 0 <= str_cap msi /\ AIMG_TOP <= dsdata ds msi /\ 0 <= blkof msi
    /\ (msi = SShort /\ DBi = [] /\ dsdata ds msi = ds + 73 /\ str_cap msi = 22
        \/ exists pid d asz, msi = SLong d asz /\ DBi = [(pid, d, asz)] /\ In (pid, d, asz) LBi /\ dsdata ds msi = d /\ str_cap msi = asz - 1
                             /\ 48 <= asz <= 2 * leni + 48 /\ (ds + DS_SIZE <= d \/ d + asz <= ds) /\ addressable mi d asz /\ app_obj d asz).
  Proof.
    intros LBi mi leni DBi msi ppi hmi (DI & BLK & DSA & DSW & DSO & SBA). pose proof xs_nums as (N1 & _ & _ & _ & _ & _ & N7 & _).
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DI) as [_ _ _ _ _ (cs0 & SR0 & HL0) _ _ _ HPP _ HHM _].
    pose proof (di_pl _ _ _ _ _ _ _ _ _ _ _ DI) as PL. pose proof (di_len0 _ _ _ _ _ _ _ _ _ _ _ DI) as L0.
    pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as DHI.
    replace (ds + 8 + 64) with (ds + 72) in * by lia. unfold epof, dsdata in *.
    unfold AIMG_TOP, AAPP_HI, DS_SIZE, SSO_CAP in *.
    destruct msi as [|d asz]; cbn [str_data str_cap blkof ds_blk sb_addr] in *; unfold SSO_CAP in *.
    - repeat split; try lia. left. subst DBi. repeat split; lia.
    - destruct SR0 as (_ & _ & _ & _ & (Hd & _ & Hde & _ & Ha46 & _) & _).
      destruct BLK as (pid & -> & INb). destruct SBA as [SA SO]. pose proof SO as (Q1 & Q2 & Q3). unfold AIMG_TOP, AAPP_HI in Q1, Q2, Q3.
      pose proof (di_asz _ _ _ _ _ _ _ _ _ _ _ DI d asz eq_refl) as ASZ.
      pose proof (di_dj _ _ _ _ _ _ _ _ _ _ _ DI d asz eq_refl) as DJ.
      destruct (di_pow _ _ _ _ _ _ _ _ _ _ _ DI d asz eq_refl) as (j & Hj & Ej).
      pose proof (Z.pow_le_mono_r 2 0 j ltac:(lia) Hj) as PJ. change (2 ^ 0) with 1 in PJ.
      assert (A48 : 48 <= asz) by (rewrite Ej; clear - PJ; nia).
      repeat split; try lia. right. exists pid, d, asz. split; [reflexivity|]. split; [reflexivity|]. split; [exact INb|].
      split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact DJ|]. split; [exact SA | exact SO].
  Qed.

  Record xinv (i : Z) (msF : machine_state) (moi : Model) (si : as_St H) (mi : mem) (R : bvmap 5 word)
               (LBi DBi : list block) (msi : sbuf) (ppi hmi : Z) : Prop := XINV {
    xi_vis  : as_VIS H si msF = MS R F (Z_to_bv 64 AXLOOP) fc None mi (seg_rom asegs);
    xi_rf   : rfull R;
    xi_rt   : rtbl (XW i ppi (epof msi) 0 0) R RTXH;
    xi_st   : ftbl (XW i ppi (epof msi) 0 0) spz mi STX;
    xi_kr   : as_AKREL H si (mkCfg msF moi);
    xi_mp   : as_MPRES H mo moi;
    xi_mi   : mem_inv asegs mi;
    xi_stk  : stk asegs mi lo spz;
    xi_err  : exists e : word, rw_cells asegs mi (errno_addr tp) [C4 e];
    xi_raux : as_rauxv_ok H mi B;
    xi_rh   : as_RHEAP H si LBi mi;
    xi_rfs  : as_RFS H LF mi;
    xi_ac   : ACONST mi;
    xi_sz   : stack0 mi lo shi;
    xi_lv   : LINV_P5 mi;
    xi_perm : Permutation LBi (DBi ++ LBk);
    xi_rep  : ds_rep_w LBi mi ds err (len + i) DBi msi ppi hmi fl fill;
    xi_pp   : ppi - dsdata ds msi = pp - dsdata ds ms + i;
    xi_own  : lb_own DBi mi;
    xi_xp   : xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m mi;
    xi_al   : as_AL H si >= as_AL H s - 8 * (blkof msi - blkof ms);
    xi_bsm  : lb_small LBi <= lb_small LBk + 64512;
    xi_bcn  : Z.of_nat (length LBi) <= Z.of_nat (length LBk) + 1;
    xi_blg  : nlarge LBi <= nlarge LBk + 1;
    xi_src  : srcx_keep H LBk LF spz [(ds, ds + DS_SIZE)] mi p n;
    xi_i    : 0 <= i < n
  }.

  Definition XNEXT (i : Z) : config -> Prop :=
    fun cf => (exists i' msF' mo' s' m' R' LB' DB' ms' pp' hm', i < i' /\ cf = mkCfg msF' mo' /\ xinv i' msF' mo' s' m' R' LB' DB' ms' pp' hm')
              \/ POSTxs cf.

  Definition WB : list (Z * Z) := [(spz - 8192, spz); (ds + 56, ds + 72)].

  Definition wok (LBi : list block) (W : list (Z * Z)) : Prop :=
    Forall (aclient_write_ok H LBi) W /\ Forall (afs_write_ok H LF) W /\ Forall stack0_ok W /\ wins_hi W /\ Forall aconst_ok W
    /\ (forall a k, a + k <= AIMG_TOP -> disjoint_from W a k).

  Lemma disjoint_join : forall W1 W2 a k, disjoint_from W1 a k -> disjoint_from W2 a k -> disjoint_from (W1 ++ W2) a k.
  Proof. induction W1 as [|[l h] W1 IH]; intros W2 a k O1 O2; [exact O2|]. cbn in O1 |- *. destruct O1 as [O0 O1]. split; [exact O0 | exact (IH _ _ _ O1 O2)]. Qed.

  Lemma wok_app : forall LBi W1 W2, wok LBi W1 -> wok LBi W2 -> wok LBi (W1 ++ W2).
  Proof.
    intros LBi W1 W2 (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). unfold wok, wins_hi in *.
    repeat split; try (apply Forall_app; split; assumption).
    intros a k Ha. apply disjoint_join; auto.
  Qed.

  Lemma wb_ok : forall LBi, wok LBi WB.
  Proof.
    intros LBi. pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & _).
    pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    unfold wok, WB, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *.
    split; [|split; [|split; [|split; [|split]]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. clear - N6. lia.
      + right; right; right; right; left. clear - N4 N5. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - N6 N10 A1. lia.
      + right. exists f. split; [exact Hf|]. clear - IF1 IF2. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok, AHI_LO; cbn [fst snd].
      + left. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [right | left]; clear - N11 SH; lia.
    - unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + right. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; clear - N1 N11; lia.
    - intros a k Ha. cbn [disjoint_from]. clear - Ha N1 N6 A1. lia.
  Qed.

  Lemma wd_ok : forall LBi mi leni DBi msi ppi hmi si q k,
    ds_rep_w LBi mi ds err leni DBi msi ppi hmi fl fill -> as_RHEAP H si LBi mi -> lb_own DBi mi -> as_RFS H LF mi ->
    dsdata ds msi <= q -> 0 <= k -> q + k <= epof msi ->
    wok LBi [(q, q + k)] /\ AIMG_TOP <= q /\ q + k <= lo /\ wr_at asegs mi q k /\ accessible mi q k /\ shvis mi q (q + k)
    /\ in_app_mem q (q + k) /\ (q + k <= ds + 8 \/ ds + 72 <= q)
    /\ ((ds <= q /\ q + k <= ds + DS_SIZE /\ DBi = []) \/ (exists pid d asz, DBi = [(pid, d, asz)] /\ d <= q /\ q + k <= d + asz)).
  Proof.
    intros LBi mi leni DBi msi ppi hmi si q k REPi RHi OWNi RFSi Hq Hk Hqk.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & _).
    pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    pose proof (rep_facts LBi mi leni DBi msi ppi hmi REPi) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & CASE).
    pose proof REPi as (DIi & BLKi & DSAi & DSWi & DSOi & SBAi).
    unfold epof in *.
    destruct CASE as [(E & EDB & Hdat & Hcap)|(pid & d & asz & E & EDB & INb & Hdat & Hcap & Hasz & Hdj & Had & Hao)].
    -
      rewrite Hdat, Hcap in *.
      unfold wok, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
      split; [split; [|split; [|split; [|split; [|split]]]]|].
      + apply Forall_cons; [| apply Forall_nil]. unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE.
        right; right; right; right; left. clear - N4 N5 Hq Hqk. lia.
      + apply Forall_cons; [| apply Forall_nil]. unfold afs_write_ok; cbn [fst snd].
        right. exists f. split; [exact Hf|]. clear - IF1 IF2 Hq Hqk. lia.
      + apply Forall_cons; [| apply Forall_nil]. unfold stack0_ok, AHI_LO; cbn [fst snd].
        destruct N11 as [N11|N11]; [right | left]; clear - N11 SH Hq Hqk; lia.
      + unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct N11 as [N11|N11]; [left | right]; clear - N1 N11 Hq Hqk; lia.
      + apply Forall_cons; [| apply Forall_nil].
        destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; clear - N1 N11 Hq Hqk; lia.
      + intros a k0 Ha. cbn [disjoint_from]. clear - Ha N1 Hq. lia.
      + split; [clear - N1 Hq; lia|]. split; [clear - N2 Hqk; lia|].
        split; [eapply wr_at_sub; [exact DSWi | clear - Hq; lia | clear - Hqk; lia | exact Hk]|].
        split; [eapply (addressable_accessible mi ds 392); [exact DSAi | clear - Hq; lia | clear - Hqk; lia | pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DIi); unfold AAPP_HI; lia]|].
        split.
        { pose proof (ah_frm_shvis H HH LF mi f RFSi Hf) as SV.
          destruct (ah_RFS_range H HH LF mi RFSi) as [_ FR]. pose proof (FR f Hf) as (_ & K1 & K2 & _). unfold AFS_HDR in K1.
          eapply shvis_sub; [exact SV | clear - K1 N9; lia | clear - IF1 Hq; lia | clear - IF2 Hqk; lia | clear - Hk; lia
                            | clear - K1 N9 IF2 N1; lia]. }
        split; [unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI; destruct N11 as [N11|N11]; [left | right]; clear - N1 N11 Hq Hqk N7 N5 N10 A2; lia|].
        split; [right; clear - Hq; lia|].
        left. split; [clear - Hq; lia|]. split; [clear - Hqk; lia | exact EDB].
    -
      rewrite Hdat, Hcap in *.
      pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RHi INb) as (R0 & R16 & Rn & RI & RC & RF & RAPP).
      unfold blk_addr, blk_size in R0, R16, Rn, RI, RC, RF, RAPP. cbn [fst snd] in R0, R16, Rn, RI, RC, RF, RAPP.
      pose proof Hao as (O1 & O2 & O3).
      unfold wok, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO in *.
      split; [split; [|split; [|split; [|split; [|split]]]]|].
      + apply Forall_cons; [| apply Forall_nil]. unfold aclient_write_ok; cbn [fst snd].
        right; right; left. exists (pid, d, asz). split; [exact INb|]. cbn [blk_addr blk_size fst snd]. clear - Hq Hqk. lia.
      + apply Forall_cons; [| apply Forall_nil]. unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE in *.
        left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - RF RI Hq Hqk. lia.
      + apply Forall_cons; [| apply Forall_nil]. unfold stack0_ok, AHI_LO; cbn [fst snd].
        destruct O2 as [O2|O2]; [right | left]; clear - O2 SH Hq Hqk; lia.
      + unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd].
        destruct O2 as [O2|O2]; [left | right]; clear - O1 O2 Hq Hqk; lia.
      + apply Forall_cons; [| apply Forall_nil].
        destruct O2 as [O2|O2]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; clear - O1 O2 Hq Hqk; lia.
      + intros a k0 Ha. cbn [disjoint_from]. clear - Ha O1 Hq. lia.
      + split; [clear - O1 Hq; lia|]. split; [clear - RC CEIL Hqk; lia|].
        assert (OWb : wr_at asegs mi d asz).
        { rewrite EDB in OWNi. exact (lb_own_In _ _ (pid, d, asz) OWNi (or_introl eq_refl)). }
        split; [eapply wr_at_sub; [exact OWb | exact Hq | clear - Hqk; lia | exact Hk]|].
        split; [eapply (addressable_accessible mi d asz); [exact Had | exact Hq | clear - Hqk; lia | clear - O3; unfold AAPP_HI in *; lia]|].
        split.
        { pose proof (ah_blk_shvis H HH si LBi mi pid d asz RHi INb) as SV.
          eapply shvis_sub; [exact SV | clear - R0; lia | exact Hq | clear - Hqk; lia | clear - Hk; lia | clear - R0 Rn; lia]. }
        split; [unfold in_app_mem, ASHADOW_BASE, AHI_LO, AAPP_HI; destruct O2 as [O2|O2]; [left | right]; clear - O1 O2 Hq Hqk RC A2; lia|].
        split; [clear - Hdj Hq Hqk Hk Rn; lia|].
        right. exists pid, d, asz. split; [exact EDB|]. clear - Hq Hqk. lia.
  Qed.

  Lemma xs_frame : forall LBi mi leni DBi msi ppi hmi si W m1,
    ds_rep_w LBi mi ds err leni DBi msi ppi hmi fl fill -> as_RHEAP H si LBi mi -> lb_own DBi mi -> as_RFS H LF mi ->
    stk asegs mi lo spz -> (exists e : word, rw_cells asegs mi (errno_addr tp) [C4 e]) -> as_rauxv_ok H mi B -> ACONST mi ->
    stack0 mi lo shi -> LINV_P5 mi ->
    wok LBi W -> munch W mi m1 -> wmono asegs mi m1 ->
    as_RHEAP H si LBi m1 /\ lb_own DBi m1 /\ as_RFS H LF m1 /\ stk asegs m1 lo spz
    /\ (exists e : word, rw_cells asegs m1 (errno_addr tp) [C4 e]) /\ as_rauxv_ok H m1 B /\ ACONST m1 /\ stack0 m1 lo shi /\ LINV_P5 m1
    /\ addressable m1 ds DS_SIZE /\ wr_at asegs m1 ds DS_SIZE /\ sb_addr m1 msi.
  Proof.
    intros LBi mi leni DBi msi ppi hmi si W m1 REPi RHi OWNi RFSi STKi (e & ERRi) RAUXi ACi S0i LVi (WC & WF & WS & WH & WA & WO) MU WM.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & _).
    pose proof REPi as (DIi & BLKi & DSAi & DSWi & DSOi & SBAi). pose proof DSOi as (O1 & O2 & O3).
    split; [eapply (ah_RHEAP_frame H HH); [exact RHi | exact MU | exact WM | exact WC]|].
    split; [eapply lb_own_wmono; [exact OWNi | exact WM]|].
    split; [eapply (ah_RFS_frame H HH); [exact RFSi | exact MU | exact WM | exact WF]|].
    split.
    { eapply stk_transport; [exact STKi | exact MU | exact WM |]. intros x Hx. right.
      pose proof STKi as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _].
      pose proof (WM (wa x) HV) as HV'.
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)).
      { unfold wa. rewrite unsigned_lit by (clear - T1 T2 Hx; lia). clear - Hx CEIL A1. unfold AIMG_TOP. lia. }
      rewrite (BakeStackRep.wview_high m1 (wa x) HX) in HV'.
      destruct (m1 (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction]. }
    split.
    { exists e. eapply rw_cells_transport; [exact ERRi | exact MU | exact WM |].
      cbn [cells_size csize]. rewrite TP, unsigned_lit by (clear; unfold ATP; lia). apply WO. clear. unfold ATP, AIMG_TOP. cbn. lia. }
    split; [eapply (ah_rauxv_frame H HH); [exact RAUXi | exact MU | exact WM | exact WC]|].
    split; [eapply ACONST_frame; [exact ACi | exact MU | exact WM | exact WA]|].
    split; [eapply stack0_transport; [exact S0i | exact MU | exact WM | exact WS]|].
    split.
    { eapply LINV_P5_cl; [exact LVi|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by exact Ha.
      apply (disjoint_outside W a 1); [| clear; lia]. apply WO. unfold aimg_client in Hc. clear - Hc. unfold AIMG_TOP. lia. }
    split; [eapply addressable_transport_hi; [exact DSAi | exact MU | exact WM | exact O3 | exact WH]|].
    split; [eapply wr_at_transport; [exact DSWi | exact WM]|].
    destruct msi as [|d asz]; [exact I|]. cbn [sb_addr] in SBAi |- *. destruct SBAi as [SA SO]. split; [| exact SO].
    destruct SO as (Q1 & Q2 & Q3). eapply addressable_transport_hi; [exact SA | exact MU | exact WM | exact Q3 | exact WH].
  Qed.

  Lemma agree_munch' : forall W m0 m' (P : Z -> Prop), munch W m0 m' -> (forall a, P a -> 0 <= a < 2 ^ 64 /\ outside W a) ->
    CRep.agree_on P m0 m'.
  Proof. intros W m0 m' P MU HP a Ha. destruct (HP a Ha) as [R O]. apply MU. rewrite unsigned_lit by exact R. exact O. Qed.

  Lemma ivl_disj : forall a k b L, 0 < k -> 0 < L -> (forall x, a <= x < a + k -> ~ (b <= x < b + L)) -> a + k <= b \/ b + L <= a.
  Proof.
    intros a k b L Hk HL HP. destruct (Z.lt_ge_cases a b) as [L1|L1].
    - destruct (Z.le_gt_cases (a + k) b) as [L2|L2]; [left; exact L2|]. exfalso. apply (HP b); lia.
    - destruct (Z.le_gt_cases (b + L) a) as [L2|L2]; [right; exact L2|]. exfalso. apply (HP a); lia.
  Qed.

  Ltac wev := cbn [fst snd edenot]; unfold wenv, XW; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app]; rewrite ?LbB_PcOvf.w_add_g; first [reflexivity | f_equal; lia].
  Ltac went := lazymatch goal with |- _ /\ _ => split; [reflexivity | wev] end.
  Ltac rew_tbl := repeat (apply Forall2_cons; [went|]); apply Forall2_nil.

  Ltac rgetx HRT r G :=
    lazymatch type of HRT with
    | rtbl ?Wl ?R ?RT =>
        let e := eval vm_compute in (match List.find (fun re => bv_eqb (fst re) r) RT with Some re => snd re | None => ELit 0 end) in
        assert (G : PropExec.getr R r = edenot (wenv Wl) e)
          by (apply (rtbl_In Wl R RT r e HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
        cbn [edenot] in G; unfold wenv, XW in G; unfold HLib.Eseed, reg_ev, Wx in G;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
              Init.Nat.add Nat.sub nth app] in G; rewrite ?LbB_PcOvf.w_add_g in G
    end.

  Lemma dtx_of_rep : forall LBi mi leni DBi msi ppi hmi i c k,
    ds_rep_w LBi mi ds err leni DBi msi ppi hmi fl fill ->
    ftbl (XW i ppi (epof msi) c k) ds mi DTX /\ rw_cells asegs mi (ds + 8) [C8 (Z_to_bv 64 VT_SB_A)].
  Proof.
    intros LBi mi leni DBi msi ppi hmi i c k REPi. pose proof REPi as (DIi & BLKi & DSAi & DSWi & DSOi & SBAi).
    pose proof xs_nums as (N1 & _).
    destruct (di_sb _ _ _ _ _ _ _ _ _ _ _ DIi) as [Fvt _ _ _ _ _ _ Fpp Fep _ _ _ _].
    replace (ds + 8 + 48) with (ds + 56) in Fpp by lia. replace (ds + 8 + 56) with (ds + 64) in Fep by lia.
    replace (ds + 8 + 64) with (ds + 72) in Fep by lia.
    split.
    - unfold DTX. apply (LbB_PcOvfS.ftbl_cons1 _ ds _ 56 8 _ _ _ _ Fpp ltac:(lia)); [eapply wr_at_sub; [exact DSWi | lia | unfold DS_SIZE; lia | lia] | reflexivity | unfold AIMG_TOP in N1; lia |].
      apply (LbB_PcOvfS.ftbl_cons1 _ ds _ 64 8 _ _ _ _ Fep ltac:(lia)); [eapply wr_at_sub; [exact DSWi | lia | unfold DS_SIZE; lia | lia] | reflexivity | unfold AIMG_TOP in N1; lia |].
      constructor.
    - apply rw_cells_of_fld8; [exact Fvt | eapply wr_at_sub; [exact DSWi | lia | unfold DS_SIZE; lia | lia]].
  Qed.

  Lemma xs_copy : forall i msF moi si mi R LBi DBi msi ppi hmi,
    xinv i msF moi si mi R LBi DBi msi ppi hmi -> ppi < epof msi -> as_SR H (XNEXT i) (mkCfg msF moi).
  Proof.
    intros i msF moi si mi R LBi DBi msi ppi hmi XI ROOM. destruct XI.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
    pose proof (rep_facts LBi mi (len + i) DBi msi ppi hmi xi_rep0) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & CASE).
    pose proof xi_rep0 as (DIi & BLKi & DSAi & DSWi & DSOi & SBAi).
    set (k := Z.min (epof msi - ppi) (n - i)).
    assert (HK : 0 < k <= n - i /\ ppi + k <= epof msi /\ ((n - i < epof msi - ppi /\ k = n - i) \/ (epof msi - ppi <= n - i /\ k = epof msi - ppi))).
    { subst k. clear - ROOM xi_i0 D1. lia. }
    destruct HK as (HK1 & HK2 & HKC).
    destruct (wd_ok LBi mi (len + i) DBi msi ppi hmi si ppi k xi_rep0 xi_rh0 xi_own0 xi_rfs0 ltac:(clear - D1; lia) ltac:(clear - HK1; lia) HK2)
      as (WD & PPI & PPL & WRd & ACd & SVd & INd & DPP & DCASE).

    destruct (srcx_keep_now H LBk LF spz _ mi p n si LBi xi_src0 xi_ac0 xi_mi0 xi_rh0 (fun b Hb => Permutation_in b (Permutation_sym xi_perm0) (in_or_app DBi LBk b (or_intror Hb)))) as (bs & BSL & BB & BA & BV).
    pose proof SRC as (P0 & Pn & _ & IAM & PSTK & PDJ).
    set (srcb := firstn (Z.to_nat k) (skipn (Z.to_nat i) bs)).
    assert (SB : bytes_at asegs mi (p + i) srcb).
    { subst srcb. replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by (clear - xi_i0; lia). apply bytes_at_mid; [exact BB | rewrite BSL; clear - xi_i0 HK1; lia]. }
    assert (SL : length srcb = Z.to_nat k) by (subst srcb; rewrite length_firstn, length_skipn, BSL; clear - xi_i0 HK1; lia).
    assert (ACS : accessible mi (p + i) k) by (eapply accessible_sub; [exact BA | clear - xi_i0; lia | clear - HK1; lia | clear - HK1; lia]).
    assert (SVS : shvis mi (p + i) (p + i + k)) by (eapply shvis_sub; [exact BV | exact P0 | clear - xi_i0; lia | clear - HK1; lia | clear - HK1; lia | clear - P0 N13; lia]).
    assert (INS : in_app_mem (p + i) (p + i + k)) by (eapply in_app_mem_sub; [exact IAM | clear - xi_i0; lia | clear - HK1; lia]).
    destruct (rw_cells_of_wr_hi mi ppi k WRd PPI ltac:(clear - HK1; lia)) as (junk & DJ).

    assert (SEPp : forall x, ppi <= x < ppi + k -> ~ (p <= x < p + n)).
    { intros x Hx. pose proof WD as (_ & _ & _ & _ & WA & _).
      eapply (srcx_apart H HH LBk LF spz [(ds, ds + DS_SIZE)] mi p n mi [] x si LBi ppi (ppi + k) xi_src0 xi_ac0 xi_mi0 (Forall_nil _) (xpres_refl _ _ _ _ _)
                xi_rh0 (fun b Hb => Permutation_in b (Permutation_sym xi_perm0) (in_or_app DBi LBk b (or_intror Hb))) Hx (Forall_inv (proj1 WD))).
      - clear - Hx PPI N1 D2 HK2. unfold AIMG_TOP in *. lia.
      - destruct WRd as (_ & _ & WW). replace x with (ppi + (x - ppi)) by lia. apply WW. clear - Hx. lia.
      - exact (Forall_inv WA x Hx).
      - intros Hc. rewrite app_nil_r. cbn [rin_ivs fst snd].
        destruct DCASE as [(C1 & C2 & _)|(pid & d & asz & EDB & C1 & C2)]; [left; clear - Hx C1 C2; lia|].
        exfalso. rewrite EDB in xi_perm0.
        destruct (blk_cls H HH si LBi mi LBk [(pid, d, asz)] pid d asz spz x xi_rh0 (Permutation_trans xi_perm0 (Permutation_app_comm _ _))
                    (or_introl eq_refl) ltac:(clear - N6 CEIL N2 N1; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia) Hc) as [Cx|(_ & Cx & _)].
        + clear - Cx Hx C2 PPL CEIL N6 LO. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
        + apply Cx. clear - Hx C1 C2. lia. }
    assert (SEP : p + i + k <= ppi \/ ppi + k <= p + i).
    { apply ivl_disj; [exact (proj1 HK1) | exact (proj1 HK1) |]. intros x Hx K. apply (SEPp x K). clear - Hx xi_i0 HK1. lia. }
    assert (SRCD : p + i + k <= ds + 8 \/ ds + 72 <= p + i).
    { destruct (ivl_disj (p + i) k ds DS_SIZE (proj1 HK1) ltac:(unfold DS_SIZE; lia)) as [K|K]; [| left; clear - K; lia | right; clear - K; unfold DS_SIZE in K; lia].
      intros x Hx. apply (proj1 (PDJ x ltac:(clear - Hx xi_i0 HK1; lia))). }
    assert (SRCS : p + i + k <= spz - 64 - AINTRIN_STACK \/ spz <= p + i).
    { clear - PSTK xi_i0 HK1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AINTRIN_STACK in *. lia. }
    assert (HLS : AIMG_TOP <= sh (hull_lo (p + i))).
    { pose proof (hull_lo_le (p + i) ltac:(clear - P0 xi_i0; lia)) as (Q1 & Q2 & Q3). unfold sh, AIMG_TOP. rewrite ASHADOW_BASE_val.
      clear - P0 xi_i0 Q2. Z.div_mod_to_equations. lia. }
    assert (HLD : AIMG_TOP <= sh (hull_lo ppi)).
    { pose proof (hull_lo_le ppi ltac:(clear - D0 D1; lia)) as (Q1 & Q2 & Q3). unfold sh, AIMG_TOP. rewrite ASHADOW_BASE_val.
      clear - D0 D1 Q2. Z.div_mod_to_equations. lia. }
    destruct (dtx_of_rep LBi mi (len + i) DBi msi ppi hmi i 0 k xi_rep0) as [HDT VTi].
    assert (HRT : rtbl (XW i ppi (epof msi) 0 k) R RTXH) by (eapply rtbl_rew; [| exact xi_rt0]; rew_tbl).
    assert (HST : ftbl (XW i ppi (epof msi) 0 k) spz mi STX) by (eapply ftbl_rew; [| exact xi_st0]; rew_tbl).
    pose proof WD as (_ & _ & _ & _ & WA & _).

    eapply (ahh_evt_then H HH _ _ si msF _ moi xi_kr0 xi_vis0).
    { eapply (xr_copy H HH ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mi ds p n i ppi (epof msi) 0 k lo
                DSOi DSWi xi_stk0 CEIL ltac:(clear - LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2
                (proj1 xi_lv0) VTi).
      - clear - P0 N15 N13 xi_i0 D0 D1 D2 HK1 HK2. lia.
      - exact xi_rf0.
      - exact HRT.
      - exact HST.
      - exact HDT.
      - exact xi_mi0.
      - exact xi_ac0.
      - exact ROOM.
      - clear - xi_i0; lia.
      - exact HKC.
      - exact SB.
      - exact SL.
      - exact DJ.
      - exact SEP.
      - exact ACS.
      - exact ACd.
      - exact SVS.
      - exact SVd.
      - exact INS.
      - exact INd.
      - exact (Forall_inv WA).
      - exact PPI.
      - exact PPL.
      - exact SRCS.
      - exact DPP.
      - exact SRCD.
      - exact HLS.
      - exact HLD. }
    intros msF1 mo1 KR1 MP1 POST.
    destruct POST as (R1 & m1 & RF1 & MU & WM & MI1 & AC1 & CB1 & DT1 & CASES).

    pose proof (wok_app LBi WB [(ppi, ppi + k)] (wb_ok LBi) WD) as WOK. change (WB ++ [(ppi, ppi + k)]) with (WC sp ds ppi k) in WOK.
    destruct (xs_frame LBi mi (len + i) DBi msi ppi hmi si (WC sp ds ppi k) m1 xi_rep0 xi_rh0 xi_own0 xi_rfs0 xi_stk0 xi_err0 xi_raux0
                xi_ac0 xi_sz0 xi_lv0 WOK MU WM) as (RH1 & OWN1 & RFS1 & STK1 & ERR1 & RAUX1 & _ & S01 & LV1 & DSA1 & DSW1 & SBA1).

    assert (WMIX : forall X, (forall a, ds <= a < ds + DS_SIZE -> rin_ivs X a) -> Forall (LbB_HKit.wmix DBi spz X) (WC sp ds ppi k)).
    { intros X HX. unfold WC. repeat apply Forall_cons; try apply Forall_nil; unfold LbB_HKit.wmix; cbn [fst snd].
      - left. clear - N6 A1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right; left. intros a Ha. apply HX. clear - Ha. unfold DS_SIZE. lia.
      - destruct DCASE as [(C1 & C2 & _)|(pid & d & asz & EDB & C1 & C2)].
        + right; left. intros a Ha. apply HX. clear - Ha C1 C2. lia.
        + right; right. exists pid, d, asz. rewrite EDB. split; [left; reflexivity | clear - C1 C2; lia]. }
    assert (PERM' : Permutation LBi (LBk ++ DBi)) by (eapply Permutation_trans; [exact xi_perm0 | apply Permutation_app_comm]).
    assert (XP1 : xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m1).
    { eapply (LbB_HKit.xpres_munch_mixed H HH si LBi LBk DBi spz _ _ m mi m1 xi_xp0 xi_rh0 PERM'
                ltac:(clear - N6 CEIL N2 N1; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia) MU WM).
      apply WMIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }
    assert (SRC1 : srcx_keep H LBk LF spz [(ds, ds + DS_SIZE)] m1 p n).
    { eapply srcx_keep_fwd0; [exact xi_src0|].
      eapply (LbB_HKit.xpres_munch_mixed H HH si LBi LBk DBi spz _ _ mi mi m1 (xpres_refl _ _ _ _ _) xi_rh0 PERM'
                ltac:(clear - N6 CEIL N2 N1; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia) MU WM).
      apply WMIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }

    assert (REP1 : ds_rep_w LBi m1 ds err (len + (i + k)) DBi msi (ppi + k) hmi fl fill).
    { pose proof DIi as DI0. destruct DIi as [Dpos Dal Dhi Ddef Dvt Dsb DBeq Dmx Dpow Dlen0 Dpl Dasz Ddj Dios D320 D336 D360 D368 Derr].
      assert (AGo : forall P : Z -> Prop, (forall a, P a -> (ds <= a < ds + 56 \/ ds + 72 <= a < ds + DS_SIZE) /\ ~ (ppi <= a < ppi + k)) ->
                    CRep.agree_on P mi m1).
      { intros P HP. eapply agree_munch'; [exact MU|]. intros a Ha. destruct (HP a Ha) as [R1' R2']. unfold WC. cbn [outside].
        clear - R1' R2' N1 N2 N6 LO Dhi. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AAPP_HI in *. lia. }
      assert (FO : forall a (w : nat) v, (ds <= a /\ a + Z.of_nat w <= ds + 56) \/ (ds + 72 <= a /\ a + Z.of_nat w <= ds + DS_SIZE) ->
                   (a + Z.of_nat w <= ppi \/ ppi + k <= a) -> CRep.fld ASEGS mi a w v -> CRep.fld ASEGS m1 a w v).
      { intros a w v Ho Hd HF. eapply (fld_ag mi m1 (fun x => (ds <= x < ds + 56 \/ ds + 72 <= x < ds + DS_SIZE) /\ ~ (ppi <= x < ppi + k)));
          [clear - Ho N1; unfold AIMG_TOP in *; lia | clear - Ho Dhi; unfold DS_SIZE in *; lia | | apply AGo; intros x Hx; exact Hx | exact HF].
        intros x Hx. clear - Ho Hd Hx. lia. }
      destruct Dsb as [Fvt Floc Fbi Fni Fei (cs & STR & CSL) Fpb Fpp Fep Hpp Fhm Hhm Fmode].
      replace (ds + 8 + 64) with (ds + 72) in * by lia.
      assert (DATd : (ds + 73 <= ppi /\ ppi + k <= ds + 96) \/ ppi + k <= ds \/ ds + DS_SIZE <= ppi).
      { unfold epof in HK2. destruct CASE as [(Em & _ & Hdat & Hcap)|(pid & d & asz & Em & _ & _ & Hdat & Hcap & _ & Hdj & _)];
          rewrite Hdat, Hcap in *; [clear - HK2 D1; lia | clear - HK2 Hdj D1 HK1; unfold DS_SIZE in *; lia]. }
      split; [| split; [exact BLKi | split; [exact DSA1 | split; [exact DSW1 | split; [exact DSOi | exact SBA1]]]]].
      rewrite (ds_blk_lbl _ _ _ BLKi).
      eapply (ds_inv_resb _ (lbl LBi) mi m1 ds err (len + i) (len + (i + k)) (lbl DBi) msi ppi hmi fl fill msi (ppi + k) hmi fl fill DI0).
      -
        constructor; replace (ds + 8 + 64) with (ds + 72) by lia.
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fvt].
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Floc].
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fbi].
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fni].
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fei].
        +
          destruct (strA_recontent (lbl LBi) mi m1 (ds + 72) msi cs (ppi - dsdata ds msi) srcb STR CSL ltac:(clear - D1; lia)
                      ltac:(unfold Zlen; rewrite SL; clear - HK1 HK2 D1; unfold epof in *; lia)) as (cs' & STR' & CSL').
          * apply mdef_of_wr_at_hi; [eapply wr_at_sub; [exact DSW1 | lia | unfold DS_SIZE; lia | lia] | clear - N1; lia].
          * eapply agree_munch'; [exact MU|]. intros a [Ha Hna]. unfold WC. cbn [outside]. unfold str_fp in Ha.
            unfold Zlen in Hna. rewrite SL in Hna. unfold dsdata in *.
            destruct DCASE as [(C1 & C2 & EDB)|(pid & d & asz & EDB & C1 & C2)].
            -- assert (Em : msi = SShort) by (destruct msi; [reflexivity | rewrite EDB in BLKi; cbn in BLKi; destruct BLKi as (? & K & _); discriminate K]).
               rewrite Em in *. cbn [str_data str_cap] in *. destruct Ha as [Ha|Ha]; [| destruct Ha].
               unfold zwin in Ha. clear - Ha Hna C1 C2 N1 N2 N6 LO HK1 Dhi. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
            -- assert (Em : msi = SLong d asz).
               { destruct msi as [|d' asz']; [rewrite EDB in BLKi; cbn in BLKi; discriminate BLKi|].
                 cbn in BLKi. destruct BLKi as (q & K & _). rewrite EDB in K. injection K as _ <- <-. reflexivity. }
               rewrite Em in *. cbn [str_data str_cap] in *. destruct STR as (_ & _ & _ & HL4 & (Hd & _ & Hdsz & _) & _).
               pose proof (ah_blocks H HH _ _ _ (pid, d, asz) xi_rh0) as BR.
               destruct CASE as [(K & _)|(pid' & d' & asz' & K & EDB' & INb & _ & _ & _ & Hdj' & _)]; [discriminate K|]. injection K as <- <-.
               rewrite EDB in EDB'. injection EDB' as <-.
               specialize (BR INb). destruct BR as (R0 & _ & Rn & RI & RC & _). cbn [blk_addr blk_size fst snd] in R0, Rn, RI, RC.
               unfold zwin in Ha. cbn [str_cap] in HL4.
               clear - Ha Hna C1 C2 N1 N2 N6 LO HK1 R0 Rn RI RC CEIL HL4 Dhi Hdj' A2. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
          * replace (str_data (ds + 72) msi + (ppi - dsdata ds msi)) with ppi by (unfold dsdata; lia).
            destruct CB1 as [[_ B1] _]. cbn [cells_bytes cbytes] in B1. rewrite app_nil_r in B1. exact B1.
          * exists cs'. split; [exact STR' | rewrite CSL'; exact CSL].
        + apply FO; [left; cbn; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fpb].
        + replace (ds + 8 + 48) with (ds + 56) by lia. eapply (fld_of_ftbl _ ds m1 DTXC 56 8 _ (ppi + k) DT1); [left; reflexivity |]. wev.
        + replace (ds + 8 + 56) with (ds + 64) by lia. eapply (fld_of_ftbl _ ds m1 DTXC 64 8 _ _ DT1); [right; left; reflexivity |]. unfold epof, dsdata. wev.
        + unfold epof, dsdata in *. clear - Hpp HK1 HK2. lia.
        + apply FO; [right; cbn; unfold DS_SIZE; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fhm].
        + exact Hhm.
        + apply FO; [right; cbn; unfold DS_SIZE; lia | cbn; clear - DATd DPP HK1; unfold DS_SIZE in *; lia | exact Fmode].
      - eapply ios_inv_frame; [exact Dios | clear - N1; unfold AIMG_TOP in *; lia | clear - Dhi; lia |].
        apply AGo. intros a Ha. unfold zwin in Ha. split; [clear - Ha; unfold DS_SIZE; lia|].
        clear - Ha DATd DPP HK1. unfold DS_SIZE in *. lia.
      - apply mdef_of_wr_at_hi; [exact DSW1 | exact N1].
      - apply AGo. intros a Ha. unfold zwin in Ha. split; [clear - Ha; unfold DS_SIZE; lia|].
        clear - Ha DATd DPP HK1. unfold DS_SIZE in *. lia.
      - clear - HK1; lia.
      - unfold dsdata in *. clear - Dpl HK1. lia.
      - intros d asz Em. split; [| split; [exact (Dmx d asz Em) | split; [exact (Dpow d asz Em) | exact (Ddj d asz Em)]]].
        pose proof (Dasz d asz Em). clear - H0 HK1. lia. }

    destruct CASES as [(Hc & E1 & HRT1 & HST1)|(Hx & E1 & HRT1)].
    -
      apply (ah_done H HH). unfold XNEXT. left. exists (i + k), msF1, mo1, si, m1, R1, LBi, DBi, msi, (ppi + k), hmi.
      split; [clear - HK1; lia|]. split; [reflexivity|].
      constructor.
      + exact E1.
      + exact RF1.
      + eapply rtbl_rew; [| exact HRT1]. rew_tbl.
      + eapply ftbl_rew; [| exact HST1]. rew_tbl.
      + exact KR1.
      + exact (ah_mpres_trans H HH _ _ _ xi_mp0 MP1).
      + exact MI1.
      + exact STK1.
      + exact ERR1.
      + exact RAUX1.
      + exact RH1.
      + exact RFS1.
      + exact AC1.
      + exact S01.
      + exact LV1.
      + exact xi_perm0.
      + exact REP1.
      + clear - xi_pp0. lia.
      + exact OWN1.
      + exact XP1.
      + exact xi_al0.
      + exact xi_bsm0.
      + exact xi_bcn0.
      + exact xi_blg0.
      + exact SRC1.
      + clear - Hc xi_i0 HK1. lia.
    -
      assert (EN : i + k = n) by (clear - Hx HK1; lia).
      apply (ah_done H HH). unfold XNEXT. right. unfold POSTxs, pc_post.
      rewrite (rfull_eq R1 RF1) in E1.
      rgetx HRT1 (1%bv : reg) G1. rgetx HRT1 (2%bv : reg) G2. rgetx HRT1 (3%bv : reg) G3. rgetx HRT1 (4%bv : reg) G4.
      rgetx HRT1 (8%bv : reg) G8. rgetx HRT1 (9%bv : reg) G9. rgetx HRT1 (10%bv : reg) G10.
      rgetx HRT1 (18%bv : reg) G18. rgetx HRT1 (19%bv : reg) G19. rgetx HRT1 (20%bv : reg) G20. rgetx HRT1 (21%bv : reg) G21.
      rgetx HRT1 (22%bv : reg) G22. rgetx HRT1 (23%bv : reg) G23. rgetx HRT1 (24%bv : reg) G24. rgetx HRT1 (25%bv : reg) G25.
      rgetx HRT1 (26%bv : reg) G26. rgetx HRT1 (27%bv : reg) G27.
      rewrite G1, G2, G3, G4, G8, G9, G10, G18, G19, G20, G21, G22, G23, G24, G25, G26, G27 in E1. rewrite EN in E1.
      exists (PropExec.getr R1 5), (PropExec.getr R1 6), (PropExec.getr R1 7), (PropExec.getr R1 11), (PropExec.getr R1 12),
             (PropExec.getr R1 13), (PropExec.getr R1 14), (PropExec.getr R1 15), (PropExec.getr R1 16), (PropExec.getr R1 17),
             (PropExec.getr R1 28), (PropExec.getr R1 29), (PropExec.getr R1 30), (PropExec.getr R1 31), m1.
      destruct ERR1 as (e1 & ERR1). exists e1, si, LBi. cbn [cfg_ms cfg_model].
      split; [exact E1|]. split; [exact KR1|]. split; [exact (ah_mpres_trans H HH _ _ _ xi_mp0 MP1)|].
      split; [exact MI1|]. split; [exact STK1|]. split; [exact ERR1|]. split; [exact RAUX1|]. split; [exact RH1|].
      split; [exact RFS1|]. split; [exact AC1|]. split; [exact S01|]. split; [exact LV1|].
      exists DBi, msi, (ppi + k), hmi. split; [exact xi_perm0|].
      split; [replace (len + n) with (len + (i + k)) by (clear - EN; lia); exact REP1|].
      split; [clear - xi_pp0 EN; lia|]. split; [exact OWN1|]. split; [exact XP1 | exact xi_al0].
  Qed.

  Definition W0 : list (Z * Z) := [(spz - 64, spz); (ds + 56, ds + 72)].

  Lemma firstn1_skipn : forall (bs : list byte) k d, (k < length bs)%nat -> firstn 1 (skipn k bs) = [nth k bs d].
  Proof.
    intros bs k d Hk. destruct (skipn k bs) as [|b r] eqn:SK.
    - exfalso. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia.
    - cbn. f_equal. rewrite <- (Nat.add_0_r k), <- nth_skipn, SK. reflexivity.
  Qed.

  Lemma stk_join : forall mm lo' mid hi, stk asegs mm lo' mid -> stk asegs mm mid hi -> stk asegs mm lo' hi.
  Proof.
    intros mm lo' mid hi (A1 & A2 & A3) (B1 & B2 & B3). split; [exact A1|]. split; [exact B2|].
    intros a Ha. destruct (Z.lt_ge_cases a mid); [apply A3 | apply B3]; lia.
  Qed.

  Lemma stk_hi_of_xpres : forall LBx X m1 m2 mid hi,
    stk asegs m1 mid hi -> xpres H LBx mid X m1 m2 -> (forall a, mid <= a < hi -> ~ rin_ivs X a) -> stk asegs m2 mid hi.
  Proof.
    intros LBx X m1 m2 mid hi (S1 & S2 & S3) XP HX. split; [exact S1|]. split; [exact S2|].
    intros a Ha. destruct (S3 a Ha) as [W1 [b R1]].
    destruct (XP a ltac:(lia) (conj (or_introl (proj1 Ha)) (HX a Ha))) as [E WV].
    split; [exact (WV W1)|]. exists b. unfold mrd in *. rewrite E. exact R1.
  Qed.

  Lemma rep_reframe : forall LBi ma mb leni DBi msi ppi hmi si i c k,
    ds_rep_w LBi ma ds err leni DBi msi ppi hmi fl fill -> as_RHEAP H si LBi ma ->
    munch W0 ma mb -> wmono asegs ma mb ->
    ftbl (XW i ppi (epof msi) c k) ds mb DTX ->
    ds_rep_w LBi mb ds err leni DBi msi ppi hmi fl fill.
  Proof.
    intros LBi ma mb leni DBi msi ppi hmi si i c k REPa RHa MU WM DT.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & _).
    pose proof (rep_facts LBi ma leni DBi msi ppi hmi REPa) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & CASE).
    pose proof REPa as (DIa & BLKa & DSAa & DSWa & DSOa & SBAa). pose proof DSOa as (O1 & O2 & O3).
    assert (WH : wins_hi W0).
    { unfold wins_hi, W0, AIMG_TOP, ALOWSH_LO, AHI_LO, DS_SIZE in *. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - right. clear - N6 A1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia. }
    assert (DSAb : addressable mb ds DS_SIZE) by (eapply addressable_transport_hi; [exact DSAa | exact MU | exact WM | exact O3 | exact WH]).
    assert (DSWb : wr_at asegs mb ds DS_SIZE) by (eapply wr_at_transport; [exact DSWa | exact WM]).
    assert (SBAb : sb_addr mb msi).
    { destruct msi as [|d asz]; [exact I|]. cbn [sb_addr] in SBAa |- *. destruct SBAa as [SA SO]. split; [| exact SO].
      destruct SO as (Q1 & Q2 & Q3). eapply addressable_transport_hi; [exact SA | exact MU | exact WM | exact Q3 | exact WH]. }
    split; [| split; [exact BLKa | split; [exact DSAb | split; [exact DSWb | split; [exact DSOa | exact SBAb]]]]].
    pose proof DIa as DI0. destruct DIa as [Dpos Dal Dhi Ddef Dvt Dsb DBeq Dmx Dpow Dlen0 Dpl Dasz Ddj Dios D320 D336 D360 D368 Derr].
    assert (AGo : forall P : Z -> Prop, (forall a, P a -> (ds <= a < ds + 56 \/ ds + 72 <= a < ds + DS_SIZE)) -> CRep.agree_on P ma mb).
    { intros P HP. eapply agree_munch'; [exact MU|]. intros a Ha. pose proof (HP a Ha) as R1'. unfold W0. cbn [outside].
      clear - R1' N1 N2 N6 LO Dhi. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK, AAPP_HI in *. lia. }
    assert (FO : forall a (w : nat) v, (ds <= a /\ a + Z.of_nat w <= ds + 56) \/ (ds + 72 <= a /\ a + Z.of_nat w <= ds + DS_SIZE) ->
                 CRep.fld ASEGS ma a w v -> CRep.fld ASEGS mb a w v).
    { intros a w v Ho HF. eapply (fld_ag ma mb (fun x => ds <= x < ds + 56 \/ ds + 72 <= x < ds + DS_SIZE));
        [clear - Ho N1; unfold AIMG_TOP in *; lia | clear - Ho Dhi; unfold DS_SIZE in *; lia | | apply AGo; intros x Hx; exact Hx | exact HF].
      intros x Hx. clear - Ho Hx. lia. }
    destruct Dsb as [Fvt Floc Fbi Fni Fei (cs & STR & CSL) Fpb Fpp Fep Hpp Fhm Hhm Fmode].
    replace (ds + 8 + 64) with (ds + 72) in * by lia.
    rewrite (ds_blk_lbl _ _ _ BLKa).
    eapply (ds_inv_resb _ (lbl LBi) ma mb ds err leni leni (lbl DBi) msi ppi hmi fl fill msi ppi hmi fl fill DI0).
    - constructor; replace (ds + 8 + 64) with (ds + 72) by lia.
      + apply FO; [left; cbn; lia | exact Fvt].
      + apply FO; [left; cbn; lia | exact Floc].
      + apply FO; [left; cbn; lia | exact Fbi].
      + apply FO; [left; cbn; lia | exact Fni].
      + apply FO; [left; cbn; lia | exact Fei].
      + exists cs. split; [| exact CSL]. eapply str_frame; [exact STR|].
        eapply agree_munch'; [exact MU|]. intros a Ha. unfold W0. cbn [outside]. unfold str_fp in Ha.
        destruct CASE as [(Em & EDB & Hdat & Hcap)|(pid & d & asz & Em & EDB & INb & Hdat & Hcap & Hasz & Hdj & Had & Hao)]; rewrite Em in *;
          cbn [str_data str_cap] in *.
        * destruct Ha as [Ha|Ha]; [| destruct Ha]. unfold zwin in Ha.
          clear - Ha N1 N2 N6 LO Dhi. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
        * destruct STR as (_ & _ & _ & HL4 & (Hd & _ & Hdsz & _) & _). cbn [str_cap] in HL4.
          pose proof (ah_blocks H HH _ _ _ (pid, d, asz) RHa INb) as (R0 & _ & Rn & RI & RC & _). cbn [blk_addr blk_size fst snd] in R0, Rn, RI, RC.
          unfold zwin in Ha.
          clear - Ha N1 N2 N6 LO R0 Rn RI RC CEIL HL4 Dhi Hdj A2. unfold AIMG_TOP, DS_SIZE, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      + apply FO; [left; cbn; lia | exact Fpb].
      + replace (ds + 8 + 48) with (ds + 56) by lia. eapply (fld_of_ftbl _ ds mb DTX 56 8 _ ppi DT); [left; reflexivity |]. wev.
      + replace (ds + 8 + 56) with (ds + 64) by lia. eapply (fld_of_ftbl _ ds mb DTX 64 8 _ _ DT); [right; left; reflexivity |]. unfold epof, dsdata. wev.
      + exact Hpp.
      + apply FO; [right; cbn; unfold DS_SIZE; lia | exact Fhm].
      + exact Hhm.
      + apply FO; [right; cbn; unfold DS_SIZE; lia | exact Fmode].
    - eapply ios_inv_frame; [exact Dios | clear - N1; unfold AIMG_TOP in *; lia | clear - Dhi; lia |].
      apply AGo. intros a Ha. unfold zwin in Ha. clear - Ha; unfold DS_SIZE; lia.
    - apply mdef_of_wr_at_hi; [exact DSWb | exact N1].
    - apply AGo. intros a Ha. unfold zwin in Ha. clear - Ha; unfold DS_SIZE; lia.
    - lia.
    - exact Dpl.
    - intros d asz Em. split; [exact (Dasz d asz Em) | split; [exact (Dmx d asz Em) | split; [exact (Dpow d asz Em) | exact (Ddj d asz Em)]]].
  Qed.

  Lemma ksrc_ok : forall mi (R : bvmap 5 word) X bs mm c i' pp' ep' k',
    bytes_at asegs mi p bs -> length bs = Z.to_nat n -> 0 <= i' < n -> c = bv_unsigned (nth (Z.to_nat i') bs (Z_to_bv 8 0)) ->
    munch W0 mi mm ->
    kentry_ok asegs (HLib.Eseed R (XW i' pp' ep' c k' ++ X)) mm (KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 51)) 0) 1 (EVar 54)).
  Proof.
    intros mi R X bs mm c i' pp' ep' k' BB BSL Hi Hc MU.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
    pose proof SRC as (P0 & Pn & _ & IAM & PSTK & PDJ).
    assert (BB' : bytes_at asegs mm p bs).
    { eapply bytes_at_transport; [exact BB | exact MU |]. rewrite BSL, Z2Nat.id by lia. unfold W0. cbn [disjoint_from]. split; [| split; [| exact I]].
      - clear - PSTK N13. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - destruct (ivl_disj p n ds DS_SIZE N0 ltac:(unfold DS_SIZE; lia)) as [K|K]; [| left; clear - K; lia | right; clear - K; unfold DS_SIZE in K; lia].
        intros x Hx. exact (proj1 (PDJ x Hx)). }
    set (E := HLib.Eseed R (XW i' pp' ep' c k' ++ X)).
    assert (EV : forall n0, (32 <= n0 < 56)%N -> ev E n0 = ev (wenv (XW i' pp' ep' c k')) n0).
    { intros n0 Hn0. subst E. apply Eseed_wenv. exact Hn0. }
    assert (Hs : estart E (SA (EAlu ALU_ADD (EVar 35) (EVar 51)) 0) = p + i').
    { unfold estart. cbn [a_base a_off edenot]. rewrite (EV 35%N), (EV 51%N) by (split; [discriminate|reflexivity]).
      unfold wenv, XW; unfold HLib.Eseed, reg_ev, Wx;
        lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add Nat.sub nth app].
      rewrite LbB_PcOvf.w_add_g, unsigned_lit by (clear - P0 Hi N15; lia). clear; lia. }
    cbn [kentry_ok]. split; [clear; lia|]. split; [unfold flat; rewrite Hs; clear - P0 Hi N15; lia|].
    rewrite (adenot_of_estart E _ (p + i') Hs ltac:(clear - P0 Hi N15; lia)).
    cbn [edenot]. rewrite (EV 54%N) by (split; [discriminate|reflexivity]).
    unfold wenv, XW; unfold HLib.Eseed, reg_ev, Wx;
      lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op Init.Nat.add Nat.sub nth app].
    rewrite Hc, word_to_le_bytes_1.
    pose proof (bytes_at_rdn asegs mm p bs (Z.to_nat i') 1 BB' ltac:(rewrite BSL; clear - Hi; lia)) as RD.
    unfold wa in RD. rewrite Z2Nat.id in RD by (clear - Hi; lia). rewrite <- LbB_Conv.rdn_HL in RD.
    rewrite (firstn1_skipn bs (Z.to_nat i') (Z_to_bv 8 0)) in RD by (rewrite BSL; clear - Hi; lia). exact RD.
  Qed.

  Lemma rtxp_of_rtxo : forall W (R1 : bvmap 5 word) y5 y6 y7 a0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    rtbl W R1 RTXO -> a0 = edenot (wenv W) (EVar 54) ->
    rtbl W (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) y5 y6 y7
                (PropExec.getr R1 8) (PropExec.getr R1 9) a0 y11 y12 y13 y14 y15 y16 y17
                (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21)
                (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                (PropExec.getr R1 26) (PropExec.getr R1 27) y28 y29 y30 y31) RTXP.
  Proof.
    intros W R1 y5 y6 y7 a0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HT Ha0.
    assert (G : forall r e, In (r, e) RTXO -> PropExec.getr R1 r = edenot (wenv W) e) by (intros r e Hi; exact (rtbl_In W R1 RTXO r e HT Hi)).
    unfold rtbl, RTXP. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
      first [ exact Ha0
            | rewrite (getr_mkR_keptR R1 _ y5 y6 y7 a0 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 eq_refl) by (cbn; tauto);
              apply G; unfold RTXO; repeat (first [left; reflexivity | right]) ].
  Qed.
  Lemma w0_ok : forall LBi, wok LBi W0.
  Proof.
    intros LBi. pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & _).
    pose proof DSIN as ((f & Hf & IF1 & IF2) & _).
    assert (SH : sh aceil >= 0x7fff8000) by (unfold sh, ASHADOW_BASE; clear - A1; Z.div_mod_to_equations; lia).
    unfold wok, W0, DS_SIZE, AFS_SIZE, AIMG_TOP, AHI_LO, ALOWSH_LO, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *.
    split; [|split; [|split; [|split; [|split]]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. clear - N6. lia.
      + right; right; right; right; left. clear - N4 N5. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold afs_write_ok; cbn [fst snd]; unfold AFS_SIZE.
      + left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP. clear - N6 N10 A1. lia.
      + right. exists f. split; [exact Hf|]. clear - IF1 IF2. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok, AHI_LO; cbn [fst snd].
      + left. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [right | left]; clear - N11 SH; lia.
    - unfold wins_hi, AIMG_TOP, ALOWSH_LO, AHI_LO. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      + right. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [left | right]; clear - N1 N11; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - N6 A1. lia.
      + destruct N11 as [N11|N11]; [apply LbB_DPdK.aconst_ok_lo | apply LbB_DPdK.aconst_ok_hi]; unfold AIMG_TOP; clear - N1 N11; lia.
    - intros a k Ha. cbn [disjoint_from]. clear - Ha N1 N6 A1. lia.
  Qed.

  Lemma ICM_le : forall x, 0 <= x -> 0 <= ICM x <= 4 * x.
  Proof. intros x Hx. unfold ICM. destruct (Z.leb_spec x 64512); lia. Qed.

  Lemma lbk_meas : lb_small LBk <= lb_small LB /\ Z.of_nat (length LBk) <= Z.of_nat (length LB) /\ nlarge LBk <= nlarge LB.
  Proof.
    rewrite (pc_lb_small_perm _ _ PERM), (pc_nlarge_perm _ _ PERM), (Permutation_length PERM), pc_lb_small_app, pc_nlarge_app, length_app.
    assert (FD : Forall (fun b => 0 <= blk_size b) DB).
    { apply Forall_forall. intros b Hb. assert (HbL : In b LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; left; exact Hb).
      pose proof (ah_blocks H HH _ _ _ b RH HbL) as (_ & _ & Rn & _). exact Rn. }
    pose proof (pc_lb_small_nonneg DB FD). pose proof (pc_nlarge_nonneg DB). lia.
  Qed.

  Lemma xs_full : forall i msF moi si mi R LBi DBi msi ppi hmi,
    xinv i msF moi si mi R LBi DBi msi ppi hmi -> epof msi <= ppi -> as_SR H (XNEXT i) (mkCfg msF moi).
  Proof.
    intros i msF moi si mi R LBi DBi msi ppi hmi XI FULL. destruct XI.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
    pose proof (rep_facts LBi mi (len + i) DBi msi ppi hmi xi_rep0) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & CASE).
    pose proof xi_rep0 as (DIi & BLKi & DSAi & DSWi & DSOi & SBAi).
    assert (PPE : ppi = epof msi) by (clear - FULL D1; lia).
    pose proof lbk_meas as (KM1 & KM2 & KM3). pose proof SRC as (P0 & Pn & _ & IAM & PSTK & PDJ).

    destruct (srcx_keep_now H LBk LF spz _ mi p n si LBi xi_src0 xi_ac0 xi_mi0 xi_rh0 (fun b Hb => Permutation_in b (Permutation_sym xi_perm0) (in_or_app DBi LBk b (or_intror Hb)))) as (bs & BSL & BB & BA & BV).
    set (c := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
    assert (CR : 0 <= c <= 255).
    { subst c. pose proof (bv_unsigned_in_range _ (nth (Z.to_nat i) bs (Z_to_bv 8 0))) as Rc. change (bv_modulus 8) with 256 in Rc. clear - Rc. lia. }
    destruct (dtx_of_rep LBi mi (len + i) DBi msi ppi hmi i c 0 xi_rep0) as [HDT VTi].
    assert (HRT : rtbl (XW i ppi (epof msi) c 0) R RTXH) by (eapply rtbl_rew; [| exact xi_rt0]; rew_tbl).
    assert (HST : ftbl (XW i ppi (epof msi) c 0) spz mi STX) by (eapply ftbl_rew; [| exact xi_st0]; rew_tbl).

    eapply (ahh_evt_then H HH _ _ si msF _ moi xi_kr0 xi_vis0).
    { eapply (xr_b ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mi ds p n i ppi (epof msi) c 0 lo
                DSOi DSWi xi_stk0 CEIL ltac:(clear - LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2
                (proj1 xi_lv0) VTi).
      - clear - P0 N15 N13 xi_i0 D0 D1 D2 CR N14. unfold epof in *. lia.
      - exact xi_rf0.
      - exact HRT.
      - exact HST.
      - exact HDT.
      - exact xi_mi0.
      - exact FULL.
      - clear - xi_i0; lia.
      - intros mm [MUm WMm] MIm. eapply (ksrc_ok mi R [] bs mm c i ppi (epof msi) 0 BB BSL xi_i0 eq_refl MUm). }
    intros msF1 mo1 KR1 MP1 (R1 & m1 & E1 & RF1 & HRT1 & HST1 & HDT1 & [MU1 WM1] & MI1).

    destruct (xs_frame LBi mi (len + i) DBi msi ppi hmi si W0 m1 xi_rep0 xi_rh0 xi_own0 xi_rfs0 xi_stk0 xi_err0 xi_raux0
                xi_ac0 xi_sz0 xi_lv0 (w0_ok LBi) MU1 WM1) as (RH1 & OWN1 & RFS1 & STK1 & (e1 & ERR1) & RAUX1 & AC1 & S01 & LV1 & DSA1 & DSW1 & SBA1).
    pose proof (rep_reframe LBi mi m1 (len + i) DBi msi ppi hmi si i c 0 xi_rep0 xi_rh0 MU1 WM1 HDT1) as REP1.
    assert (PERM' : Permutation LBi (LBk ++ DBi)) by (eapply Permutation_trans; [exact xi_perm0 | apply Permutation_app_comm]).
    assert (SPX : aceil <= spz) by (clear - N6 CEIL N2 N1; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia).
    assert (W0MIX : forall LBr X, (forall a, ds <= a < ds + DS_SIZE -> rin_ivs X a) -> Forall (LbB_HKit.wmix LBr spz X) W0).
    { intros LBr X HX. unfold W0. repeat apply Forall_cons; try apply Forall_nil; unfold LbB_HKit.wmix; cbn [fst snd].
      - left. clear - N6 A1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right; left. intros a Ha. apply HX. clear - Ha. unfold DS_SIZE. lia. }
    assert (XPm1 : xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m1).
    { eapply (LbB_HKit.xpres_munch_mixed H HH si LBi LBk DBi spz _ _ m mi m1 xi_xp0 xi_rh0 PERM' SPX MU1 WM1).
      apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }
    assert (SRCm1 : srcx_keep H LBk LF spz [(ds, ds + DS_SIZE)] m1 p n).
    { eapply srcx_keep_fwd0; [exact xi_src0|].
      eapply (LbB_HKit.xpres_munch_mixed H HH si LBi LBk DBi spz _ _ mi mi m1 (xpres_refl _ _ _ _ _) xi_rh0 PERM' SPX MU1 WM1).
      apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }

    rewrite (rfull_eq R1 RF1) in E1.
    rgetx HRT1 (1%bv : reg) G1. rgetx HRT1 (2%bv : reg) G2. rgetx HRT1 (4%bv : reg) G4.
    rgetx HRT1 (10%bv : reg) G10. rgetx HRT1 (11%bv : reg) G11.
    rewrite <- (Z_to_bv_bv_unsigned sp) in G2. rewrite LbB_PcOvf.w_add_g in G2.
    assert (U2 : bv_unsigned (PropExec.getr R1 2) = spz - 64).
    { rewrite G2. apply unsigned_lit. clear - N6 N7 A1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia. }

    assert (BUD : ICM (str_grow msi) <= as_AL H si /\ 8 * blkof msi + ICM (str_grow msi) <= 8 * str_grow msi).
    { pose proof (di_pl _ _ _ _ _ _ _ _ _ _ _ DIi) as PL. unfold ds_cost in COST. unfold epof, dsdata in *.
      pose proof (rep_facts LB m len DB ms pp hm REP) as (_ & _ & _ & _ & _ & _ & _ & B7 & _).
      destruct CASE as [(Em & _ & Hdat & Hcap)|(pid & d & asz & Em & _ & _ & Hdat & Hcap & Hasz & _)]; rewrite Em in *; cbn [str_grow blkof str_data str_cap] in *.
      - replace (ICM 48) with 0 by reflexivity. clear - COST xi_al0 N16 N0 B7. lia.
      - pose proof (ICM_le (2 * asz) ltac:(clear - Hasz D4; lia)) as IC. clear - COST xi_al0 N16 N0 B7 IC PL PPE xi_i0 Hasz. lia. }
    destruct BUD as [BUD1 BUD2].

    eapply (ah_seq H HH).
    { eapply ((LbB_PcOvfS.ovf_okA H HHbp)
                (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
                (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
                (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
                (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
                (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
                (PropExec.getr R1 31) F fc msF1 m1 mo1 si LBi LBk DBi LF lo B shi e1 ds err (len + i) c msi hmi fl fill).
      - unfold pc_pre. split; [exact E1|]. split; [exact RH1|]. split; [exact KR1|]. split; [exact RAUX1|].
        split; [rewrite U2; clear - SPB; lia|]. split; [exact BB64|]. split; [rewrite U2; clear - SP16; Z.div_mod_to_equations; lia|].
        split; [rewrite U2; exact (proj1 (stk_split asegs m1 lo (spz - 64) spz STK1 ltac:(clear - LO N6 CEIL; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia)))|].
        split; [exact CEIL|]. split; [rewrite U2; clear - LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia|].
        split; [rewrite G4; exact ERR1|]. split; [exact MI1|]. split; [rewrite G4; exact TP|].
        split; [rewrite G1, unsigned_lit by (clear; lia); reflexivity|].
        split; [exact LV1|]. split; [exact AC1|]. split; [exact RFS1|]. split; [exact S01|]. rewrite U2. clear - SPS. lia.
      - exact G10.
      - rewrite G11. reflexivity.
      - exact CR.
      - unfold epof in PPE. rewrite <- PPE. exact REP1.
      - exact xi_perm0.
      - exact OWN1.
      - exact DSIN.
      - clear - LEN xi_i0. lia.
      - clear - xi_bsm0 KM1 BS. lia.
      - clear - xi_bcn0 KM2 BC. lia.
      - clear - xi_blg0 KM3 BL. lia.
      - exact BUD1.
      - exact TRO. }
    intros [msF2 mo2] POST2.
    destruct POST2 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & e2 & sk2 & LB2
                      & VIS2 & KR2 & MP2 & MI2 & STK2 & ERR2 & RAUX2 & RH2 & RFS2 & AC2 & S02 & LV2 & (pid' & d' & PERM2 & REP2 & OWN2 & XP2 & AL2)).
    cbn [cfg_ms cfg_model] in *.
    rewrite U2 in STK2, XP2. rewrite G4 in ERR2.
    set (msn := SLong d' (str_grow msi)) in *. set (ppn := d' + str_cap msi + 1) in *.
    pose proof (rep_facts LB2 m2 (len + i + 1) [(pid', d', str_grow msi)] msn ppn ppn REP2) as (E0 & E1' & E2 & E3' & E4 & E5 & E6 & E7 & CASE2).
    pose proof REP2 as (DI2 & BLK2 & DSA2 & DSW2 & DSO2 & SBA2).
    destruct (dtx_of_rep LB2 m2 (len + i + 1) _ msn ppn ppn i c 0 REP2) as [HDT2 VT2].

    assert (XIV : Forall (fun iv : Z * Z => spz - 64 + 64 <= fst iv \/ snd iv <= spz - 64) ((ds, ds + DS_SIZE) :: sbx msi)).
    { apply Forall_cons; [cbn [fst snd]; right; clear - N2 LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia|].
      destruct CASE as [(Em & _)|(pid & d & asz & Em & EDB & INb & Hdat & Hcap & Hasz & Hdj & Had & Hao)]; rewrite Em; cbn [sbx]; [apply Forall_nil|].
      pose proof (ah_blocks H HH _ _ _ (pid, d, asz) xi_rh0 INb) as (R0 & _ & Rn & RI & RC & _). cbn [blk_addr blk_size fst snd] in R0, Rn, RI, RC.
      pose proof (sh_nsh_high d asz ltac:(clear - R0; lia) Rn ltac:(clear - RC A2; unfold AAPP_HI; lia)) as SH.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; cbn [fst snd]; right.
      - clear - RC CEIL LO. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - clear - SH A1 CEIL LO. unfold AHI_LO, XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia. }
    assert (XCL : forall a, spz - 64 <= a < spz -> ~ rin_ivs ((ds, ds + DS_SIZE) :: sbx msi) a).
    { intros a Ha K. clear - XIV Ha K. induction XIV as [|iv X0 Hiv _ IH]; [exact K|]. cbn in K. destruct K as [K|K]; [| exact (IH K)].
      destruct iv as [l h]; cbn [fst snd] in Hiv, K. lia. }
    assert (STK2' : stk asegs m2 lo spz).
    { eapply stk_join; [exact STK2|]. eapply (stk_hi_of_xpres LBk _ m1 m2); [| exact XP2 | exact XCL].
      exact (proj2 (stk_split asegs m1 lo (spz - 64) spz STK1 ltac:(clear - LO N6 CEIL; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia))). }
    assert (HST2 : ftbl (XW i ppn (epof msn) c 0) spz m2 STX).
    { assert (HST1' : ftbl (XW i ppn (epof msn) c 0) spz m1 STX) by (eapply ftbl_rew; [| exact HST1]; rew_tbl).
      eapply (LbB_PcOvfS.ftbl_xpres H LBk (spz - 64) _ _ spz m1 m2 STX (-64) 0 HST1' XP2 ltac:(vm_compute; reflexivity)).
      split; [left; clear; lia|]. replace (spz + -64 + (0 - -64)) with (spz - 64 + 64) by lia. replace (spz + -64) with (spz - 64) by lia. exact XIV. }
    assert (HRT2 : rtbl (XW i ppn (epof msn) c 0)
                     (mkR (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) t0' t1' t2'
                          (PropExec.getr R1 8) (PropExec.getr R1 9) (Z_to_bv 64 c) a1' a2' a3' a4' a5' a6' a7'
                          (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20) (PropExec.getr R1 21)
                          (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
                          (PropExec.getr R1 26) (PropExec.getr R1 27) t3' t4' t5' t6') RTXP).
    { apply rtxp_of_rtxo; [eapply rtbl_rew; [| exact HRT1]; rew_tbl | symmetry; wev]. }
    assert (RPC : ret_pc (PropExec.getr R1 1) = Z_to_bv 64 AXORA) by (rewrite G1; unfold AXORA; apply ret_pc_even; [clear; lia | reflexivity]). rewrite RPC in VIS2.

    eapply (ahh_evt_then H HH _ _ sk2 msF2 _ mo2 KR2 VIS2).
    { eapply (xr_after_ovf ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m2 ds p n i ppn (epof msn) c 0 lo
                DSO2 DSW2 STK2' CEIL ltac:(clear - LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2
                (proj1 LV2) VT2).
      - clear - P0 N15 N13 xi_i0 E0 E1' E2 CR N14. unfold epof in *. lia.
      - apply rfull_mkR.
      - exact HRT2.
      - exact HST2.
      - exact HDT2.
      - exact MI2.
      - exact AC2. }
    intros msF3 mo3 KR3 MP3 (R3 & m3 & RF3 & MU3 & WM3 & MI3 & AC3 & HDT3 & CASES).

    change (munch W0 m2 m3) in MU3.
    destruct (xs_frame LB2 m2 (len + i + 1) _ msn ppn ppn sk2 W0 m3 REP2 RH2 OWN2 RFS2 STK2' (ex_intro _ e2 ERR2) RAUX2 AC2 S02 LV2
                (w0_ok LB2) MU3 WM3) as (RH3 & OWN3 & RFS3 & STK3 & ERR3 & RAUX3 & _ & S03 & LV3 & DSA3 & DSW3 & SBA3).
    pose proof (rep_reframe LB2 m2 m3 (len + i + 1) _ msn ppn ppn sk2 i c 0 REP2 RH2 MU3 WM3 HDT3) as REP3.

    assert (XDROP : forall Xt, (forall a, ds <= a < ds + DS_SIZE -> rin_ivs Xt a) -> xpres H LBk spz Xt m1 m2).
    { intros Xt HXt.
      assert (XPw : xpres H LBk spz (Xt ++ sbx msi) m1 m2).
      { eapply xpres_weaken; [exact XP2 | clear; lia | intros b Hb; exact Hb |].
        intros a Ha. cbn [rin_ivs fst snd] in Ha. apply rin_ivs_app. destruct Ha as [Ha|Ha]; [left; apply HXt; exact Ha | right; exact Ha]. }
      destruct CASE as [(Em & _)|(pid & d & asz & Em & EDB & INb & _)]; rewrite Em in XPw; cbn [sbx] in XPw.
      - rewrite app_nil_r in XPw. exact XPw.
      - eapply (xpres_drop_blk H HH si LBi m1 LBk DBi pid d asz spz Xt m1 m2 RH1 PERM'); [rewrite EDB; left; reflexivity | exact SPX | exact XPw]. }
    assert (PERM2' : Permutation LB2 (LBk ++ [(pid', d', str_grow msi)])) by (eapply Permutation_trans; [exact PERM2 | apply Permutation_cons_append]).
    assert (XPm3 : xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m3).
    { eapply (LbB_HKit.xpres_munch_mixed H HH sk2 LB2 LBk _ spz _ _ m m2 m3); [| exact RH2 | exact PERM2' | exact SPX | exact MU3 | exact WM3 |].
      - eapply xpres_trans; [exact XPm1 | apply XDROP]. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha.
      - apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }
    assert (SRC3 : srcx_keep H LBk LF spz [(ds, ds + DS_SIZE)] m3 p n).
    { eapply srcx_keep_fwd0; [exact SRCm1|].
      eapply (LbB_HKit.xpres_munch_mixed H HH sk2 LB2 LBk _ spz _ _ m1 m2 m3); [| exact RH2 | exact PERM2' | exact SPX | exact MU3 | exact WM3 |].
      - apply XDROP. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha.
      - apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }

    assert (AL3 : as_AL H sk2 >= as_AL H s - 8 * (blkof msn - blkof ms)).
    { subst msn. cbn [blkof]. clear - AL2 xi_al0 BUD2. lia. }
    pose proof (rep_facts LB m len DB ms pp hm REP) as (B0 & B1 & _).
    assert (GR : 48 <= str_grow msi).
    { destruct CASE as [(Em & _)|(pid & d & asz & Em & _ & _ & _ & _ & Hasz & _)]; rewrite Em; cbn [str_grow]; [clear - N16 xi_i0; lia | clear - Hasz N16 xi_i0; lia]. }
    assert (MS3 : lb_small LB2 <= lb_small LBk + 64512 /\ Z.of_nat (length LB2) <= Z.of_nat (length LBk) + 1 /\ nlarge LB2 <= nlarge LBk + 1).
    { rewrite (pc_lb_small_perm _ _ PERM2), (pc_nlarge_perm _ _ PERM2), (Permutation_length PERM2), lb_small_cons, nlarge_cons. cbn [length blk_size snd].
      pose proof (nsmall_bounds (str_grow msi) ltac:(clear - GR; lia)) as NS. pose proof (nlg_bounds (str_grow msi)) as NL.
      unfold nsmall in NS |- *. destruct (Z.leb_spec (str_grow msi) 64512); clear - NS NL GR H0; lia. }
    destruct MS3 as (MS31 & MS32 & MS33).
    assert (PPN : ppn - dsdata ds msn = pp - dsdata ds ms + (i + 1)).
    { subst ppn msn. unfold dsdata in *. cbn [str_data]. unfold epof, dsdata in PPE. clear - xi_pp0 PPE. lia. }
    pose proof (ah_mpres_trans H HH _ _ _ (ah_mpres_trans H HH _ _ _ xi_mp0 MP1) (ah_mpres_trans H HH _ _ _ MP2 MP3)) as MP03.
    destruct CASES as [(Hc & E3 & HRT3 & HST3)|(Hx & E3 & HRT3)].
    -
      apply (ah_done H HH). unfold XNEXT. left.
      exists (i + 1), msF3, mo3, sk2, m3, R3, LB2, [(pid', d', str_grow msi)], msn, ppn, ppn.
      split; [clear; lia|]. split; [reflexivity|].
      constructor.
      + exact E3.
      + exact RF3.
      + eapply rtbl_rew; [| exact HRT3]. rew_tbl.
      + eapply ftbl_rew; [| exact HST3]. rew_tbl.
      + exact KR3.
      + exact MP03.
      + exact MI3.
      + exact STK3.
      + exact ERR3.
      + exact RAUX3.
      + exact RH3.
      + exact RFS3.
      + exact AC3.
      + exact S03.
      + exact LV3.
      + exact PERM2.
      + replace (len + (i + 1)) with (len + i + 1) by (clear; lia). exact REP3.
      + exact PPN.
      + exact OWN3.
      + exact XPm3.
      + exact AL3.
      + exact MS31.
      + exact MS32.
      + exact MS33.
      + exact SRC3.
      + clear - Hc xi_i0. lia.
    -
      assert (EN : i + 1 = n) by (clear - Hx xi_i0; lia).
      apply (ah_done H HH). unfold XNEXT. right. unfold POSTxs, pc_post.
      rewrite (rfull_eq R3 RF3) in E3.
      rgetx HRT3 (1%bv : reg) K1. rgetx HRT3 (2%bv : reg) K2. rgetx HRT3 (3%bv : reg) K3. rgetx HRT3 (4%bv : reg) K4.
      rgetx HRT3 (8%bv : reg) K8. rgetx HRT3 (9%bv : reg) K9. rgetx HRT3 (10%bv : reg) K10.
      rgetx HRT3 (18%bv : reg) K18. rgetx HRT3 (19%bv : reg) K19. rgetx HRT3 (20%bv : reg) K20. rgetx HRT3 (21%bv : reg) K21.
      rgetx HRT3 (22%bv : reg) K22. rgetx HRT3 (23%bv : reg) K23. rgetx HRT3 (24%bv : reg) K24. rgetx HRT3 (25%bv : reg) K25.
      rgetx HRT3 (26%bv : reg) K26. rgetx HRT3 (27%bv : reg) K27.
      rewrite K1, K2, K3, K4, K8, K9, K10, K18, K19, K20, K21, K22, K23, K24, K25, K26, K27 in E3. rewrite EN in E3.
      exists (PropExec.getr R3 5), (PropExec.getr R3 6), (PropExec.getr R3 7), (PropExec.getr R3 11), (PropExec.getr R3 12),
             (PropExec.getr R3 13), (PropExec.getr R3 14), (PropExec.getr R3 15), (PropExec.getr R3 16), (PropExec.getr R3 17),
             (PropExec.getr R3 28), (PropExec.getr R3 29), (PropExec.getr R3 30), (PropExec.getr R3 31), m3.
      destruct ERR3 as (e3 & ERR3). exists e3, sk2, LB2. cbn [cfg_ms cfg_model].
      split; [exact E3|]. split; [exact KR3|]. split; [exact MP03|].
      split; [exact MI3|]. split; [exact STK3|]. split; [exact ERR3|]. split; [exact RAUX3|]. split; [exact RH3|].
      split; [exact RFS3|]. split; [exact AC3|]. split; [exact S03|]. split; [exact LV3|].
      exists [(pid', d', str_grow msi)], msn, ppn, ppn. split; [exact PERM2|].
      split; [replace (len + n) with (len + i + 1) by (clear - EN; lia); exact REP3|].
      split; [clear - PPN EN; lia|]. split; [exact OWN3|]. split; [exact XPm3 | exact AL3].
  Qed.

  Lemma xs_step : forall i msF moi si mi R LBi DBi msi ppi hmi,
    xinv i msF moi si mi R LBi DBi msi ppi hmi -> as_SR H (XNEXT i) (mkCfg msF moi).
  Proof.
    intros i msF moi si mi R LBi DBi msi ppi hmi XI. destruct (Z.lt_ge_cases ppi (epof msi)) as [L|L].
    - exact (xs_copy i msF moi si mi R LBi DBi msi ppi hmi XI L).
    - exact (xs_full i msF moi si mi R LBi DBi msi ppi hmi XI L).
  Qed.

  Lemma xs_loop : forall (fuel : nat) i msF moi si mi R LBi DBi msi ppi hmi,
    (Z.to_nat (n - i) <= fuel)%nat -> xinv i msF moi si mi R LBi DBi msi ppi hmi -> as_SR H POSTxs (mkCfg msF moi).
  Proof.
    induction fuel as [|fuel IH]; intros i msF moi si mi R LBi DBi msi ppi hmi Hf XI.
    - pose proof (xi_i _ _ _ _ _ _ _ _ _ _ _ XI) as Hi. exfalso. clear - Hf Hi. lia.
    - eapply (ah_seq H HH); [exact (xs_step i msF moi si mi R LBi DBi msi ppi hmi XI)|].
      intros cf [(i' & msF' & mo' & s' & m' & R' & LB' & DB' & ms' & pp' & hm' & Hlt & -> & XI')|PO].
      + pose proof (xi_i _ _ _ _ _ _ _ _ _ _ _ XI') as Hi'. apply (IH i' msF' mo' s' m' R' LB' DB' ms' pp' hm'); [clear - Hf Hlt Hi'; lia | exact XI'].
      + apply (ah_done H HH). exact PO.
  Qed.

  Lemma xs_main : forall t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF,
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ds + 8)) (Z_to_bv 64 p) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                             s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AXSP) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) ->
    as_SR H POSTxs (mkCfg msF mo).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF VIS KR.
    pose proof xs_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & (A1 & A2) & N9 & N10 & N11 & N12 & N13 & N14 & N15 & N16).
    pose proof (rep_facts LB m len DB ms pp hm REP) as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & CASE).
    pose proof REP as (DI & BLK & DSA & DSW & DSO & SBA). pose proof SRC as (P0 & Pn & KEEP & IAM & PSTK & PDJ).
    pose proof lbk_meas as (KM1 & KM2 & KM3).
    destruct (dtx_of_rep LB m len DB ms pp hm 0 0 0 REP) as [HDT VT].
    assert (HRT : rtbl (XW 0 pp (epof ms) 0 0)
                    (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ds + 8)) (Z_to_bv 64 p) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7
                         s8 s9 s10 s11 t3 t4 t5 t6) RTXE).
    { unfold rtbl, RTXE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (etransitivity; [reflexivity|]); symmetry; wev. }
    assert (SPX : aceil <= spz) by (clear - N6 CEIL N2 N1; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia).
    assert (PERM' : Permutation LB (LBk ++ DB)) by (eapply Permutation_trans; [exact PERM | apply Permutation_app_comm]).
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
    { eapply (xr_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m ds p n 0 pp (epof ms) 0 0 lo
                DSO DSW STK CEIL ltac:(clear - LO; unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia) N7 N2
                (proj1 LV) VT).
      - clear - P0 N15 N13 N0 D0 D1 D2 N14. unfold epof in *. lia.
      - reflexivity.
      - apply rfull_mkR.
      - exact HRT.
      - exact HDT.
      - exact MI. }
    intros msF1 mo1 KR1 MP1 (R1 & m1 & E1 & RF1 & HRT1 & HST1 & HDT1 & [MU1 WM1] & MI1).
    change (munch W0 m m1) in MU1.
    destruct (xs_frame LB m len DB ms pp hm s W0 m1 REP RH OWN RFS STK (ex_intro _ errv ERRN) RAUX AC S0 LV (w0_ok LB) MU1 WM1)
      as (RH1 & OWN1 & RFS1 & STK1 & ERR1 & RAUX1 & AC1 & S01 & LV1 & DSA1 & DSW1 & SBA1).
    pose proof (rep_reframe LB m m1 len DB ms pp hm s 0 0 0 REP RH MU1 WM1 HDT1) as REP1.
    assert (W0MIX : forall LBr X, (forall a, ds <= a < ds + DS_SIZE -> rin_ivs X a) -> Forall (LbB_HKit.wmix LBr spz X) W0).
    { intros LBr X HX. unfold W0. repeat apply Forall_cons; try apply Forall_nil; unfold LbB_HKit.wmix; cbn [fst snd].
      - left. clear - N6 A1. unfold XSP_STACK, OVF_STACK, AOPNEW_STACK, AMALLOC_STACK in *. lia.
      - right; left. intros a Ha. apply HX. clear - Ha. unfold DS_SIZE. lia. }
    assert (XP1 : xpres H LBk spz ((ds, ds + DS_SIZE) :: sbx ms) m m1).
    { eapply (LbB_HKit.xpres_munch_mixed H HH s LB LBk DB spz _ _ m m m1 (xpres_refl _ _ _ _ _) RH PERM' SPX MU1 WM1).
      apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }
    assert (SRC1 : srcx_keep H LBk LF spz [(ds, ds + DS_SIZE)] m1 p n).
    { eapply srcx_keep_fwd0; [exact KEEP|].
      eapply (LbB_HKit.xpres_munch_mixed H HH s LB LBk DB spz _ _ m m m1 (xpres_refl _ _ _ _ _) RH PERM' SPX MU1 WM1).
      apply W0MIX. intros a Ha. cbn [rin_ivs fst snd]. left. exact Ha. }
    assert (MS0 : lb_small LB <= lb_small LBk + 64512 /\ Z.of_nat (length LB) <= Z.of_nat (length LBk) + 1 /\ nlarge LB <= nlarge LBk + 1).
    { rewrite (pc_lb_small_perm _ _ PERM), (pc_nlarge_perm _ _ PERM), (Permutation_length PERM), pc_lb_small_app, pc_nlarge_app, length_app.
      destruct CASE as [(Em & EDB & _)|(pid & d & asz & Em & EDB & INb & _ & _ & Hasz & _)]; rewrite EDB; cbn [length].
      - cbn. clear. lia.
      - rewrite lb_small_cons, nlarge_cons. cbn [lb_small nlarge fold_right blk_size snd].
        pose proof (nlg_bounds asz) as NL. unfold nsmall. destruct (Z.leb_spec asz 64512); clear - NL Hasz H0; lia. }
    destruct MS0 as (MS01 & MS02 & MS03).
    apply (xs_loop (Z.to_nat n) 0 msF1 mo1 s m1 R1 LB DB ms pp hm); [clear; lia|].
    constructor.
    - exact E1.
    - exact RF1.
    - exact HRT1.
    - exact HST1.
    - exact KR1.
    - exact MP1.
    - exact MI1.
    - exact STK1.
    - exact ERR1.
    - exact RAUX1.
    - exact RH1.
    - exact RFS1.
    - exact AC1.
    - exact S01.
    - exact LV1.
    - exact PERM.
    - rewrite Z.add_0_r. exact REP1.
    - clear; lia.
    - exact OWN1.
    - exact XP1.
    - clear; lia.
    - exact MS01.
    - exact MS02.
    - exact MS03.
    - exact SRC1.
    - clear - N0; lia.
  Qed.
End XS.

Theorem xsp_okA {HCEIL : HeapCeil} : forall H, asan_rt_hyps_bp H -> xsp_stmtA H.
Proof.
  intros H HHbp ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc msF m mo s LB LBk DB LF lo B shi errv ds err len p n ms pp hm fl fill
         PRE Ha0 Ha1 Ha2 N0 REP PERM OWN DSIN SRC LEN BS BC BL COST TRO.
  destruct PRE as (VIS & RH & KR & RAUX & SPB & BB & SP16 & STK & CEIL & LO & ERRN & MI & TP & RA2 & LV & AC & RFS & S0 & SPS).
  subst a0 a1 a2.
  exact (xs_main H HHbp ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LBk DB LF lo B shi errv ds err len p n ms pp hm fl fill
           RH RAUX SPB BB SP16 STK CEIL LO ERRN MI TP LV AC RFS S0 SPS N0 REP PERM OWN DSIN SRC LEN BS BC BL COST TRO
           t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 msF VIS KR).
Qed.
