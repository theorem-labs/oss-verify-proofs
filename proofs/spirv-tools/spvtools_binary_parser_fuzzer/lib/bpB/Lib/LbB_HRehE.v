(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HRehStmt LbB_HKit LbB_VecT LbB_HEmpS LbB_HEmpD LbB_HEmpI LbB_HEmpR LbB_HEmpNd
  LbB_HRehK LbB_HRehD LbB_HRehL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma firstn_repeat8 : forall {X : Type} (x : X) (j k : nat), (j + 8 <= k)%nat -> firstn 8 (skipn j (repeat x k)) = repeat x 8.
Proof.
  intros X x j k Hk. revert k Hk. induction j as [|j IH]; intros k Hk.
  - cbn [skipn]. destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try lia. reflexivity.
  - destruct k as [|k]; [lia|]. cbn [repeat skipn]. apply IH. lia.
Qed.

Lemma rw_cells_CB_to_C8 : forall m A bs w, rw_cells asegs m A [CB 8 bs] -> bs = le8 w -> rw_cells asegs m A [C8 w].
Proof.
  intros m A bs w [[Hwf HB] HW] E. subst bs. split; [split|].
  - cbn. split; exact I.
  - cbn [cells_bytes cbytes] in HB |- *. exact HB.
  - cbn [cells_size csize] in HW |- *. exact HW.
Qed.

Lemma zero_cell8 : forall m p (k : nat) (i : Z), rw_cells asegs m p [CB k (poison_bytes k 0)] -> 0 <= p -> 0 <= i -> 8 * i + 8 <= Z.of_nat k ->
  HRep.cellw asegs m (p + 8 * i) 8 0.
Proof.
  intros m p k i RC Hp Hi Hk.
  destruct (rw_cells_CB_split asegs m p k (Z.to_nat (8 * i)) _ RC ltac:(lia)) as [_ R2].
  rewrite Z2Nat.id in R2 by lia.
  destruct (rw_cells_CB_split asegs m (p + 8 * i) _ 8 _ R2 ltac:(lia)) as [R3 _].
  apply cellw8_of_rw_cells; [| lia | lia]. eapply rw_cells_CB_to_C8; [exact R3|].
  unfold poison_bytes. rewrite firstn_repeat8 by lia. reflexivity.
Qed.

Lemma disjoint_from_nodes : forall (l : list (Z * (Z * Z))) a k,
  (forall e, In e l -> a + k <= HRehashModel.addr Z e \/ HRehashModel.addr Z e + 8 <= a) ->
  disjoint_from (map (fun e => (HRehashModel.addr Z e, HRehashModel.addr Z e + 8)) l) a k.
Proof.
  intros l a k. induction l as [|e l IH]; intros Hd; cbn; [exact I|].
  split; [apply Hd; left; reflexivity | apply IH; intros e' He'; apply Hd; right; exact He'].
Qed.

Lemma Forall_nodes : forall (P : Z * Z -> Prop) (l : list (Z * (Z * Z))),
  (forall e, In e l -> P (HRehashModel.addr Z e, HRehashModel.addr Z e + 8)) ->
  Forall P (map (fun e => (HRehashModel.addr Z e, HRehashModel.addr Z e + 8)) l).
Proof. intros P l Hl. apply Forall_map. apply Forall_forall. intros e He. exact (Hl e He). Qed.

Section RehE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (spz : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj bl bc : Z) (ents : list (Z * (Z * Z))).
  Variables (lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variables (LBe : list block).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation ent := (Z * (Z * Z))%type.
  #[local] Notation addr := (HRehashModel.addr Z).
  #[local] Notation hkey := (HRehashModel.hkey Z).
  #[local] Notation sent := (obj + 16).

  Hypothesis U0 : umapx MI_A 24 (nval24 ASEGS) (lbl LBe) m0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOR : lo <= spz - AREH_STACK.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis SPB : spz <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis SHI : spz <= shi.

  #[local] Opaque bseq_next.
  Abbreviation QRx := (QR H ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bc ents lo B shi m0 mo0).

  Lemma stage_post : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) (errv : word) (LB' LBn : list block) (pid : bptr) (p : Z),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) y10 y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 (obj / 8 + SHBASE)) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE))
                             s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
                        F (Z_to_bv 64 R_MS) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    RFRAME ra s0 s1 s2 s3 s4 s5 spz m -> spz mod 16 = 0 -> 2 ^ 45 <= spz - 64 -> spz <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 ->
    mem_inv asegs m -> stk asegs m lo spz -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 24) -> agree_on m0 m (obj + 16) 24 ->
    cell8 ASEGS m obj p -> cell8 ASEGS m (obj + 8) n ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) (poison_bytes (Z.to_nat (8 * n)) 0)] ->
    addressable m p (8 * n) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 24) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ (pid, p, 8 * n) :: LBn) -> Permutation (lbl LBn) (map (fun e : ent => (addr e, 24)) ents) ->
    lb_own ((pid, p, 8 * n) :: LBn) m ->
    xpres H LB0 spz [(obj, obj + 40)] m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    as_SR H QRx (mkCfg msF mo).
  Proof.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 errv LB' LBn pid p
      VIS FRZ KR MP FR SP16 SPL SPH RAE MI ST ERR RA NODES HDR24 Cbl Cbc ZER ADP ADH ADN WRH RH PE PM OWN XP RF AC S0 AL.
    destruct (bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & Hncase).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold AREH_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3).
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).

    assert (INP : In (pid, p, 8 * n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH INP) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).

    assert (INN : forall e, In e ents -> exists q, In (q, addr e, 24) LBn /\ In (q, addr e, 24) LB').
    { intros e He. destruct (lbl_in_inv LBn (addr e) 24 (Permutation_in _ (Permutation_sym PM) (in_map (fun e0 : ent => (addr e0, 24)) _ _ He))) as (q & Hq).
      exists q. split; [exact Hq|]. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. right. exact Hq. }
    pose proof (ah_nodup H HH _ _ _ RH) as NDB.
    assert (HPN : forall e, In e ents -> apart p (8 * n) (addr e) 24).
    { intros e He. destruct (INN e He) as (q & HqN & HqL).
      assert (Hne : pid <> q).
      { intros <-.
        assert (ND1 : List.NoDup (map blk_id (LB0 ++ (pid, p, 8 * n) :: LBn))) by (eapply Permutation_NoDup; [apply Permutation_map; exact PE | exact NDB]).
        rewrite map_app in ND1. apply NoDup_app_remove_l in ND1. cbn [map blk_id Datatypes.fst] in ND1.
        inversion ND1 as [|z l Hni Hnd]; subst. apply Hni. apply (in_map blk_id) in HqN. exact HqN. }
      pose proof (ah_disj H HH _ _ _ _ _ RH INP HqL Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D.
      unfold apart. clear - D. lia. }
    assert (NAPP : forall e, In e ents -> aapp (addr e) 24).
    { intros e He. destruct (INN e He) as (q & _ & HqL). pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & _ & _ & _ & BA). exact BA. }
    assert (WRP : wr_at asegs m p (8 * n)) by exact (lb_own_In _ m _ OWN (or_introl eq_refl)).
    assert (WRN : forall e, In e ents -> wr_at asegs m (addr e) 24).
    { intros e He. destruct (INN e He) as (q & HqN & _). exact (lb_own_In _ m _ OWN (or_intror HqN)). }

    destruct (u_hdr U0) as [_ _ Cp10 Csz0 Cmlf0 _].
    assert (Cp1 : cell8 ASEGS m sent (hdaddr ents)) by (eapply cellw_agree; [exact Cp10 | eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | lia | cbn; lia]).
    assert (CH : chain ASEGS m ents).
    { apply lnk_chain. eapply lnk_agree; [apply lnk_chain; exact (u_chain U0) | |].
      - intros a Ha. eapply agree_on_sub; [exact (NODES a Ha) | lia | cbn; lia].
      - intros a Ha. destruct (ent_facts _ _ _ _ _ _ a U0 Ha) as (Ha0 & Ha1 & _). lia. }
    assert (HASH : forall e, In e ents -> cell8 ASEGS m (addr e + 8) (hkey e)).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & C8k & _).
      eapply cellw_agree; [exact C8k | eapply agree_on_sub; [exact (NODES e He) | lia | cbn; lia] | lia | cbn; lia]. }
    assert (BK0 : forall i, 0 <= i < n -> cell8 ASEGS m (p + 8 * i) 0).
    { intros i Hi. apply (zero_cell8 m p _ i ZER); lia. }

    remember (mkR y1 (Z_to_bv 64 (spz - 64)) gp tp y5 y6 y7 (Z_to_bv 64 n) (Z_to_bv 64 obj) y10 y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 (obj + 8)) (Z_to_bv 64 SHBASE) (Z_to_bv 64 (obj / 8 + SHBASE)) (Z_to_bv 64 ((obj + 8) / 8 + SHBASE))
                  s6 s7 s8 s9 s10 s11 y28 y29 y30 y31) as R eqn:HR0.
    assert (RG : REGF gp tp s6 s7 s8 s9 s10 s11 spz obj bc R) by (unfold REGF; subst R; repeat split; reflexivity).
    destruct (loop_all gp tp s6 s7 s8 s9 s10 s11 spz F fc obj bl bc p ents (lbl LBe) m0 m U0 Hlast
                (conj Hp0 (conj Hp16 (conj HpI (conj HpC HpA)))) HPN HPO OCE OAPP NAPP (conj SPL SPH)
                R RG Cp1 CH HASH Cbl BK0 ADP ADH ADN MI WRP WRH WRN) as (R' & M' & Hms & RGX & FINAL).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.

    assert (MUW : munch (WL obj bc p ents) m M' /\ wmono asegs m M' /\ mem_inv asegs M'
                  /\ addressable M' p (8 * n) /\ addressable M' obj 40 /\ (forall e, In e ents -> addressable M' (addr e) 24) /\ wr_at asegs M' obj 40).
    { destruct FINAL as [[HE ->] | (P' & Bf' & LS)].
      - split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact ADP|]. split; [exact ADH|]. split; [exact ADN | exact WRH].
      - destruct LS as [_ _ _ _ _ _ _ Ladp Ladh Ladn Lmu Lwm Lmi _ Lwrh _].
        split; [exact Lmu|]. split; [exact Lwm|]. split; [exact Lmi|]. split; [exact Ladp|]. split; [exact Ladh|]. split; [exact Ladn | exact Lwrh]. }
    destruct MUW as (MU & WM & MI' & ADP' & ADH' & ADN' & WRH').

    assert (WOK : Forall (aclient_write_ok H LB') (WL obj bc p ents) /\ Forall (afs_write_ok H LF) (WL obj bc p ents)
                  /\ Forall aconst_ok (WL obj bc p ents) /\ Forall stack0_ok (WL obj bc p ents)
                  /\ Forall (wmix ((pid, p, 8 * n) :: LBn) spz [(obj, obj + 40)]) (WL obj bc p ents)).
    { destruct (blk_win H HH LF s LB' m pid p (8 * n) p (p + 8 * n) RH INP ltac:(lia) ltac:(lia)) as (P1 & P2 & P3 & P4 & P5).
      destruct (obj_window_ok H HH LF obj LB' m (obj + 16) (obj + 24) RF LFO ltac:(lia) ltac:(lia)) as (Q1 & Q2 & Q3 & Q4).
      assert (NW : forall e, In e ents -> aclient_write_ok H LB' (addr e, addr e + 8) /\ afs_write_ok H LF (addr e, addr e + 8)
                     /\ aconst_ok (addr e, addr e + 8) /\ stack0_ok (addr e, addr e + 8) /\ wmix ((pid, p, 8 * n) :: LBn) spz [(obj, obj + 40)] (addr e, addr e + 8)).
      { intros e He. destruct (INN e He) as (q & HqN & HqL).
        destruct (blk_win H HH LF s LB' m q (addr e) 24 (addr e) (addr e + 8) RH HqL ltac:(lia) ltac:(lia)) as (N1 & N2 & N3 & N4 & N5).
        split; [exact N1|]. split; [exact N2|]. split; [exact N3|]. split; [exact N4|].
        right; right. exists q, (addr e), 24. split; [right; exact HqN | cbn; lia]. }
      unfold WL.
      split; [apply Forall_cons; [exact P1 | apply Forall_cons; [exact Q1 | apply Forall_nodes; intros e He; exact (proj1 (NW e He))]]|].
      split; [apply Forall_cons; [exact P2 | apply Forall_cons; [exact Q2 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (NW e He)))]]|].
      split; [apply Forall_cons; [exact P3 | apply Forall_cons; [exact Q3 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (proj2 (NW e He))))]]|].
      split; [apply Forall_cons; [exact P4 | apply Forall_cons; [exact Q4 | apply Forall_nodes; intros e He; exact (proj1 (proj2 (proj2 (proj2 (NW e He)))))]]|].
      apply Forall_cons; [right; right; exists pid, p, (8 * n); split; [left; reflexivity | cbn; lia]|].
      apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs Datatypes.fst Datatypes.snd] in *; left; lia|].
      apply Forall_nodes. intros e He. exact (proj2 (proj2 (proj2 (proj2 (NW e He))))). }
    destruct WOK as (W1 & W2 & W3 & W4 & W5).
    destruct (client_frame H HH s LB' LF B _ m M' RH RF AC RA MU WM W1 W2 W3) as (RH' & RF' & AC' & RA').
    assert (S0' : stack0 M' lo shi) by (eapply stack0_transport; [exact S0 | exact MU | exact WM | exact W4]).
    assert (XP' : xpres H LB0 spz [(obj, obj + 40)] m0 M').
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: LBn) spz [(obj, obj + 40)] _ m0 m M');
        [exact XP | exact RH | exact PE | lia | exact MU | exact WM | exact W5]. }
    assert (OWN' : lb_own ((pid, p, 8 * n) :: LBn) M') by exact (lb_own_wmono _ _ _ OWN WM).

    assert (DJ : forall a k, 0 <= k -> (a + k <= p \/ p + 8 * n <= a) -> (a + k <= obj + 16 \/ obj + 24 <= a) ->
                 (forall e, In e ents -> a + k <= addr e \/ addr e + 8 <= a) -> disjoint_from (WL obj bc p ents) a k).
    { intros a k Hk D1 D2 D3. unfold WL. cbn [disjoint_from app]. split; [exact D1|]. split; [exact D2|]. apply disjoint_from_nodes. exact D3. }
    assert (NODEWIN : forall e, In e ents -> forall e', In e' ents -> addr e + 8 + 16 <= addr e' \/ addr e' + 8 <= addr e + 8).
    { intros e He e' He'. destruct (Z.eq_dec (addr e') (addr e)) as [Eq | Ne]; [lia|].
      pose proof (nodes_apart _ _ _ _ _ _ e' e U0 He' He Ne) as Hap. unfold apart in Hap. lia. }
    assert (FR' : RFRAME ra s0 s1 s2 s3 s4 s5 spz M').
    { unfold RFRAME in FR |- *. eapply rw_cells_transport; [exact FR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat].
      apply DJ; [lia | clear - HpC ACL LOR'; lia | clear - OCE ACL LOR'; lia |].
      intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _). destruct (INN e He) as (q & _ & HqL).
      pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & _ & QC & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC.
      clear - QC ACL LOR'. lia. }
    assert (ST' : stk asegs M' lo spz).
    { destruct FINAL as [[HE HM] | (P' & Bf' & LS)]; [rewrite HM; exact ST|].
      eapply LbB_TopKit.stk_wmono; [exact ST | exact WM |]. clear - ACL ACF1. lia. }
    assert (ERR' : rw_cells asegs M' (errno_addr tp) [C4 errv]).
    { assert (EA : errno_addr tp = 7100340) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
      rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU | exact WM |]. cbn [cells_size csize Z.of_nat].
      apply DJ; [lia | unfold AIMG_TOP in HpI; clear - HpI; lia | unfold AIMG_TOP in OB3; clear - OB3; lia |].
      intros e He. destruct (INN e He) as (q & _ & HqL). pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & QI & _).
      cbn [blk_addr Datatypes.fst Datatypes.snd] in QI. unfold AIMG_TOP in QI. clear - QI. lia. }

    assert (NODES' : forall e, In e ents -> agree_on m0 M' (addr e + 8) 16).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      eapply agree_on_trans; [eapply agree_on_sub; [exact (NODES e He) | lia | lia] |].
      eapply agree_of_munch; [exact MU | | lia | lia]. intros z Hz.
      pose proof (HPN e He) as Hpe. unfold apart in Hpe, Heo.
      apply (disjoint_outside _ (addr e + 8) 16 z); [|lia]. apply DJ; [lia | clear - Hpe; lia | clear - Heo; lia | exact (NODEWIN e He)]. }

    assert (HAG : forall a k, 0 <= k -> obj <= a -> a + k <= obj + 16 \/ (obj + 24 <= a /\ a + k <= obj + 40) -> agree_on m M' a k).
    { intros a k Hk Ha Hak. eapply agree_of_munch; [exact MU | | lia | lia]. intros z Hz. apply (disjoint_outside _ a k z); [|lia].
      apply DJ; [lia | clear - HPO Ha Hak Hk; unfold apart in HPO; lia | clear - Ha Hak Hk; lia |].
      intros e He. destruct (u_node U0 (addr e) (hkey e) (snd (snd e)) ltac:(destruct e as [q [k' v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      clear - Heo Ha Hak Hk. unfold apart in Heo. lia. }
    assert (Cbl' : cell8 ASEGS M' obj p) by (eapply cellw_agree; [exact Cbl | apply HAG; lia | lia | cbn; lia]).
    assert (Cbc' : cell8 ASEGS M' (obj + 8) n) by (eapply cellw_agree; [exact Cbc | apply HAG; lia | lia | cbn; lia]).
    assert (Csz' : cell8 ASEGS M' (obj + 24) (Zlength ents)).
    { eapply cellw_agree; [exact Csz0 | | lia | cbn; lia]. eapply agree_on_trans; [eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | apply HAG; cbn; lia]. }
    assert (Cmlf' : cell4 ASEGS M' (obj + 32) 0x3f800000).
    { eapply cellw_agree; [exact Cmlf0 | | lia | cbn; lia]. eapply agree_on_trans; [eapply agree_on_sub; [exact HDR24 | lia | cbn; lia] | apply HAG; cbn; lia]. }
    assert (DEFH' : HRep.defined M' obj 40).
    { destruct (rw_cells_of_wr_hi M' obj 40 WRH' ltac:(unfold AIMG_TOP in *; lia) ltac:(lia)) as (hbs & HBS).
      pose proof (defined_of_rw_cells_hi M' obj _ HBS ltac:(unfold AIMG_TOP in *; lia)) as D. cbn [cells_size csize] in D. exact D. }

    assert (HU : exists ents', Permutation ents' ents /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB') M' obj p n ents').
    { assert (NODEF : forall q k v (ents' : list ent), Permutation ents' ents -> In (q, (k, v)) ents' ->
                 cell8 ASEGS M' (q + 8) k ->
                 In (q, 24) (lbl LB') /\ 0 < q /\ q + 24 <= 2 ^ 47 /\ q mod 16 = 0
                 /\ cell8 ASEGS M' (q + 8) k /\ cell4 ASEGS M' (q + 16) k /\ 0 <= k < 2 ^ 32 /\ nval24 ASEGS M' q v
                 /\ apart q 24 obj 40 /\ (n <> 0 -> apart q 24 p (8 * n))).
      { intros q k v ents' PERM Hin C8k. assert (Hine : In (q, (k, v)) ents) by (eapply Permutation_in; [exact PERM | exact Hin]).
        destruct (u_node U0 q k v Hine) as (_ & Hq0 & Hq1 & Hqal & _ & C4 & Hk & Hnv & Hap & _).
        pose proof (NODES' _ Hine) as TL. unfold HRehashModel.addr in TL. cbn [fst snd] in TL.
        split; [destruct (INN _ Hine) as (qi & _ & HqL); exact (lbl_in _ _ _ _ HqL)|].
        split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqal|]. split; [exact C8k|].
        split; [eapply cellw_agree; [exact C4 | eapply agree_on_sub; [exact TL | lia | cbn; lia] | lia | cbn; lia]|].
        split; [exact Hk|].
        split; [eapply nval24_agree; [exact Hnv | eapply agree_on_sub; [exact TL | lia | lia] | lia | lia]|].
        split; [exact Hap|].
        intros _. pose proof (HPN _ Hine) as X. unfold HRehashModel.addr in X. cbn [fst snd] in X. unfold apart in X |- *. clear - X. lia. }
      destruct FINAL as [[HE HM] | (P' & Bf' & LS)].
      - exists (@nil ent). rewrite HE in *. split; [apply Permutation_refl|].
        constructor; try (intros; exfalso; assumption).
        + constructor; [exact Cbl' | exact Cbc' | rewrite HM; exact Cp1 | exact Csz' | exact Cmlf' | exact DEFH'].
        + exact Hoal. + exact Ho0. + exact Ho1. + exact HnB.
        + unfold Zlength. cbn [length Z.of_nat]. lia.
        + right. split; [lia | exact (lbl_in _ _ _ _ INP)].
        + exact Hp16. + intros _; exact Hp0. + lia. + intros _. exact HPO.
        + intros i Hi. exists 0. split; [rewrite HM; exact (BK0 i Hi) | left; reflexivity].
        + constructor.
        + exact I.
      - exists P'. destruct LS as [PERM BI HP Cp1' CH' HASH' BK _ _ _ _ _ _ _ _ _].
        rewrite app_nil_r in PERM, Cp1', CH'.
        assert (Hnoty : forall P1 y z P2, P' = P1 ++ y :: z :: P2 -> addr y <> sent).
        { intros P1 y z P2 HP' Heq. assert (Hin : In y ents) by (eapply Permutation_in; [exact PERM | rewrite HP'; apply in_app_iff; right; left; reflexivity]).
          destruct y as [q [k v]]. destruct (u_node U0 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn in Heq. lia. }
        split; [exact PERM|].
        constructor.
        + constructor; [exact Cbl' | exact Cbc' | exact Cp1' | | exact Cmlf' | exact DEFH'].
          unfold Zlength. rewrite (Permutation_length PERM). exact Csz'.
        + exact Hoal. + exact Ho0. + exact Ho1. + exact HnB.
        + unfold Zlength. rewrite (Permutation_length PERM). pose proof (u_load U0) as HL. unfold Zlength in HL. lia.
        + right. split; [lia | exact (lbl_in _ _ _ _ INP)].
        + exact Hp16. + intros _; exact Hp0. + lia. + intros _. exact HPO.
        + intros i Hi. exists (Bf' i). split; [exact (BK i Hi)|].
          destruct (binv_weak Z n sent P' Bf' i BI Hi Hnoty) as [Hb | [Hb | [Hb (x & P'' & HP' & Hx)]]]; [left; exact Hb | right; left; exact Hb | right; right].
          split; [exact Hb|]. split; [rewrite HP'; discriminate|]. rewrite HP'. destruct x as [q [k v]]. cbn. symmetry. exact Hx.
        + apply (proj2 (base.NoDup_ListNoDup _)). exact (perm_nodup _ _ _ _ _ _ _ U0 PERM).
        + exact CH'.
        + intros q k v Hin. apply (NODEF q k v P' PERM Hin). exact (HASH' (q, (k, v)) ltac:(eapply Permutation_in; [exact PERM | exact Hin])).
        + intros q q' Hq Hq' Hne. apply (u_napart U0); [| | exact Hne].
          * apply in_map_iff in Hq. destruct Hq as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He].
          * apply in_map_iff in Hq'. destruct Hq' as (e & <- & He). apply in_map. eapply Permutation_in; [exact PERM | exact He]. }
    destruct HU as (ents' & PERM' & U').
    assert (SH' : umap_sh M' 24 (p, n, ents')).
    { unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c. cbn [Datatypes.fst Datatypes.snd]. split; [intros _; exact ADP'|].
      intros q k v Hin. exact (ADN' (q, (k, v)) ltac:(eapply Permutation_in; [exact PERM' | exact Hin])). }
    assert (PM' : Permutation (lbl ((pid, p, 8 * n) :: LBn)) (umap_blocks 24 p n ents')).
    { unfold umap_blocks. destruct (Z.eqb_spec n 0); [lia|]. cbn [lbl map app blk_addr blk_size Datatypes.fst Datatypes.snd].
      apply perm_skip. eapply Permutation_trans; [exact PM|].
      change (fun e : Z * (Z * Z) => (Datatypes.fst e, 24)) with (fun e : ent => (addr e, 24)).
      apply Permutation_map. apply Permutation_sym. exact PERM'. }

    destruct RGX as (Q2 & Q3 & Q4 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    pose proof (msteps_full asegs _ _ Hms FHF) as HF1. cbn [ms_regs] in HF1.
    rewrite (rfull_eq R' HF1) in VIS1.
    rewrite Q2, Q3, Q4, Q22, Q23, Q24, Q25, Q26, Q27 in VIS1.
    eapply (stage_repi H HH ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 spz sk0 LB0 LF obj bc ents lo B shi m0 mo0
              s msF1 mo1 M' F fc);
      [ unfold spr; exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1]
      | exact FR' | exact SP16 | unfold spr; exact SPL | exact SPH | exact RAE | exact MI' | exact ST' | exact ERR' | exact RA'
      | exact U' | exact SH' | exact PERM' | exact ADH' | exact WRH'
      | exact RH' | exact PE | exact PM' | exact OWN' | exact XP' | exact RF' | exact AC' | exact S0' | exact AL ].
  Qed.
End RehE.
