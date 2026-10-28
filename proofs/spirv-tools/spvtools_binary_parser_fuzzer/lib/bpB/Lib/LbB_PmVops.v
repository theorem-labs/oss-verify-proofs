(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec LbB_PmVup LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Lemma po_cost_le : forall n, po_cost n <= 2 ^ 34.
Proof. exact po_cost_hi. Qed.

Lemma pm_phi_blocks_nonneg : forall bs, Forall (fun q : Z * Z => 0 <= snd q) bs -> 0 <= pm_phi_blocks bs.
Proof.
  intros bs F. unfold pm_phi_blocks.
  assert (G : 0 <= fold_right (fun (b : Z * Z) (acc : Z) => (if ICM_LARGE <? snd b then snd b else 0) + acc) 0 bs).
  { induction bs as [|q bs IH]; cbn; [lia|]. pose proof (Forall_inv F) as F1. cbn beta in F1.
    specialize (IH (Forall_inv_tail F)). destruct (ICM_LARGE <? snd q); lia. }
  lia.
Qed.

Lemma pm_phi_blocks_ge : forall bs A n, Forall (fun q : Z * Z => 0 <= snd q) bs -> In (A, n) bs -> ICM_LARGE < n ->
  8 * n <= pm_phi_blocks bs.
Proof.
  intros bs A n F Hin Hn. unfold pm_phi_blocks.
  assert (G : forall l, Forall (fun q : Z * Z => 0 <= snd q) l ->
             0 <= fold_right (fun (b : Z * Z) (acc : Z) => (if ICM_LARGE <? snd b then snd b else 0) + acc) 0 l).
  { intros l Fl. pose proof (pm_phi_blocks_nonneg l Fl) as P. unfold pm_phi_blocks in P. lia. }
  induction bs as [|q bs IH]; [destruct Hin|]. cbn.
  pose proof (Forall_inv F) as F1. cbn beta in F1. pose proof (Forall_inv_tail F) as F2.
  destruct Hin as [->|Hin].
  - cbn [snd]. destruct (Z.ltb_spec ICM_LARGE n); [| lia]. pose proof (G bs F2). lia.
  - specialize (IH F2 Hin). destruct (ICM_LARGE <? snd q); lia.
Qed.

Section Blk.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma cblk_facts : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal A n,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> In (A, n) (c_blocks c) ->
    exists pid, In (pid, A, n) LBs /\ In (pid, A, n) LB /\ In (A, n) (lbl LB) /\ ablock_range H A n /\ n <= 2 ^ 31.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal A n OK X Hin.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as RH. pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as [OWN1 OWN2].
    destruct (xb_facts H HH w s LB LBs TB m c (A, n) OK RH OWN1 OWN2 Hin) as (pid & A1 & A2 & A3 & A4). cbn [fst snd] in *.
    exists pid. split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
    assert (FN : Forall (fun q : Z * Z => 0 <= snd q) (c_blocks c)).
    { apply Forall_forall. intros [A' n'] Hq. destruct (xb_facts H HH w s LB LBs TB m c (A', n') OK RH OWN1 OWN2 Hq) as (_ & _ & _ & _ & (_ & _ & Rn & _)). exact Rn. }
    destruct (Z_lt_le_dec ICM_LARGE n) as [Hl|Hl]; [| unfold ICM_LARGE in Hl; lia].
    pose proof (pm_phi_blocks_ge (c_blocks c) A n FN Hin Hl) as G.
    pose proof (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X) as (_ & AL2 & _). unfold pm_cap in AL2.
    pose proof (po_cost_le (wa_n w)). unfold PM_RESERVE in AL2. lia.
  Qed.
End Blk.

Section Raw.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.

  Lemma pm_run_raw0 : forall (w : pmwA H) s (mo : Model) m msF R F fc (pc : Z) RT X kn fuel stops scr nx SSr scs scr'
                            RT' (Q : config -> Prop),
    mem_inv asegs m ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tblX w X R RT -> tbl_okX (xbound X) RT = true ->
    sym_exec asegs fuel true stops scr (SS pc (srs sr_id RT) [] kn nx) [] = (SSr, scs, scr') ->
    know_ok asegs (Eseed R (wenv_vals w ++ X)) m kn ->
    scs_denot asegs m (Eseed R (wenv_vals w ++ X)) scs ->
    sr_tbl_checkX (xbound X) (s_regs SSr) RT' = true ->
    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (s_pc SSr)) fc None (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) (seg_rom asegs) ->
       rfull R1 ->
       mem_inv asegs (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) ->
       regs_tblX w X R1 RT' ->
       regs_ok (Eseed R (wenv_vals w ++ X)) (s_regs SSr) R1 ->
       log_flat (Eseed R (wenv_vals w ++ X)) (s_log SSr) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s mo m msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' RT' Q
           MI KR VIS RF HT Hok Hex HK Hsc Htb K.
    pose proof (regs_ok_of_tbl w R RT X _ HT Hok) as HR.
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (srs sr_id RT) kn nx SSr scs scr'
                (Eseed R (wenv_vals w ++ X)) m (seg_rom asegs) R Hex HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    pose proof (msteps_full asegs _ _ Hms RF) as RF'. cbn [ms_regs] in RF'.
    pose proof (msteps_mem_inv asegs _ _ Hms MI) as MI'. cbn [ms_mem] in MI'.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF' mo' KR' MP' VIS'.
    rewrite <- (rfull_eq R' RF') in VIS'.
    eapply K; [exact KR' | exact MP' | exact VIS' | exact RF' | exact MI' | eapply regs_tbl_of_run; [exact HR' | exact Htb] | exact HR' | exact Hlf].
  Qed.

  Lemma pm_run_raw : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal msF R F fc (pc : Z) RT X kn fuel stops scr nx SSr scs scr'
                            RT' (Q : config -> Prop),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    as_AKREL H s (mkCfg msF mo) ->
    as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R ->
    regs_tblX w X R RT -> tbl_okX (xbound X) RT = true ->
    sym_exec asegs fuel true stops scr (SS pc (srs sr_id RT) [] kn nx) [] = (SSr, scs, scr') ->
    know_ok asegs (Eseed R (wenv_vals w ++ X)) m kn ->
    scs_denot asegs m (Eseed R (wenv_vals w ++ X)) scs ->
    sr_tbl_checkX (xbound X) (s_regs SSr) RT' = true ->
    (forall msF1 mo1 R1,
       as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS R1 F (Z_to_bv 64 (s_pc SSr)) fc None (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) (seg_rom asegs) ->
       rfull R1 ->
       mem_inv asegs (mem_denot (Eseed R (wenv_vals w ++ X)) m (s_log SSr)) ->
       regs_tblX w X R1 RT' ->
       regs_ok (Eseed R (wenv_vals w ++ X)) (s_regs SSr) R1 ->
       log_flat (Eseed R (wenv_vals w ++ X)) (s_log SSr) ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal msF R F fc pc RT X kn fuel stops scr nx SSr scs scr' RT' Q
           OK X0 KR VIS RF HT Hok Hex HK Hsc Htb K.
    pose proof (regs_ok_of_tbl w R RT X _ HT Hok) as HR.
    destruct (@SymRun3.run_sound (PropExec.mkFP F fc) asegs fuel stops scr pc (srs sr_id RT) kn nx SSr scs scr'
                (Eseed R (wenv_vals w ++ X)) m (seg_rom asegs) R Hex HR HK Hsc) as (R' & HR' & Hlf & Hms).
    rewrite !mkst_MS in Hms.
    pose proof (msteps_full asegs _ _ Hms RF) as RF'. cbn [ms_regs] in RF'.
    pose proof (msteps_mem_inv asegs _ _ Hms (xa_meminv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) as MI'. cbn [ms_mem] in MI'.
    eapply (sr_blk H HH); [exact KR | exact VIS | exact RF | exact Hms |].
    intros msF' mo' KR' MP' VIS'.
    rewrite <- (rfull_eq R' RF') in VIS'.
    eapply K; [exact KR' | exact MP' | exact VIS' | exact RF' | exact MI' | eapply regs_tbl_of_run; [exact HR' | exact Htb] | exact HR' | exact Hlf].
  Qed.

  Lemma pm_kn_fix_ok : forall w s LB LBs m mo c ins tbl ftbl TB spal E,
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal -> env_world H w E ->
    tbl_closed tbl = true -> keys_ok (map fst tbl) = true -> tbl_closed ftbl = true -> fkeys_ok (map fst ftbl) = true ->
    know_ok ASEGS E m PM_KN_FIX
    /\ (forall k e, In (k, e) tbl -> kentry_ok ASEGS E m (KWord (SA (EVar WV_S1) k) 8 e))
    /\ (forall k e, In (k, e) ftbl -> kentry_ok ASEGS E m (KWord (SA (EVar WV_FF) k) 8 e)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hc Hk Hfc Hfk.
    pose proof (pm_kn_base_ok H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal E OK X HE Hc Hk Hfc Hfk) as KB.
    unfold pm_kn_base, know_ok in KB. apply Forall_app in KB as [K1 K23]. apply Forall_app in K23 as [K2 K3].
    split; [exact K1|]. split.
    - intros k e Hin. apply (proj1 (Forall_forall _ _) K2). unfold slot_kn. apply in_map_iff. exists (k, e). split; [reflexivity | exact Hin].
    - intros k e Hin. apply (proj1 (Forall_forall _ _) K3). unfold fslot_kn. apply in_map_iff. exists (k, e). split; [reflexivity | exact Hin].
  Qed.
End Raw.

Ltac pm_goR HHH OK X KR VIS RF HT Xs kn0 HK0 fuel stops dirs nx RT' :=
  lazymatch type of X with PMXAT ?H ?LINV ?w ?s ?LB ?LBs ?m ?mo ?c ?ins ?tbl ?ftbl ?TB ?spal =>
  lazymatch type of HT with regs_tblX _ _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ _ _ =>
    let fixes := eval vm_compute in (skipn (length kn0) (kn_fix3 30 fuel ins stops (SCR dirs [] []) pc (srs sr_id RT) kn0 nx)) in
    let kn := constr:(kn0 ++ fixes) in
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_run_raw H HHH LINV w s LB LBs m mo c ins tbl ftbl TB spal _ R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr'
                RT' _ OK X KR VIS RF HT);
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | unfold know_ok; apply Forall_app; split; [exact HK0 | cbn [List.app]; pmk_list H HHH w OK X (env_world_seed H w R Xs)]
      | idtac
      | vm_compute; reflexivity
      | idtac ]
    end end end end.

Ltac pm_goR0 HHH MI KR VIS RF HT Xs kn HK fuel stops dirs nx RT' :=
  lazymatch type of HT with regs_tblX ?w _ ?R ?RT =>
  lazymatch type of VIS with _ = MS _ ?F (Z_to_bv 64 ?pc) ?fc _ ?m _ =>
  lazymatch type of KR with as_AKREL ?H ?s (mkCfg ?msF ?mo) =>
    let r := eval vm_compute in (sym_exec ASEGS fuel true stops (SCR dirs [] []) (SS pc (srs sr_id RT) [] kn nx) []) in
    lazymatch r with (?ss', ?scs, ?scr') =>
      let SSr := fresh "SSr" in pose (SSr := ss');
      eapply (pm_run_raw0 H HHH w s mo m msF R F fc pc RT Xs kn fuel stops (SCR dirs [] []) nx SSr scs scr' RT' _ MI KR VIS RF HT);
      [ vm_compute; reflexivity
      | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
      | exact HK
      | idtac
      | vm_compute; reflexivity
      | idtac ]
    end end end end.

Section Annot.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma HHa : asan_rt_hyps H. Proof. exact (rt_bp_base H HHbp). Qed.

  Lemma pm_annot : forall (w : pmwA H) s msF mo R F fc m1 (beg len oldmid newmid ret : Z) (Q : config -> Prop),
    pmw_okA H w ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 AANNOTATE_CC) fc None m1 (seg_rom asegs) -> rfull R ->
    PropExec.getr R 10%bv = Z_to_bv 64 beg -> PropExec.getr R 11%bv = Z_to_bv 64 (beg + len) ->
    PropExec.getr R 12%bv = Z_to_bv 64 (beg + oldmid) -> PropExec.getr R 13%bv = Z_to_bv 64 (beg + newmid) ->
    PropExec.getr R 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R 1%bv = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    beg mod 8 = 0 -> 0 <= len <= 2 ^ 40 -> 0 <= oldmid <= len -> 0 <= newmid <= len -> aapp beg len ->
    SHAD m1 beg (cc_gen len oldmid) -> stk asegs m1 (wa_lo w) (wa_s1 w) -> mem_inv asegs m1 -> ACONST m1 ->
    (forall msF2 mo2 m2 R2, as_AKREL H s (mkCfg msF2 mo2) -> as_MPRES H mo mo2 ->
       as_VIS H s msF2 = MS R2 F (Z_to_bv 64 ret) fc None m2 (seg_rom asegs) -> rfull R2 ->
       munch [(sh beg, sh beg + nsh len); (wa_s1 w - AINTRIN_STACK, wa_s1 w)] m1 m2 -> wmono asegs m1 m2 -> mem_inv asegs m2 ->
       stk asegs m2 (wa_lo w) (wa_s1 w) -> SHAD m2 beg (cc_gen len newmid) -> ACONST m2 ->
       (forall r, In r KEPT_REGS -> PropExec.getr R2 r = PropExec.getr R r) ->
       as_SR H Q (mkCfg msF2 mo2)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s msF mo R F fc m1 beg len oldmid newmid ret Q OK KR VIS RF G10 G11 G12 G13 G2 G1 Hret2 Hret
           Hal Hlen Hold Hnew HAPP SH STK MI AC K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (aapp_bounds _ _ HAPP ltac:(lia)) as (B1 & B2 & B3 & B4 & B5).
    rewrite (rfull_eq R RF) in VIS.
    eapply (ahh_evt_then H HHa _); [exact KR | exact VIS | |].
    { eapply (rt_bp_annot H HHbp) with (beg := beg) (len := len) (oldmid := oldmid) (newmid := newmid) (lo := wa_lo w).
      - exact G10.
      - exact G11.
      - exact G12.
      - exact G13.
      - exact Hal.
      - exact Hlen.
      - exact Hold.
      - exact Hnew.
      - exact HAPP.
      - lia.
      - exact SH.
      - rewrite G2, u64_of_Z by lia. exact STK.
      - lia.
      - rewrite G2, u64_of_Z by lia. unfold AINTRIN_STACK. lia.
      - exact MI.
      - exact AC.
      - eapply aapp_in_app_mem; [exact HAPP | lia | lia]. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (t0 & t1 & t2 & a0' & a1' & a2' & a3' & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & VIS2 & MU & WM & MI2 & STK2 & SH2 & AC2').
    rewrite G2, !u64_of_Z in MU by lia. rewrite G2, !u64_of_Z in STK2 by lia. rewrite G1, (ret_pc_even ret Hret Hret2) in VIS2.
    eapply (K msF2 mo2 m2); [exact KR2 | exact MP2 | exact VIS2 | apply rfull_mkR | exact MU | exact WM | exact MI2 | exact STK2 | exact SH2 | exact AC2' |].
    intros r Hr.
    repeat (destruct Hr as [<-|Hr]; [first [reflexivity | (cbn; rewrite G1; reflexivity) | (cbn; reflexivity)] |]); destruct Hr.
  Qed.
End Annot.

Definition ffkeep {HCEIL : HeapCeil} {H : asr} (w : pmwA H) (m m' : mem) : Prop :=
  forall k cs, 0 <= k -> k + Z.of_nat (cells_size cs) <= 16384 -> rw_cells asegs m (wa_ff w + k) cs -> rw_cells asegs m' (wa_ff w + k) cs.

Lemma ffkeep_refl {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) m, ffkeep w m m.
Proof. intros w m k cs _ _ C. exact C. Qed.
Lemma ffkeep_trans {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) m1 m2 m3, ffkeep w m1 m2 -> ffkeep w m2 m3 -> ffkeep w m1 m3.
Proof. intros w m1 m2 m3 A B k cs Hk Hn C. exact (B k cs Hk Hn (A k cs Hk Hn C)). Qed.
Lemma ffkeep_munch {HCEIL : HeapCeil} {H : asr} : forall (w : pmwA H) W m m',
  munch W m m' -> wmono asegs m m' -> Forall (fun iv : Z * Z => wa_ff w + 16384 <= fst iv \/ snd iv <= wa_ff w) W -> ffkeep w m m'.
Proof.
  intros w W m m' MU WM FW k cs Hk Hn C. eapply rw_cells_transport; [exact C | exact MU | exact WM |].
  clear - FW Hk Hn. induction W as [|[lo hi] W IH]; [exact I|]. cbn [disjoint_from].
  pose proof (Forall_inv FW) as D. cbn [fst snd] in D. split; [lia | exact (IH (Forall_inv_tail FW))].
Qed.

Section Def.
  Context {HCEIL : HeapCeil}.

  Lemma shad_defined : forall m A sbs x, SHAD m A sbs -> AIMG_TOP <= A ->
    sh A <= x < sh A + Z.of_nat (length sbs) -> m (Z_to_bv 64 x) <> None.
  Proof.
    intros m A sbs x (A0 & A8 & [(B0 & B1 & B2) _]) HA Hx.
    set (i := Z.to_nat (x - sh A)).
    assert (Hi : (i < length sbs)%nat) by (subst i; lia).
    pose proof (B2 i Hi) as Bi. subst i. rewrite Z2Nat.id in Bi by lia. replace (sh A + (x - sh A)) with x in Bi by lia.
    destruct (nth_error sbs (Z.to_nat (x - sh A))) as [bb|] eqn:En.
    2:{ exfalso. apply nth_error_None in En. lia. }
    unfold wa in Bi. apply (def_of_mrd_hi m x bb); [| exact Bi].
    assert (sh AIMG_TOP <= sh A) by (apply sh_mono; lia). replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity.
    unfold AIMG_TOP. lia.
  Qed.

  Lemma stk_defined : forall m lo hi x, stk asegs m lo hi -> AIMG_TOP <= lo -> hi <= 2 ^ 64 -> lo <= x < hi -> m (Z_to_bv 64 x) <> None.
  Proof.
    intros m lo hi x STK Hlo Hhi Hx. destruct STK as (_ & _ & SS). destruct (SS x ltac:(lia)) as [_ (bb & Hbb)].
    unfold wa in Hbb. apply (def_of_mrd_hi m x bb); [lia | exact Hbb].
  Qed.

  Lemma annot_dm : forall M1 m2 beg len sbs lo lo' hi,
    munch [(sh beg, sh beg + nsh len); (lo', hi)] M1 m2 -> SHAD m2 beg sbs -> Z.of_nat (length sbs) = nsh len ->
    stk asegs m2 lo hi -> aceil <= lo -> lo <= lo' -> hi <= 2 ^ 64 -> AIMG_TOP <= beg ->
    forall x, M1 x <> None -> m2 x <> None.
  Proof.
    intros M1 m2 beg len sbs lo lo' hi MU SH Hlen STK Hlo Hlo' Hhi Hbeg x Hx.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct (outside_dec [(sh beg, sh beg + nsh len); (lo', hi)] (bv_unsigned x)) as [Ho|(a & b & Hin & Hr)].
    - rewrite (MU x Ho). exact Hx.
    - rewrite <- (Z_to_bv_bv_unsigned x). destruct Hin as [Hin|[Hin|[]]]; injection Hin as <- <-.
      + apply (shad_defined m2 beg sbs); [exact SH | exact Hbeg | lia].
      + apply (stk_defined m2 lo hi); [exact STK | unfold AIMG_TOP in *; lia | exact Hhi | lia].
  Qed.
End Def.

Lemma edenot_and7_add3 : forall E n e, edenot E (EVar n) = Z_to_bv 64 e -> 0 <= e < 2 ^ 64 ->
  edenot E (EAlu ALU_ADD (EAlu ALU_AND (EVar n) (ELit 7)) (ELit 3)) = Z_to_bv 64 (e mod 8 + 3).
Proof.
  intros E n e He Hr. cbn [edenot]. cbn [edenot] in He. rewrite He. cbn [alu64 alu]. apply bv_eq.
  rewrite bv_add_unsigned, bv_and_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small e) by lia. change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  change (3 mod 2 ^ 64) with 3. reflexivity.
Qed.

Lemma edenot_sext_byte : forall E n j, edenot E (EVar n) = Z_to_bv 64 j -> 0 <= j < 128 ->
  edenot E (EExt true 0 1 (EVar n)) = Z_to_bv 64 j.
Proof.
  intros E n j He Hj. cbn [edenot]. cbn [edenot] in He. rewrite He. unfold ext_val, ext_Z. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * N.of_nat 1)%N with 8%N.
  rewrite Z.div_1_r. rewrite (Z.mod_small j (2 ^ 64)) by (cbn -[Z.lt Z.le]; lia). rewrite (Z.mod_small j 256) by lia.
  rewrite bv_swrap_small; [reflexivity|]. unfold bv_half_modulus. change (bv_modulus 8) with 256. change (256 / 2) with 128. lia.
Qed.

Lemma br_ge_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x <? y).
Proof.
  intros x y Hx Hy. cbn [branch_taken]. unfold bv_lts. rewrite !Z_to_bv_signed.
  assert (HM : bv_half_modulus 64 = 2 ^ 63) by reflexivity.
  rewrite !bv_swrap_small by (rewrite HM; lia). reflexivity.
Qed.

Lemma sext32_unsigned_mod : forall E n x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
  bv_unsigned (edenot E (EExt true 0 4 (EVar n))) mod 2 ^ 32 = x.
Proof.
  intros E n x He Hx. cbn [edenot]. cbn [edenot] in He. rewrite He. unfold ext_val, ext_Z. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). change (8 * N.of_nat 4)%N with 32%N.
  rewrite Z.div_1_r. rewrite (Z.mod_small x (2 ^ 64)) by lia. rewrite (Z.mod_small x (2 ^ 32)) by lia.
  rewrite (bv_swrap32_cases x) by lia. destruct (Z.ltb_spec x (2 ^ 31)).
  - rewrite (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_small. lia.
  - replace ((x - 2 ^ 32) mod 2 ^ 64) with (x - 2 ^ 32 + 2 ^ 64) by (Z.div_mod_to_equations; lia).
    replace (x - 2 ^ 32 + 2 ^ 64) with (x + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma mod64_mod32 : forall v, (v mod 2 ^ 64) mod 2 ^ 32 = v mod 2 ^ 32.
Proof. intros v. apply Z.mod_mod_divide. exists (2 ^ 32). reflexivity. Qed.

Lemma fld4_mod : forall M a v v', fld ASEGS M a 4 v -> v mod 2 ^ 32 = v' mod 2 ^ 32 -> fld ASEGS M a 4 v'.
Proof.
  intros M a v v' F E. unfold fld in *. rewrite F. f_equal. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64).
  rewrite <- (Z_to_le_bytes_mod 4 (v mod 2 ^ 64) 32) by (cbn; lia). rewrite <- (Z_to_le_bytes_mod 4 (v' mod 2 ^ 64) 32) by (cbn; lia).
  rewrite !mod64_mod32, E. reflexivity.
Qed.

Section Slots.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Lemma kslot_of_cells : forall (w : pmwA H) E m' k e, pmw_okA H w -> env_world H w E -> wclosed e = true ->
    rw_cells asegs m' (wa_s1 w + k) [C8 (edenot (Eseed bvmap_empty (wenv_vals w)) e)] ->
    0 <= k -> k + 8 <= 1216 ->
    kentry_ok asegs E m' (KWord (SA (EVar WV_S1) k) 8 e).
  Proof.
    intros w E m' k e OK HE Hc C Hk0 Hk1. pose proof (pmw_bounds H w OK) as BND.
    eapply (kword_of_rw_cells asegs E m' (wa_s1 w + k) _ 0%nat (C8 _)); [exact C | reflexivity | reflexivity | lia | | lia | cbn; lia |].
    - unfold estart. cbn [a_base a_off]. rewrite (ev_s1 H w E OK HE). lia.
    - cbn [cbytes]. unfold le8. f_equal. symmetry. apply edenot_wclosed; [exact Hc|]. intros n Hn. apply HE. unfold WV_LAST. lia.
  Qed.
End Slots.

Lemma estart_var : forall E n off v, edenot E (EVar n) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> estart E (SA (EVar n) off) = v + off.
Proof. intros E n off v He Hv. unfold estart. cbn [a_base a_off]. rewrite He, u64_of_Z by lia. reflexivity. Qed.

Lemma sc_flat_lit : forall segs m E a n x l, estart E a = x -> elenZ E n = l -> 0 <= x < 2 ^ 64 -> 0 <= l -> x + l <= 2 ^ 64 ->
  sc_denot segs m E (SCFlat a n).
Proof. intros segs m E a n x l Ha Hn H0 H1 H2. cbn [sc_denot]. unfold flat. rewrite Ha, Hn. lia. Qed.

Lemma sc_disj_lit : forall segs m E a1 n1 a2 n2 x1 l1 x2 l2,
  estart E a1 = x1 -> elenZ E n1 = l1 -> estart E a2 = x2 -> elenZ E n2 = l2 ->
  0 <= x1 < 2 ^ 64 -> 0 <= l1 -> x1 + l1 <= 2 ^ 64 -> 0 <= x2 < 2 ^ 64 -> 0 <= l2 -> x2 + l2 <= 2 ^ 64 ->
  (x1 + l1 <= x2 \/ x2 + l2 <= x1) -> sc_denot segs m E (SCDisj a1 n1 a2 n2).
Proof.
  intros segs m E a1 n1 a2 n2 x1 l1 x2 l2 Ha1 Hn1 Ha2 Hn2 A B C D F G DJ. cbn [sc_denot]. unfold flat.
  rewrite Ha1, Hn1, Ha2, Hn2. lia.
Qed.

Lemma sc_br_of : forall segs m E t c a b, branch_taken c (edenot E a) (edenot E b) = t -> sc_denot segs m E (SCBr t c a b).
Proof. intros segs m E t c a b Hb. cbn [sc_denot]. exact Hb. Qed.

Lemma mod16_mod8 : forall b, b mod 16 = 0 -> b mod 8 = 0.
Proof. intros b Hb. Z.div_mod_to_equations. lia. Qed.

Section Arith.
  Context {HCEIL : HeapCeil}.
  Lemma sh_aceil_le : sh aceil <= aceil.
  Proof. pose proof aceil_facts. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_end_le : forall A n, 0 <= A -> 0 <= n -> A + n <= aceil -> sh A + nsh n <= sh aceil.
  Proof. intros A n HA Hn HC. pose proof aceil_al8. unfold sh, nsh. Z.div_mod_to_equations. lia. Qed.
End Arith.

Lemma fld_of_cell8 : forall m a (v : word), rw_cells asegs m a [C8 v] -> 0 <= a -> fld ASEGS m a 8 (bv_unsigned v).
Proof.
  intros m a v Hc Ha. unfold fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. rewrite Z_to_bv_bv_unsigned. exact RD.
Qed.
Lemma fld_of_cell4 : forall m a (v : word), rw_cells asegs m a [C4 v] -> 0 <= a -> fld ASEGS m a 4 (bv_unsigned v).
Proof.
  intros m a v Hc Ha. unfold fld.
  pose proof (rw_cells_read asegs m a _ 0%nat _ Hc eq_refl) as RD. replace (a + Z.of_nat 0) with a in RD by lia.
  rewrite <- rdn_of_ov. rewrite Z_to_bv_bv_unsigned. exact RD.
Qed.

Lemma shaddr_bounds : forall x, 0 <= x < AAPP_HI -> 0 <= x / 8 + SHBASE /\ x / 8 + SHBASE + 8 <= 2 ^ 64.
Proof. intros x Hx. unfold AAPP_HI, SHBASE in *. Z.div_mod_to_equations. lia. Qed.
