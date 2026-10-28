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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BArr BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td LbB_TdKit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp LbB_PmSL.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_WoGen LbB_SnXD LbB_SnXK LbB_SnXT LbB_SnXO1.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_SnXC1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma xlb_small_perm : forall L L', Permutation L L' -> lb_small L = lb_small L'.
Proof. intros L L' P. induction P; cbn [lb_small fold_right] in *; unfold lb_small in *; cbn [fold_right]; lia. Qed.
Lemma xnlarge_perm : forall L L', Permutation L L' -> nlarge L = nlarge L'.
Proof. intros L L' P. induction P; unfold nlarge in *; cbn [fold_right]; lia. Qed.
Lemma xlb_small_app : forall L L', lb_small (L ++ L') = lb_small L + lb_small L'.
Proof. intros L L'. induction L as [|b L IH]; [reflexivity|]. cbn [app]. rewrite !lb_small_cons, IH. lia. Qed.
Lemma xnlarge_app : forall L L', nlarge (L ++ L') = nlarge L + nlarge L'.
Proof. intros L L'. induction L as [|b L IH]; [reflexivity|]. cbn [app]. rewrite !nlarge_cons, IH. lia. Qed.
Lemma xtb_meas : forall (TB : list block), (length TB <= 1)%nat -> lb_small TB <= 64512 /\ 0 <= nlarge TB <= 1.
Proof.
  intros [|b [|b' TB]] HL; cbn [length] in HL; [cbn; lia | | lia].
  rewrite lb_small_cons, nlarge_cons. cbn [lb_small nlarge fold_right].
  pose proof (nlg_bounds (blk_size b)). unfold nsmall. destruct (Z.leb_spec (blk_size b) 64512); lia.
Qed.
Lemma xxfer_kept : forall LB TB LBk LB' TB', Permutation LB (TB ++ LBk) -> ds_xfer LB TB LB' TB' -> Permutation LB' (TB' ++ LBk).
Proof.
  intros LB TB LBk LB' TB' P1 (LR & X1 & X2).
  assert (PR : Permutation LR LBk).
  { apply (Permutation_app_inv_l TB). eapply Permutation_trans; [apply Permutation_sym; exact X1 | exact P1]. }
  eapply Permutation_trans; [exact X2|]. apply Permutation_app_head. exact PR.
Qed.

Section ExS.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation kst_ex := LbB_SnXT.kst_ex (only parsing).
  Local Notation shT := LbB_SnXT.shT (only parsing).
  Local Notation kT := LbB_SnXT.kT (only parsing).
  Local Notation wok := LbB_SnXT.wok (only parsing).
  Local Notation wok_facts := LbB_SnXT.wok_facts (only parsing).
  Local Notation wk_win := LbB_SnXT.wk_win (only parsing).
  Local Notation fin_wider := LbB_SnXT.fin_wider (only parsing).
  Local Notation rtbl_sw := LbB_SnXT.rtbl_sw (only parsing).
  Local Notation ftbl_sw := LbB_SnXT.ftbl_sw (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 4 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Local Notation ftbl_xpres := (@LbB_SnXT.ftbl_xpres HCEIL H) (only parsing).
  Local Notation Wx := (@LbB_SnXT.Wx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Px := (@LbB_SnXT.Px HCEIL H e ff fp) (only parsing).
  Local Notation ex_ranges := (@LbB_SnXT.ex_ranges HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_vals := (@LbB_SnXT.ex_vals HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_wins := (@LbB_SnXT.ex_wins HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xobj_range := (@LbB_SnXT.xobj_range HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation ex_keepT := (@LbB_SnXT.ex_keepT HCEIL H HHbp e ff fp HP FF THI PCI) (only parsing).
  Local Notation ex_keep := (@LbB_SnXT.ex_keep HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation evWx := (@LbB_SnXT.evWx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation kst_ex_ok := (@LbB_SnXT.kst_ex_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation evT := (@LbB_SnXT.evT HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_start := (@LbB_SnXT.shT_start HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_apart := (@LbB_SnXT.shT_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation shb_eq0 := (@LbB_SnXT.shb_eq0 ff) (only parsing).
  Local Notation this_apart := (@LbB_SnXT.this_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation kT_ok := (@LbB_SnXT.kT_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
  Local Notation scT_flat := (@LbB_SnXT.scT_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation scP_flat := (@LbB_SnXT.scP_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tS := (@LbB_SnXT.tS H e) (only parsing).
  Local Notation tFw := (@LbB_SnXT.tFw ff) (only parsing).
  Local Notation tHw := (@LbB_SnXT.tHw ff) (only parsing).
  Local Notation tF := (@LbB_SnXT.tF ff) (only parsing).
  Local Notation tH := (@LbB_SnXT.tH ff) (only parsing).
  Local Notation tab_vals := (@LbB_SnXT.tab_vals HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3w := (@LbB_SnXT.tabs_wf3w HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3 := (@LbB_SnXT.tabs_wf3 HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation wk_stk := (@LbB_SnXT.wk_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation shb_eq := (@LbB_SnXT.shb_eq ff) (only parsing).
  Local Notation tabs_ok3w := (@LbB_SnXT.tabs_ok3w HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_ok3 := (@LbB_SnXT.tabs_ok3 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation Px_step3w := (@LbB_SnXT.Px_step3w HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Px_step3 := (@LbB_SnXT.Px_step3 HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Wx_sw1 := (@LbB_SnXT.Wx_sw1 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Wx_sw := (@LbB_SnXT.Wx_sw HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation ex_shvis := (@LbB_SnXC1.ex_shvis HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation fr_app := (@LbB_SnXC1.fr_app HCEIL H e ff fp HP FF) (only parsing).
  Local Notation fr_addr := (@LbB_SnXC1.fr_addr HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation xwin_stk := (@LbB_SnXC1.xwin_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xwin_fr := (@LbB_SnXC1.xwin_fr H e ff) (only parsing).
  Local Notation Px_win := (@LbB_SnXC1.Px_win HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation obj_apart := (@LbB_SnXC1.obj_apart HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation blk_apart := (@LbB_SnXC1.blk_apart HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xds_run := (@LbB_SnXC1.xds_run HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xcut := (@LbB_SnXC1.xcut HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Notation SP := (xSP e) (only parsing).
  Notation this := (x_this e) (only parsing).
  Notation pcons := (x_pcons e) (only parsing).

  Ltac evwx := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, Wx;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Ltac tnormp H :=
    lazymatch type of H with
    | ftbl ?W ?B ?m ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    | rtbl ?W ?R ?t =>
        let l := eval vm_compute in t in
        let E := fresh "E" in assert (E : t = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in H; clear E
    end.

  Ltac exrun3w hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR [] [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3wd dirs hF hH HRT HSF HFT HHT HPX HMI fuel stops kx :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HPX with Px ?XSc ?sk ?LBk _ =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HFT with ftbl _ _ _ ?FT =>
      lazymatch type of HHT with ftbl _ _ _ ?HT =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS SF []; tFw hF FT []; tHw hH HT []]) in
        let kf := eval vm_compute in (kfix stops pc (HLib.srs sr_id RT) ((kst_ex ++ kx) ++ fknT L0)) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR dirs [] []) (SS pc (HLib.srs sr_id RT) [] (((kst_ex ++ kx) ++ kf) ++ fknT L0) 70) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound Wx) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 58) (s_log SSr) SF) in
          let ks2 := eval vm_compute in (nkeys (EVar 52) (s_log SSr) FT) in
          let ks3 := eval vm_compute in (nkeys PD_SHB (s_log SSr) HT) in
          eapply (dk_runN Wx [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]
                    (tabs_wf3w hF hH SF FT HT ks1 ks2 ks3 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                       ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    (Px XSc sk LBk) (fun m0 m0' => Px_step3w hF hH XSc sk LBk SF FT HT ks1 ks2 ks3 m0 m0' eq_refl)
                    Q R F pc fc m ro RT [] ((kst_ex ++ kx) ++ kf) fuel stops (SCR dirs [] []) 70%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply (tabs_ok3w hF hH XSc sk LBk); [vm_compute; reflexivity | exact HPX | exact HSF | exact HFT | exact HHT | vm_compute; reflexivity .. ]
          | exact HPX | exact HMI
          | unfold know_ok; apply Forall_app; split; [apply Forall_app; split; [apply (kst_ex_ok _ _ XSc sk LBk); exact HPX | ] | ]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end end end end
    end.

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 1016 128 HRT HSF HFT HHT HPX HMI fuel stops kx.

  Ltac tsplit HTS H1 H2 H3 :=
    lazymatch type of HTS with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_cast_no_check (@eq_refl _ l)); rewrite E in HTS; clear E end;
    apply Forall_cons_iff in HTS as [H1 HTS]; apply Forall_cons_iff in HTS as [H2 HTS]; apply Forall_cons_iff in HTS as [H3 _];
    cbn [fst snd] in H1, H2, H3.

  Ltac rgetx HRT r H :=
    lazymatch type of HRT with rtbl _ ?R ?RT =>
      let e0 := eval vm_compute in (match find (fun p : reg * expr => bv_eqb (fst p) r) RT with Some p => snd p | None => ELit 0 end) in
      assert (H : PropExec.getr R r = edenot (wenv Wx) e0)
        by (apply (rtbl_In Wx R RT r e0 HRT); apply LbB_DCtorK.inb_In'; vm_compute; reflexivity);
      unfold wenv in H; cbn [edenot] in H; unfold HLib.Eseed, reg_ev, Wx in H;
      lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
            Init.Nat.add Nat.sub nth app] in H;
      rewrite ?w_mul, ?w_add, ?w_addm, ?v_addi_Z in H by (pose proof ex_vals; pose proof ex_wins; lia)
    end.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Local Notation ds := (ff + SX_DS_OFF) (only parsing).
  Local Notation LFx := ((4, ff, fp) :: x_LF e) (only parsing).
  Local Notation CHx := ((xSP e, bv_unsigned (x_ra e)) :: x_CH e) (only parsing).

  Lemma xchain_call : forall XSc sk LBk m', Px XSc sk LBk m' ->
    as_chain H m' (xSP e) CHx /\ (forall f r, In (f, r) CHx -> xS1 e + 16 <= f).
  Proof.
    intros XSc sk LBk m' HI.
    pose proof (xchain H HH e ff fp XSc sk LBk m' HP HI) as CH0.
    pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SV & _).
    pose proof (xpre_geo H e HP) as (CE & LO & SH1 & SH2 & SP16 & _).
    pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & _ & _).
    pose proof aceil_facts as ACF.
    destruct (xpre_all H e HP) as (_ & _ & _ & _ & _ & _ & (_ & _ & CHU)).
    change (xsaved e) with ([C8 (x_s8 e); C8 (x_s7 e); C8 (x_s6 e); C8 (x_s5 e); C8 (x_s4 e); C8 (x_s3 e);
                             C8 (x_s2 e); C8 (x_s1 e)] ++ [C8 (x_s0 e); C8 (x_ra e)]) in SV.
    apply rw_cells_app in SV as [_ SV2]. cbn [cells_size csize] in SV2. unfold SX_SAVED in SV2.
    replace (xSP e - 80 + Z.of_nat (8 + (8 + (8 + (8 + (8 + (8 + (8 + (8 + 0)))))))))
      with (xSP e - 16) in SV2 by lia.
    pose proof (bv_unsigned_in_range 64 (x_s0 e)) as R0. pose proof (bv_unsigned_in_range 64 (x_ra e)) as R1.
    change (bv_modulus 64) with (2 ^ 64) in R0, R1.
    split.
    - eapply (ah_chain_cons H HH); [exact CH0 | lia | lia | exact SP16 | unfold AAPP_HI, ASX_STACK, ADS_STACK in *; lia | unfold AAPP_HI in *; lia |].
      rewrite !Z_to_bv_bv_unsigned. exact SV2.
    - intros f r [EQ|IN]; [injection EQ as <- <-; lia|]. pose proof (CHU f r IN). lia.
  Qed.

  Definition xsess (LBc : list block) (len : Z) (DB : list block) (m : mem) : Prop :=
    ds_repA0 LBc m ds (-4) len DB /\ Permutation LBc (DB ++ x_LB e) /\ lb_own DB m.

  Lemma xsess_facts : forall LBc len DB m, xsess LBc len DB m ->
    (length DB <= 1)%nat /\ 0 <= len
    /\ lb_small LBc + 2 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LBc) + 2 <= RT_CNT_MAX /\ nlarge LBc + 2 <= RT_LARGE_MAX
    /\ (forall b, In b (x_LB e) -> In b LBc).
  Proof.
    intros LBc len DB m (REP & PM & OWN).
    pose proof (proj1 (dla_blocks _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP)) as DL.
    pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) as (_ & _ & _ & _ & L0).
    destruct HP as (_ & _ & B1 & B2 & B3 & _).
    destruct (xtb_meas DB DL) as [T1 T2].
    rewrite (xlb_small_perm _ _ PM), (xnlarge_perm _ _ PM), (Permutation_length PM), xlb_small_app, xnlarge_app, length_app.
    split; [exact DL|]. split; [exact L0|]. split; [lia|]. split; [lia|]. split; [lia|].
    intros b Hb. apply (Permutation_in _ (Permutation_sym PM)). apply in_or_app. right. exact Hb.
  Qed.

  Lemma x_ds_pre : forall entry cost DB XSc s LBc m msF mo R F fc,
    Px XSc s LBc m -> Permutation LBc (DB ++ x_LB e) -> (length DB <= 1)%nat -> lb_own DB m ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 entry) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
    PropExec.getr R 2 = Z_to_bv 64 (xS1 e) -> PropExec.getr R 8 = Z_to_bv 64 (xSP e) -> PropExec.getr R 4 = x_tp e ->
    bv_unsigned (PropExec.getr R 1) mod 2 = 0 -> cost <= as_AL H s ->
    exists errv,
    ds_pre H LINV_P5 entry (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 5) (PropExec.getr R 6)
           (PropExec.getr R 7) (PropExec.getr R 8) (PropExec.getr R 9) (PropExec.getr R 10) (PropExec.getr R 11) (PropExec.getr R 12)
           (PropExec.getr R 13) (PropExec.getr R 14) (PropExec.getr R 15) (PropExec.getr R 16) (PropExec.getr R 17) (PropExec.getr R 18)
           (PropExec.getr R 19) (PropExec.getr R 20) (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23) (PropExec.getr R 24)
           (PropExec.getr R 25) (PropExec.getr R 26) (PropExec.getr R 27) (PropExec.getr R 28) (PropExec.getr R 29) (PropExec.getr R 30)
           (PropExec.getr R 31) F fc msF m mo s LBc DB LFx CHx cost (x_lo e) (x_B e) (x_shi e) errv.
  Proof.
    intros entry cost DB XSc s LBc m msF mo R F fc HI PM DL OWN KR VIS RF FZ G2 G8 G4 Hra Hc.
    pose proof HI as (RFS & _ & RH & AC & MI & S0 & RA & (errv & ER) & ST & _).
    pose proof (xpre_geo H e HP) as (CE & LO & SH1 & SH2 & SP16 & TP).
    pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof aceil_facts as ACF.
    destruct (xchain_call XSc s LBc m HI) as [CHN CHU].
    pose proof HP as (_ & _ & B1 & B2 & B3 & _ & SPB & B64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LFL & _ & _ & _ & _ & _ & TR & _).
    destruct (xtb_meas DB DL) as [T1 T2].
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    assert (Us0 : bv_unsigned (PropExec.getr R 8) = xSP e) by (rewrite G8; apply unsigned_lit; lia).
    exists errv. unfold ds_pre. rewrite Us1, Us0. rewrite (rfull_eq R RF) in VIS.
    refine (conj VIS (conj FZ (conj RH (conj KR (conj OWN _))))).
    rewrite (xlb_small_perm _ _ PM), (xnlarge_perm _ _ PM), (Permutation_length PM), xlb_small_app, xnlarge_app, length_app.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact RA|]. split; [lia|]. split; [exact B64|].
    split; [clear - S32; Z.div_mod_to_equations; lia|].
    split; [exact (proj1 (stk_split asegs m (x_lo e) (xS1 e) (xSP e) ST ltac:(lia)))|].
    split; [exact CE|]. split; [unfold ASX_STACK, ASN_STACK, ADS_STACK in *; lia|].
    split; [rewrite G4; exact ER|]. split; [exact MI|]. split; [rewrite G4; exact TP|].
    split; [exact Hra|]. split; [exact (xlinv H HH e ff fp XSc s LBc m HP HI)|].
    split; [exact AC|]. split; [exact RFS|].
    split; [cbn [length]; unfold SX_FRAMES, SN_FRAMES, DS_FRAMES in *; lia|].
    split; [exact S0|]. split; [lia|].
    split; [exact CHN|].
    split; [unfold pf_ok, DS_PF; apply Forall_nil|].
    split; [intros fp' ra' Hin; pose proof (CHU fp' ra' Hin); lia|].
    split; [exact TR | exact Hc].
  Qed.

  Lemma sf_xpres : forall LBx X0 XS m m' SF, as_RFS H LFx m' ->
    ftbl Wx (xS1 e) m SF -> fin 0 16 (fkeys SF) = true ->
    xpres H LBx (xS1 e) (X0 ++ XS) m m' -> Forall (fs_scratch H LFx) XS ->
    Forall (fun iv : Z * Z => snd iv <= xS1 e) X0 ->
    ftbl Wx (xS1 e) m' SF.
  Proof.
    intros LBx X0 XS m m' SF RF2 HSF Hf XP FXS FX0.
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & _ & _ & _ & LOS1 & _).
    eapply (ftbl_xpres LBx (xS1 e) (X0 ++ XS)); [exact HSF | exact XP |].
    intros k w Hi. destruct (fin_In _ _ _ k w Hf Hi) as (K1 & K2 & K3).
    split; [left; lia|]. apply Forall_app. split.
    - eapply Forall_impl; [| exact FX0]. intros iv K. cbn beta in K |- *. right. lia.
    - eapply Forall_impl; [| exact FXS]. intros iv FSi.
      destruct (xfsw_ok H HH e ff fp m' iv RF2 FF CE FSi) as (_ & _ & _ & _ & _ & _ & B7 & _). right. lia.
  Qed.

  Lemma x_ds_back : forall (G : Prop) (X0 : list (Z * Z)) XSc s LBc m mo R F fc RT SF (ret cost : Z) res (Qc : list block -> mem -> Prop) (c' : config),
    Px XSc s LBc m -> rfull R -> rtbl Wx R RT -> ftbl Wx (xS1 e) m SF -> fin 0 16 (fkeys SF) = true ->
    PropExec.getr R 1 = Z_to_bv 64 ret -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    PropExec.getr R 2 = Z_to_bv 64 (xS1 e) -> PropExec.getr R 4 = x_tp e ->
    Forall (fun iv : Z * Z => (ff + 8 <= fst iv /\ snd iv <= ff + SX_FLAGP) \/ iv = (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)) X0 ->
    (forall LB' m', Qc LB' m' -> Forall (fun iv : Z * Z => ff <= fst iv -> wr_at asegs m' (fst iv) (snd iv - fst iv)) X0) ->
    ds_post H LINV_P5 (PropExec.getr R 1) (PropExec.getr R 2) (PropExec.getr R 3) (PropExec.getr R 4) (PropExec.getr R 8) (PropExec.getr R 9)
            (PropExec.getr R 18) (PropExec.getr R 19) (PropExec.getr R 20) (PropExec.getr R 21) (PropExec.getr R 22) (PropExec.getr R 23)
            (PropExec.getr R 24) (PropExec.getr R 25) (PropExec.getr R 26) (PropExec.getr R 27)
            F fc s LBc (x_LB e) LFx X0 cost (x_lo e) (x_B e) (x_shi e) m mo res Qc c' ->
    (forall s' LB' m' R' F' fc' XS,
       as_AKREL H s' c' -> as_MPRES H mo (cfg_model c') ->
       as_VIS H s' (cfg_ms c') = MS R' F' (Z_to_bv 64 ret) fc' None m' (seg_rom asegs) -> rfull R' -> frm_zero fc' ->
       rtbl Wx R' (keptk RT) -> (forall d, res = Some d -> PropExec.getr R' 10 = Z_to_bv 64 d) ->
       ftbl Wx (xS1 e) m' SF -> Px (XSc ++ XS) s' LB' m' -> Qc LB' m' ->
       as_AL H s' >= as_AL H s - cost -> G) ->
    G.
  Proof.
    intros G X0 XSc s LBc m mo R F fc RT SF ret cost res Qc c' HI RF HRT HSF Hf G1 Hr2 Hr G2 G4 FX0 WX0 POST K.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & errv1 & s1 & LB1
                      & XS & F1 & fc1 & VIS1 & FZ1 & RES & KR1 & MP1 & MI1 & STK1 & ERR1 & RA1 & RH1 & QC1 & FXS & XP
                      & RFS1 & AC1 & S01 & LI1 & AL1).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof ex_wins as (W2 & W3 & W5 & W8 & W9 & W10 & W11 & W12).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    rewrite G1, (ret_pc_even ret Hr Hr2) in VIS1. rewrite Us1 in STK1, XP. rewrite G4 in ERR1.
    assert (FX0s : Forall (fun iv : Z * Z => snd iv <= xS1 e) X0).
    { eapply Forall_impl; [| exact FX0]. intros iv [[K1 K2]| ->]; cbn [fst snd]; unfold SX_FLAGP, RtB_Td.ATDLOC in *; lia. }
    eapply (K s1 LB1 m1 _ F1 fc1 XS KR1 MP1 VIS1 (rfull_mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) FZ1).
    - eapply rtbl_keep; [exact (rtbl_keptk Wx R RT HRT) | apply rsub_keptk |].
      intros r Hr0. cbn [In KEPT] in Hr0. rewrite <- G1.
      repeat (destruct Hr0 as [<-|Hr0]; [reflexivity|]). destruct Hr0.
    - intros d Hd. exact (RES d Hd).
    - exact (sf_xpres (x_LB e) X0 XS m m1 SF RFS1 HSF Hf XP FXS FX0s).
    - eapply (xinv_sr_gen H HH e ff fp XSc XS (X0 ++ XS) s LBc (x_LB e) s1 LB1 m m1 HP HI (fun b Hb => Hb) XP FXS).
      + apply Forall_app. split.
        * eapply Forall_impl; [| exact FX0]. intros iv [KK| ->]; [right; left; exact KK | right; right; right; right; reflexivity].
        * apply Forall_forall. intros iv Hiv. left. exact Hiv.
      + exact RFS1.
      + exact RH1.
      + exact AC1.
      + exact MI1.
      + exact STK1.
      + exists errv1. exact ERR1.
      + exact RA1.
      + apply Forall_app. split.
        * pose proof (WX0 LB1 m1 QC1) as WW. rewrite Forall_forall in WW |- *. intros iv Hiv Hc.
          pose proof (proj1 (Forall_forall _ _) FX0 iv Hiv) as KK.
          apply (WW iv Hiv). destruct KK as [[K1 K2]| ->]; [lia|]. exfalso. cbn [fst snd] in Hc.
          unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *. clear - Hc W11 R4' R8'. lia.
        * eapply Forall_impl; [| exact FXS]. intros iv FSi Hiv. cbn [fst snd] in Hiv |- *.
          destruct (xfsw_ok H HH e ff fp m1 iv RFS1 FF CE FSi) as (_ & _ & _ & B4 & B5 & _ & B7 & _).
          pose proof ex_vals as (V1 & _).
          unfold SX_FLAGP, ASX_STACK, ADS_STACK in *. clear - Hiv B4 B5 B7 W11 W12 LOS1 S1SP V1 R1' R2'.
          split; [lia|]. split; [lia|]. intros i Hi. exfalso. lia.
      + exact LI1.
    - exact QC1.
    - exact AL1.
  Qed.

  Definition xsr (pc : Z) (RT : list (reg * expr)) (SF : list fent) (len spent : Z) (c : config) : Prop :=
    exists (s : as_St H) F fc XSc LBc DB,
      as_AKREL H s c /\ as_MPRES H (x_mo e) (cfg_model c) /\ frm_zero fc
      /\ xcut pc F fc RT SF XSc s LBc (xsess LBc len DB) (as_VIS H s (cfg_ms c))
      /\ as_AL H s >= as_AL H (x_s e) - spent.

  Definition xsr0 (pc : Z) (RT : list (reg * expr)) (SF : list fent) (c : config) : Prop :=
    exists (s : as_St H) F fc XSc,
      as_AKREL H s c /\ as_MPRES H (x_mo e) (cfg_model c) /\ frm_zero fc
      /\ xcut pc F fc RT SF XSc s (x_LB e) (fun m => addressable m ds DS_SIZE) (as_VIS H s (cfg_ms c))
      /\ as_AL H s >= as_AL H (x_s e).

  Definition rcall (RT : list (reg * expr)) (ret : Z) (a0 a1 a2 : word) : Prop :=
    forall R, rtbl Wx R RT ->
      PropExec.getr R 1 = Z_to_bv 64 ret /\ PropExec.getr R 2 = Z_to_bv 64 (xS1 e) /\ PropExec.getr R 8 = Z_to_bv 64 (xSP e)
      /\ PropExec.getr R 4 = x_tp e /\ PropExec.getr R 10 = a0 /\ PropExec.getr R 11 = a1 /\ PropExec.getr R 12 = a2.

  Lemma x_ds_obj : forall XSc s LBc m, Px XSc s LBc m -> addressable m ds DS_SIZE ->
    ds_obj H LFx m (xS1 e) ds DS_SIZE /\ obj_inframe LFx ds DS_SIZE.
  Proof.
    intros XSc s LBc m HI DA.
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    destruct (fr_app 32 392 ltac:(lia) ltac:(lia) ltac:(lia)) as [DSO DSH].
    assert (OI : obj_inframe LFx ds DS_SIZE).
    { exists (4, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 4) with 1024.
      unfold SX_DS_OFF, DS_SIZE. lia. }
    split; [| exact OI]. unfold ds_obj, SX_DS_OFF, DS_SIZE in *.
    split; [exact DA|]. split; [clear - R6'; Z.div_mod_to_equations; lia|].
    split; [right; exact OI|]. split; [unfold AIMG_TOP, AFS_HDR in *; lia|]. split; [unfold AAPP_HI in *; lia|].
    split; [left; unfold ADS_STACK; lia | exact DSO].
  Qed.

  Lemma ds_cost_le : forall l, 0 <= l <= 1024 -> 0 <= ds_cost l <= 32768.
  Proof. intros l Hl. unfold ds_cost. lia. Qed.

  Lemma x_inobj : forall m O n O' j, obj_inframe (x_LF e) O n -> ds_obj H (x_LF e) (x_m e) (xSP e) O n ->
    addressable m O' j -> O <= O' -> 0 <= j -> O' + j <= O + n -> O' mod 8 = 0 ->
    ds_obj H LFx m (xS1 e) O' j.
  Proof using HHbp HP FF.
    intros m O n O' j (f & INf & L1 & U1) (_ & _ & _ & P0 & PU & _ & (A1 & A2 & A3)) AD Ho Hj Hon Hal.
    destruct (xpre_all H e HP) as (_ & (_ & _ & CE & LO) & _ & _ & (RF & _) & _).
    destruct (ah_RFS_range H (rt_bp_base H HHbp) _ _ RF) as ((F1 & F2 & F3 & F4) & AR).
    pose proof (AR f INf) as (K1 & K2 & K3 & K4 & K5).
    pose proof (xS1_facts H e HP) as (_ & S1SP & _).
    unfold ds_obj. split; [exact AD|]. split; [exact Hal|].
    split; [right; exists f; split; [right; exact INf | lia]|].
    split; [lia|]. split; [lia|].
    split; [left; unfold ASX_STACK, ASN_STACK in LO; lia|].
    unfold app_obj. lia.
  Qed.

  Lemma x_pdiag : pdiag0_stmtA H LINV_P5 ds_repA0 ->
    forall (Q : config -> Prop) RT SF (ret : Z) c,
    xsr0 APDIAG RT SF c -> fin 0 16 (fkeys SF) = true ->
    rcall RT ret (Z_to_bv 64 ds) (Z_to_bv 64 this) (Z_to_bv 64 ((-4) mod 2 ^ 64)) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    (forall c', xsr ret (keptk RT) SF 0 0 c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof using HHbp HP FF THI PCI.
    intros HPD Q RT SF ret [msF mo] (s & F & fc & XSc & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & DA).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10 & G11 & G12).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                      & ALe & _ & OBt & _ & _ & ICR & OBp & _ & PC16 & _).
    pose proof HI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WF & _).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    destruct (ex_keepT XSc s (x_LB e) m HI) as (ADt & RWpc & RWic & ADp & RWp32).
    pose proof ex_vals as (_ & _ & T0 & T1 & T8 & _).
    destruct (x_ds_obj XSc s (x_LB e) m HI DA) as [OBd IFd].
    destruct (addressable_split8 m this 288 8 ADt eq_refl eq_refl ltac:(lia)) as [_ AD8].
    destruct (addressable_split8 m (this + 8) (288 - 8) 8 AD8 eq_refl eq_refl ltac:(lia)) as [AD8' _].
    destruct (addressable_split8 m this 288 80 ADt eq_refl eq_refl ltac:(lia)) as [_ AD80].
    destruct (addressable_split8 m (this + 80) (288 - 80) 8 AD80 eq_refl eq_refl ltac:(lia)) as [AD80' _].
    destruct (x_ds_pre APDIAG 0 [] XSc s (x_LB e) m msF mo R F fc HI (Permutation_refl _) ltac:(cbn [length]; lia)
                (lb_own_nil m) KR VIS RF FZ G2 G8 G4
                ltac:(rewrite G1, unsigned_lit by lia; exact Hr2) ltac:(unfold SX_COST, SN_COST in *; lia)) as (errv & DP).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    eapply (ah_seq H (rt_bp_base H HHbp)).
    { eapply (HPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s (x_LB e) LFx
                CHx (x_lo e) (x_B e) (x_shi e) errv ds this pcons (x_icount e) (-4)).
      - exact DP.
      - exact G10.
      - exact G11.
      - exact G12.
      - reflexivity.
      - rewrite Us1. exact (x_inobj m this 288 (this + 8) 8 THI OBt AD8' ltac:(lia) ltac:(lia) ltac:(lia)
                              ltac:(clear - T8; Z.div_mod_to_equations; lia)).
      - exact (proj1 RWpc).
      - rewrite Us1. exact (x_inobj m this 288 (this + 80) 8 THI OBt AD80' ltac:(lia) ltac:(lia) ltac:(lia)
                              ltac:(clear - T8; Z.div_mod_to_equations; lia)).
      - exact (proj1 RWic).
      - exact ICR.
      - exact PC16.
      - rewrite Us1. exact OBd.
      - eapply wr_at_sub; [exact WF | | |]; unfold SX_DS_OFF, DS_SIZE, SX_FLAGP; lia.
      - exact IFd.
      - rewrite Us1. exact (x_inobj m pcons 48 pcons 48 PCI OBp ADp ltac:(lia) ltac:(lia) ltac:(lia)
                              ltac:(clear - PC16; Z.div_mod_to_equations; lia)).
      - exact RWp32.
      - intros a Ha Hb. pose proof PCI as (f & INf & P1 & P2). pose proof FF as (_ & _ & FD).
        destruct (FD f INf) as [FDa _]. change (fsz 4) with 1024 in FDa. unfold SX_DS_OFF, DS_SIZE in Ha. lia. }
    intros c' POST.
    eapply (x_ds_back (as_SR H Q c') [(ds, ds + DS_SIZE)] XSc s (x_LB e) m mo R F fc RT SF ret 0 None
              (fun LB' m' => Permutation LB' (x_LB e) /\ ds_repA0 LB' m' ds (-4) 0 [] /\ wr_at asegs m' ds DS_SIZE) c' HI RF HRT HSF Hf G1
              Hr2 Hr G2 G4); [ | | exact POST |].
    - apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold SX_DS_OFF, DS_SIZE, SX_FLAGP. lia.
    - intros LB' m' (_ & _ & WR'). apply Forall_cons; [| apply Forall_nil]. intros _. cbn [fst snd].
      replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'.
    - intros s' LB' m' R' F' fc' XS KR' MP' VIS' RF' FZ' HRT' _ HSF' HI' (PL' & REP' & _) AL'.
      apply K. exists s', F', fc', (XSc ++ XS), LB', [].
      split; [exact KR'|]. split; [exact (ah_mpres_trans H (rt_bp_base H HHbp) _ _ _ MP MP')|]. split; [exact FZ'|].
      split; [| lia].
      exists R', m'. split; [exact VIS'|]. split; [exact RF'|]. split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HI'|].
      split; [destruct HI' as (_ & _ & _ & _ & MI' & _); exact MI'|].
      exact (conj REP' (conj PL' (lb_own_nil m'))).
  Qed.

  Lemma x_cseq : put_cseq_stmtA H LINV_P5 ds_repA0 ->
    forall (Q : config -> Prop) RT SF len spent (ret p n : Z) c,
    xsr APUT_CSEQ RT SF len spent c -> fin 0 16 (fkeys SF) = true ->
    rcall RT ret (Z_to_bv 64 ds) (Z_to_bv 64 p) (Z_to_bv 64 n) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= n -> AIMG_LO + 64 <= p -> p + n + 64 <= AIMG_TOP ->
    (forall m', ACONST m' -> accessible m' p n) ->
    (exists bs, length bs = Z.to_nat n /\ forall m', mem_inv asegs m' -> bytes_at asegs m' p bs) ->
    len + n <= 1024 -> spent + 32768 <= SX_COST ->
    (forall c', xsr ret (keptk RT) SF (len + n) (spent + 32768) c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HCSEQ Q RT SF len spent ret p n [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr Hn Hp0 Hp ACC BYT Hlen Hsp K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (REP & PM & OWN)).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10 & G11 & G12).
    destruct (xsess_facts LBc len DB m (conj REP (conj PM OWN))) as (DL & L0 & M1 & M2 & M3 & INC).
    pose proof (ds_cost_le (len + n) ltac:(lia)) as DC.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ALe & _).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof aceil_facts as ((ACe1 & ACe2) & ACe3 & ACe4).
    pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) as (DA & _).
    destruct (x_ds_obj XSc s LBc m HI DA) as [OBd IFd].
    destruct (x_ds_pre APUT_CSEQ (ds_cost (len + n)) DB XSc s LBc m msF mo R F fc HI PM DL OWN KR VIS RF FZ G2 G8 G4
                ltac:(rewrite G1, unsigned_lit by lia; exact Hr2) ltac:(unfold SX_COST, SN_COST in *; lia)) as (errv & DP).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    eapply (ah_seq H HH).
    { eapply (HCSEQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LBc (x_LB e) LFx
                ((xSP e, bv_unsigned (x_ra e)) :: x_CH e) (x_lo e) (x_B e) (x_shi e) errv ds (-4) len p n DB).
      - exact DP.
      - exact G10.
      - exact G11.
      - exact G12.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd.
      - exact Hn.
      - left. unfold AIMG_LO in *. lia.
      -
        destruct BYT as (bs & LEN & BYT'). exists bs. split; [exact LEN|]. intros m' XS. intros.
        lazymatch goal with ACm : ACONST m', MIm : mem_inv asegs m' |- _ =>
          split; [exact (BYT' m' MIm)|]; split; [exact (ACC m' ACm)|]; eapply ACONST_shvis; [exact ACm | lia | lia | lia] end.
      - unfold in_app_mem, ASHADOW_BASE, AIMG_TOP, AIMG_LO in *. left. lia.
      - rewrite Us1. left. unfold ADS_STACK, AIMG_TOP in *. lia.
      - intros a Ha. split.
        + unfold SX_DS_OFF, AIMG_TOP, AFS_HDR in *. lia.
        + intros (b & Hb & Hr0). assert (HbL : In b LBc) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
          destruct HI as (_ & _ & RH & _).
          pose proof (ah_blocks H HH _ _ _ _ RH HbL) as (_ & _ & _ & BT & _). unfold AIMG_TOP in *. lia.
      - unfold DS_MAXLEN. lia.
      - exact M1.
      - exact M3. }
    intros c' POST.
    eapply (x_ds_back (as_SR H Q c') [(ds, ds + DS_SIZE)] XSc s LBc m mo R F fc RT SF ret (ds_cost (len + n)) (Some ds)
              (ds_op_Q ds_repA0 LBc DB ds (-4) (len + n)) c' HI RF HRT HSF Hf G1 Hr2 Hr G2 G4); [ | | exact POST |].
    - apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold SX_DS_OFF, DS_SIZE, SX_FLAGP. lia.
    - intros LB' m' (B' & _ & _ & _ & WR'). apply Forall_cons; [| apply Forall_nil]. intros _. cbn [fst snd].
      replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'.
    - intros s' LB' m' R' F' fc' XS KR' MP' VIS' RF' FZ' HRT' _ HSF' HI' (DB' & XF & REP' & OWN' & _) AL'.
      apply K. exists s', F', fc', (XSc ++ XS), LB', DB'.
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ'|].
      split; [| lia].
      exists R', m'. split; [exact VIS'|]. split; [exact RF'|]. split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HI'|].
      split; [destruct HI' as (_ & _ & _ & _ & MI' & _); exact MI'|].
      split; [exact REP'|]. split; [exact (xxfer_kept _ _ _ _ _ PM XF) | exact OWN'].
  Qed.

  Definition rcall1 (RT : list (reg * expr)) (ret : Z) (a0 a1 : word) : Prop :=
    forall R, rtbl Wx R RT ->
      PropExec.getr R 1 = Z_to_bv 64 ret /\ PropExec.getr R 2 = Z_to_bv 64 (xS1 e) /\ PropExec.getr R 8 = Z_to_bv 64 (xSP e)
      /\ PropExec.getr R 4 = x_tp e /\ PropExec.getr R 10 = a0 /\ PropExec.getr R 11 = a1.
  Definition rcall0 (RT : list (reg * expr)) (ret : Z) (a0 : word) : Prop :=
    forall R, rtbl Wx R RT ->
      PropExec.getr R 1 = Z_to_bv 64 ret /\ PropExec.getr R 2 = Z_to_bv 64 (xS1 e) /\ PropExec.getr R 8 = Z_to_bv 64 (xSP e)
      /\ PropExec.getr R 4 = x_tp e /\ PropExec.getr R 10 = a0.

  Lemma x_u64 : put_u64_stmtA H LINV_P5 ds_repA0 ->
    forall (Q : config -> Prop) RT SF len spent (ret x : Z) c,
    xsr APUT_U64 RT SF len spent c -> fin 0 16 (fkeys SF) = true ->
    rcall1 RT ret (Z_to_bv 64 ds) (Z_to_bv 64 x) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= x < 2 ^ 64 ->
    len + 24 <= 1024 -> spent + 32768 <= SX_COST ->
    (forall c', xsr ret (keptk RT) SF (len + 24) (spent + 32768) c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HU64 Q RT SF len spent ret x [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr Hx Hlen Hsp K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (REP & PM & OWN)).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10 & G11).
    destruct (xsess_facts LBc len DB m (conj REP (conj PM OWN))) as (DL & L0 & M1 & M2 & M3 & INC).
    pose proof (ds_cost_le (len + 24) ltac:(lia)) as DC.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ALe & _).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) as (DA & _).
    destruct (x_ds_obj XSc s LBc m HI DA) as [OBd IFd].
    destruct (x_ds_pre APUT_U64 (ds_cost (len + 24)) DB XSc s LBc m msF mo R F fc HI PM DL OWN KR VIS RF FZ G2 G8 G4
                ltac:(rewrite G1, unsigned_lit by lia; exact Hr2) ltac:(unfold SX_COST, SN_COST in *; lia)) as (errv & DP).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    eapply (ah_seq H HH).
    { eapply (HU64 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LBc (x_LB e) LFx
                ((xSP e, bv_unsigned (x_ra e)) :: x_CH e) (x_lo e) (x_B e) (x_shi e) errv ds (-4) len x DB).
      - exact DP.
      - exact G10.
      - exact G11.
      - exact Hx.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd.
      - unfold DS_MAXLEN. lia.
      - exact M1.
      - exact M3. }
    intros c' POST.
    eapply (x_ds_back (as_SR H Q c') [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XSc s LBc m mo R F fc RT SF ret (ds_cost (len + 24)) (Some ds)
              (ds_op_Q ds_repA0 LBc DB ds (-4) (len + 24)) c' HI RF HRT HSF Hf G1 Hr2 Hr G2 G4); [ | | exact POST |].
    - apply Forall_cons; [| apply Forall_cons; [right; reflexivity | apply Forall_nil]]. left. cbn [fst snd]. unfold SX_DS_OFF, DS_SIZE, SX_FLAGP. lia.
    - intros LB' m' (B' & _ & _ & _ & WR'). apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; intros Hc; cbn [fst snd] in *.
      + replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'.
      + exfalso. unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *. lia.
    - intros s' LB' m' R' F' fc' XS KR' MP' VIS' RF' FZ' HRT' _ HSF' HI' (DB' & XF & REP' & OWN' & _) AL'.
      apply K. exists s', F', fc', (XSc ++ XS), LB', DB'.
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ'|].
      split; [| lia].
      exists R', m'. split; [exact VIS'|]. split; [exact RF'|]. split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HI'|].
      split; [destruct HI' as (_ & _ & _ & _ & MI' & _); exact MI'|].
      split; [exact REP'|]. split; [exact (xxfer_kept _ _ _ _ _ PM XF) | exact OWN'].
  Qed.

  Lemma x_u32 : put_u32_stmtA H LINV_P5 ds_repA0 ->
    forall (Q : config -> Prop) RT SF len spent (ret x : Z) c,
    xsr APUT_U32 RT SF len spent c -> fin 0 16 (fkeys SF) = true ->
    rcall1 RT ret (Z_to_bv 64 ds) (Z_to_bv 64 (sx32 x)) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 ->
    0 <= x < 2 ^ 32 ->
    len + 24 <= 1024 -> spent + 32768 <= SX_COST ->
    (forall c', xsr ret (keptk RT) SF (len + 24) (spent + 32768) c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HU32 Q RT SF len spent ret x [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr Hx Hlen Hsp K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (REP & PM & OWN)).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10 & G11).
    destruct (xsess_facts LBc len DB m (conj REP (conj PM OWN))) as (DL & L0 & M1 & M2 & M3 & INC).
    pose proof (ds_cost_le (len + 24) ltac:(lia)) as DC.
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ALe & _).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) as (DA & _).
    destruct (x_ds_obj XSc s LBc m HI DA) as [OBd IFd].
    destruct (x_ds_pre APUT_U32 (ds_cost (len + 24)) DB XSc s LBc m msF mo R F fc HI PM DL OWN KR VIS RF FZ G2 G8 G4
                ltac:(rewrite G1, unsigned_lit by lia; exact Hr2) ltac:(unfold SX_COST, SN_COST in *; lia)) as (errv & DP).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    eapply (ah_seq H HH).
    { eapply (HU32 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LBc (x_LB e) LFx
                ((xSP e, bv_unsigned (x_ra e)) :: x_CH e) (x_lo e) (x_B e) (x_shi e) errv ds (-4) len x DB).
      - exact DP.
      - exact G10.
      - exact G11.
      - exact Hx.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd.
      - unfold DS_MAXLEN. lia.
      - exact M1.
      - exact M3. }
    intros c' POST.
    eapply (x_ds_back (as_SR H Q c') [(ds, ds + DS_SIZE); (RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8)] XSc s LBc m mo R F fc RT SF ret (ds_cost (len + 24)) (Some ds)
              (ds_op_Q ds_repA0 LBc DB ds (-4) (len + 24)) c' HI RF HRT HSF Hf G1 Hr2 Hr G2 G4); [ | | exact POST |].
    - apply Forall_cons; [| apply Forall_cons; [right; reflexivity | apply Forall_nil]]. left. cbn [fst snd]. unfold SX_DS_OFF, DS_SIZE, SX_FLAGP. lia.
    - intros LB' m' (B' & _ & _ & _ & WR'). apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]; intros Hc; cbn [fst snd] in *.
      + replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'.
      + exfalso. unfold RtB_Td.ATDLOC, AIMG_TOP, AFS_HDR in *. lia.
    - intros s' LB' m' R' F' fc' XS KR' MP' VIS' RF' FZ' HRT' _ HSF' HI' (DB' & XF & REP' & OWN' & _) AL'.
      apply K. exists s', F', fc', (XSc ++ XS), LB', DB'.
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ'|].
      split; [| lia].
      exists R', m'. split; [exact VIS'|]. split; [exact RF'|]. split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HI'|].
      split; [destruct HI' as (_ & _ & _ & _ & MI' & _); exact MI'|].
      split; [exact REP'|]. split; [exact (xxfer_kept _ _ _ _ _ PM XF) | exact OWN'].
  Qed.

  Definition xsr3 (pc : Z) (RT : list (reg * expr)) (SF : list fent) (spent : Z) (c : config) : Prop :=
    exists (s : as_St H) F fc XSc LBc,
      as_AKREL H s c /\ as_MPRES H (x_mo e) (cfg_model c) /\ frm_zero fc
      /\ xcut pc F fc RT SF XSc s LBc (fun m => Permutation LBc (x_LB e) /\ addressable m ds DS_SIZE) (as_VIS H s (cfg_ms c))
      /\ as_AL H s >= as_AL H (x_s e) - spent.

  Lemma x_dtor : ds_dtor_stmtA H LINV_P5 ds_repA0 ->
    forall (Q : config -> Prop) RT SF len spent c,
    xsr ADS_DTOR RT SF len spent c -> fin 0 16 (fkeys SF) = true ->
    rcall0 RT SN_DTOR_RA1 (Z_to_bv 64 ds) -> spent <= SX_COST ->
    (forall c', xsr3 SN_DTOR_RA1 (keptk RT) SF spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros HDTOR Q RT SF len spent [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hsp K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (REP & PM & OWN)).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10).
    destruct (xsess_facts LBc len DB m (conj REP (conj PM OWN))) as (DL & L0 & M1 & M2 & M3 & INC).
    pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PFE & _ & _ & ALe & _).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof (dla_def _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) as (DA & _).
    destruct (x_ds_obj XSc s LBc m HI DA) as [OBd IFd].
    destruct (x_ds_pre ADS_DTOR 0 DB XSc s LBc m msF mo R F fc HI PM DL OWN KR VIS RF FZ G2 G8 G4
                ltac:(rewrite G1, unsigned_lit by (unfold SN_DTOR_RA1; lia); reflexivity) ltac:(unfold SX_COST, SN_COST in *; lia)) as (errv & DP).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    eapply (ah_seq H HH).
    { eapply (HDTOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc msF m mo s LBc (x_LB e) LFx
                ((xSP e, bv_unsigned (x_ra e)) :: x_CH e) (x_lo e) (x_B e) (x_shi e) errv ds (-4) len DB).
      - exact DP.
      - rewrite G1, unsigned_lit by (unfold SN_DTOR_RA1; lia). eapply pf_ok_call; [exact PFE |].
        intros pp Hpp. cbn in Hpp. destruct Hpp as [<-|[]]. unfold SN_PF, SN_DTOR_RA1, SN_DTOR_RA2. cbn [In]. clear. tauto.
      - exact G10.
      - exact REP.
      - exact PM.
      - rewrite Us1. exact OBd.
      - exact IFd. }
    intros c' POST.
    eapply (x_ds_back (as_SR H Q c') [(ds, ds + DS_SIZE)] XSc s LBc m mo R F fc RT SF SN_DTOR_RA1 0 None
              (fun LB' m' => Permutation LB' (x_LB e) /\ addressable m' ds DS_SIZE /\ wr_at asegs m' ds DS_SIZE) c' HI RF HRT HSF Hf G1
              eq_refl ltac:(unfold SN_DTOR_RA1; lia) G2 G4); [ | | exact POST |].
    - apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. unfold SX_DS_OFF, DS_SIZE, SX_FLAGP. lia.
    - intros LB' m' (_ & _ & WR'). apply Forall_cons; [| apply Forall_nil]. intros _. cbn [fst snd].
      replace (ds + DS_SIZE - ds) with DS_SIZE by lia. exact WR'.
    - intros s' LB' m' R' F' fc' XS KR' MP' VIS' RF' FZ' HRT' _ HSF' HI' (PL' & DA' & _) AL'.
      apply K. exists s', F', fc', (XSc ++ XS), LB'.
      split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ'|].
      split; [| lia].
      exists R', m'. split; [exact VIS'|]. split; [exact RF'|]. split; [exact HRT'|]. split; [exact HSF'|]. split; [exact HI'|].
      split; [destruct HI' as (_ & _ & _ & _ & MI' & _); exact MI'|].
      split; [exact PL' | exact DA'].
  Qed.

  Lemma x_run : forall (Q : config -> Prop) pc RT SF len spent pc' RT' SF' c,
    xsr pc RT SF len spent c ->
    (forall R F fc m XSc s LBc DB, rfull R -> rtbl Wx R RT -> ftbl Wx (xS1 e) m SF -> Px XSc s LBc m -> mem_inv asegs m ->
       xsess LBc len DB m ->
       evt asegs (xcut pc' F fc RT' SF' XSc s LBc (xsess LBc len DB)) (MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs))) ->
    (forall c', xsr pc' RT' SF' len spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros Q pc RT SF len spent pc' RT' SF' [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) RUN K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & SS).
    eapply (ahh_evt_then H HH (xcut pc' F fc RT' SF' XSc s LBc (xsess LBc len DB))); [exact KR | exact VIS | exact (RUN R F fc m XSc s LBc DB RF HRT HSF HI MI SS) |].
    intros msF' mo' KR' MP' P'. apply K. exists s, F, fc, XSc, LBc, DB.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ|]. split; [exact P' | exact AL].
  Qed.

  Lemma xsess_win : forall s LBc len DB m m' W,
    as_RHEAP H s LBc m -> as_RFS H LFx m' -> xsess LBc len DB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => (x_lo e <= fst iv /\ snd iv <= xS1 e) \/ fs_scratch H LFx iv) W ->
    xsess LBc len DB m'.
  Proof.
    intros s LBc len DB m m' W RH RF' (REP & PM & OWN) MU WM FW.
    pose proof ex_ranges as (R1' & R2' & R3' & R4' & R5' & R6' & R7' & R8' & R9' & R10' & R11' & R12').
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    pose proof aceil_facts as ((ACe1 & ACe2) & ACe3 & ACe4).
    destruct (fr_app 32 392 ltac:(lia) ltac:(lia) ltac:(lia)) as [DSO DSH].
    assert (OBd : fsobj H LFx ds DS_SIZE).
    { right. exists (4, ff, fp). split; [left; reflexivity|]. unfold ff_addr, ff_class. cbn [fst snd]. change (fsz 4) with 1024.
      unfold SX_DS_OFF, DS_SIZE. lia. }
    assert (DSA : aapp ds DS_SIZE).
    { unfold SX_DS_OFF, DS_SIZE. unfold aapp, aapp_lo, aapp_hi, AFS_HDR, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO in *. lia. }
    assert (BLK : forall b, In b DB -> ablock_range H (blk_addr b) (blk_size b) /\ fsobj H LFx (blk_addr b) (blk_size b)).
    { intros b Hb. assert (HbL : In b LBc) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
      split; [exact (ah_blocks H HH _ _ _ _ RH HbL)|]. destruct b as [[pid A] n]. exact (fsobj_block H HH _ _ _ _ pid A n RH HbL). }
    assert (SHLT : forall a, 0 <= a <= AAPP_HI -> sh a + 1 <= aceil).
    { intros a Ha. unfold sh. rewrite ASHADOW_BASE_val. unfold AAPP_HI in *. clear - Ha ACe1. Z.div_mod_to_equations. lia. }
    split; [| split; [exact PM|]].
    - eapply (dla_frame _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc LBc m m' ds (-4) len DB REP);
        [| intros b Hb; exact (proj1 (proj2 (dla_blocks _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len DB REP) b Hb))].
      intros a Ha Hin. unfold wa. apply MU. rewrite unsigned_lit by exact Ha. apply LbB_DPdK.outside_of.
      eapply Forall_impl; [| exact FW]. intros iv K. cbn beta.
      destruct Hin as [Hin|[(b & Hb & Hin)|[(b & Hb & Hin)|Hin]]].
      + destruct K as [K|K].
        * unfold SX_DS_OFF, DS_SIZE in *. lia.
        * pose proof (fsobj_scratch H HH LFx ds DS_SIZE m' iv RF' OBd ltac:(unfold SX_DS_OFF, AIMG_TOP, AFS_HDR in *; lia) ltac:(unfold DS_SIZE; lia)
                        ltac:(unfold SX_DS_OFF, DS_SIZE, AAPP_HI in *; lia) DSA K). lia.
      + destruct (BLK b Hb) as [(B0 & B16 & Bn & BI & BC & BF & BA) OBb]. destruct K as [K|K].
        * lia.
        * pose proof (fsobj_scratch H HH LFx (blk_addr b) (blk_size b) m' iv RF' OBb ltac:(lia) Bn ltac:(unfold AAPP_HI; lia) BA K). lia.
      + destruct (BLK b Hb) as [(B0 & B16 & Bn & BI & BC & BF & BA) OBb]. destruct K as [K|K].
        * pose proof (SHLT (blk_addr b + blk_size b) ltac:(unfold AAPP_HI; lia)).
          assert (sh (blk_addr b) + nsh (blk_size b) <= sh (blk_addr b + blk_size b) + 1) by (unfold sh, nsh; clear - Bn; Z.div_mod_to_equations; lia). lia.
        * pose proof (fsobj_scratch_sh H HH LFx (blk_addr b) (blk_size b) m' iv RF' OBb ltac:(lia) Bn ltac:(unfold AAPP_HI; lia) K). lia.
      + destruct K as [K|K].
        * pose proof (SHLT (ds + DS_SIZE) ltac:(unfold SX_DS_OFF, DS_SIZE, AAPP_HI, AIMG_TOP, AFS_HDR, AFS_SIZE in *; lia)).
          assert (sh ds + nsh DS_SIZE <= sh (ds + DS_SIZE) + 1) by (unfold sh, nsh, DS_SIZE; clear; Z.div_mod_to_equations; lia). lia.
        * pose proof (fsobj_scratch_sh H HH LFx ds DS_SIZE m' iv RF' OBd ltac:(unfold SX_DS_OFF, AIMG_TOP, AFS_HDR in *; lia) ltac:(unfold DS_SIZE; lia)
                        ltac:(unfold SX_DS_OFF, DS_SIZE, AAPP_HI in *; lia) K). lia.
    - unfold lb_own in *. eapply Forall_impl; [| exact OWN]. intros b Wb. exact (wr_at_wmono _ _ _ _ Wb WM).
  Qed.

  Lemma x_stk_back : forall (G : Prop) XSc s LBc len DB m m' R R' RT SF (STK : Z),
    Px XSc s LBc m -> xsess LBc len DB m -> rtbl Wx R RT -> ftbl Wx (xS1 e) m SF -> fin 0 16 (fkeys SF) = true ->
    0 <= STK <= 8192 ->
    munch [(xS1 e - STK, xS1 e)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    (forall r, In r KEPT -> PropExec.getr R' r = PropExec.getr R r) ->
    (Px XSc s LBc m' -> xsess LBc len DB m' -> rtbl Wx R' (keptk RT) -> ftbl Wx (xS1 e) m' SF -> G) -> G.
  Proof.
    intros G XSc s LBc len DB m m' R R' RT SF STK HI SS HRT HSF Hf HS MU WM MI' KP K.
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
    assert (HI' : Px XSc s LBc m').
    { eapply (Px_win XSc s LBc m m'); [exact HI | exact MU | exact WM | exact MI' |].
      apply Forall_cons; [apply xwin_stk; lia | apply Forall_nil]. }
    apply K.
    - exact HI'.
    - destruct HI as (_ & _ & RH & _). destruct HI' as (RF' & _).
      eapply (xsess_win s LBc len DB m m'); [exact RH | exact RF' | exact SS | exact MU | exact WM |].
      apply Forall_cons; [left; cbn [fst snd]; lia | apply Forall_nil].
    - eapply rtbl_keep; [exact (rtbl_keptk Wx R RT HRT) | apply rsub_keptk | exact KP].
    - eapply (ftbl_munch Wx (xS1 e) m m' SF _ 0 16); [exact HSF | exact MU | exact WM | exact Hf |].
      cbn [disjoint_from]. lia.
  Qed.

  Lemma x_strlen : forall (Q : config -> Prop) RT SF len spent (ret P L : Z) (vn : N) c,
    xsr ASTRLEN_STUB RT SF len spent c -> fin 0 16 (fkeys SF) = true ->
    rcall0 RT ret (Z_to_bv 64 P) -> ret mod 2 = 0 -> 0 <= ret < 2 ^ 64 -> cstrA P L ->
    edenot (wenv Wx) (EVar vn) = Z_to_bv 64 L ->
    (forall c', xsr ret (keptk RT ++ [(10%bv, EVar vn)]) SF len spent c' -> as_SR H Q c') ->
    as_SR H Q c.
  Proof.
    intros Q RT SF len spent ret P L vn [msF mo] (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hf RC Hr2 Hr CS EV K.
    cbn [cfg_ms cfg_model] in *.
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & SS).
    destruct (RC R HRT) as (G1 & G2 & G8 & G4 & G10).
    pose proof (xpre_geo H e HP) as (CE & LO & _). pose proof (xS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    destruct (ex_keep XSc s LBc m HI) as (AC & _ & _ & ST & _).
    assert (Us1 : bv_unsigned (PropExec.getr R 2) = xS1 e) by (rewrite G2; apply unsigned_lit; lia).
    rewrite (MS_full_eq R F _ fc m _ RF) in VIS.
    eapply (ahh_evt_then H HH _ _ s msF _ mo KR VIS).
    { eapply (LbB_PmSL.strlen_cstr_tleaf (ah_strlen H HH) (P, L)); cbn [fst snd]; rewrite ?Us1.
      - exact (proj1 (stk_split asegs m (x_lo e) (xS1 e) (xSP e) ST ltac:(lia))).
      - exact CE.
      - unfold AINTRIN_STACK. lia.
      - clear - S32. Z.div_mod_to_equations. lia.
      - lia.
      - exact MI.
      - exact AC.
      - split; [exact CS | exact G10]. }
    intros msF' mo' KR' MP' POST.
    destruct POST as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & EQ & MU & WM & MI' & ST' & AC' & RES).
    rewrite Us1 in MU. rewrite G1, (ret_pc_even ret Hr Hr2) in EQ.
    lazymatch type of EQ with _ = MS ?R1 _ _ _ _ _ _ => set (R1' := R1) in * end.
    eapply (x_stk_back (as_SR H Q (mkCfg msF' mo')) XSc s LBc len DB m m' R R1' RT SF AINTRIN_STACK HI SS HRT HSF Hf
              ltac:(unfold AINTRIN_STACK; lia) MU WM MI').
    { intros r Hr0. cbn [In KEPT] in Hr0. subst R1'.
      repeat (destruct Hr0 as [<-|Hr0]; [first [reflexivity | exact (eq_sym G1)]|]). destruct Hr0. }
    intros HI' SS' HRT' HSF'.
    apply K. exists s, F, fc, XSc, LBc, DB.
    split; [exact KR'|]. split; [exact (ah_mpres_trans H HH _ _ _ MP MP')|]. split; [exact FZ|]. split; [| exact AL].
    exists R1', m'. split; [exact EQ|]. split; [apply rfull_mkR|].
    split; [apply rtbl_app; [exact HRT' | apply Forall_cons; [| apply Forall_nil]; cbn [fst snd]; rewrite EV; exact RES]|].
    split; [exact HSF'|]. split; [exact HI'|]. split; [exact MI' | exact SS'].
  Qed.

  Lemma xsess_run : forall s LBc len DB m m' (hF hH : Z) SF FT HT ks1 ks2 ks3, wok hF hH = true -> hF <= 32 -> hH <= 4 ->
    as_RHEAP H s LBc m -> xsess LBc len DB m ->
    munch (winsT [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]) m m' -> wmono asegs m m' -> xsess LBc len DB m'.
  Proof.
    intros s LBc len DB m m' hF hH SF FT HT ks1 ks2 ks3 WOK HF HH' RH (REP & PM & OWN) MU WM.
    split; [| split; [exact PM|]].
    - eapply (xds_run LBc m m' len DB hF hH SF FT HT ks1 ks2 ks3 WOK HF HH' REP); [| exact MU].
      apply Forall_forall. intros b Hb.
      assert (HbL : In b LBc) by (apply (Permutation_in _ (Permutation_sym PM)); apply in_or_app; left; exact Hb).
      exact (ah_blocks H HH _ _ _ _ RH HbL).
    - unfold lb_own in *. eapply Forall_impl; [| exact OWN]. intros b Wb. exact (wr_at_wmono _ _ _ _ Wb WM).
  Qed.

  Lemma xsr_mono : forall pc RT SF len spent len' spent' c, xsr pc RT SF len spent c -> len <= len' -> spent <= spent' ->
    xsr pc RT SF len' spent' c.
  Proof.
    intros pc RT SF len spent len' spent' c (s & F & fc & XSc & LBc & DB & KR & MP & FZ & CUT & AL) Hl Hs.
    exists s, F, fc, XSc, LBc, DB. split; [exact KR|]. split; [exact MP|]. split; [exact FZ|]. split; [| lia].
    destruct CUT as (R & m & VIS & RF & HRT & HSF & HI & MI & (REP & PM & OWN)).
    exists R, m. split; [exact VIS|]. split; [exact RF|]. split; [exact HRT|]. split; [exact HSF|]. split; [exact HI|]. split; [exact MI|].
    split; [exact (dla_mono _ _ (ds_laws_A LINV_P5 (fun m0 h => h)) LBc m ds (-4) len len' DB REP Hl) | split; [exact PM | exact OWN]].
  Qed.
End ExS.
