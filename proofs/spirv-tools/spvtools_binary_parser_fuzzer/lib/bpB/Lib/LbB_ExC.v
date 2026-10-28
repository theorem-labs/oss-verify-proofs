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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DPdK LbB_PmXp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_WoGen LbB_ExDefs LbB_ExKit LbB_ExT.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExC.
  Local Notation PD_SHB := LbB_DPdK.PD_SHB (only parsing).

  Local Notation kst_ex := LbB_ExT.kst_ex (only parsing).
  Local Notation shT := LbB_ExT.shT (only parsing).
  Local Notation kT := LbB_ExT.kT (only parsing).
  Local Notation wok := LbB_ExT.wok (only parsing).
  Local Notation wok_facts := LbB_ExT.wok_facts (only parsing).
  Local Notation wk_win := LbB_ExT.wk_win (only parsing).
  Local Notation fin_wider := LbB_ExT.fin_wider (only parsing).
  Local Notation rtbl_sw := LbB_ExT.rtbl_sw (only parsing).
  Local Notation ftbl_sw := LbB_ExT.ftbl_sw (only parsing).
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable e : xent H.
  Variables (ff fp : Z).

  Variables (p1 n1 p2 n2 : Z).
  Hypothesis HP : xpre H e.
  Hypothesis FF : fresh_frame H (x_LF e) 3 ff fp.

  Hypothesis THI : obj_inframe (x_LF e) (x_this e) 288.
  Hypothesis PCI : obj_inframe (x_LF e) (x_pcons e) 48.

  Local Notation ftbl_xpres := (@LbB_ExT.ftbl_xpres HCEIL H) (only parsing).
  Local Notation Wx := (@LbB_ExT.Wx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Px := (@LbB_ExT.Px HCEIL H e ff fp) (only parsing).
  Local Notation ex_ranges := (@LbB_ExT.ex_ranges HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_vals := (@LbB_ExT.ex_vals HCEIL H e ff fp HP FF) (only parsing).
  Local Notation ex_wins := (@LbB_ExT.ex_wins HCEIL H e ff fp HP FF) (only parsing).
  Local Notation xobj_range := (@LbB_ExT.xobj_range HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation ex_keepT := (@LbB_ExT.ex_keepT HCEIL H HHbp e ff fp HP FF THI PCI) (only parsing).
  Local Notation ex_keep := (@LbB_ExT.ex_keep HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation evWx := (@LbB_ExT.evWx H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation kst_ex_ok := (@LbB_ExT.kst_ex_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation evT := (@LbB_ExT.evT HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_start := (@LbB_ExT.shT_start HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation shT_apart := (@LbB_ExT.shT_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation shb_eq0 := (@LbB_ExT.shb_eq0 ff) (only parsing).
  Local Notation this_apart := (@LbB_ExT.this_apart HCEIL H HHbp e ff fp HP FF THI) (only parsing).
  Local Notation kT_ok := (@LbB_ExT.kT_ok HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF THI PCI) (only parsing).
  Local Notation scT_flat := (@LbB_ExT.scT_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation scP_flat := (@LbB_ExT.scP_flat HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tS := (@LbB_ExT.tS H e) (only parsing).
  Local Notation tFw := (@LbB_ExT.tFw ff) (only parsing).
  Local Notation tHw := (@LbB_ExT.tHw ff) (only parsing).
  Local Notation tF := (@LbB_ExT.tF ff) (only parsing).
  Local Notation tH := (@LbB_ExT.tH ff) (only parsing).
  Local Notation tab_vals := (@LbB_ExT.tab_vals HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3w := (@LbB_ExT.tabs_wf3w HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_wf3 := (@LbB_ExT.tabs_wf3 HCEIL H e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation wk_stk := (@LbB_ExT.wk_stk HCEIL H e ff fp HP FF) (only parsing).
  Local Notation shb_eq := (@LbB_ExT.shb_eq ff) (only parsing).
  Local Notation tabs_ok3w := (@LbB_ExT.tabs_ok3w HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation tabs_ok3 := (@LbB_ExT.tabs_ok3 HCEIL H HHbp e ff fp p1 n1 p2 n2 HP FF) (only parsing).
  Local Notation Px_step3w := (@LbB_ExT.Px_step3w HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Px_step3 := (@LbB_ExT.Px_step3 HCEIL H HHbp e ff fp HP FF) (only parsing).
  Local Notation Wx_sw1 := (@LbB_ExT.Wx_sw1 HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
  Local Notation Wx_sw := (@LbB_ExT.Wx_sw HCEIL H e ff fp p1 n1 p2 n2) (only parsing).
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

  Ltac exrun3 HRT HSF HFT HHT HPX HMI fuel stops kx := exrun3w 504 64 HRT HSF HFT HHT HPX HMI fuel stops kx.

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

  Local Notation ds := (ff + EX_DS_OFF) (only parsing).

  Lemma ex_shvis : forall XSc sk LBk m, Px XSc sk LBk m -> shvis m ff (ff + 512).
Proof using HHbp HP FF.
  intros XSc sk LBk m HPx.
  destruct (ex_keep XSc sk LBk m HPx) as (_ & _ & _ & _ & _ & (W0 & W1 & WW) & _).
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (_ & _ & F3 & _ & _ & _ & _ & _ & _ & _ & F11 & _ & _ & F14 & F15 & _).
  assert (M : (ff + 512) mod 64 = 0) by (rewrite Zplus_mod, F3; reflexivity).
  assert (L : hull_lo ff = ff) by (unfold hull_lo; rewrite F3; lia).
  assert (R : hull_hi (ff + 512) = ff + 512) by (unfold hull_hi; rewrite M; change ((64 - 0) mod 64) with 0; lia).
  unfold shvis, stk. rewrite L, R, <- F11.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (V : wview asegs m (wa a) <> None) by (replace a with (sh ff + (a - sh ff)) by lia; apply WW; lia).
  split; [exact V | apply rd_of_wr_hi; [lia | exact V]].
Qed.

  Lemma fr_app : forall k n, 0 <= k -> k + n <= 512 -> 0 <= n -> app_obj (ff + k) n /\ ff + k + n + 64 <= AAPP_HI.
Proof using HP FF.
  intros k n K0 Kn N0.
  pose proof ex_ranges as (_ & _ & _ & _ & R5 & _ & _ & R8 & _ & _ & R11 & _).
  pose proof ex_wins as (W1 & _ & _ & _ & _ & _ & _ & W8).
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (_ & _ & _ & _ & _ & F6 & _).
  unfold app_obj, AAPP_HI in *.
  split; [split; [lia | split; [destruct R11; [left | right]; lia | lia]] | lia].
Qed.

  Lemma fr_addr : forall m HT k0 n, ftbl Wx (ff / 8) m HT ->
    forallb (fun j => fent_in (SHBASE + k0 / 8 + Z.of_nat j, 1%nat, ELit 0) HT) (seq 0 (Z.to_nat (n / 8))) = true ->
    0 <= k0 -> k0 + n <= 512 -> k0 mod 8 = 0 -> 0 <= n -> n mod 8 = 0 -> addressable m (ff + k0) n.
Proof using HP FF.
  intros m HT k0 n HFT HB K0 Kn K8 N0 N8.
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (F1 & _ & F3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F14 & F15 & _).
  pose proof shb_eq as SB.
  assert (M8 : ff mod 8 = 0) by (clear - F3; Z.div_mod_to_equations; lia).
  assert (D : k0 / 8 + n / 8 <= 64) by (clear - K0 Kn N0; Z.div_mod_to_equations; lia).
  assert (D0 : 0 <= k0 / 8) by (apply Z.div_pos; lia).
  assert (D1 : 0 <= n / 8) by (apply Z.div_pos; lia).
  assert (SH : ff / 8 + (SHBASE + k0 / 8) = sh (ff + k0)).
  { rewrite (sh_rel ff (ff + k0) M8 ltac:(lia)). replace (ff + k0 - ff) with k0 by lia. lia. }
  apply (addr_of_zents Wx (ff / 8) m HT (SHBASE + k0 / 8) (ff + k0) n HFT HB SH); [lia | | exact N0 | exact N8 |].
  - rewrite Zplus_mod, M8, K8. reflexivity.
  - rewrite <- SH. lia.
Qed.

  Lemma fr_str : forall m FT k, ftbl Wx ff m FT -> fent_in (k, 2%nat, ELit 0) FT = true -> 0 <= k -> k + 24 <= 504 ->
    wr_at asegs m ff 504 -> exists j, rw_cells asegs m (ff + k) [C2 (Z_to_bv 64 0); CB 22 j].
Proof using HP FF.
  intros m FT k HFT HK K0 K24 WR.
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (F1 & _).
  pose proof (ftbl_In Wx ff m FT _ _ _ HFT (fent_in_In _ _ HK)) as R1.
  assert (E0 : edenot (wenv Wx) (ELit 0) = Z_to_bv 64 0) by reflexivity.
  rewrite E0 in R1.
  assert (W2 : wr_at asegs m (ff + k + 2) 22) by (eapply wr_at_sub; [exact WR | lia | lia | lia]).
  destruct (rw_cells_of_wr_hi m (ff + k + 2) 22 W2 ltac:(unfold AIMG_TOP; lia) ltac:(lia)) as (j & J).
  change (Z.to_nat 22) with 22%nat in J.
  exists j. exact (rw_C2_CB m (ff + k) (Z_to_bv 64 0) j R1 J).
Qed.

  Lemma xwin_stk : forall a b, xS1 e - 8192 <= a -> b <= xS1 e -> xwin H e ff (a, b).
Proof using HP FF.
  intros a b A B. pose proof (xS1_facts H e HP) as (_ & S1SP & _ & _ & LOS1 & _).
  unfold xwin, EX_SAVED. cbn [fst snd]. left. lia.
Qed.
  Lemma xwin_fr : forall a b, ff <= a -> b <= ff + 504 -> xwin H e ff (a, b).
Proof using.
  intros a b A B. unfold xwin, EX_FLAGP. cbn [fst snd]. right. left. lia.
Qed.

  Lemma Px_win : forall XSc sk LBk m m' W, Px XSc sk LBk m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    Forall (xwin H e ff) W -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
  intros XSc sk LBk m m' W HPx MU WM MI FW.
  destruct (ex_keep XSc sk LBk m HPx) as (_ & _ & _ & ST & _).
  pose proof (xpre_geo H e HP) as (CE & _).
  pose proof aceil_facts as (AC1 & _).
  assert (ST' : stk asegs m' (x_lo e) (xSP e)) by (apply (stk_wmono m m'); [exact ST | exact WM | lia]).
  exact (xinv_munch H HH e ff fp XSc sk LBk m m' W HP HPx MU WM MI ST' FW).
Qed.

  Lemma obj_apart : forall O n, obj_inframe (x_LF e) O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI ->
    (O + n <= ff \/ ff + 512 <= O) /\ O + n <= xS1 e - 8192.
Proof using HHbp HP FF.
  intros O n (f & Hf & L1 & L2) O0 N0 OH.
  pose proof FF as (_ & _ & FD). destruct (FD f Hf) as [D _]. change (fsz 3) with 512 in D.
  pose proof (xpre_all H e HP) as (_ & _ & _ & _ & (RF & _) & _).
  destruct (ah_RFS_range H HH _ _ RF) as [_ FR].
  pose proof (FR f Hf) as (_ & _ & K3 & _).
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _).
  pose proof (xS1_facts H e HP) as (_ & _ & _ & _ & LOS1 & CE).
  split; lia.
Qed.

  Lemma blk_apart : forall b, ablock_range H (blk_addr b) (blk_size b) ->
    blk_addr b + blk_size b <= xS1 e - 8192
    /\ (blk_addr b + blk_size b <= ff \/ ff + 512 <= blk_addr b)
    /\ (blk_addr b + blk_size b <= sh ff \/ sh ff + 64 <= blk_addr b)
    /\ sh (blk_addr b) + nsh (blk_size b) <= xS1 e - 8192
    /\ (sh (blk_addr b) + nsh (blk_size b) <= ff \/ ff + 512 <= sh (blk_addr b))
    /\ (sh (blk_addr b) + nsh (blk_size b) <= sh ff \/ sh ff + 64 <= sh (blk_addr b)).
Proof using HP FF.
  intros b. generalize (blk_addr b) (blk_size b). clear b. intros A n (A0 & A16 & N0 & AT & AC & AF & AP).
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
  pose proof (xS1_facts H e HP) as (_ & _ & _ & _ & LOS1 & CE).
  pose proof aceil_facts as (AC1 & _).
  pose proof (aapp_disjoint_sh A n ff 512 AP ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as D1.
  change (nsh 512) with 64 in D1.
  pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE A n F10 ltac:(lia) ltac:(unfold AAPP_HI; lia) N0) as D2.
  pose proof (sh_aapp_range A n AP N0) as (_ & S2 & _).
  assert (S3 : sh aceil < aceil) by (apply sh_below_aceil; unfold AAPP_HI; lia).
  assert (B2 : A + n <= ff \/ ff + 512 <= A) by (destruct AF; [left | right]; lia).
  assert (S6 : sh A + nsh n <= sh ff \/ sh ff + 64 <= sh A).
  { destruct B2 as [B2|B2].
    - left. clear - A16 N0 F3 B2. unfold sh, nsh. Z.div_mod_to_equations. lia.
    - right. rewrite F11. apply sh_mono. exact B2. }
  split; [lia|]. split; [exact B2|]. split; [destruct D1; [right | left]; lia|].
  split; [lia|]. split; [destruct D2; [left | right]; lia|]. exact S6.
Qed.

  Lemma xds_run : forall LB m m' len DB (hF hH : Z) SF FT HT ks1 ks2 ks3, wok hF hH = true -> hF <= 32 -> hH <= 4 ->
    ds_repA0 LB m ds (-4) len DB -> Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) DB ->
    munch (winsT [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]) m m' -> ds_repA0 LB m' ds (-4) len DB.
Proof using HP FF.
  intros LB m m' len DB hF hH SF FT HT ks1 ks2 ks3 WK HF HH4 DS FB MU.
  pose proof ex_wins as (X1 & X2 & X3 & _).
  pose proof shb_eq as SB.
  assert (S32 : sh (ff + 32) = sh ff + 4) by exact (sh_add8 ff 4).
  assert (N392 : nsh DS_SIZE = 49) by reflexivity.
  eapply dsa_frame; [exact DS | | intros b Hb; exact (proj1 (proj2 (dsa_blocks _ _ _ _ _ _ DS) b Hb))].
  intros a Ha Hin. apply MU.
  unfold winsT, LbB_ExT.tS, LbB_ExT.tFw, LbB_ExT.tHw. cbn [map tB tlo thi outside].
  unfold wa. rewrite HLib.u64_of_Z by lia.
  rewrite N392 in Hin. unfold EX_DS_OFF, DS_SIZE in Hin. rewrite S32 in Hin.
  destruct Hin as [Hd | [(b & Hb & Hr) | [(b & Hb & Hr) | Hs]]].
  - split; [lia | split; [lia | split; [lia | exact I]]].
  - pose proof (blk_apart b (proj1 (Forall_forall _ _) FB b Hb)) as (B1 & B2 & B3 & B4 & B5 & B6).
    split; [lia | split; [lia | split; [lia | exact I]]].
  - pose proof (blk_apart b (proj1 (Forall_forall _ _) FB b Hb)) as (B1 & B2 & B3 & B4 & B5 & B6).
    split; [lia | split; [lia | split; [lia | exact I]]].
  - split; [lia | split; [lia | split; [lia | exact I]]].
Qed.

  Definition xcut (pc : Z) (F : bvmap 5 word) (fc : bv 32) (RT : list (reg * expr)) (SF : list fent)
      (XSc : list (Z * Z)) (sk : as_St H) (LBc : list block) (S : mem -> Prop) : machine_state -> Prop :=
    fun ms => exists R m, ms = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R
      /\ rtbl Wx R RT /\ ftbl Wx (xS1 e) m SF /\ Px XSc sk LBc m /\ mem_inv asegs m /\ S m.
End ExC.
