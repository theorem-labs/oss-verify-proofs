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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtorR1 LbB_DPdK LbB_PmXp.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PrsStmt LbB_TablStmt LbB_SnStmt LbB_WoGen LbB_SnXD LbB_SnXK LbB_SnXT LbB_SnXO1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ExC.
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

  Lemma ex_shvis : forall XSc sk LBk m, Px XSc sk LBk m -> shvis m ff (ff + 1024).
Proof using HHbp HP FF.
    intros XSc sk LBk m HI.
    destruct HI as (RF & _).
    pose proof (ah_frm_shvis H (rt_bp_base H HHbp) _ m (4, ff, fp) RF (or_introl eq_refl)) as SV.
    unfold ff_addr, ff_class in SV. cbn [fst snd] in SV. change (fsz 4) with 1024 in SV. exact SV.
  Qed.

  Lemma fr_app : forall k n, 0 <= k -> k + n <= 1024 -> 0 <= n -> app_obj (ff + k) n /\ ff + k + n + 64 <= AAPP_HI.
Proof using HP FF.
  intros k n K0 KN N0.
  pose proof ex_ranges as (_ & _ & _ & R4 & R5 & _ & _ & R8 & R9 & _ & R11 & R12).
  unfold app_obj, AAPP_HI, AFS_HDR in *.
  split; [split; [lia | split; [destruct R11; [left | right]; lia | lia]] | lia].
Qed.

  Lemma fr_addr : forall m HT k0 n, ftbl Wx (ff / 8) m HT ->
    forallb (fun j => fent_in (SHBASE + k0 / 8 + Z.of_nat j, 1%nat, ELit 0) HT) (seq 0 (Z.to_nat (n / 8))) = true ->
    0 <= k0 -> k0 + n <= 1024 -> k0 mod 8 = 0 -> 0 <= n -> n mod 8 = 0 -> addressable m (ff + k0) n.
Proof using HP FF.
    intros m HT k0 n FT HB K0 KN K8 N0 N8.
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    assert (F0 : 0 <= ff) by (unfold AIMG_TOP, AFS_HDR in *; lia).
    assert (FK8 : (ff + k0) mod 8 = 0) by (clear - R6 K8; Z.div_mod_to_equations; lia).
    assert (ESH : ff / 8 + (SHBASE + k0 / 8) = sh (ff + k0))
      by (unfold sh, SHBASE, ASHADOW_BASE; clear - R6 K8; Z.div_mod_to_equations; lia).
    eapply (addr_of_zents Wx (ff / 8) m HT (SHBASE + k0 / 8) (ff + k0) n FT HB ESH); [lia | exact FK8 | exact N0 | exact N8 |].
    assert (D1 : 8 * ((ff + k0) / 8) <= ff + k0) by (clear - F0 K0; Z.div_mod_to_equations; lia).
    assert (D2 : 8 * (n / 8) <= n) by (clear - N0; Z.div_mod_to_equations; lia).
    unfold sh, ASHADOW_BASE, AFS_SIZE in *. lia.
  Qed.

  Lemma xwin_stk : forall a b, xS1 e - 8192 <= a -> b <= xS1 e -> xwin H e ff (a, b).
Proof using HP FF.
  intros a b A B. pose proof (xS1_facts H e HP) as (_ & (S2 & _) & _ & _ & S5 & _).
  unfold xwin, SX_SAVED. cbn [fst snd]. left. lia.
Qed.
  Lemma xwin_fr : forall a b, ff <= a -> b <= ff + 1016 -> xwin H e ff (a, b).
Proof using.
  intros a b A B. unfold xwin, SX_FLAGP. cbn [fst snd]. right; left; lia.
Qed.

  Lemma Px_win : forall XSc sk LBk m m' W, Px XSc sk LBk m -> munch W m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    Forall (xwin H e ff) W -> Px XSc sk LBk m'.
Proof using HHbp HP FF.
  intros XSc sk LBk m m' W HPx MU WM MI FW.
  assert (ST : stk asegs m' (x_lo e) (xSP e)).
  { pose proof HPx as HI. unfold LbB_SnXT.Px, xinv in HI. destruct HI as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _).
    pose proof (xS1_facts H e HP) as (_ & _ & _ & _ & _ & CE). pose proof aceil_facts as ACF.
    eapply stk_wmono; [exact ST | exact WM | lia]. }
  exact (xinv_munch H (rt_bp_base H HHbp) e ff fp XSc sk LBk m m' W HP HPx MU WM MI ST FW).
Qed.

  Lemma obj_apart : forall O n, obj_inframe (x_LF e) O n -> 0 <= O -> 0 <= n -> O + n <= AAPP_HI ->
    (O + n <= ff \/ ff + 1024 <= O) /\ O + n <= xS1 e - 8192.
Proof using HHbp HP FF.
    intros O n (f & IN & O1 & O2) H0 Hn Htop.
    pose proof (rt_bp_base H HHbp) as HH0.
    destruct (xpre_all H e HP) as (_ & _ & _ & _ & (RF & _) & _).
    destruct (ah_RFS_range H HH0 _ _ RF) as [_ AR].
    pose proof (AR f IN) as (K & Q1 & Q2 & _ & _).
    pose proof FF as (_ & _ & FD). destruct (FD f IN) as [D _]. change (fsz 4) with 1024 in D.
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof (xS1_facts H e HP) as (S0 & (S1 & S2) & S3 & S4 & S5 & S6).
    split; [destruct D; [right | left]; lia | lia].
  Qed.

  Lemma blk_apart : forall b, ablock_range H (blk_addr b) (blk_size b) ->
    blk_addr b + blk_size b <= xS1 e - 8192
    /\ (blk_addr b + blk_size b <= ff \/ ff + 1024 <= blk_addr b)
    /\ (blk_addr b + blk_size b <= sh ff \/ sh ff + 128 <= blk_addr b)
    /\ sh (blk_addr b) + nsh (blk_size b) <= xS1 e - 8192
    /\ (sh (blk_addr b) + nsh (blk_size b) <= ff \/ ff + 1024 <= sh (blk_addr b))
    /\ (sh (blk_addr b) + nsh (blk_size b) <= sh ff \/ sh ff + 128 <= sh (blk_addr b)).
Proof using HP FF.
    intros b (B0 & B16 & Bn & BI & BC & BF & BAPP).
    pose proof ex_ranges as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12).
    pose proof (xS1_facts H e HP) as (S0 & (S1 & S2) & S3 & S4 & S5 & S6).
    set (A := blk_addr b) in *. set (n := blk_size b) in *. clearbody A n.
    unfold aapp, aapp_lo, aapp_hi in BAPP.
    assert (DA : 8 * (A / 8) <= A < 8 * (A / 8) + 8) by (clear; Z.div_mod_to_equations; lia).
    assert (DN : 8 * ((n + 7) / 8) <= n + 7 < 8 * ((n + 7) / 8) + 8) by (clear; Z.div_mod_to_equations; lia).
    assert (DF : 8 * (ff / 8) <= ff < 8 * (ff / 8) + 8) by (clear; Z.div_mod_to_equations; lia).
    unfold sh, nsh, ASHADOW_BASE, AIMG_TOP, AFS_HDR, AFS_SIZE, ALOWSH_LO, AHI_LO in *.
    split; [lia|]. split; [destruct BF; [left | right]; lia|].
    split; [destruct BAPP; [left | right]; lia|]. split; [lia|].
    split; [destruct R11; [right | left]; lia|].
    destruct BF; [left | right]; lia.
  Qed.

  Lemma xds_run : forall LB m m' len DB (hF hH : Z) SF FT HT ks1 ks2 ks3, wok hF hH = true -> hF <= 32 -> hH <= 4 ->
    ds_repA0 LB m ds (-4) len DB -> Forall (fun b => ablock_range H (blk_addr b) (blk_size b)) DB ->
    munch (winsT [tS SF ks1; tFw hF FT ks2; tHw hH HT ks3]) m m' -> ds_repA0 LB m' ds (-4) len DB.
Proof using HP FF.
  intros LB m m' len DB hF hH SF FT HT ks1 ks2 ks3 WOK HF HHh REP DBR MU.
  apply (dsa_frame LB LB m m' ds (-4) len DB REP);
    [| intros b Hb; exact (proj1 (proj2 (dsa_blocks LB m ds (-4) len DB REP) b Hb))].
  intros a Ha K. apply MU.
  unfold winsT, LbB_SnXT.tS, LbB_SnXT.tFw, LbB_SnXT.tHw. cbn [map tB tlo thi outside].
  rewrite (wa_unsigned a Ha).
  pose proof ex_wins as (W1 & W2 & W3 & _ & _ & _ & _ & _).
  pose proof shb_eq as SB.
  pose proof (xframe_facts H (x_LF e) ff fp FF) as (_ & _ & F3 & _).
  unfold SX_DS_OFF, DS_SIZE in K.
  destruct K as [K|[(b & Hb & K)|[(b & Hb & K)|K]]].
  - lia.
  - pose proof (blk_apart b (proj1 (Forall_forall _ _) DBR b Hb)) as (P1 & P2 & P3 & _). lia.
  - pose proof (blk_apart b (proj1 (Forall_forall _ _) DBR b Hb)) as (_ & _ & _ & P4 & P5 & P6). lia.
  - assert (S4 : sh (ff + 32) = sh ff + 4) by (rewrite <- (sh_add8 ff 4); f_equal; lia).
    change (nsh 392) with 49 in K. lia.
Qed.

  Definition xcut (pc : Z) (F : bvmap 5 word) (fc : bv 32) (RT : list (reg * expr)) (SF : list fent)
      (XSc : list (Z * Z)) (sk : as_St H) (LBc : list block) (S : mem -> Prop) : machine_state -> Prop :=
    fun ms => exists R m, ms = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) /\ rfull R
      /\ rtbl Wx R RT /\ ftbl Wx (xS1 e) m SF /\ Px XSc sk LBc m /\ mem_inv asegs m /\ S m.
End ExC.
