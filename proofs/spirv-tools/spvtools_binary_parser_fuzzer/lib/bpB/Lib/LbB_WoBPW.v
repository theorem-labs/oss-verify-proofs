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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_SR LbB_Conv LbB_MILB LbB_PrsStmt LbB_HKit LbB_HStKit LbB_PmExit LbB_PiStmt LbB_PiInit LbB_PmTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_RwStm LbB_PmHTK LbB_PmMagRS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoGen LbB_WoDefs LbB_WoKit LbB_WoBP LbB_PmMagK LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmMagW LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_WoBPS.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Ltac bw_in := solve [cbn [In]; repeat (first [left; reflexivity | right])].

Ltac bw_csz := repeat match goal with |- context [Z.of_nat (cells_size ?cs)] =>
  let k := eval vm_compute in (Z.of_nat (cells_size cs)) in change (Z.of_nat (cells_size cs)) with k end.

Ltac bw_fa := match goal with |- Forall _ ?l => let l' := eval vm_compute in l in change l with l' end;
  repeat (apply Forall_cons; [cbv beta; assumption|]); apply Forall_nil.

Lemma bw_mrd : forall m a v b, fldA m a 1 v -> word_to_le_bytes 1 (Z_to_bv 64 v) = [b] -> mrd asegs m (wa a) = Some b.
Proof.
  intros m a v b F WB. unfold fldA, fld in F. unfold mrd, wa.
  rewrite WB in F. simpl in F.
  destruct (m (Z_to_bv 64 a)) as [x|].
  - injection F as F. subst x. reflexivity.
  - change (seg_rom asegs (Z_to_bv 64 a)) with (PropExec.seg_rom ASEGS (Z_to_bv 64 a)).
    destruct (PropExec.seg_rom ASEGS (Z_to_bv 64 a)) as [x|]; [injection F as F; subst x; reflexivity | discriminate F].
Qed.

Lemma bw_shad : forall m m' a (bs : list byte) n0 n v b,
  u8arr asegs m a bs -> munch [(a + Z.of_nat n0, a + Z.of_nat (n0 + n))] m m' -> wmono asegs m m' ->
  (n0 + n <= length bs)%nat -> word_to_le_bytes 1 (Z_to_bv 64 v) = [b] ->
  Forall (fun k => fldA m' (a + k) 1 v) (map Z.of_nat (seq n0 n)) ->
  u8arr asegs m' a (firstn n0 bs ++ repeat b n ++ skipn (n0 + n) bs).
Proof.
  intros m m' a bs n0 n v b (BA & WA) MU WM Hn WB FA.
  assert (LEN : length (firstn n0 bs ++ repeat b n ++ skipn (n0 + n) bs) = length bs)
    by (rewrite !length_app, length_firstn, repeat_length, length_skipn; lia).
  destruct BA as (A0 & A1 & BR).
  split; [|rewrite LEN; exact (wr_at_wmono _ _ _ _ WA WM)].
  split; [exact A0|]. split; [rewrite LEN; exact A1|].
  rewrite LEN. intros i Hi.
  assert (Hai : bv_unsigned (wa (a + Z.of_nat i)) = a + Z.of_nat i) by (unfold wa; apply unsigned_lit; lia).
  destruct (Nat.lt_ge_cases i n0) as [L|L].
  - rewrite nth_error_app1 by (rewrite length_firstn; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i n0) as [_|]; [|lia].
    rewrite <- (BR i Hi).
    assert (OUT : outside [(a + Z.of_nat n0, a + Z.of_nat (n0 + n))] (bv_unsigned (wa (a + Z.of_nat i))))
      by (rewrite Hai; cbn [outside]; split; [lia | exact I]).
    unfold mrd. rewrite (MU _ OUT). reflexivity.
  - destruct (Nat.lt_ge_cases i (n0 + n)) as [L2|L2].
    + rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      rewrite nth_error_app1 by (rewrite repeat_length; lia).
      rewrite nth_error_repeat by lia.
      assert (FI : fldA m' (a + Z.of_nat i) 1 v).
      { rewrite Forall_forall in FA. apply (FA (Z.of_nat i)). apply in_map. apply in_seq. lia. }
      exact (bw_mrd m' (a + Z.of_nat i) v b FI WB).
    + rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
      rewrite nth_error_app2 by (rewrite repeat_length; lia). rewrite repeat_length.
      rewrite nth_error_skipn.
      replace (n0 + n + (i - Nat.min n0 (length bs) - n))%nat with i by lia.
      rewrite <- (BR i Hi).
      assert (OUT : outside [(a + Z.of_nat n0, a + Z.of_nat (n0 + n))] (bv_unsigned (wa (a + Z.of_nat i))))
        by (rewrite Hai; cbn [outside]; split; [lia | exact I]).
      unfold mrd. rewrite (MU _ OUT). reflexivity.
Qed.

Lemma bw_wb : word_to_le_bytes 1 (Z_to_bv 64 18446744073709551608) = [Z_to_bv 8 248].
Proof.
  match goal with |- ?l = _ => let l' := eval vm_compute in l in change l with l' end.
  f_equal. apply bv_eq. vm_compute. reflexivity.
Qed.

Section BPW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Let HH : asan_rt_hyps H := rt_bp_base H HHbp.

  Lemma bw_keep : forall e ff fp XSc s LB m M' lo hi,
    wpre H e -> winv H e ff fp XSc s LB m -> 0 <= lo -> lo <= hi -> hi <= 422 ->
    munch [(sh ff + lo, sh ff + hi)] m M' -> wmono asegs m M' -> mem_inv asegs M' ->
    winv H e ff fp XSc s LB M' /\ (bp_slots H e ff m -> bp_slots H e ff M')
    /\ Forall (bp_flw H e ff) [(sh ff + lo, sh ff + hi)].
  Proof.
    intros e ff fp XSc s LB m M' lo hi HP HI L0 L1 L2 MU WM MI.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    assert (ST : stk asegs M' (w_lo e) (wSP e)).
    { apply (stk_keepW _ m M' _ _ (winv_stk H _ _ _ _ _ _ _ HI) MU WM). unfold AIMG_TOP. lia. }
    assert (FW : Forall (wwin H e ff) [(sh ff + lo, sh ff + hi)]).
    { apply Forall_cons; [|apply Forall_nil]. unfold wwin. cbn [fst snd]. right. right. lia. }
    split; [exact (winv_munch H HH e ff fp XSc s LB m M' _ HP HI MU WM MI ST FW)|].
    split.
    - intros (S1 & S2 & S3).
      split; [|split]; (eapply rw_cells_transport; [eassumption | exact MU | exact WM |]);
        bw_csz; cbn [disjoint_from]; (split; [lia | exact I]).
    - apply Forall_cons; [|apply Forall_nil]. unfold bp_flw. cbn [fst snd]. repeat split; lia.
  Qed.

  Lemma bw_pierr : forall e ff fp XSc s LB LBs m M' w lo hi,
    wpre H e -> winv H e ff fp XSc s LB m -> bp_wl H e ff w -> 0 <= lo -> lo <= hi -> hi <= 422 ->
    munch [(sh ff + lo, sh ff + hi)] m M' -> wmono asegs m M' -> mem_inv asegs M' ->
    (exists c', pi_err H LINV_P5 w s LB LBs m c') -> exists c', pi_err H LINV_P5 w s LB LBs M' c'.
  Proof.
    intros e ff fp XSc s LB LBs m M' w lo hi HP HI WL L0 L1 L2 MU WM MI PE.
    destruct (bw_keep e ff fp XSc s LB m M' lo hi HP HI L0 L1 L2 MU WM MI) as (HI' & _ & FW).
    pose proof (wpre_geo H e HP) as (_ & _ & _ & _ & _ & TP).
    destruct PE as (c & RH & SO & LO & PR & PS & HC & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & MI0 & ER & RA & AC & S0 & LV & AL & PD).
    destruct WL as (WP & WC & WW & WN & WLB & WS0 & WLO & WB & WSH).
    assert (HC' : pc_cons c = ff + 3376) by (rewrite HC; exact WC).
    rewrite WP in PR, PS.
    exists c.
    split; [exact (winv_rh H _ _ _ _ _ _ _ HI')|].
    split; [exact SO|].
    split; [unfold lb_own in *; eapply Forall_impl; [| exact LO]; intros b Hb; exact (wr_at_wmono _ _ _ _ Hb WM)|].
    split; [rewrite WP; exact (flw_parser_repA H HH e ff fp XSc s LB (pw_LB0 H w) LBs m M' c _ HP HI PR HC' SO MU FW)|].
    split; [rewrite WP; exact (flw_parser_sh H HH e ff fp XSc s LB (pw_LB0 H w) LBs m M' c _ HP HI PR PS HC' SO MU WM FW)|].
    split; [exact HC|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
    split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
    split; [exact MI|].
    split; [destruct (winv_er H _ _ _ _ _ _ _ HI') as (ev & EV); exists ev; rewrite TP in EV; exact EV|].
    split; [rewrite WB; exact (winv_ra H _ _ _ _ _ _ _ HI')|].
    split; [exact (winv_ac H _ _ _ _ _ _ _ HI')|].
    split; [rewrite WLO, WSH; exact (winv_s0 H _ _ _ _ _ _ _ HI')|].
    split; [destruct HI' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LV'); exact LV'|].
    split; [exact AL|].
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    rewrite WP in PD |- *. unfold PARSER_SIZE in *. intros i Hi.
    rewrite (MU (Z_to_bv 64 (ff + 3456 + i))); [apply PD; exact Hi|].
    rewrite unsigned_lit by lia. cbn [outside]. split; [lia | exact I].
  Qed.

  Lemma bw_pfresh : forall e ff fp XSc s LB LBs m M' w c lo hi,
    wpre H e -> winv H e ff fp XSc s LB m -> bp_wl H e ff w -> 0 <= lo -> lo <= hi -> hi <= 422 ->
    munch [(sh ff + lo, sh ff + hi)] m M' -> wmono asegs m M' -> mem_inv asegs M' ->
    bp_pfresh H w s LB LBs m c -> bp_pfresh H w s LB LBs M' c.
  Proof.
    intros e ff fp XSc s LB LBs m M' w c lo hi HP HI WL L0 L1 L2 MU WM MI (PP & FR & AL & CC).
    destruct (bw_keep e ff fp XSc s LB m M' lo hi HP HI L0 L1 L2 MU WM MI) as (_ & _ & FW).
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    split; [exact (bp_pp_keepW H HH e ff fp XSc w s LB LBs m M' c _ HP HI WL PP MU WM FW)|].
    split; [exact FR|]. split; [exact AL|].
    destruct WL as (WP & WC & _). rewrite WC in *.
    eapply rw_cells_transport; [exact CC | exact MU | exact WM |].
    bw_csz. cbn [disjoint_from]. split; [lia | exact I].
  Qed.

  Lemma bp_kmagf_of_kwcf : forall e ff fp Q mo0, bp_kwcf H e ff fp Q mo0 -> bp_kmagf H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 K s LB LBs m mo msF R F fc XSc w r VIS RF FZ KR MP HP HI SL SHD RC REGS R24 RB WL PE.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    pose proof SHD as (_ & SHW).
    replace (Z.of_nat (length (map (Z_to_bv 8) (wo_sh [14; 20; 21]%nat)))) with 476 in SHW by (vm_compute; reflexivity).
    assert (PRE : LbB_WoBPS.bp_x2_pre R m (sh ff)).
    { unfold LbB_WoBPS.bp_x2_pre. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RC))))))|].
      split; [exact SHW|]. split; lia. }
    destruct (LbB_WoBPS.bp_x2_bp R F fc m (sh ff) PRE) as (R' & M' & MS & MU & WM & FL).
    pose proof (msteps_mem_inv asegs _ _ MS (winv_mi H _ _ _ _ _ _ _ HI)) as MI. cbn [ms_mem] in MI.
    destruct FL as (F217 & F216 & R10 & R19 & KEEP).
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    destruct (bw_keep e ff fp XSc s LB m M' 216 218 HP HI ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI) as (HI' & SLk & _).
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w r); [exact VIS1 | exact RF1 | exact FZ | exact KR1
      | exact (ah_mpres_trans H HH _ _ _ MP MP1) | exact HP | exact HI' | exact (SLk SL) | | | rewrite KEEP by bw_in; exact REGS | | exact RB
      | exact WL | ].
    - unfold bp_shad.
      assert (EQ : map (Z_to_bv 8) (wo_sh [20; 21]%nat)
                   = firstn 216 (map (Z_to_bv 8) (wo_sh [14; 20; 21]%nat)) ++ repeat (Z_to_bv 8 248) 2
                     ++ skipn (216 + 2) (map (Z_to_bv 8) (wo_sh [14; 20; 21]%nat))).
      { rewrite firstn_map, skipn_map, <- map_repeat, <- !map_app. f_equal; vm_compute; reflexivity. }
      rewrite EQ.
      apply (bw_shad m M' (sh ff) _ 216 2 18446744073709551608 (Z_to_bv 8 248) SHD MU WM).
      + apply Nat.leb_le. vm_compute. reflexivity.
      + exact bw_wb.
      + bw_fa.
    - unfold bp_rc in *. rewrite R19, !KEEP by bw_in.
      destruct RC as (C2 & C3 & C4 & C8 & C9 & _ & C20).
      split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C8|]. split; [exact C9|].
      split; [reflexivity | exact C20].
    - rewrite KEEP by bw_in. exact R24.
    - exact (bw_pierr e ff fp XSc s LB LBs m M' w 216 218 HP HI WL ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI PE).
  Qed.

  Lemma bp_klexit_of_kmagf : forall e ff fp Q mo0, bp_kmagf H e ff fp Q mo0 -> bp_klexit H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 K s LB LBs m mo msF R F fc XSc w r VIS RF FZ KR MP HP HI SL SHD RC REGS R24 RB WL PE.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    pose proof SHD as (_ & SHW).
    replace (Z.of_nat (length (map (Z_to_bv 8) (wo_sh [14; 16; 20; 21]%nat)))) with 476 in SHW by (vm_compute; reflexivity).
    assert (PRE : LbB_WoBPS.bp_x1_pre R m (sh ff)).
    { unfold LbB_WoBPS.bp_x1_pre. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RC))))))|].
      split; [exact SHW|]. split; lia. }
    destruct (LbB_WoBPS.bp_x1_bp R F fc m (sh ff) PRE) as (R' & M' & MS & MU & WM & FL).
    pose proof (msteps_mem_inv asegs _ _ MS (winv_mi H _ _ _ _ _ _ _ HI)) as MI. cbn [ms_mem] in MI.
    destruct FL as (F281 & F280 & F279 & F278 & R10 & R19 & KEEP).
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    destruct (bw_keep e ff fp XSc s LB m M' 278 282 HP HI ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI) as (HI' & SLk & _).
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w r); [exact VIS1 | exact RF1 | exact FZ | exact KR1
      | exact (ah_mpres_trans H HH _ _ _ MP MP1) | exact HP | exact HI' | exact (SLk SL) | | | rewrite KEEP by bw_in; exact (proj1 REGS) | | exact RB
      | exact WL | ].
    - unfold bp_shad.
      assert (EQ : map (Z_to_bv 8) (wo_sh [14; 20; 21]%nat)
                   = firstn 278 (map (Z_to_bv 8) (wo_sh [14; 16; 20; 21]%nat)) ++ repeat (Z_to_bv 8 248) 4
                     ++ skipn (278 + 4) (map (Z_to_bv 8) (wo_sh [14; 16; 20; 21]%nat))).
      { rewrite firstn_map, skipn_map, <- map_repeat, <- !map_app. f_equal; vm_compute; reflexivity. }
      rewrite EQ.
      apply (bw_shad m M' (sh ff) _ 278 4 18446744073709551608 (Z_to_bv 8 248) SHD MU WM).
      + apply Nat.leb_le. vm_compute. reflexivity.
      + exact bw_wb.
      + bw_fa.
    - unfold bp_rc in *. rewrite R19, !KEEP by bw_in.
      destruct RC as (C2 & C3 & C4 & C8 & C9 & _ & C20).
      split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C8|]. split; [exact C9|].
      split; [reflexivity | exact C20].
    - rewrite KEEP by bw_in. exact R24.
    - exact (bw_pierr e ff fp XSc s LB LBs m M' w 278 282 HP HI WL ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI PE).
  Qed.

  Lemma bp_k480_of_khdr : forall e ff fp Q mo0, bp_khdr H e ff fp Q mo0 -> bp_k480 H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 K s LB LBs m mo msF R F fc XSc w c VIS RF FZ KR MP HP HI SL SHD RC REGS WL PRS.
    pose proof (hdr_geo H e ff fp XSc s LB m HP HI) as G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15).
    pose proof SHD as (_ & SHW).
    replace (Z.of_nat (length (map (Z_to_bv 8) (wo_sh [18; 20; 21]%nat)))) with 476 in SHW by (vm_compute; reflexivity).
    assert (PRE : LbB_WoBPS.bp_x0_pre R m (sh ff)).
    { unfold LbB_WoBPS.bp_x0_pre. split; [exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 RC))))))|].
      split; [exact SHW|]. split; lia. }
    destruct (LbB_WoBPS.bp_x0_bp R F fc m (sh ff) PRE) as (R' & M' & MS & MU & WM & FL).
    pose proof (msteps_mem_inv asegs _ _ MS (winv_mi H _ _ _ _ _ _ _ HI)) as MI. cbn [ms_mem] in MI.
    destruct FL as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & R10 & R19 & KEEP).
    eapply (sr_msteps H HH s msF mo R F _ fc m R' _ M' Q KR VIS RF MS).
    intros msF1 mo1 KR1 MP1 VIS1 RF1.
    destruct (bw_keep e ff fp XSc s LB m M' 344 374 HP HI ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI) as (HI' & SLk & _).
    apply (K s LB LBs M' mo1 msF1 R' F fc XSc w c); [exact VIS1 | exact RF1 | exact FZ | exact KR1
      | exact (ah_mpres_trans H HH _ _ _ MP MP1) | exact HP | exact HI' | exact (SLk SL) | | | | exact WL | ].
    - unfold bp_shad.
      assert (EQ : map (Z_to_bv 8) (wo_sh [20; 21]%nat)
                   = firstn 344 (map (Z_to_bv 8) (wo_sh [18; 20; 21]%nat)) ++ repeat (Z_to_bv 8 248) 30
                     ++ skipn (344 + 30) (map (Z_to_bv 8) (wo_sh [18; 20; 21]%nat))).
      { rewrite firstn_map, skipn_map, <- map_repeat, <- !map_app. f_equal; vm_compute; reflexivity. }
      rewrite EQ.
      apply (bw_shad m M' (sh ff) _ 344 30 18446744073709551608 (Z_to_bv 8 248) SHD MU WM).
      + apply Nat.leb_le. vm_compute. reflexivity.
      + exact bw_wb.
      + bw_fa.
    - unfold bp_rc in *. rewrite R19, !KEEP by bw_in.
      destruct RC as (C2 & C3 & C4 & C8 & C9 & _ & C20).
      split; [exact C2|]. split; [exact C3|]. split; [exact C4|]. split; [exact C8|]. split; [exact C9|].
      split; [reflexivity | exact C20].
    - unfold bp_r480 in *. rewrite !KEEP by bw_in. exact REGS.
    - exact (bw_pfresh e ff fp XSc s LB LBs m M' w c 344 374 HP HI WL ltac:(lia) ltac:(lia) ltac:(lia) MU WM MI PRS).
  Qed.
End BPW.
