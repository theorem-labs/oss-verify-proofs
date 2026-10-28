From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition BP_A480 : Z := 0xeb480.
Definition BP_HDR : Z := 0xeb4fc.
Definition BP_MAG : Z := 0xeba74.
Definition BP_HGOOD : Z := 0xebdc4.
Definition BP_D4 : Z := 0xebdec.
Definition BP_LOOP : Z := 0xec0b4.
Definition BP_LEXIT : Z := 0xec0e0.
Definition BP_MAGF : Z := 0xec0f4.
Definition BP_WCF : Z := 0xec100.

Definition WO_OBJS : list (nat * nat) :=
  [(3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5); (3, 5);
   (50, 8); (50, 8); (2, 2); (50, 8); (4, 4); (50, 8); (30, 8); (30, 8); (8, 4); (36, 8)]%nat.

Fixpoint wo_sh_go (L : list nat) (k : nat) (os : list (nat * nat)) : list Z :=
  match os with
  | [] => []
  | (n, r) :: os' =>
      repeat (if existsb (Nat.eqb k) L then 0 else 0xf8) n
      ++ repeat (match os' with [] => 0xf3 | _ => 0xf2 end) r
      ++ wo_sh_go L (S k) os'
  end.

Definition wo_sh (L : list nat) : list Z := repeat 0xf1 4 ++ wo_sh_go L 0 WO_OBJS.

Definition bp_st5 (st : stateC) : stateC :=
  {| st_words := st_words st; st_nwords := st_nwords st; st_diag := st_diag st; st_widx := 5;
     st_icount := st_icount st; st_endian := st_endian st; st_flags := st_flags st;
     st_m1 := st_m1 st; st_m2 := st_m2 st; st_m3 := st_m3 st; st_v1 := st_v1 st; st_v2 := st_v2 st; st_v3 := st_v3 st |}.

Definition bp_ste (st : stateC) (e : Z) : stateC :=
  {| st_words := st_words st; st_nwords := st_nwords st; st_diag := st_diag st; st_widx := 5;
     st_icount := st_icount st; st_endian := e; st_flags := e;
     st_m1 := st_m1 st; st_m2 := st_m2 st; st_m3 := st_m3 st; st_v1 := st_v1 st; st_v2 := st_v2 st; st_v3 := st_v3 st |}.

Definition bp_fresh (st : stateC) (words n : Z) : Prop :=
  pi_hdr (bp_ste st 0) words n 0 /\ (st_flags st = 0 \/ st_flags st = 1).

Section BP.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition bp_fr (e : went H) (ff fp : Z) (XSc : list (Z * Z)) (m : mem) : Prop :=
       as_RFS H ((6, ff, fp) :: w_LF e) m /\ fresh_frame H (w_LF e) 6 ff fp
    /\ stk asegs m (w_lo e) (wSP e)
    /\ rw_cells asegs m (wSP e - WO_SAVED) (wsaved e)
    /\ rw_cells asegs m (ff + WO_FLAGP) [C8 (Z_to_bv 64 fp)]
    /\ wr_at asegs m ff 3456 /\ wr_at asegs m (ff + 3744) (WO_FLAGP - 3744) /\ wr_at asegs m fp 1
    /\ xpres H (w_LB e) (wSP e) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XW H ff fp ++ XSc) (w_m e) m
    /\ Forall (fs_scratch H (w_LF e)) XSc.

  Definition bp_shad (ff : Z) (L : list nat) (m : mem) : Prop :=
    u8arr asegs m (sh ff) (map (Z_to_bv 8) (wo_sh L)).

  Definition bp_slots (e : went H) (ff : Z) (m : mem) : Prop :=
    rw_cells asegs m (wS1 e) [C8 (wz (ff + 3360)); C8 (wz ff)]
    /\ rw_cells asegs m (wS1 e + 24)
         [C8 (wz (w_words e)); C8 (wz (w_n e)); C8 (wz ASHADOW_BASE); C8 (wz (ff + 2224)); C8 (wz (ff + 3376))]
    /\ rw_cells asegs m (wS1 e + 80) [C8 (wz ff)].

  Definition bp_rc (e : went H) (ff : Z) (R : bvmap 5 word) : Prop :=
    getr R 2 = wz (wS1 e) /\ getr R 3 = w_gp e /\ getr R 4 = w_tp e /\ getr R 8 = w_sp e
    /\ getr R 9 = wz (wS1 e) /\ getr R 19 = wz (sh ff) /\ getr R 20 = wz ff.

  Definition bp_r480 (ff : Z) (R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 3456) /\ getr R 21 = wz (ff + 2920) /\ getr R 22 = wz (ff + 3504)
    /\ getr R 23 = wz 0x3f800000 /\ getr R 24 = wz (ff + 2944) /\ getr R 25 = wz (ff + 2968)
    /\ getr R 26 = wz (ff + 3696) /\ getr R 27 = wz (ff + 2752).

  Definition bp_rmag (e : went H) (ff : Z) (R : bvmap 5 word) : Prop :=
    getr R 10 = wz (w_words e) /\ getr R 11 = wz (w_n e) /\ getr R 18 = wz (ff + 3456) /\ getr R 21 = wz (ff + 2920)
    /\ getr R 22 = wz (ff + 3504) /\ getr R 23 = wz 0x3f800000 /\ getr R 24 = wz (ff + 2944) /\ getr R 25 = wz (ff + 1728)
    /\ getr R 26 = wz (ff + 3696) /\ getr R 27 = wz ASHADOW_BASE.

  Definition bp_rg (ff : Z) (R : bvmap 5 word) : Prop :=
    getr R 18 = wz (ff + 3456) /\ getr R 21 = wz (ff + 2920) /\ getr R 22 = wz (ff + 3504)
    /\ getr R 23 = wz 0x3f800000 /\ getr R 24 = wz (ff + 3544) /\ getr R 25 = wz (ff + 1728)
    /\ getr R 26 = wz (ff + 3696) /\ getr R 27 = wz ASHADOW_BASE.

  Definition bp_wl (e : went H) (ff : Z) (w : piw H) : Prop :=
    pw_p H w = ff + 3456 /\ pw_cons H w = ff + 3376 /\ pw_words H w = w_words e /\ pw_n H w = w_n e
    /\ pw_LB0 H w = w_LB e /\ pw_s0 H w = w_s e /\ pw_lo H w = w_lo e /\ pw_B H w = w_B e /\ pw_shi H w = w_shi e.

  Definition bp_pp (w : piw H) (LB LBs : list block) (m : mem) (c : parserC) : Prop :=
    parser_repA LB m (pw_p H w) c /\ parser_sh m (pw_p H w) c
    /\ pc_cons c = pw_cons H w /\ pc_user c = pw_user H w /\ st_diag (pc_state c) = pw_diag H w
    /\ state_own LB (pw_LB0 H w) LBs (pc_state c) /\ lb_own LBs m /\ wr_at asegs m (pw_cons H w) 48.

  Definition bp_al (w : piw H) (s : as_St H) (st : stateC) : Prop :=
    as_AL H s >= as_AL H (pw_s0 H w) - pm_phi (pi_c0 st)
    /\ pm_cap (pi_c0 st) + PM_RESERVE <= po_cost (pw_n H w) /\ po_cost (pw_n H w) <= as_AL H (pw_s0 H w).

  Definition bp_bin (e : went H) (ff : Z) (m : mem) : Prop :=
    fld ASEGS m (ff + 1728) 8 (w_words e) /\ fld ASEGS m (ff + 1736) 8 (w_n e) /\ w_words e <> 0 /\ 5 <= w_n e.

  Definition bp_hdr0 (e : went H) (ff fp : Z) (L : list nat) (pc : Z) (REGS : bvmap 5 word -> Prop)
      (PRS : piw H -> as_St H -> list block -> list block -> mem -> parserC -> Prop) (Q : config -> Prop) (mo0 : Model) : Prop :=
    forall s LB LBs m mo msF R F fc XSc (w : piw H) (c : parserC),
      as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
      as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      wpre H e -> winv H e ff fp XSc s LB m -> bp_slots e ff m -> bp_shad ff L m ->
      bp_rc e ff R -> REGS R -> bp_wl e ff w -> PRS w s LB LBs m c ->
      as_SR H Q (mkCfg msF mo).

  Definition bp_pfresh (w : piw H) (s : as_St H) (LB LBs : list block) (m : mem) (c : parserC) : Prop :=
    bp_pp w LB LBs m c /\ bp_fresh (pc_state c) (pw_words H w) (pw_n H w) /\ bp_al w s (bp_ste (pc_state c) 0)
    /\ rw_cells asegs m (pw_cons H w + 32) [C8 (wz 0)].

  Definition bp_ploop (LF : list fframe) (e : went H) (ff : Z) (w : piw H) (s : as_St H) (LB LBs : list block) (m : mem)
      (c : parserC) : Prop :=
    exists ee : Z, piw_ok H w LF m /\ bp_pp w LB LBs m c /\ pi_hdr (bp_st5 (pc_state c)) (pw_words H w) (pw_n H w) ee
      /\ bp_al w s (bp_st5 (pc_state c)) /\ bp_bin e ff m /\ rw_cells asegs m (pw_cons H w + 32) [C8 (wz 0)].

  Definition bp_k480 (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [18; 20; 21]%nat BP_A480 (bp_r480 ff) bp_pfresh Q mo0.

  Definition bp_khdr (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [20; 21]%nat BP_HDR (bp_r480 ff) bp_pfresh Q mo0.

  Definition bp_kmag (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [14; 20; 21]%nat BP_MAG (bp_rmag e ff)
      (fun w s LB LBs m c => bp_pfresh w s LB LBs m c /\ w_words e <> 0 /\ 5 <= w_n e) Q mo0.

  Definition bp_kgood (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [14; 20; 21]%nat BP_HGOOD (bp_rg ff) (bp_ploop ((6, ff, fp) :: w_LF e) e ff) Q mo0.

  Definition bp_kd4 (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [14; 16; 20; 21]%nat BP_D4 (fun R => bp_rg ff R /\ getr R 10 = wz (-4))
      (bp_ploop ((6, ff, fp) :: w_LF e) e ff) Q mo0.

  Definition bp_kloop (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_hdr0 e ff fp [14; 16; 20; 21]%nat BP_LOOP (bp_rg ff) (bp_ploop ((6, ff, fp) :: w_LF e) e ff) Q mo0.

  Definition bp_kexit (e : went H) (ff fp : Z) (L : list nat) (pc : Z) (SL : went H -> Z -> mem -> Prop)
      (REGS : bvmap 5 word -> Prop) (Q : config -> Prop) (mo0 : Model) : Prop :=
    forall s LB LBs m mo msF R F fc XSc (w : piw H) (r : Z),
      as_VIS H s msF = MS R F (Z_to_bv 64 pc) fc None m (seg_rom asegs) -> rfull R -> frm_zero fc ->
      as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
      wpre H e -> winv H e ff fp XSc s LB m -> SL e ff m -> bp_shad ff L m ->
      bp_rc e ff R -> REGS R -> getr R 24 = wz r -> - 2 ^ 31 <= r < 2 ^ 31 ->
      bp_wl e ff w -> (exists c', pi_err H LINV_P5 w s LB LBs m c') ->
      as_SR H Q (mkCfg msF mo).

  Definition bp_klexit (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_kexit e ff fp [14; 16; 20; 21]%nat BP_LEXIT bp_slots
      (fun R => getr R 22 = wz (ff + 3504) /\ getr R 23 = wz 0x3f800000) Q mo0.

  Definition bp_kmagf (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_kexit e ff fp [14; 20; 21]%nat BP_MAGF bp_slots (fun R => getr R 22 = wz (ff + 3504)) Q mo0.

  Definition bp_kwcf (e : went H) (ff fp : Z) (Q : config -> Prop) (mo0 : Model) : Prop :=
    bp_kexit e ff fp [20; 21]%nat BP_WCF bp_slots (fun R => getr R 22 = wz (ff + 3504)) Q mo0.

  Definition bp_flw (e : went H) (ff : Z) (iv : Z * Z) : Prop :=
    ((ff <= fst iv /\ snd iv <= ff + WO_FLAGP) \/ (sh ff <= fst iv /\ snd iv <= sh ff + 512)
     \/ (w_lo e <= fst iv /\ snd iv <= wS1 e))
    /\ (snd iv <= ff + 3376 \/ ff + 3424 <= fst iv) /\ (snd iv <= ff + 3456 \/ ff + 3744 <= fst iv)
    /\ (snd iv <= sh ff + 422 \/ sh ff + 428 <= fst iv) /\ (snd iv <= sh ff + 432 \/ sh ff + 468 <= fst iv).

  Definition bp_frl (e : went H) (ff fp : Z) (m : mem) : Prop :=
    exists XSc, bp_fr e ff fp XSc m /\ bp_slots e ff m /\ bp_shad ff [14; 16; 20; 21]%nat m.

  Lemma bp_wr_merge : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
    wr_at asegs m a n1 -> wr_at asegs m (a + n1) n2 -> wr_at asegs m a (n1 + n2).
  Proof.
    intros m a n1 n2 N1 N2 (A0 & A1 & W1) (B0 & B1 & W2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i n1) as [L|L]; [apply W1; lia|].
    replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2; lia.
  Qed.

  Lemma bp_wr_sub : forall m a n k l, wr_at asegs m a n -> 0 <= k -> 0 <= l -> k + l <= n -> wr_at asegs m (a + k) l.
  Proof.
    intros m a n k l (A0 & A1 & W) K0 L0 KL. split; [lia|]. split; [lia|].
    intros i Hi. replace (a + k + i) with (a + (k + i)) by lia. apply W; lia.
  Qed.

  Lemma winv_of_bp_fr : forall e ff fp XSc sk LBk m,
    bp_fr e ff fp XSc m -> wr_at asegs m (ff + 3456) 288 ->
    as_RHEAP H sk LBk m -> ACONST m -> mem_inv asegs m -> stack0 m (w_lo e) (w_shi e) -> as_rauxv_ok H m (w_B e) ->
    (exists errv', rw_cells asegs m (errno_addr (w_tp e)) [C4 errv']) -> LINV_P5 m ->
    winv H e ff fp XSc sk LBk m.
  Proof.
    intros e ff fp XSc sk LBk m (RF & FF & ST & SV & SF & W1 & W3 & WFP & XP & FS) W2 RH AC MI S0 RA ER LV.
    unfold winv, WO_FLAGP in *.
    assert (W12 : wr_at asegs m ff (3456 + 288)) by (apply bp_wr_merge; [lia | lia | exact W1 | exact W2]).
    assert (W : wr_at asegs m ff (3744 + (4088 - 3744))).
    { apply bp_wr_merge; [lia | lia | exact W12 | replace (ff + 3744) with (ff + (3456 + 288)) in W3 by lia; exact W3]. }
    replace (3744 + (4088 - 3744)) with 4088 in W by lia.
    split; [exact RF|]. split; [exact FF|]. split; [exact RH|]. split; [exact AC|]. split; [exact MI|].
    split; [exact S0|]. split; [exact RA|]. split; [exact ER|]. split; [exact ST|]. split; [exact SV|].
    split; [exact SF|]. split; [exact W|]. split; [exact WFP|]. split; [exact XP|]. split; [exact FS|]. exact LV.
  Qed.

  Lemma bp_fr_of_winv : forall e ff fp XSc sk LBk m,
    winv H e ff fp XSc sk LBk m -> bp_fr e ff fp XSc m /\ wr_at asegs m (ff + 3456) 288.
  Proof.
    intros e ff fp XSc sk LBk m (RF & FF & RH & AC & MI & S0 & RA & ER & ST & SV & SF & WF & WFP & XP & FS & LV).
    unfold WO_FLAGP in *.
    split; [|exact (bp_wr_sub m ff 4088 3456 288 WF ltac:(lia) ltac:(lia) ltac:(lia))].
    unfold bp_fr, WO_FLAGP.
    split; [exact RF|]. split; [exact FF|]. split; [exact ST|]. split; [exact SV|]. split; [exact SF|].
    split; [pose proof (bp_wr_sub m ff 4088 0 3456 WF ltac:(lia) ltac:(lia) ltac:(lia)) as W0; rewrite Z.add_0_r in W0; exact W0|].
    split; [exact (bp_wr_sub m ff 4088 3744 (4088 - 3744) WF ltac:(lia) ltac:(lia) ltac:(lia))|].
    split; [exact WFP|]. split; [exact XP|]. exact FS.
  Qed.

  Hypothesis HH : asan_rt_hyps H.

  Lemma bp_rin_ex : forall X a, rin_ivs X a -> exists iv, In iv X /\ fst iv <= a < snd iv.
  Proof.
    induction X as [|iv X IH]; cbn; intros a K; [destruct K|].
    destruct K as [K|K]; [exists iv; split; [left; reflexivity | exact K]|].
    destruct (IH a K) as (iv' & I1 & I2). exists iv'. split; [right; exact I1 | exact I2].
  Qed.

  Lemma bp_frl_keep : forall e ff fp (w : piw H), wpre H e -> bp_wl e ff w ->
    forall m m' XS, bp_frl e ff fp m -> Forall (fs_scratch H ((6, ff, fp) :: w_LF e)) XS ->
    xpres H (pw_LB0 H w) (wS1 e) ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (pw_p H w, pw_p H w + PARSER_SIZE) :: XS) m m' ->
    stk asegs m' (pw_lo H w) (wS1 e) -> as_RFS H ((6, ff, fp) :: w_LF e) m' -> bp_frl e ff fp m'.
  Proof.
    intros e ff fp w HP WL m m' XS (XSc & (RF & FF & ST & SV & SF & W1 & W3 & WFP & XP0 & FS) & (SL1 & SL2 & SL3) & SHD) FSn XP ST2 RF2.
    destruct WL as (WP & WC & WW & WN & WLB & WS0 & WLO & WB & WSH).
    rewrite WP, WLB in XP. rewrite WLO in ST2.
    pose proof (wpre_geo H e HP) as (CE & LO' & SH1 & SH2 & SPA & TP).
    pose proof (wS1_facts H e HP) as (S32 & S1SP & S1L & SPH & LOS1 & _).
    pose proof (wframe_facts H _ _ _ FF) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
    pose proof aceil_facts as ACF.
    unfold PARSER_SIZE, WO_FLAGP, WO_SAVED in *.
    assert (XK : Forall (fun iv : Z * Z =>
                   (snd iv <= w_lo e /\ (snd iv <= ff \/ ff + 4096 <= fst iv) /\ (snd iv <= sh ff \/ sh ff + 512 <= fst iv)
                    /\ (snd iv <= fp \/ fp + 1 <= fst iv) /\ (forall a, fst iv <= a < snd iv ->
                         rin_ivs ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: XW H ff fp ++ XSc ++ XS) a))
                   \/ iv = (ff + 3456, ff + 3456 + 288))
                 ((RtB_Td.ATDLOC, RtB_Td.ATDLOC + 8) :: (ff + 3456, ff + 3456 + 288) :: XS)).
    { apply Forall_cons; [left; cbn [fst snd]|apply Forall_cons; [right; reflexivity|]].
      - split; [unfold RtB_Td.ATDLOC in *; lia|]. split; [left; unfold RtB_Td.ATDLOC; lia|].
        split; [left; unfold RtB_Td.ATDLOC; lia|]. split; [left; unfold RtB_Td.ATDLOC; lia|].
        intros a Ha. left. exact Ha.
      - apply Forall_forall. intros iv IN. left.
        pose proof (proj1 (Forall_forall _ _) FSn iv IN) as FSi.
        destruct (wfsw_ok H HH e ff fp m' iv RF2 FF CE FSi) as (_ & _ & _ & _ & B5 & B6 & B7 & _ & B9).
        split; [exact B7|]. split; [exact B5|]. split; [exact B6|]. split; [exact B9|].
        intros a Ha. right. apply rin_ivs_app. right. apply rin_ivs_app. right.
        clear - IN Ha. induction XS as [|iv' XS IH]; [destruct IN|].
        destruct IN as [->|IN]; [left; exact Ha| right; exact (IH IN)]. }
    pose proof (proj1 (Forall_forall _ _) XK) as XKf. clear XK.
    assert (LN : Z.of_nat (length (map (Z_to_bv 8) (wo_sh [14; 16; 20; 21]%nat))) = 476) by (vm_compute; reflexivity).
    exists (XSc ++ XS). split; [|split].
    - unfold bp_fr, WO_FLAGP, WO_SAVED.
      split; [exact RF2|]. split; [exact FF|].
      split.
      { destruct (stk_split asegs m (w_lo e) (wS1 e) (wSP e) ST ltac:(lia)) as [_ STu].
        assert (STu2 : stk asegs m' (wS1 e) (wSP e)).
        { eapply xpres_stk; [exact XP | exact STu | lia |].
          apply Forall_forall. intros iv Hiv.
          destruct (XKf iv Hiv) as [(K1 & _)|K]; [right; lia | subst iv; cbn [fst snd]; right; lia]. }
        exact (stk_merge asegs m' (w_lo e) (wS1 e) (wSP e) ST2 STu2 ltac:(lia)). }
      split.
      { eapply xpres_rw_cells; [exact XP | exact SV |]. split; [left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & _)|K]; [right; lia | subst iv; cbn [fst snd]; right; lia]. }
      split.
      { eapply xpres_rw_cells; [exact XP | exact SF |]. split; [right; right; right; right; left; cbn [cells_size csize]; lia|].
        apply Forall_forall. intros iv Hiv. cbn [cells_size csize].
        destruct (XKf iv Hiv) as [(K1 & K2 & _)|K]; [destruct K2; [right | left]; lia | subst iv; cbn [fst snd]; right; lia]. }
      split.
      { eapply xpres_wr_at; [exact XP | exact W1 |]. split; [right; right; right; right; left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & K2 & _)|K]; [destruct K2; [right | left]; lia | subst iv; cbn [fst snd]; left; lia]. }
      split.
      { eapply xpres_wr_at; [exact XP | exact W3 |]. split; [right; right; right; right; left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & K2 & _)|K]; [destruct K2; [right | left]; lia | subst iv; cbn [fst snd]; right; lia]. }
      split.
      { eapply xpres_wr_at; [exact XP | exact WFP |]. split; [right; right; right; right; left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & K2 & K3 & K4 & _)|K]; [destruct K4; [right | left]; lia | subst iv; cbn [fst snd]; left; lia]. }
      split.
      { eapply xpres_trans; [eapply xpres_weaken; [exact XP0 | lia | intros b Hb; exact Hb |] |].
        - intros a Ha. cbn [rin_ivs] in Ha. destruct Ha as [Ha|Ha]; [left; exact Ha | right].
          apply rin_ivs_app in Ha as [Ha|Ha]; [apply rin_ivs_app; left; exact Ha|].
          apply rin_ivs_app; right; apply rin_ivs_app; left; exact Ha.
        - eapply xpres_weaken; [exact XP | lia | intros b Hb; exact Hb |].
          intros a Ha. destruct (bp_rin_ex _ _ Ha) as (iv & Iiv & Ia).
          destruct (XKf iv Iiv) as [(_ & _ & _ & _ & K5)|K]; [exact (K5 a Ia)|].
          subst iv. cbn [fst snd] in Ia. right. apply rin_ivs_app. left. cbn [XW rin_ivs fst snd].
          right; right; left. change (fsz 6) with 4096. lia. }
      apply Forall_app. split; [exact FS|]. eapply Forall_impl; [| exact FSn]. intros iv X. exact (fs_scratch_mono H _ _ _ X).
    - unfold bp_slots in *. split; [|split].
      + eapply xpres_rw_cells; [exact XP | exact SL1 |]. split; [left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & _)|K]; [right; lia | subst iv; cbn [fst snd]; right; lia].
      + eapply xpres_rw_cells; [exact XP | exact SL2 |]. split; [left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & _)|K]; [right; lia | subst iv; cbn [fst snd]; right; lia].
      + eapply xpres_rw_cells; [exact XP | exact SL3 |]. split; [left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & _)|K]; [right; lia | subst iv; cbn [fst snd]; right; lia].
    - unfold bp_shad in *. destruct SHD as [SB SW]. split.
      + eapply xpres_bytes_at; [exact XP | exact SB |]. rewrite LN.
        split; [right; right; right; right; right; left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & K2 & K3 & _)|K]; [destruct K3; [right | left]; lia | subst iv; cbn [fst snd]; lia].
      + eapply xpres_wr_at; [exact XP | exact SW |]. rewrite LN.
        split; [right; right; right; right; right; left; lia|].
        apply Forall_forall. intros iv Hiv.
        destruct (XKf iv Hiv) as [(K1 & K2 & K3 & _)|K]; [destruct K3; [right | left]; lia | subst iv; cbn [fst snd]; lia].
  Qed.
End BP.
