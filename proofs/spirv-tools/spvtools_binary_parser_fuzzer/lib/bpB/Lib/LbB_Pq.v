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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 BsWalk RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BakeStackRep FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_Own.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_DiagStmt LbB_DStat LbB_DRep LbB_DKit LbB_DKitN.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PcStmt LbB_PqK LbB_PqK2 LbB_PqR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DCtorK LbB_DCtor LbB_DPdK LbB_PcOvf LbB_PcXsp.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma pq_mul32 : forall x, 0 <= x < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 32) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 5)) = Z_to_bv 64 (x - x mod 32).
Proof.
  intros x Hx. apply bv_eq. cbn [mul_div alu64 alu].
  rewrite bv_mul_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x), (Z.mod_small 32), (Z.mod_small 5), (Z.mod_small 63) by lia. change (Z.land 5 63) with 5.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as B.
  assert (0 <= x / 32 < 2 ^ 59) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma inr_In : forall (r : reg) (l : list reg), existsb (fun y => bv_eqb y r) l = true -> In r l.
Proof.
  intros r l. induction l as [|r' l IH]; cbn [existsb]; [discriminate|].
  intros Hb. apply orb_true_iff in Hb as [Hb|Hb].
  - left. unfold bv_eqb in Hb. apply Z.eqb_eq in Hb. apply bv_eq in Hb. exact Hb.
  - right. exact (IH Hb).
Qed.

Lemma ftbl_of_fld : forall W B m k (w : nat) v, CRep.fld ASEGS m (B + k) w v -> wr_at asegs m (B + k) (Z.of_nat w) ->
  0 <= B + k -> B + k + Z.of_nat w <= 2 ^ 64 -> ftbl W B m [(k, w, ELit v)].
Proof.
  intros W B m k w v HF HW H0 H1. constructor; [| constructor]. cbn [edenot].
  apply (rw_CB_of_rdn m (B + k) w (Z_to_bv 64 v) H0 H1); [exact HF | exact HW].
Qed.

Section ReIos.
  #[local] Notation fld := (CRep.fld ASEGS).
  Lemma ds_inv_reios : forall A M M' ds err len B m pp hm fl fill fill',
    ds_inv A M ds err len B m pp hm fl fill -> (fill' = 2 ^ 32 - 1 \/ fill' = 32) ->
    fld M' (ds + 136) 8 0 -> fld M' (ds + 256) 4 fill' -> mdef M' ds 392 ->
    (forall a, 0 <= a < 2 ^ 64 -> ds_foot ds B a -> ~ (ds + 136 <= a < ds + 144) -> ~ (ds + 256 <= a < ds + 260) ->
               M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
    ds_inv A M' ds err len B m pp hm fl fill'.
  Proof.
    intros A M M' ds err len B m pp hm fl fill fill' DI Hf' HW' HF' HD' OUT.
    pose proof (di_pos _ _ _ _ _ _ _ _ _ _ _ DI) as G1. pose proof (di_hi _ _ _ _ _ _ _ _ _ _ _ DI) as G3.
    pose proof (di_B _ _ _ _ _ _ _ _ _ _ _ DI) as GB.
    assert (AG : forall P : Z -> Prop,
              (forall a, P a -> 0 <= a < 2 ^ 64 /\ ds_foot ds B a /\ ~ (ds + 136 <= a < ds + 144) /\ ~ (ds + 256 <= a < ds + 260)) ->
              agree_on P M M').
    { intros P HP a Ha. destruct (HP a Ha) as (X1 & X2 & X3 & X4). apply OUT; assumption. }
    destruct DI.
    assert (FO : forall a (k : nat) v, ds <= a -> a + Z.of_nat k <= ds + 392 ->
                 (a + Z.of_nat k <= ds + 136 \/ ds + 144 <= a) -> (a + Z.of_nat k <= ds + 256 \/ ds + 260 <= a) ->
                 fld M a k v -> fld M' a k v).
    { intros a k v Ho Hk Hd1 Hd2 HF. eapply (fld_ag M M' (fun x => a <= x < a + Z.of_nat k)); [lia | lia | intros x Hx; exact Hx | | exact HF].
      apply AG. intros x Hx. split; [lia|]. split; [left; unfold zwin, DS_SIZE; lia | lia]. }
    constructor; try assumption.
    - apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption].
    - assert (SBD : forall d asz, m = SLong d asz -> 0 < d /\ d + asz <= 2 ^ 63).
      { intros d asz E. subst m. destruct (si_str _ _ _ _ _ _ di_sb) as (cs & SR & _).
        destruct SR as (_ & _ & _ & _ & (Hd & _ & Hde & _) & _). lia. }
      eapply sb_inv_frame; [exact di_sb | clear - G1 G3; lia | clear - G1 G3; lia | |
        intros blk Hb; destruct (si_str _ _ _ _ _ _ di_sb) as (cs & SR & _);
        exact (@str_blocks_live AC_A ASEGS LY_A MI_A _ _ _ _ _ SR blk Hb)].
      apply AG. intros a Ha. unfold sb_fp, zwin in Ha. destruct Ha as [Ha|Ha].
      + split; [lia|]. split; [left; unfold zwin, DS_SIZE; lia | lia].
      + destruct m as [|d asz]; [destruct Ha|]. specialize (di_dj d asz eq_refl). specialize (SBD d asz eq_refl).
        split; [lia|]. split; [right; exists d, asz; rewrite GB; split; [left; reflexivity | lia] | lia].
    - destruct di_ios. constructor; try assumption; try (apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption]).
      + replace (ds + 112 + 24) with (ds + 136) by lia. exact HW'.
      + intros i Hi. apply FO; [lia | cbn; lia | cbn; lia | cbn; lia |]. apply ii_zero. exact Hi.
      + replace (ds + 112 + 144) with (ds + 256) by lia. exact HF'.
    - apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption].
    - apply FO; [lia | cbn; lia | cbn; lia | cbn; lia | assumption].
  Qed.
End ReIos.

Definition kst_q0 : list kentry :=
  [ KImg 0x17e000 0x186000; KWord (SA (ELit 0) SHCELL) 8 (ELit SHBASE); KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
    KWr (SA (EVar 33) (-8192)) (ELit 8192); KRange (EVar 33) (2 ^ 45) (2 ^ 47) ].

Definition RTQ0 : list (reg * expr) :=
  [(1%bv, EVar 34); (2%bv, EVar 33); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 37); (9%bv, EVar 38);
   (18%bv, EVar 39); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 42); (22%bv, EVar 43); (23%bv, EVar 44);
   (24%bv, EVar 45); (25%bv, EVar 46); (26%bv, EVar 47); (27%bv, EVar 48); (10%bv, EVar 32); (11%bv, EVar 35); (12%bv, EVar 36)].

Section PQ.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (ds p n len err lo : Z) (LF : list fframe) (LB DB : list block)
            (ms : sbuf) (pp hm fl fill : Z) (sA : as_St H).

  Record pq_ctx : Prop := PQ_CTX {
    c_a0 : a0 = Z_to_bv 64 ds;
    c_a1 : a1 = Z_to_bv 64 p;
    c_a2 : a2 = Z_to_bv 64 n;
    c_rep : ds_rep_w LB m0 ds err len DB ms pp hm fl fill;
    c_dsv : shvis m0 ds (ds + DS_SIZE);
    c_dsin : obj_inframe LF ds DS_SIZE;
    c_pn : 0 <= p /\ p + n <= 2 ^ 47 /\ 0 <= n <= DS_MAXLEN;
    c_p0 : 0 < p \/ n = 0;
    c_stk : stk asegs m0 lo (bv_unsigned sp);
    c_ceil : aceil <= lo;
    c_lo : lo <= bv_unsigned sp - ADS_STACK;
    c_sp16 : bv_unsigned sp mod 16 = 0;
    c_sphi : bv_unsigned sp <= AAPP_HI;
    c_spds : ds + DS_SIZE <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= ds;
    c_mi : mem_inv asegs m0;
    c_ac : ACONST m0;
    c_lv : LINV_P5 m0;
    c_tp : tp = Z_to_bv 64 ATP;
    c_rfs : as_RFS H LF m0;
    c_lfn : (length LF + 2 <= AFS_MAXLIVE_BP)%nat;
    c_rh : as_RHEAP H sA LB m0
  }.
  Hypothesis CTX : pq_ctx.
  Let Ha0 : a0 = Z_to_bv 64 ds := c_a0 CTX.
  Let Ha1 : a1 = Z_to_bv 64 p := c_a1 CTX.
  Let Ha2 : a2 = Z_to_bv 64 n := c_a2 CTX.
  Let REP0 : ds_rep_w LB m0 ds err len DB ms pp hm fl fill := c_rep CTX.
  Let DSV : shvis m0 ds (ds + DS_SIZE) := c_dsv CTX.
  Let DSin : obj_inframe LF ds DS_SIZE := c_dsin CTX.
  Let PN : 0 <= p /\ p + n <= 2 ^ 47 /\ 0 <= n <= DS_MAXLEN := c_pn CTX.
  Let STK : stk asegs m0 lo (bv_unsigned sp) := c_stk CTX.
  Let CEIL : aceil <= lo := c_ceil CTX.
  Let LO : lo <= bv_unsigned sp - ADS_STACK := c_lo CTX.
  Let SP16 : bv_unsigned sp mod 16 = 0 := c_sp16 CTX.
  Let SPHI : bv_unsigned sp <= AAPP_HI := c_sphi CTX.
  Let SPDS : ds + DS_SIZE <= bv_unsigned sp - ADS_STACK \/ bv_unsigned sp <= ds := c_spds CTX.
  Let MI0 : mem_inv asegs m0 := c_mi CTX.
  Let AC0 : ACONST m0 := c_ac CTX.
  Let LV0 : LINV_P5 m0 := c_lv CTX.
  Let TP : tp = Z_to_bv 64 ATP := c_tp CTX.
  Let RFS0 : as_RFS H LF m0 := c_rfs CTX.
  Let LFn : (length LF + 2 <= AFS_MAXLIVE_BP)%nat := c_lfn CTX.
  Let RH0 : as_RHEAP H sA LB m0 := c_rh CTX.

  Notation spz := (bv_unsigned sp) (only parsing).
  Definition W0 : list word :=
    [Z_to_bv 64 ds; sp; ra; Z_to_bv 64 p; Z_to_bv 64 n; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9; s10; s11; gp; tp].

  Lemma HHb : asan_rt_hyps H. Proof. exact (rt_bp_base H HHbp). Qed.
  Lemma SM1 : stack_malloc_stmt_bp H 1 AFS_MALLOC_1. Proof. apply stack_malloc_bp_of_donor. exact (ah_fs1 H HHb). Qed.

  Lemma ds_facts : addressable m0 ds DS_SIZE /\ wr_at asegs m0 ds DS_SIZE /\ app_obj ds DS_SIZE /\ ds mod 8 = 0 /\ 0 < ds
    /\ ds + DS_SIZE + 64 <= AAPP_HI /\ as_FSB H + AFS_HDR <= ds /\ ds + DS_SIZE <= as_FSB H + AFS_SIZE /\ ds + DS_SIZE <= aceil
    /\ (fl = DS_FL0 \/ fl = DS_FLHEX) /\ (fill = 2 ^ 32 - 1 \/ fill = 32) /\ 0 <= len /\ dsf ds fl m0
    /\ CRep.fld ASEGS m0 (ds + 136) 8 0 /\ CRep.fld ASEGS m0 (ds + 256) 4 fill.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    pose proof REP0 as (DI & BLK & DSA & DSW & DSO & SBA). pose proof DSO as (O1 & O2 & O3).
    destruct (LbB_DCtor.inframe_facts H HHb LF m0 ds DS_SIZE RFS0 DSin ltac:(unfold DS_SIZE; clear; lia) O1) as (DSH & _ & F3 & F4).
    destruct (ah_RFS_range H HHb LF m0 RFS0) as [(B1 & B2 & B3 & B4) FR].
    assert (F3' : as_FSB H + AFS_HDR <= ds).
    { destruct DSin as (f & Hf & X1 & X2). pose proof (FR f Hf) as (_ & L2 & _). clear - X1 L2. lia. }
    clear F3.
    pose proof DI as DI'. destruct DI'. pose proof di_ios as II. destruct II. pose proof di_sb as SB. destruct SB.
    assert (W8 : forall a, ds <= a -> a + 8 <= ds + DS_SIZE -> wr_at asegs m0 a 8) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    assert (W4 : forall a, ds <= a -> a + 4 <= ds + DS_SIZE -> wr_at asegs m0 a 4) by (intros a X Y; eapply wr_at_sub; [exact DSW | lia | lia | lia]).
    unfold DS_SIZE in *.
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    constructor.
    - apply rw_cells_of_fld8; [exact di_vt | apply W8; lia].
    - apply rw_cells_of_fld8; [exact si_vt | apply W8; lia].
    - apply rw_cells_of_fld8; [exact ii_vt | apply W8; lia].
    - replace (ds + 120) with (ds + 112 + 8) by lia. apply rw_cells_of_fld4; [exact ii_flags | apply W4; lia].
    - replace (ds + 144) with (ds + 112 + 32) by lia. apply rw_cells_of_fld4; [exact ii_state | apply W4; lia].
    - replace (ds + 152) with (ds + 112 + 40) by lia. apply rw_cells_of_fld8; [exact ii_rdbuf | apply W8; lia].
    - replace (ds + 160) with (ds + 112 + 48) by lia. apply rw_cells_of_fld8; [exact ii_loc | apply W8; lia].
    - replace (ds + 248) with (ds + 112 + 136) by lia. apply rw_cells_of_fld8; [exact ii_tie | apply W8; lia].
    - replace (ds + 136) with (ds + 112 + 24) by lia. exact ii_width.
    - replace (ds + 256) with (ds + 112 + 144) by lia. exact ii_fill.
  Qed.

  Lemma p_ranges : 0 <= spz < 2 ^ 64 /\ aceil + ADS_STACK <= spz /\ 0x7fff7f800000 <= aceil <= 0x7fffff800000.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    pose proof (bv_unsigned_in_range 64 sp) as R. change (bv_modulus 64) with (2 ^ 64) in R.
    pose proof aceil_facts as ((A1 & A2) & _). split; [lia|]. split; [lia|]. lia.
  Qed.

  Definition P0w (m : mem) : Prop := munch [(spz - 8192, spz)] m0 m /\ wmono asegs m0 m.

  Lemma p0_keep : forall m, P0w m -> mem_inv asegs m -> ACONST m /\ LINV_P5 m /\ stk asegs m lo spz.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros m [MU WM] MI. pose proof p_ranges as (R1 & R2 & R3).
    split.
    { eapply ACONST_frame; [exact AC0 | exact MU | exact WM |]. apply Forall_cons; [| apply Forall_nil].
      apply LbB_DPdK.aconst_ok_hi. unfold ADS_STACK in *. lia. }
    split.
    { eapply LINV_P5_cl; [exact LV0|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia.
      cbn [outside]. unfold aimg_client, ADS_STACK in *. split; [lia | exact I]. }
    eapply LbB_PqK.stk_keep; [exact STK | exact MU | exact WM | unfold AIMG_TOP, ADS_STACK in *; lia].
  Qed.

  Ltac evWW := cbn [edenot]; unfold wenv, HLib.Eseed, reg_ev, LbB_PqK2.W2, LbB_PqK.W1, W0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app length N.of_nat Pos.of_succ_nat Pos.succ N.add Pos.add].
  Ltac evw0 := unfold estart, elenZ; cbn [edenot a_base a_off]; unfold HLib.Eseed, reg_ev, W0;
    lazy [ev eb N.ltb N.compare PosDef.Pos.compare PosDef.Pos.compare_cont N.to_nat PosDef.Pos.to_nat PosDef.Pos.iter_op
          Init.Nat.add Nat.sub nth app].

  Lemma kst_q0_ok : forall R X m, P0w m -> mem_inv asegs m -> know_ok asegs (HLib.Eseed R (W0 ++ X)) m kst_q0.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros R X m PW MI. destruct (p0_keep m PW MI) as (AC & (RL & _) & ST).
    pose proof p_ranges as (R1 & R2 & R3).
    pose proof (ACONST_shbase m AC) as [_ CS]. pose proof (ACONST_uar m AC) as [_ CU].
    unfold ADS_STACK in *.
    unfold know_ok, kst_q0. repeat apply Forall_cons; try apply Forall_nil.
    - apply kimg_relro. exact RL.
    - eapply (kword_of_rw_cells asegs _ m ASHBASE_CELL _ 0%nat (C8 (wz 0x7fff8000))); [exact CS | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold ASHBASE_CELL; cbn; lia | unfold ASHBASE_CELL; cbn; lia | reflexivity].
    - eapply (kword_of_rw_cells asegs _ m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact CU | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off edenot]; rewrite unsigned_lit by lia; reflexivity
        | unfold AUAR_CELL; cbn; lia | unfold AUAR_CELL; cbn; lia | reflexivity].
    - eapply kwr_of_stk; [exact ST | | |]; evw0; rewrite ?unsigned_lit by lia; lia.
    - cbn [kentry_ok]. evw0. unfold AAPP_HI in *. lia.
  Qed.

  Definition tS0 (T : list fent) (ks : list (Z * nat)) : tab := (EVar 33, spz, -8192, 0, T, ks).

  Lemma tabs_wf0 : forall T ks, fwcl (wbound W0) T = true -> fin (-8192) 0 (fkeys T ++ ks) = true -> tabs_wf W0 [tS0 T ks].
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros T ks C F1. pose proof p_ranges as (R1 & R2 & R3). split.
    - repeat constructor; cbn [tb tB tlo thi ttbl tks tS0]; try reflexivity; try assumption; unfold ADS_STACK in *; lia.
    - intros u1 u2 H1 H2 Hb. destruct H1 as [<-|[]]; destruct H2 as [<-|[]]. vm_compute in Hb. discriminate Hb.
  Qed.

  Lemma P0w_step : forall T ks m m', P0w m -> munch (winsT [tS0 T ks]) m m' -> wmono asegs m m' -> mem_inv asegs m' -> P0w m'.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros T ks m m' [MU0 WM0] MU WM _. split; [| eapply wmono_trans; eassumption].
    eapply munch_trans; [exact MU0|]. eapply munch_weaken; [| exact MU].
    apply sub_fp_of. apply Forall_cons; [| apply Forall_nil]. exists (spz - 8192, spz). split; [left; reflexivity | cbn; lia].
  Qed.

  Lemma tabs_ok0 : forall m T ks, P0w m -> mem_inv asegs m -> ftbl W0 spz m T -> fin (-8192) 0 ks = true ->
    tabs_ok W0 m [tS0 T ks].
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros m T ks PW MI HT F1. destruct (p0_keep m PW MI) as (_ & _ & ST).
    apply Forall_cons; [| apply Forall_nil]. split; [exact HT|].
    intros k w Hi. cbn [tB tks tS0] in *. destruct (fin_In _ _ _ k w F1 Hi) as (H1 & H2 & H3).
    pose proof LO as LO'. unfold ADS_STACK in LO'.
    pose proof (wr_at_of_stk asegs m lo spz ST) as W. eapply wr_at_sub; [exact W | lia | lia | lia].
  Qed.

  Ltac dkrun0 HRT HSF HP HMI fuel stops :=
    lazymatch goal with
    | |- evt asegs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None ?m ?ro) =>
      lazymatch type of HSF with ftbl _ _ _ ?SF =>
      lazymatch type of HRT with rtbl _ _ ?RT =>
        let L0 := constr:([tS0 SF []]) in
        let r := eval vm_compute in
          (sym_exec asegs fuel true stops (SCR [] [] []) (SS pc (HLib.srs sr_id RT) [] (kst_q0 ++ fknT L0) 60) []) in
        lazymatch r with
        | (?SSr, ?scs, ?scr') =>
          let RT' := eval vm_compute in (wtbl (wbound W0) (s_regs SSr)) in
          let ks1 := eval vm_compute in (nkeys (EVar 33) (s_log SSr) SF) in
          eapply (dk_runN W0 [tS0 SF ks1] (tabs_wf0 SF ks1 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
                    P0w (P0w_step SF ks1) Q R F pc fc m ro RT [] kst_q0 fuel stops (SCR [] [] []) 60%N SSr scs scr' RT');
          [ assumption | exact HRT | vm_compute; reflexivity
          | apply tabs_ok0; [exact HP | exact HMI | exact HSF | vm_compute; reflexivity]
          | exact HP | exact HMI | apply kst_q0_ok; [exact HP | exact HMI]
          | vm_cast_no_check (@eq_refl _ (SSr, scs, scr'))
          | | vm_compute; reflexivity | vm_compute; reflexivity | ]
        end
      end end
    end.

  Definition RTQ1 : list (reg * expr) :=
    [(1%bv, ELit 0xf6318); (3%bv, EVar 49); (4%bv, EVar 50); (8%bv, EVar 33); (10%bv, ELit 96);
     (18%bv, EVar 32); (19%bv, EVar 40); (20%bv, EVar 41); (21%bv, EVar 35); (22%bv, EVar 36); (23%bv, EVar 44);
     (24%bv, EVar 45); (25%bv, ELit SHBASE); (26%bv, EVar 47); (27%bv, EVar 48)].

  Lemma pq_p1 :
    evt asegs (fun msx => exists R1 m1, msx = MS R1 F (Z_to_bv 64 AFS_MALLOC_1) fc None m1 (seg_rom asegs) /\ rfull R1
                  /\ rtbl W0 R1 RTQ1 /\ PropExec.getr R1 2 = Z_to_bv 64 ((spz - 192) - (spz - 192) mod 32)
                  /\ PropExec.getr R1 9 = PropExec.getr R1 2
                  /\ ftbl W0 spz m1 TS0 /\ P0w m1 /\ mem_inv asegs m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APUT_CSEQ) fc None m0 (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    pose proof p_ranges as (R1' & R2' & R3').
    assert (RF0 : rfull (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)) by apply rfull_mkR.
    assert (HRT : rtbl W0 (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) RTQ0).
    { unfold rtbl, RTQ0. repeat constructor; cbn [fst snd]; [exact Ha0 | exact Ha1 | exact Ha2]. }
    assert (HSF : ftbl W0 spz m0 []) by constructor.
    assert (HP : P0w m0) by (split; [apply munch_refl | apply wmono_refl]).
    unfold APUT_CSEQ.
    dkrun0 HRT HSF HP MI0 600%nat [AFS_MALLOC_1].
    { constructor. }
    intros R1 m1 RF1 HRT1 HTS1 HP1 HMI1 MU1 WM1.
    lazymatch type of HTS1 with ftbls _ _ ?T =>
      let l := eval vm_compute in T in
      let E := fresh "E" in assert (E : T = l) by (vm_compute; reflexivity); rewrite E in HTS1; clear E end.
    apply Forall_cons_iff in HTS1 as [HSF1 _]. cbn [fst snd] in HSF1. cbn [s_pc].
    apply evt_done. exists R1, m1. split; [reflexivity|]. split; [exact RF1|].
    split; [apply (rtbl_sub _ _ _ _ HRT1); vm_compute; reflexivity|].
    split.
    { rewrite (rtbl_In W0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). cbn [edenot].
      change (ev (wenv W0) 33) with sp.
      assert (EA : alu64 ALU_ADD sp (Z_to_bv 64 (-192)) = Z_to_bv 64 (spz - 192)).
      { rewrite <- (Z_to_bv_bv_unsigned sp) at 1. rewrite w_addm by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia).
        f_equal; clear; lia. }
      rewrite EA. rewrite pq_mul32 by (clear - R1' R2' R3'; unfold ADS_STACK in *; lia). reflexivity. }
    split.
    { rewrite (rtbl_In W0 R1 _ 9%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
      rewrite (rtbl_In W0 R1 _ 2%bv (EMd M_MUL (ELit 32) (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-192))) (ELit 5))) HRT1
                ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)). reflexivity. }
    split; [apply (ftbl_sub _ _ _ _ _ HSF1); vm_compute; reflexivity|].
    split; [exact HP1 | exact HMI1].
  Qed.

  Lemma new_frame1 : forall LFx m ff fp, as_RFS H ((1, ff, fp) :: LFx) m -> obj_inframe LFx ds DS_SIZE ->
    fresh_frame H LFx 1 ff fp
    /\ (ff + 128 <= ds \/ ds + DS_SIZE <= ff) /\ (fp + 1 <= ds \/ ds + DS_SIZE <= fp)
    /\ (hull_hi (ds + DS_SIZE) <= ff \/ ff + 128 <= hull_lo ds).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros LFx m ff fp RF DSx.
    destruct (ah_RFS_range H HHb _ _ RF) as [FO FR].
    pose proof (FR (1, ff, fp) (or_introl eq_refl)) as (K1 & K2 & K3 & (K4 & K5) & K6).
    cbn [ff_class ff_addr ff_flag fst snd] in K1, K2, K3, K4, K5, K6. unfold fsz in K3. change (64 * 2 ^ 1) with 128 in K3.
    pose proof (ah_RFS_nodup H HHb _ _ RF) as ND. cbn [map ff_addr fst snd] in ND. apply NoDup_cons_iff in ND as [NI _].
    assert (DJ : forall f, In f LFx -> (ff + 128 <= ff_addr f \/ ff_addr f + fsz (ff_class f) <= ff) /\ fp <> ff_flag f).
    { intros f Hf. assert (Hne : ff <> ff_addr f) by (intros E; apply NI; rewrite E; apply in_map; exact Hf).
      destruct (ah_RFS_disj H HHb _ _ (1, ff, fp) f RF (or_introl eq_refl) (or_intror Hf) Hne) as [D1 D2].
      cbn [ff_addr ff_class ff_flag fst snd] in D1, D2. unfold fsz in D1 at 1. change (64 * 2 ^ 1) with 128 in D1. split; [exact D1 | exact D2]. }
    destruct DSx as (f & Hf & F1 & F2).
    pose proof (FR f (or_intror Hf)) as (L1 & L2 & L3 & (L4 & L5) & L6).
    assert (FM : fsz (ff_class f) mod 64 = 0) by (unfold fsz; rewrite Z.mul_comm; apply Z_mod_mult).
    destruct (DJ f Hf) as [D1 D2]. pose proof ds_facts as (_ & _ & _ & DS8 & _).
    unfold AFS_HDR, AFS_FLAGS, DS_SIZE in *.
    split.
    { split; [exact (FR (1, ff, fp) (or_introl eq_refl)) | split; [exact FO|]]. intros g Hg. destruct (DJ g Hg) as [E1 E2].
      split; [unfold fsz at 1; change (64 * 2 ^ 1) with 128; exact E1 | exact E2]. }
    split; [clear - D1 F1 F2; lia|]. split; [clear - K6 L2 F1 F2; lia|].
    unfold hull_lo, hull_hi. clear - D1 F1 F2 L4 FM K4 DS8. Z.div_mod_to_equations. lia.
  Qed.

  Lemma mk_qg1 : forall ff fp spa, fresh_frame H LF 1 ff fp ->
    (ff + 128 <= ds \/ ds + DS_SIZE <= ff) -> (fp + 1 <= ds \/ ds + DS_SIZE <= fp) ->
    (hull_hi (ds + DS_SIZE) <= ff \/ ff + 128 <= hull_lo ds) ->
    spa mod 32 = 0 -> spz - 208 <= spa <= spz - 192 ->
    qg1 H sp ds p n fl lo ff fp spa.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff fp spa (FR & FO & _) D1 D2 D3 A1 A2.
    pose proof ds_facts as (_ & _ & DSO & DS8 & _ & DSH & F3 & F4 & DSM & FL & _).
    constructor.
    - split; [exact CEIL | exact LO].
    - split; [exact SP16 | exact SPHI].
    - split; [exact A1 | exact A2].
    - split; [exact DSO | split; [exact DS8 | split; [exact DSH | exact DSM]]].
    - split; [clear - F3; unfold AFS_HDR in F3; lia | exact F4].
    - exact PN.
    - exact FL.
    - split; [exact FR | exact FO].
    - split; [exact D1 | split; [exact D2 | exact D3]].
  Qed.

  Definition WA (ff fp spa : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16); (ds + 256, ds + 260)].

  Definition WB (ff fp ff2 fp2 : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16); (ds + 256, ds + 260);
     (fp2, fp2 + 1); (ff2, ff2 + 128); (sh ff2, sh ff2 + 16); (ds + 136, ds + 144)].

  Lemma wa_keep : forall ff fp spa m, fresh_frame H LF 1 ff fp ->
    (ff + 128 <= ds \/ ds + DS_SIZE <= ff) -> (fp + 1 <= ds \/ ds + DS_SIZE <= fp) ->
    (hull_hi (ds + DS_SIZE) <= ff \/ ff + 128 <= hull_lo ds) ->
    munch (WA ff fp spa) m0 m -> wmono asegs m0 m ->
    addressable m ds DS_SIZE /\ wr_at asegs m ds DS_SIZE /\ shvis m ds (ds + DS_SIZE) /\ dsf ds fl m /\ LINV_P5 m /\ ACONST m
    /\ stk asegs m lo spz /\ CRep.fld ASEGS m (ds + 136) 8 0.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff fp spa m (FR & FO & _) D1 D2 D3 MU WM. unfold WA in *.
    pose proof FO as (B1 & B2 & B3 & B4). pose proof FR as (K1 & K2 & K3 & (K4 & K5) & K6).
    unfold fsz in K3. change (64 * 2 ^ 1) with 128 in K3.
    pose proof aceil_facts as ((A1 & A2) & A3 & A4). pose proof p_ranges as (R1 & R2 & R3).
    pose proof ds_facts as (DSA & DSW & DSO & DS8 & DS0 & DSH & F3 & F4 & DSM & FL & FIL & LEN0 & DF & W0' & _).
    pose proof DSO as (O1 & O2 & O3).
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    assert (SH : 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) <= sh ds /\ sh ds + 49 <= sh (as_FSB H + AFS_SIZE)
                 /\ sh (as_FSB H) <= sh ff /\ sh ff + 16 <= sh (as_FSB H + AFS_SIZE) /\ sh (as_FSB H + AFS_SIZE) + 2048 <= sh spz
                 /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
                 /\ (sh ff + 16 <= sh ds \/ sh ds + 49 <= sh ff)
                 /\ sh ds - 8 <= sh (hull_lo ds) /\ sh (hull_hi (ds + DS_SIZE)) <= sh ds + 57
                 /\ (sh ff + 16 <= sh (hull_lo ds) \/ sh (hull_hi (ds + DS_SIZE)) <= sh ff)).
    { unfold DS_SIZE in *. clear - B1 B2 F3 F4 K2 K3 K4 R2 R3 A2 DS8 D1 D3 CEIL LO SPHI.
      unfold sh, hull_lo, hull_hi, ASHADOW_BASE, AFS_SIZE, AFS_HDR, AIMG_TOP, ADS_STACK, AAPP_HI in *. Z.div_mod_to_equations. lia. }
    destruct SH as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
    unfold DS_SIZE, ADS_STACK, AFS_HDR, AFS_FLAGS, AFS_SIZE, ALOWSH_LO, AHI_LO, AIMG_TOP, AAPP_HI in *.
    assert (DSH49 : disjoint_from (WA ff fp spa) (sh ds) 49).
    { unfold WA, AFS_FLAGS. cbn [disjoint_from]. clear - S1 S2 S3 S6 S7 S8 S9 R2 B4' F3 F4 K2 K3 K6 CEIL LO. lia. }
    assert (DSHU : disjoint_from (WA ff fp spa) (sh (hull_lo ds)) (sh (hull_hi (ds + 392)) - sh (hull_lo ds))).
    { unfold WA, AFS_FLAGS. cbn [disjoint_from]. clear - S1 S2 S3 S6 S7 S8 S10 S11 S12 R2 B4' F3 F4 K2 K3 K6 CEIL LO. lia. }
    split; [eapply addressable_transport; [exact DSA | exact MU | exact WM | exact DSH49]|].
    split; [eapply wr_at_transport; [exact DSW | exact WM]|].
    split; [eapply shvis_transport; [exact DSV | exact MU | exact WM | exact DSHU]|].
    split.
    { eapply LbB_PqK.dsf_keep; [exact DF | exact MU | exact WM |]. unfold LbB_PqK.DSF_FIELDS, WA, AFS_FLAGS.
      clear - R2 CEIL LO D1 D2 K6 F3 F4 B2 B4' S1 S2 S4 S5 S6 S7. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from]; lia. }
    split.
    { eapply LINV_P5_cl; [exact LV0|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by (clear - Ha; lia).
      unfold aimg_client, AIMG_LO, AIMG_TOP in Hc. unfold WA, AFS_FLAGS. apply LbB_PqK.outside_of.
      clear - Hc R2 R3 CEIL LO B1 K2 K6 F3 S1 S4. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
    split.
    { eapply ACONST_frame; [exact AC0 | exact MU | exact WM |]. unfold WA.
      repeat apply Forall_cons; try apply Forall_nil.
      - apply LbB_DPdK.aconst_ok_hi. clear - R2 R3 CEIL LO. lia.
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact B4 | clear; lia | clear; lia].
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact B4 | clear - K6; lia | clear - K6; lia].
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact B4 | clear - K2; lia | exact K3].
      - apply LbB_DPdK.aconst_ok_hi. clear - S1 S4. lia.
      - apply (aconst_ok_app (as_FSB H) 0xb09000); [exact B4 | clear - F3; lia | clear - F4; lia]. }
    split.
    { eapply LbB_PqK.stk_keep; [exact STK | exact MU | exact WM | clear - CEIL R3; unfold AIMG_TOP; lia]. }
    eapply (LbB_DRep.fld_ag m0 m (fun x => ds + 136 <= x < ds + 136 + 8)); [clear - F3 B1; lia | clear - F4 B2 A2; lia | intros x Hx; exact Hx | | exact W0'].
    intros a Ha. apply MU. rewrite unsigned_lit by (clear - Ha F3 F4 B1 B2 A2; lia). unfold WA, AFS_FLAGS. cbn [outside].
    clear - Ha R2 R3 CEIL LO D1 D2 K6 F3 F4 B2 B4' S1 S2 S4 S5 S6 S7. lia.
  Qed.

  Lemma qf1_keep_gen : forall ff fp W m m', qf1 sp ds fl lo ff fp m -> munch W m m' -> wmono asegs m m' ->
    Forall aconst_ok W -> (forall a, aimg_client a -> outside W a) -> Forall (fun iv => AIMG_TOP <= fst iv) W ->
    disjoint_from W (sh ds) (nsh DS_SIZE) ->
    disjoint_from W (sh (hull_lo ds)) (sh (hull_hi (ds + DS_SIZE)) - sh (hull_lo ds)) ->
    Forall (fun ak => disjoint_from W (ds + fst ak) (snd ak)) LbB_PqK.DSF_FIELDS ->
    qf1 sp ds fl lo ff fp m'.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff fp W m m' Q MU WM HA HI HT D1 D2 D3. destruct Q as [AC LV ST DA DW DV DF FW HW LW].
    constructor.
    - eapply ACONST_frame; [exact AC | exact MU | exact WM | exact HA].
    - eapply LINV_P5_cl; [exact LV|]. intros a Ha Hc. unfold wa. apply MU. rewrite unsigned_lit by lia. apply HI. exact Hc.
    - eapply stk_transport; [exact ST | exact MU | exact WM |]. intros x Hx. right.
      pose proof ST as (T1 & T2 & T3). destruct (T3 x Hx) as [HV _]. pose proof (WM (wa x) HV) as HV'.
      pose proof aceil_facts as ((A1 & A2) & _).
      assert (HX : AIMG_TOP <= bv_unsigned (wa x)) by (unfold wa; rewrite unsigned_lit by lia; unfold AIMG_TOP; lia).
      rewrite (BakeStackRep.wview_high m' (wa x) HX) in HV'.
      destruct (m' (wa x)) as [b|] eqn:Eb; [exists b; reflexivity | contradiction].
    - eapply addressable_transport; [exact DA | exact MU | exact WM | exact D1].
    - eapply wr_at_transport; [exact DW | exact WM].
    - eapply shvis_transport; [exact DV | exact MU | exact WM | exact D2].
    - eapply LbB_PqK.dsf_keep; [exact DF | exact MU | exact WM | exact D3].
    - eapply wr_at_transport; [exact FW | exact WM].
    - eapply wr_at_transport; [exact HW | exact WM].
    - eapply wr_at_transport; [exact LW | exact WM].
  Qed.

  Lemma fr_place : forall LFx ff fp, fresh_frame H LFx 1 ff fp ->
    as_FSB H + 0x9000 <= ff /\ ff + 128 <= as_FSB H + 0xb09000 /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp + 1 <= as_FSB H + 0x9000
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + 0xb09000 <= aceil /\ aceil + 16384 <= spz /\ spz <= 2 ^ 47
    /\ (as_FSB H + 0xb09000 <= 0x7fff7000 \/ 0x10007fff8000 <= as_FSB H) /\ aapp (as_FSB H) AFS_SIZE
    /\ 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) + 0x1200 <= sh ff /\ sh ff + 16 <= sh (as_FSB H + 0xb09000)
    /\ sh (as_FSB H + 0xb09000) + 2048 <= sh spz /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
    /\ sh (as_FSB H + 0xb09000) <= sh aceil /\ 0x7fff7f800000 <= aceil.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros LFx ff fp (FFR & FSB_OK & _).
    pose proof FFR as (K1 & K2 & K3 & (K4 & K5) & K6). unfold fsz in K3. change (64 * 2 ^ 1) with 128 in K3.
    pose proof FSB_OK as (B1 & B2 & B3 & B4). pose proof aceil_facts as ((A1 & A2) & A3 & A4). pose proof p_ranges as (R1 & R2 & R3).
    assert (B4' : as_FSB H + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= as_FSB H).
    { clear - B4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in *. destruct B4; [left | right]; lia. }
    unfold AFS_HDR, AFS_FLAGS, AFS_SIZE, AIMG_TOP, ALOWSH_LO, AHI_LO, ADS_STACK, AAPP_HI in *.
    assert (SH : 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) + 0x1200 <= sh ff /\ sh ff + 16 <= sh (as_FSB H + 0xb09000)
                 /\ sh (as_FSB H + 0xb09000) + 2048 <= sh spz /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
                 /\ sh (as_FSB H + 0xb09000) <= sh aceil).
    { clear - K2 K3 B1 B2 R2 R3 SPHI. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    repeat match goal with |- _ /\ _ => split end; try assumption; clear B4 B4'; lia.
  Qed.

  Lemma wa_laws : forall LBx LFx ff fp spa, fresh_frame H LF 1 ff fp -> In (1, ff, fp) LFx -> obj_inframe LFx ds DS_SIZE ->
    spz - 208 <= spa ->
    Forall (aclient_write_ok H LBx) (WA ff fp spa) /\ Forall stack0_ok (WA ff fp spa) /\ Forall aconst_ok (WA ff fp spa)
    /\ (forall a, aimg_client a -> outside (WA ff fp spa) a) /\ Forall (fun iv => AIMG_TOP <= fst iv) (WA ff fp spa).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros LBx LFx ff fp spa FR I1 OD SPA.
    pose proof (fr_place LF ff fp FR) as (K2 & K3 & K4 & K6 & K6' & B1 & B2 & R2 & R3 & B4 & AP & S1 & S2 & S3 & S4 & S5 & S6 & S7 & A1).
    pose proof ds_facts as (_ & _ & DSO & _ & _ & DSH & F3 & F4 & DSM & _). unfold AFS_HDR, AFS_SIZE, DS_SIZE in F3, F4, DSM.
    assert (SA : ALOWSH_LO <= sh aceil) by (clear - A1; unfold sh, ASHADOW_BASE, ALOWSH_LO in *; Z.div_mod_to_equations; lia).
    unfold WA, AFS_FLAGS. split; [|split; [|split; [|split]]].
    - repeat apply Forall_cons; try apply Forall_nil; unfold aclient_write_ok; cbn [fst snd].
      + left. clear - R2 B2 SPA. lia.
      + right; right; right; right; left. clear. unfold AFS_SIZE. lia.
      + right; right; right; right; left. clear - K6 K6'. unfold AFS_SIZE in *. lia.
      + right; right; right; right; left. clear - K2 K3. unfold AFS_SIZE in *. lia.
      + right; right; right; right; right; left. clear - S2 S3 S1. unfold AFS_SIZE. unfold sh in *. lia.
      + right; right; right; right; left. clear - F3 F4. unfold AFS_SIZE. lia.
    - repeat apply Forall_cons; try apply Forall_nil; unfold stack0_ok; cbn [fst snd].
      + left. clear - R2 B2 SPA A1. unfold AHI_LO in *. lia.
      + clear - B4 SA. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA K6 K6'. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + clear - B4 SA K2 K3. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
      + right. clear - S3 S7. lia.
      + clear - B4 SA F3 F4. unfold ALOWSH_LO, AHI_LO in *. destruct B4; [right | left]; lia.
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - R2 R3 B2 A1 SPA. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear; lia | clear; unfold AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - K6; lia | clear - K6'; unfold AFS_SIZE in *; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - K2; lia | clear - K3; unfold AFS_SIZE; lia].
      + apply LbB_DPdK.aconst_ok_hi. clear - S1 S2. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - F3; lia | clear - F4; unfold AFS_SIZE; lia].
    - intros a Ha. unfold aimg_client in Ha. apply LbB_PqK.outside_of.
      clear - Ha R2 B1 B2 K2 K6 F3 S1 S2 SPA A1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - R2 B1 B2 K2 K6 F3 S1 S2 SPA A1; unfold AIMG_TOP; lia.
  Qed.

  Definition SMW (spc ff fp : Z) : list (Z * Z) :=
    [(spc - AFS_STACK, spc); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 128); (sh ff, sh ff + 16)].

  Record pq_st1 (ff1 fp1 spa : Z) (R : bvmap 5 word) (m : mem) : Prop := PQ_ST1 {
    t1_g1 : qg1 H sp ds p n fl lo ff1 fp1 spa;
    t1_fr : fresh_frame H LF 1 ff1 fp1;
    t1_rf : rfull R;
    t1_rt : rtbl (LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) R RTQ2;
    t1_ts : ftbl (LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) spz m TS0;
    t1_td : ftbl (LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) ds m [(256, 4%nat, ELit fill)];
    t1_tf : ftbl (LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) ff1 m FT20;
    t1_q1 : qf1 sp ds fl lo ff1 fp1 m;
    t1_mi : mem_inv asegs m;
    t1_rfs : as_RFS H ((1, ff1, fp1) :: LF) m;
    t1_w0 : CRep.fld ASEGS m (ds + 136) 8 0;
    t1_mu : munch (WA ff1 fp1 spa) m0 m;
    t1_wm : wmono asegs m0 m
  }.

  Lemma pq_s1 :
    evt asegs (fun msx => exists ff1 fp1 spa R m, msx = MS R F (Z_to_bv 64 APQ_P2) fc None m (seg_rom asegs) /\ pq_st1 ff1 fp1 spa R m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APUT_CSEQ) fc None m0 (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    pose proof p_ranges as (R1' & R2' & R3').
    pose proof ds_facts as (DSA & DSW & DSO & DS8 & DS0 & DSH & F3 & F4 & DSM & FL & FIL & LEN0 & DF & W00 & FI0).
    eapply evt_cut; [apply pq_p1|].
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & K2e & K9e & HTS1 & HP1 & HMI1).
    destruct (p0_keep m1 HP1 HMI1) as (AC1 & LV1 & ST1). destruct HP1 as [MU1 WM1].

    assert (K1 : PropExec.getr R1 1 = Z_to_bv 64 0xf6318).
    { apply (rtbl_In W0 R1 _ 1%bv (ELit 0xf6318) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K4 : PropExec.getr R1 4 = tp).
    { apply (rtbl_In W0 R1 _ 4%bv (EVar 50) HRT1). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (SPA0 : exists spa, spa = (spz - 192) - (spz - 192) mod 32) by (eexists; reflexivity).
    destruct SPA0 as [spa Espa]. rewrite <- Espa in K2e.
    assert (SPA : spz - 208 <= spa <= spz - 192 /\ spa mod 32 = 0).
    { subst spa. clear - SP16 R1' R2'. unfold ADS_STACK in *. Z.div_mod_to_equations. lia. }
    clear Espa. destruct SPA as [SPA SPA32].
    assert (Us : bv_unsigned (PropExec.getr R1 2) = spa)
      by (rewrite K2e; apply unsigned_lit; clear - SPA R1' R2' R3'; unfold ADS_STACK in *; lia).

    assert (RFS1 : as_RFS H LF m1).
    { eapply (ah_RFS_frame H HHb); [exact RFS0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd].
      destruct (ah_RFS_range H HHb LF m0 RFS0) as [(B1 & B2 & B3 & B4) _].
      clear - R1' R2' R3' B2. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, ADS_STACK, AFS_SIZE in *. lia. }
    assert (RH1 : as_RHEAP H sA LB m1).
    { eapply (ah_RHEAP_frame H HHb); [exact RH0 | exact MU1 | exact WM1 |].
      apply Forall_cons; [| apply Forall_nil]. left. cbn [fst snd]. clear - R2'. unfold ADS_STACK in *. lia. }
    pose proof (ah_thr H HHb sA LB m1 RH1) as THR1.
    assert (LFn1 : (length LF < AFS_MAXLIVE_BP)%nat) by (clear - LFn; lia).
    rewrite (MS_full_eq R1 F _ fc m1 _ RF1).
    eapply evt_cut.
    { apply (SM1 (PropExec.getr R1 1) (PropExec.getr R1 2) (PropExec.getr R1 3) (PropExec.getr R1 4) (PropExec.getr R1 5)
               (PropExec.getr R1 6) (PropExec.getr R1 7) (PropExec.getr R1 8) (PropExec.getr R1 9) (PropExec.getr R1 10)
               (PropExec.getr R1 11) (PropExec.getr R1 12) (PropExec.getr R1 13) (PropExec.getr R1 14) (PropExec.getr R1 15)
               (PropExec.getr R1 16) (PropExec.getr R1 17) (PropExec.getr R1 18) (PropExec.getr R1 19) (PropExec.getr R1 20)
               (PropExec.getr R1 21) (PropExec.getr R1 22) (PropExec.getr R1 23) (PropExec.getr R1 24) (PropExec.getr R1 25)
               (PropExec.getr R1 26) (PropExec.getr R1 27) (PropExec.getr R1 28) (PropExec.getr R1 29) (PropExec.getr R1 30)
               (PropExec.getr R1 31) F fc m1 LF lo RFS1 LFn1).
      - rewrite Us. destruct (stk_split asegs m1 lo spa spz ST1 ltac:(clear - LO SPA; unfold ADS_STACK in *; lia)) as [S _]. exact S.
      - exact CEIL.
      - rewrite Us. clear - LO SPA. unfold AFS_STACK, ADS_STACK in *. lia.
      - exact HMI1.
      - rewrite K4. exact TP.
      - exact AC1.
      - exact THR1. }
    intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff1 & fp1 & junk1 & junk2
                & E2 & MU2 & WM2 & MI2 & ST2 & RF2 & FRC & SHF & FLG & AC2).
    subst ms2. rewrite K1, ret_pc_even; [| clear; lia | reflexivity]. rewrite fsz_1, fshn_1 in MU2.
    lazymatch goal with |- evt _ _ (MS ?RR _ _ _ _ _ _) => remember RR as R2 eqn:ER2 end.
    assert (RF2' : rfull R2) by (rewrite ER2; apply rfull_mkR).
    destruct (new_frame1 LF m2 ff1 fp1 RF2 DSin) as (FRESH1 & FD1 & FD2 & FD3).
    pose proof (mk_qg1 ff1 fp1 spa FRESH1 FD1 FD2 FD3 SPA32 SPA) as G1.
    pose proof (fr_place LF ff1 fp1 FRESH1) as (Q2 & Q3 & Q4 & Q6 & Q6' & B1 & B2 & _ & _ & B4 & AP & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & A1).

    rewrite Us in MU2, ST2.
    assert (MUA : munch (WA ff1 fp1 spa) m0 m2).
    { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of; unfold WA.
      - apply Forall_cons; [| apply Forall_nil]. exists (spz - 16384, spz). split; [left; reflexivity | cbn; clear; lia].
      - apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - SPA; unfold AFS_STACK; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp1, fp1 + 1); split; [right; right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff1, ff1 + 128); split; [right; right; right; left; reflexivity | cbn; unfold fsz; cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff1, sh ff1 + 16); split; [right; right; right; right; left; reflexivity | cbn; unfold fshn; cbn; clear; lia]|].
        apply Forall_nil. }
    assert (WMA : wmono asegs m0 m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
    destruct (wa_keep ff1 fp1 spa m2 FRESH1 FD1 FD2 FD3 MUA WMA) as (DSA2 & DSW2 & DSV2 & DF2 & LV2 & _ & ST2' & W02).
    assert (FRW2 : wr_at asegs m2 ff1 128) by (destruct FRC as [_ W]; exact W).
    assert (FSW2 : wr_at asegs m2 (sh ff1) 16) by (destruct SHF as (_ & _ & _ & W); exact W).
    assert (FLW2 : wr_at asegs m2 fp1 1) by (destruct FLG as [_ W]; exact W).
    assert (Q1 : qf1 sp ds fl lo ff1 fp1 m2).
    { constructor; [exact AC2 | exact LV2 | exact ST2' | exact DSA2 | exact DSW2 | exact DSV2 | exact DF2 | exact FRW2 | exact FSW2 | exact FLW2]. }

    assert (FI2 : CRep.fld ASEGS m2 (ds + 256) 4 fill).
    { unfold AFS_HDR, AFS_SIZE, DS_SIZE, AAPP_HI in F3, F4, DSH.
      eapply (LbB_DRep.fld_ag m0 m2 (fun x => ds + 256 <= x < ds + 256 + 4)); [clear - DS0; lia | clear - DSH; cbn; lia | intros x Hx; exact Hx | | exact FI0].
      intros a Ha. rewrite (MU2 (Z_to_bv 64 a)); [apply MU1|]; rewrite unsigned_lit by (clear - Ha DS0 DSH; lia); cbn [outside].
      - clear - Ha F4 B2 R2'. unfold ADS_STACK in *. lia.
      - clear - Ha F3 F4 B2 R2' SPA Q2 Q6 FD1 FD2 Z1 Z2 Z3 Z4 Z5 B4. unfold DS_SIZE, ADS_STACK, AFS_STACK, AFS_FLAGS in *. lia. }
    apply evt_done. exists ff1, fp1, spa, R2, m2. split; [reflexivity|].

    set (WW := LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa).
    assert (EWW : WW = W0 ++ [Z_to_bv 64 ff1; Z_to_bv 64 fp1; Z_to_bv 64 fl; Z_to_bv 64 spa]) by reflexivity.
    assert (KP : forall r, In r KEPT -> PropExec.getr R2 r = PropExec.getr R1 r).
    { intros r Hr. rewrite ER2. apply (getr_mkR_keptR R1); [exact (eq_sym K1) | exact Hr]. }
    assert (HRT2 : rtbl WW R2 RTQ2).
    { assert (HK : rtbl WW R2 (keptk RTQ1)).
      { rewrite EWW. apply rtbl_wext; [vm_compute; reflexivity|].
        apply (rtbl_keep W0 R1 R2 _ KEPT); [apply rtbl_keptk; exact HRT1 | apply rsub_keptk | exact KP]. }
      assert (HX : rtbl WW R2 [(2%bv, EVar 54); (9%bv, EVar 54); (10%bv, EVar 51)]).
      { unfold rtbl. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
        - rewrite (KP 2%bv ltac:(apply inr_In; vm_compute; reflexivity)), K2e. subst WW. evWW. reflexivity.
        - rewrite (KP 9%bv ltac:(apply inr_In; vm_compute; reflexivity)), K9e, K2e. subst WW. evWW. reflexivity.
        - rewrite ER2. subst WW. cbn [PropExec.getr mkR]. evWW. reflexivity. }
      apply (rtbl_sub _ _ _ _ (rtbl_app _ _ _ _ HK HX)). vm_compute. reflexivity. }

    assert (HTS2 : ftbl WW spz m2 TS0).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch W0 spz m1 m2 _ _ (-104) 0); [exact HTS1 | exact MU2 | exact WM2 | vm_compute; reflexivity |].
      cbn [disjoint_from]. clear - SPA Q2 Q3 Q6 Q6' B2 R2' R3' Z1 Z2 Z3 Z4 Z5 Z6. unfold AFS_STACK, AFS_FLAGS, ADS_STACK in *. lia. }
    assert (HTD2 : ftbl WW ds m2 [(256, 4%nat, ELit fill)]).
    { apply ftbl_of_fld; [exact FI2 | eapply wr_at_sub; [exact DSW2 | clear; lia | unfold DS_SIZE; clear; cbn; lia | clear; cbn; lia]
                         | clear - DS0; lia | unfold AFS_HDR, AFS_SIZE, DS_SIZE, AAPP_HI in F3, F4, DSH; clear - DSH; cbn; lia]. }
    assert (HTF2 : ftbl WW ff1 m2 FT20).
    { apply (proj1 (rw_cells_app asegs m2 ff1 [CB 24 junk1] _)) in FRC as [_ FRC1].
      apply (proj1 (rw_cells_app asegs m2 _ [C8 (PropExec.getr R1 2)] _)) in FRC1 as [C24 FRC2].
      apply (proj1 (rw_cells_app asegs m2 _ [CB (Z.to_nat (fsz 1 - 40)) junk2] _)) in FRC2 as [_ C120].
      cbn [cells_size csize Nat.add] in C24, C120.
      replace (ff1 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat (Z.to_nat (fsz 1 - 40) + 0)) with (ff1 + 120) in C120 by (unfold fsz; clear; lia).
      replace (ff1 + Z.of_nat 24) with (ff1 + 24) in C24 by (clear; lia).
      unfold FT20. apply (ftbl_app WW ff1 m2 [(24, 8%nat, EVar 54)] [(120, 8%nat, EVar 52)]).
      - apply ftbl_of_C8. subst WW. evWW. rewrite <- K2e. exact C24.
      - apply ftbl_of_C8. subst WW. evWW. exact C120. }
    constructor; [exact G1 | exact FRESH1 | exact RF2' | exact HRT2 | exact HTS2 | exact HTD2 | exact HTF2 | exact Q1 | exact MI2 | exact RF2
                | exact W02 | exact MUA | exact WMA].
  Qed.

  Notation W1' ff1 fp1 spa := (LbB_PqK.W1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa) (only parsing).
  Notation W2' ff1 fp1 spa ff2 fp2 := (LbB_PqK2.W2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ds p n fl ff1 fp1 spa ff2 fp2) (only parsing).

  Record pq_st2 (ff1 fp1 spa ff2 fp2 : Z) (R : bvmap 5 word) (m : mem) : Prop := PQ_ST2 {
    t2_g1 : qg1 H sp ds p n fl lo ff1 fp1 spa;
    t2_g2 : qg2 H ds ff1 fp1 ff2 fp2;
    t2_fr1 : fresh_frame H LF 1 ff1 fp1;
    t2_fr2 : fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2;
    t2_rf : rfull R;
    t2_rt : rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQ3;
    t2_ts : ftbl (W2' ff1 fp1 spa ff2 fp2) spz m TS0;
    t2_ta : ftbl (W2' ff1 fp1 spa ff2 fp2) spa m AT2;
    t2_td : ftbl (W2' ff1 fp1 spa ff2 fp2) ds m DT3;
    t2_tf2 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff2 m FT30;
    t2_tf1 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m FT2;
    t2_th1 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m HT2;
    t2_q1 : qf1 sp ds fl lo ff1 fp1 m;
    t2_q2 : qx2 ff2 fp2 m;
    t2_mi : mem_inv asegs m;
    t2_rfs : as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m;
    t2_fill : CRep.fld ASEGS m (ds + 256) 4 32;
    t2_mu : munch (WB ff1 fp1 ff2 fp2) m0 m;
    t2_wm : wmono asegs m0 m
  }.

  Lemma sm2_keep : forall ff1 fp1 spa ff2 fp2 m m', qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    qf1 sp ds fl lo ff1 fp1 m -> munch (SMW (spa - 192) ff2 fp2) m m' -> wmono asegs m m' -> qf1 sp ds fl lo ff1 fp1 m'.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 m m' G1 G2 FR2 Q MU WM.
    pose proof (fr_place _ ff2 fp2 FR2) as (Q2 & Q3 & Q4 & Q6 & Q6' & B1 & B2 & R2 & R3 & B4 & AP & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & A1).
    pose proof ds_facts as (_ & _ & DSO & DS8 & DS0 & DSH & F3 & F4 & DSM & _). unfold AFS_HDR, AFS_SIZE, DS_SIZE, AAPP_HI in F3, F4, DSH, DSM.
    destruct G1 as [_ _ [SPA32 SPA] _ _ _ _ _ _]. destruct G2 as [_ (FD1 & FD2 & FD3) _].
    assert (SH : sh (as_FSB H) + 0x1200 <= sh ds /\ sh ds + 49 <= sh (as_FSB H + 0xb09000) /\ (sh ff2 + 16 <= sh ds \/ sh ds + 49 <= sh ff2)
                 /\ sh ds - 8 <= sh (hull_lo ds) /\ sh (hull_hi (ds + 392)) <= sh ds + 57
                 /\ (sh ff2 + 16 <= sh (hull_lo ds) \/ sh (hull_hi (ds + 392)) <= sh ff2)).
    { unfold DS_SIZE in *. clear - F3 F4 DS8 FD1 FD3 Q4. unfold sh, hull_lo, hull_hi, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
    destruct SH as (S1 & S2 & S3 & S4 & S5 & S6).
    unfold DS_SIZE in FD1, FD2. unfold SMW, AFS_STACK, AFS_FLAGS in MU.
    eapply (qf1_keep_gen ff1 fp1 _ m m' Q MU WM).
    - repeat apply Forall_cons; try apply Forall_nil.
      + apply LbB_DPdK.aconst_ok_hi. clear - R2 R3 B2 A1 SPA. lia.
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear; lia | clear; unfold AFS_SIZE; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - Q6; lia | clear - Q6'; unfold AFS_SIZE in *; lia].
      + apply (aconst_ok_app (as_FSB H) AFS_SIZE); [exact AP | clear - Q2; lia | clear - Q3; unfold AFS_SIZE; lia].
      + apply LbB_DPdK.aconst_ok_hi. clear - Z1 Z2. lia.
    - intros a Ha. unfold aimg_client in Ha. apply LbB_PqK.outside_of.
      clear - Ha R2 B1 B2 Q2 Q6 Z1 Z2 SPA A1. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
    - repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; clear - R2 B1 B2 Q2 Q6 Z1 Z2 SPA A1; unfold AIMG_TOP; lia.
    - change (nsh DS_SIZE) with 49. cbn [disjoint_from]. clear - S1 S2 S3 Z1 Z2 Z3 Z4 Z5 Z6 R2 B4 F3 F4 Q2 Q3 Q6 Q6' SPA. lia.
    - unfold DS_SIZE. cbn [disjoint_from]. clear - S1 S2 S4 S5 S6 Z1 Z2 Z3 Z4 Z5 Z6 R2 B4 F3 F4 Q2 Q3 Q6 Q6' SPA. lia.
    - unfold LbB_PqK.DSF_FIELDS. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd disjoint_from];
        clear - R2 B2 B4 F3 F4 FD1 FD2 Q6 Z1 Z2 Z3 Z4 Z5 Z6 S1 SPA; lia.
  Qed.

  Lemma pq_s2 : forall ff1 fp1 spa R m, pq_st1 ff1 fp1 spa R m ->
    evt asegs (fun msx => exists ff2 fp2 R' m', msx = MS R' F (Z_to_bv 64 APQ_P3) fc None m' (seg_rom asegs) /\ pq_st2 ff1 fp1 spa ff2 fp2 R' m')
      (MS R F (Z_to_bv 64 APQ_P2) fc None m (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa R m ST. destruct ST as [G1 FRESH1 RF HRT HTS HTD HTF Q1 MI RFS1 W0m MUA WMA].
    pose proof p_ranges as (R1' & R2' & R3').
    pose proof ds_facts as (DSA & DSW & DSO & DS8 & DS0 & DSH & F3 & F4 & DSM & FL & FIL & LEN0 & DF & W00 & FI0).
    unfold AFS_HDR, AFS_SIZE, DS_SIZE, AAPP_HI in F3, F4, DSH, DSM.
    pose proof (fr_place LF ff1 fp1 FRESH1) as (FQ2 & FQ3 & FQ4 & FQ6 & FQ6' & B1 & B2 & _ & _ & B4 & AP & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & A1).
    pose proof G1 as G1'. destruct G1' as [_ _ [SPA32 SPA] _ _ _ _ _ (FD1 & FD2 & FD3)]. unfold DS_SIZE in FD1, FD2.

    assert (HTA : ftbl (W1' ff1 fp1 spa) spa m []) by constructor.
    assert (HTH : ftbl (W1' ff1 fp1 spa) (ff1 / 8) m []) by constructor.
    assert (FN : exists fneg : bool, fill = (if fneg then 4294967295 else 32)).
    { destruct FIL as [E|E]; [exists true | exists false]; rewrite E; reflexivity. }
    destruct FN as [fneg Efill]. rewrite Efill in HTD.
    assert (HTD' : ftbl (W1' ff1 fp1 spa) ds m (if fneg then DT2N else DT2S)) by (destruct fneg; exact HTD).
    eapply evt_cut.
    { eapply (q_p2 H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds p n fl lo ff1 fp1 spa G1 (c_p0 CTX) fneg m R m RF HRT HTA HTD' HTF HTH
                (conj Q1 (LbB_PqK.P1x_refl ds ff1 spa m)) MI). }
    intros ms3 (R3 & m3 & -> & RF3 & HRT3 & HTA3 & HTF3 & HTH3 & FI3 & [_ [MU3 WM3]] & MI3 & _ & _).
    pose proof (LbB_PqK.q1_keep H sp ds p n fl lo ff1 fp1 spa G1 m m3 Q1 (conj MU3 WM3) MI3) as QF3.
    assert (RFS3 : as_RFS H ((1, ff1, fp1) :: LF) m3).
    { eapply (LbB_PqK.RFS_step1 H HHbp sp ds p n fl lo ff1 fp1 spa G1 _ [] [] [] [] [] [] [] [] m m3 RFS1 (or_introl eq_refl)); [| exact MU3 | exact WM3].
      destruct DSin as (f & Hf & X1 & X2). exists f. split; [right; exact Hf | split; [exact X1 | exact X2]]. }
    assert (HTS3 : ftbl (W1' ff1 fp1 spa) spz m3 TS0).
    { eapply (ftbl_munch _ spz m m3 _ _ (-104) 0); [exact HTS | exact MU3 | exact WM3 | vm_compute; reflexivity |].
      unfold LbB_PqK.QW1. rewrite !Z.add_assoc, LbB_PqK.shb1_eq. cbn [disjoint_from].
      clear - SPA FQ2 FQ3 B2 R2' R3' Z1 Z2 Z3 Z4 Z5 Z6 F3 F4. unfold SHBASE, ADS_STACK in *. lia. }
    assert (MUA3 : munch (WA ff1 fp1 spa) m0 m3).
    { eapply munch_trans; [exact MUA|]. eapply munch_weaken; [| exact MU3]. apply sub_fp_of. unfold LbB_PqK.QW1, WA. rewrite !Z.add_assoc, LbB_PqK.shb1_eq.
      apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - SPA; lia]|].
      apply Forall_cons; [exists (ds + 256, ds + 260); split; [do 5 right; left; reflexivity | cbn; clear; lia]|].
      apply Forall_cons; [exists (ff1, ff1 + 128); split; [do 3 right; left; reflexivity | cbn; clear; lia]|].
      apply Forall_cons; [exists (sh ff1, sh ff1 + 16); split; [do 4 right; left; reflexivity | cbn; clear; unfold SHBASE; lia]|].
      apply Forall_nil. }
    assert (WMA3 : wmono asegs m0 m3) by (eapply wmono_trans; [exact WMA | exact WM3]).

    destruct (wa_laws LB ((1, ff1, fp1) :: LF) ff1 fp1 spa FRESH1 (or_introl eq_refl)
                ltac:(destruct DSin as (f & Hf & X1 & X2); exists f; split; [right; exact Hf | split; [exact X1 | exact X2]]) (proj1 SPA))
      as (WL1 & WL2 & WL3 & WL4 & WL5).
    assert (RH3 : as_RHEAP H sA LB m3) by (eapply (ah_RHEAP_frame H HHb); [exact RH0 | exact MUA3 | exact WMA3 | exact WL1]).
    pose proof (ah_thr H HHb sA LB m3 RH3) as THR3.
    assert (LFn3 : (length ((1%Z, ff1, fp1) :: LF) < AFS_MAXLIVE_BP)%nat).
    { clear - LFn. cbn [length]. eapply Nat.lt_le_trans; [| exact LFn]. rewrite Nat.add_comm. cbn. apply Nat.lt_succ_diag_r. }

    assert (K1 : PropExec.getr R3 1 = Z_to_bv 64 0xf6874).
    { apply (rtbl_In _ R3 _ 1%bv (ELit 0xf6874) HRT3). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K4 : PropExec.getr R3 4 = tp).
    { apply (rtbl_In _ R3 _ 4%bv (EVar 50) HRT3). apply LbB_DCtorK.inb_In'. vm_compute. reflexivity. }
    assert (K2 : PropExec.getr R3 2 = Z_to_bv 64 (spa - 192)).
    { rewrite (rtbl_In _ R3 _ 2%bv (EAlu ALU_ADD (EVar 54) (ELit (-192))) HRT3 ltac:(apply LbB_DCtorK.inb_In'; vm_compute; reflexivity)).
      evWW. rewrite w_addm by (clear - SPA R1' R2' R3'; unfold ADS_STACK in *; lia). reflexivity. }
    assert (Us : bv_unsigned (PropExec.getr R3 2) = spa - 192) by (rewrite K2; apply unsigned_lit; clear - SPA R1' R2' R3'; unfold ADS_STACK in *; lia).
    pose proof QF3 as FQ3'. destruct FQ3' as [AC3 LV3 ST3 _ DSW3 _ _ _ _ _].
    rewrite (MS_full_eq R3 F _ fc m3 _ RF3).
    eapply evt_cut.
    { apply (SM1 (PropExec.getr R3 1) (PropExec.getr R3 2) (PropExec.getr R3 3) (PropExec.getr R3 4) (PropExec.getr R3 5)
               (PropExec.getr R3 6) (PropExec.getr R3 7) (PropExec.getr R3 8) (PropExec.getr R3 9) (PropExec.getr R3 10)
               (PropExec.getr R3 11) (PropExec.getr R3 12) (PropExec.getr R3 13) (PropExec.getr R3 14) (PropExec.getr R3 15)
               (PropExec.getr R3 16) (PropExec.getr R3 17) (PropExec.getr R3 18) (PropExec.getr R3 19) (PropExec.getr R3 20)
               (PropExec.getr R3 21) (PropExec.getr R3 22) (PropExec.getr R3 23) (PropExec.getr R3 24) (PropExec.getr R3 25)
               (PropExec.getr R3 26) (PropExec.getr R3 27) (PropExec.getr R3 28) (PropExec.getr R3 29) (PropExec.getr R3 30)
               (PropExec.getr R3 31) F fc m3 ((1, ff1, fp1) :: LF) lo RFS3 LFn3).
      - rewrite Us. destruct (stk_split asegs m3 lo (spa - 192) spz ST3 ltac:(clear - LO SPA; unfold ADS_STACK in *; lia)) as [S _]. exact S.
      - exact CEIL.
      - rewrite Us. clear - LO SPA. unfold AFS_STACK, ADS_STACK in *. lia.
      - exact MI3.
      - rewrite K4. exact TP.
      - exact AC3.
      - exact THR3. }
    intros ms4 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m4 & ff2 & fp2 & junk1 & junk2
                & E4 & MU4 & WM4 & MI4 & ST4 & RF4 & FRC & SHF & FLG & AC4).
    subst ms4. rewrite K1, ret_pc_even; [| clear; lia | reflexivity]. rewrite fsz_1, fshn_1 in MU4. rewrite Us in MU4, ST4.
    lazymatch goal with |- evt _ _ (MS ?RR _ _ _ _ _ _) => remember RR as R4 eqn:ER4 end.
    assert (RF4' : rfull R4) by (rewrite ER4; apply rfull_mkR).
    assert (DSin1 : obj_inframe ((1, ff1, fp1) :: LF) ds DS_SIZE).
    { destruct DSin as (f & Hf & X1 & X2). exists f. split; [right; exact Hf | split; [exact X1 | exact X2]]. }
    destruct (new_frame1 _ m4 ff2 fp2 RF4 DSin1) as (FRESH2 & GD1 & GD2 & GD3).
    assert (G2 : qg2 H ds ff1 fp1 ff2 fp2).
    { constructor; [exact (proj1 FRESH2) | split; [exact GD1 | split; [exact GD2 | exact GD3]] |].
      destruct FRESH2 as (_ & _ & FX). destruct (FX (1, ff1, fp1) (or_introl eq_refl)) as [Y1 Y2]. cbn [ff_addr ff_class ff_flag fst snd] in Y1, Y2.
      rewrite fsz_1 in Y1. clear - Y1 Y2. lia. }
    pose proof (fr_place _ ff2 fp2 FRESH2) as (P2' & P3 & P4 & P6 & P6' & _ & _ & _ & _ & _ & _ & _ & Y2 & Y3 & _).
    pose proof G2 as G2'. destruct G2' as [_ (GD1' & GD2' & _) (G12 & G12')]. unfold DS_SIZE in GD1', GD2'.

    assert (QF4 : qf1 sp ds fl lo ff1 fp1 m4) by (eapply (sm2_keep ff1 fp1 spa ff2 fp2 m3 m4 G1 G2 FRESH2 QF3); [exact MU4 | exact WM4]).
    assert (X4 : qx2 ff2 fp2 m4).
    { constructor; [destruct FRC as [_ W]; exact W | destruct SHF as (_ & _ & _ & W); exact W | destruct FLG as [_ W]; exact W]. }

    set (WW := W2' ff1 fp1 spa ff2 fp2).
    assert (EWW : WW = (W1' ff1 fp1 spa) ++ [Z_to_bv 64 ff2; Z_to_bv 64 fp2]) by reflexivity.
    assert (SMD : forall A k, (A + k <= spa - 192 - 1024 \/ spa - 192 <= A) -> (A + k <= as_FSB H \/ as_FSB H + 0x1000 <= A) ->
                 (A + k <= fp2 \/ fp2 + 1 <= A) -> (A + k <= ff2 \/ ff2 + 128 <= A) -> (A + k <= sh ff2 \/ sh ff2 + 16 <= A) ->
                 disjoint_from (SMW (spa - 192) ff2 fp2) A k).
    { intros A k D1 D2 D3 D4 D5. unfold SMW, AFS_STACK, AFS_FLAGS. cbn [disjoint_from]. clear - D1 D2 D3 D4 D5. lia. }
    assert (HTS4 : ftbl WW spz m4 TS0).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch _ spz m3 m4 _ _ (-104) 0); [exact HTS3 | exact MU4 | exact WM4 | vm_compute; reflexivity |].
      apply SMD; clear - SPA P2' P3 P6 P6' B2 R2' R3' Y2 Y3 Z1 Z4 Z5 Z6; unfold ADS_STACK in *; lia. }
    assert (HTA4 : ftbl WW spa m4 AT2).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch _ spa m3 m4 _ _ (-192) 88); [exact HTA3 | exact MU4 | exact WM4 | vm_compute; reflexivity |].
      apply SMD; clear - SPA P2' P3 P6 P6' B2 R2' R3' Y2 Y3 Z1 Z4 Z5 Z6; unfold ADS_STACK in *; lia. }
    assert (HTF4 : ftbl WW ff1 m4 FT2).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch _ ff1 m3 m4 _ _ 0 128); [exact HTF3 | exact MU4 | exact WM4 | vm_compute; reflexivity |].
      apply SMD; clear - SPA FQ2 FQ3 P2' P3 P6 P6' B2 B4 R2' R3' Y2 Y3 Z1 Z2 Z3 Z4 Z5 Z6 G12; unfold ADS_STACK in *; lia. }
    assert (HTH4 : ftbl WW (ff1 / 8) m4 HT2).
    { rewrite EWW. apply ftbl_wext; [vm_compute; reflexivity|].
      eapply (ftbl_munch _ (ff1 / 8) m3 m4 _ _ SHBASE (SHBASE + 16)); [exact HTH3 | exact MU4 | exact WM4 | vm_compute; reflexivity |].
      rewrite LbB_PqK.shb1_eq. replace (SHBASE + 16 - SHBASE) with 16 by (clear; lia).
      pose proof (LbB_PqK2.q2_dj H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) as (_ & _ & _ & _ & _ & SF12).
      apply SMD; clear - SPA FQ2 FQ3 P2' P3 P6 P6' B2 B4 R2' R3' Y2 Y3 Z1 Z2 Z3 Z4 Z5 Z6 SF12; unfold ADS_STACK in *; lia. }
    assert (HTD4 : ftbl WW ds m4 DT3).
    { apply ftbl_of_fld; [| eapply wr_at_sub; [exact (q_dsw _ _ _ _ _ _ m4 QF4) | clear; lia | unfold DS_SIZE; clear; cbn; lia | clear; cbn; lia]
                         | clear - DS0; lia | clear - DSH; cbn; lia].
      eapply (LbB_DRep.fld_ag m m4 (fun x => ds + 136 <= x < ds + 136 + 8)); [clear - DS0; lia | clear - DSH; cbn; lia | intros x Hx; exact Hx | | exact W0m].
      intros a Ha. rewrite (MU4 (Z_to_bv 64 a)); [apply MU3|]; rewrite unsigned_lit by (clear - Ha DS0 DSH; lia).
      - unfold LbB_PqK.QW1. rewrite !Z.add_assoc, LbB_PqK.shb1_eq. cbn [outside]. clear - Ha F3 F4 B2 B4 R2' SPA FQ2 FQ6 FD1 FD2 Z1 Z2 Z3 Z4 Z5. unfold SHBASE, ADS_STACK in *. lia.
      - unfold SMW, AFS_STACK, AFS_FLAGS. cbn [outside]. clear - Ha F3 F4 B2 B4 R2' SPA P2' P6 GD1' GD2' Z1 Y2 Y3 Z4 Z5. unfold ADS_STACK in *. lia. }
    assert (HTF24 : ftbl WW ff2 m4 FT30).
    { apply (proj1 (rw_cells_app asegs m4 ff2 [CB 24 junk1] _)) in FRC as [_ FRC1].
      apply (proj1 (rw_cells_app asegs m4 _ [C8 (PropExec.getr R3 2)] _)) in FRC1 as [C24 FRC2].
      apply (proj1 (rw_cells_app asegs m4 _ [CB (Z.to_nat (fsz 1 - 40)) junk2] _)) in FRC2 as [_ C120].
      cbn [cells_size csize Nat.add] in C24, C120.
      replace (ff2 + Z.of_nat 24 + Z.of_nat 8 + Z.of_nat (Z.to_nat (fsz 1 - 40) + 0)) with (ff2 + 120) in C120 by (unfold fsz; clear; lia).
      replace (ff2 + Z.of_nat 24) with (ff2 + 24) in C24 by (clear; lia).
      unfold FT30. apply (ftbl_app WW ff2 m4 [(24, 8%nat, EAlu ALU_ADD (EVar 54) (ELit (-192)))] [(120, 8%nat, EVar 56)]).
      - apply ftbl_of_C8. subst WW. evWW. rewrite w_addm by (clear - SPA R1' R2' R3'; unfold ADS_STACK in *; lia).
        replace (spa + -192) with (spa - 192) by (clear; lia). rewrite <- K2. exact C24.
      - apply ftbl_of_C8. subst WW. evWW. exact C120. }

    assert (KP : forall r, In r KEPT -> PropExec.getr R4 r = PropExec.getr R3 r).
    { intros r Hr. rewrite ER4. apply (getr_mkR_keptR R3); [exact (eq_sym K1) | exact Hr]. }
    assert (HRT4 : rtbl WW R4 RTQ3).
    { assert (HK : rtbl WW R4 (keptk RTQ2E)).
      { rewrite EWW. apply rtbl_wext; [vm_compute; reflexivity|].
        apply (rtbl_keep _ R3 R4 _ KEPT); [apply rtbl_keptk; exact HRT3 | apply rsub_keptk | exact KP]. }
      assert (HX : rtbl WW R4 [(10%bv, EVar 55)]).
      { unfold rtbl. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. rewrite ER4. subst WW. cbn [PropExec.getr mkR]. evWW. reflexivity. }
      apply (rtbl_sub _ _ _ _ (rtbl_app _ _ _ _ HK HX)). vm_compute. reflexivity. }

    assert (FI4 : CRep.fld ASEGS m4 (ds + 256) 4 32).
    { eapply (LbB_DRep.fld_ag m3 m4 (fun x => ds + 256 <= x < ds + 256 + 4)); [clear - DS0; lia | clear - DSH; cbn; lia | intros x Hx; exact Hx | | exact FI3].
      intros a Ha. apply MU4. rewrite unsigned_lit by (clear - Ha DS0 DSH; lia).
      unfold SMW, AFS_STACK, AFS_FLAGS. cbn [outside]. clear - Ha F3 F4 B2 B4 R2' SPA P2' P6 GD1' GD2' Z1 Y2 Y3 Z4 Z5. unfold ADS_STACK in *. lia. }
    assert (MUB : munch (WB ff1 fp1 ff2 fp2) m0 m4).
    { eapply munch_trans; [eapply munch_weaken; [| exact MUA3] | eapply munch_weaken; [| exact MU4]]; apply sub_fp_of; unfold WA, WB, SMW, AFS_STACK.
      - apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp1, fp1 + 1); split; [do 2 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff1, ff1 + 128); split; [do 3 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff1, sh ff1 + 16); split; [do 4 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ds + 256, ds + 260); split; [do 5 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil.
      - apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - SPA; lia]|].
        apply Forall_cons; [exists (as_FSB H, as_FSB H + AFS_FLAGS); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp2, fp2 + 1); split; [do 6 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff2, ff2 + 128); split; [do 7 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff2, sh ff2 + 16); split; [do 8 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil. }
    assert (WMB : wmono asegs m0 m4) by (eapply wmono_trans; [exact WMA3 | exact WM4]).
    apply evt_done. exists ff2, fp2, R4, m4. split; [reflexivity|].
    constructor; [exact G1 | exact G2 | exact FRESH1 | exact FRESH2 | exact RF4' | exact HRT4 | exact HTS4 | exact HTA4 | exact HTD4 | exact HTF24
                | exact HTF4 | exact HTH4 | exact QF4 | exact X4 | exact MI4 | exact RF4 | exact FI4 | exact MUB | exact WMB].
  Qed.

  Lemma nums2 : forall ff1 fp1 spa ff2 fp2, qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    as_FSB H + 0x9000 <= ff1 /\ ff1 + 128 <= as_FSB H + 0xb09000 /\ as_FSB H + 0x1000 <= fp1 /\ fp1 + 1 <= as_FSB H + 0x9000
    /\ as_FSB H + 0x9000 <= ff2 /\ ff2 + 128 <= as_FSB H + 0xb09000 /\ as_FSB H + 0x1000 <= fp2 /\ fp2 + 1 <= as_FSB H + 0x9000
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + 0xb09000 <= aceil /\ aceil + 16384 <= spz /\ spz <= 2 ^ 47 /\ spz - 208 <= spa <= spz - 192
    /\ 0x800d5000 <= sh (as_FSB H) /\ sh (as_FSB H) + 0x1200 <= sh ff1 /\ sh ff1 + 16 <= sh (as_FSB H + 0xb09000)
    /\ sh (as_FSB H) + 0x1200 <= sh ff2 /\ sh ff2 + 16 <= sh (as_FSB H + 0xb09000)
    /\ sh (as_FSB H + 0xb09000) + 2048 <= sh spz /\ sh spz <= 0x10007fff8000 /\ sh spz + 2 ^ 44 <= spz
    /\ as_FSB H + 0x9000 <= ds /\ ds + 392 <= as_FSB H + 0xb09000 /\ 0 < ds /\ ds + 392 + 64 <= 2 ^ 47
    /\ sh (as_FSB H) + 0x1200 <= sh ds /\ sh ds + 49 <= sh (as_FSB H + 0xb09000)
    /\ aceil <= lo /\ lo <= spz - 16384.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2.
    pose proof (fr_place _ ff1 fp1 FR1) as (Q2 & Q3 & Q4 & Q6 & Q6' & B1 & B2 & R2 & R3 & B4 & AP & Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & A1).
    pose proof (fr_place _ ff2 fp2 FR2) as (P2' & P3 & P4 & P6 & P6' & _ & _ & _ & _ & _ & _ & _ & Y2 & Y3 & _).
    pose proof ds_facts as (_ & _ & _ & DS8 & DS0 & DSH & F3 & F4 & _). unfold AFS_HDR, AFS_SIZE, DS_SIZE, AAPP_HI in F3, F4, DSH.
    destruct G1 as [_ _ [_ SPA] _ _ _ _ _ _].
    assert (SD : sh (as_FSB H) + 0x1200 <= sh ds /\ sh ds + 49 <= sh (as_FSB H + 0xb09000)).
    { clear - F3 F4 DS8. unfold sh, ASHADOW_BASE. Z.div_mod_to_equations. lia. }
    pose proof CEIL as C1. pose proof LO as C2. unfold ADS_STACK in C2.
    repeat match goal with |- _ /\ _ => split end; try assumption; try (clear - SPA; lia); try (clear - SD; lia); clear - DSH; cbn in DSH; lia.
  Qed.
  Lemma djs2 : forall ff1 fp1 spa ff2 fp2, qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    (as_FSB H + 0xb09000 <= 0x7fff7000 \/ 0x10007fff8000 <= as_FSB H)
    /\ (ff1 + 128 <= ds \/ ds + 392 <= ff1) /\ (fp1 + 1 <= ds \/ ds + 392 <= fp1) /\ (sh ff1 + 16 <= sh ds \/ sh ds + 49 <= sh ff1)
    /\ (ff2 + 128 <= ds \/ ds + 392 <= ff2) /\ (fp2 + 1 <= ds \/ ds + 392 <= fp2) /\ (sh ff2 + 16 <= sh ds \/ sh ds + 49 <= sh ff2)
    /\ (ff1 + 128 <= ff2 \/ ff2 + 128 <= ff1) /\ (fp1 + 1 <= fp2 \/ fp2 + 1 <= fp1) /\ (sh ff1 + 16 <= sh ff2 \/ sh ff2 + 16 <= sh ff1).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 G1 G2.
    pose proof (LbB_PqK.q1_dj H sp ds p n fl lo ff1 fp1 spa G1) as (SIDE & XF1D & XP1D & SF1D & _).
    pose proof (LbB_PqK2.q2_dj H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2) as (XF2D & XP2D & XF12 & XP12 & SF2D & SF12).
    repeat match goal with |- _ /\ _ => split end; assumption.
  Qed.

  Record pq_stx (ff1 fp1 spa ff2 fp2 : Z) (R : bvmap 5 word) (m : mem) : Prop := PQ_STX {
    tx_g1 : qg1 H sp ds p n fl lo ff1 fp1 spa;
    tx_g2 : qg2 H ds ff1 fp1 ff2 fp2;
    tx_fr1 : fresh_frame H LF 1 ff1 fp1;
    tx_fr2 : fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2;
    tx_rf : rfull R;
    tx_rt : rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQX;
    tx_ts : ftbl (W2' ff1 fp1 spa ff2 fp2) spz m TS0;
    tx_ta : ftbl (W2' ff1 fp1 spa ff2 fp2) spa m AT3;
    tx_tf2 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff2 m FT3;
    tx_th2 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff2 / 8) m HT3;
    tx_tf1 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m FT2;
    tx_th1 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m HT2;
    tx_q1 : qf1 sp ds fl lo ff1 fp1 m;
    tx_q2 : qx2 ff2 fp2 m;
    tx_mi : mem_inv asegs m;
    tx_rfs : as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m;
    tx_fill : CRep.fld ASEGS m (ds + 256) 4 32;
    tx_w0 : CRep.fld ASEGS m (ds + 136) 8 0;
    tx_mu : munch (WB ff1 fp1 ff2 fp2) m0 m;
    tx_wm : wmono asegs m0 m
  }.

  Lemma pq_x : 0 < n -> forall ff1 fp1 spa ff2 fp2 R m, pq_st2 ff1 fp1 spa ff2 fp2 R m ->
    evt asegs (fun msx => exists R' m', msx = MS R' F (Z_to_bv 64 AXSP) fc None m' (seg_rom asegs) /\ pq_stx ff1 fp1 spa ff2 fp2 R' m')
      (MS R F (Z_to_bv 64 APQ_P3) fc None m (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros NP ff1 fp1 spa ff2 fp2 R m ST. destruct ST as [G1 G2 FR1 FR2 RF HRT HTS HTA HTD HTF2 HTF1 HTH1 Q1 Q2 MI RFS2 FI MUB WMB].
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU. pose proof (djs2 ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & XF1D & XP1D & SF1D & XF2D & XP2D & SF2D & XF12 & XP12 & SF12).
    assert (HTH2 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff2 / 8) m []) by constructor.
    eapply evt_cut.
    { eapply (q_p3x H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 NP m R m RF HRT HTA HTD HTF2 HTH2
                (conj (conj Q1 Q2) (LbB_PqK2.P2x_refl ds spa ff2 fp2 m)) MI). }
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HTA1 & HTD1 & HTFx & HTHx & [_ PX] & MI1 & MU1 & WM1).
    destruct (LbB_PqK2.q2_keep H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 m m1 (conj Q1 Q2) PX MI1) as [Q1' Q2'].
    unfold LbB_PqR.QW2x in MU1. rewrite !Z.add_assoc, LbB_PqK2.shb2_eq in MU1.
    assert (RFS2' : as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m1).
    { eapply (ah_RFS_frame H HHb); [exact RFS2 | exact MU1 | exact WM1 |].
      repeat apply Forall_cons; try apply Forall_nil.
      - left. cbn [fst snd]. clear - NU. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      - right. destruct DSin as (f & Hf & X1 & X2). exists f. split; [right; right; exact Hf|]. cbn [fst snd]. clear - X1 X2. unfold DS_SIZE in *. lia.
      - right. exists (1, ff2, fp2). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite fsz_1. clear. lia.
      - left. cbn [fst snd]. clear - NU SIDE. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia. }
    assert (D4 : forall A k, (A + k <= spa - 192 \/ spa + 88 <= A) -> (A + k <= ds + 136 \/ ds + 144 <= A) ->
                 (A + k <= ff2 \/ ff2 + 128 <= A) -> (A + k <= sh ff2 \/ sh ff2 + 16 <= A) ->
                 disjoint_from [(spa + -192, spa + 88); (ds + 136, ds + 144); (ff2 + 0, ff2 + 128); (sh ff2, sh ff2 + 16)] A k).
    { intros A k D1 D2 D3 D4. cbn [disjoint_from]. clear - D1 D2 D3 D4. lia. }
    assert (HTS1 : ftbl (W2' ff1 fp1 spa ff2 fp2) spz m1 TS0).
    { eapply (ftbl_munch _ spz m m1 _ _ (-104) 0); [exact HTS | exact MU1 | exact WM1 | vm_compute; reflexivity |]. apply D4; clear - NU; lia. }
    assert (HTF1' : ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m1 FT2).
    { eapply (ftbl_munch _ ff1 m m1 _ _ 0 128); [exact HTF1 | exact MU1 | exact WM1 | vm_compute; reflexivity |]. apply D4; clear - NU SIDE XF1D XF12; lia. }
    assert (HTH1x : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m1 HT2).
    { eapply (ftbl_munch _ (ff1 / 8) m m1 _ _ SHBASE (SHBASE + 16)); [exact HTH1 | exact MU1 | exact WM1 | vm_compute; reflexivity |].
      rewrite LbB_PqK.shb1_eq. replace (SHBASE + 16 - SHBASE) with 16 by (clear; lia). apply D4; clear - NU SIDE SF1D SF12; lia. }
    assert (FI1 : CRep.fld ASEGS m1 (ds + 256) 4 32).
    { eapply (LbB_DRep.fld_ag m m1 (fun x => ds + 256 <= x < ds + 256 + 4)); [clear - NU; lia | clear - NU; lia | intros x Hx; exact Hx | | exact FI].
      intros a Ha. apply MU1. rewrite unsigned_lit by (clear - Ha NU; lia). cbn [outside]. clear - Ha NU SIDE XF2D. lia. }
    assert (W01 : CRep.fld ASEGS m1 (ds + 136) 8 0) by (apply (fld_of_ftbl _ ds m1 _ 136 8%nat (ELit 0) 0 HTD1); [left; reflexivity | reflexivity]).
    assert (MUB1 : munch (WB ff1 fp1 ff2 fp2) m0 m1).
    { eapply munch_trans; [exact MUB|]. eapply munch_weaken; [| exact MU1]. apply sub_fp_of. unfold WB.
      apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
      apply Forall_cons; [exists (ds + 136, ds + 144); split; [do 9 right; left; reflexivity | cbn; clear; lia]|].
      apply Forall_cons; [exists (ff2, ff2 + 128); split; [do 7 right; left; reflexivity | cbn; clear; lia]|].
      apply Forall_cons; [exists (sh ff2, sh ff2 + 16); split; [do 8 right; left; reflexivity | cbn; clear; lia]|].
      apply Forall_nil. }
    apply evt_done. exists R1, m1. split; [reflexivity|].
    constructor; try assumption. eapply wmono_trans; [exact WMB | exact WM1].
  Qed.

  Lemma flag0_of_tbl : forall W fp m, ftbl W fp m LTZ -> mrd asegs m (wa fp) = Some (b8 0).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros W fp m HL. pose proof (ftbl_In W fp m LTZ 0 1 (ELit 0) HL ltac:(left; reflexivity)) as C.
    rewrite Z.add_0_r in C. destruct C as [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)).
    rewrite Z.add_0_r in B. exact B.
  Qed.

  Lemma rel2 : forall ff1 fp1 spa ff2 fp2 m m', qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m -> munch (LbB_PqK2.QW2 ds spa ff2 fp2) m m' -> wmono asegs m m' ->
    ftbl (W2' ff1 fp1 spa ff2 fp2) fp2 m' LTZ -> as_RFS H ((1, ff1, fp1) :: LF) m'.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 m m' G1 G2 FR1 FR2 RF MU WM HL.
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU. pose proof (djs2 ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & _).
    pose proof (ah_release H HHb _ m m' _ 1 ff2 fp2 RF (or_introl eq_refl) MU WM) as KR. rewrite lf_remove_head in KR. apply KR.
    - unfold LbB_PqK2.QW2. rewrite !Z.add_assoc, LbB_PqK2.shb2_eq.
      repeat apply Forall_cons; try apply Forall_nil.
      + left. left. cbn [fst snd]. clear - NU. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      + left. right. destruct DSin as (f & Hf & X1 & X2). exists f. split; [right; right; exact Hf|]. cbn [fst snd]. clear - X1 X2. unfold DS_SIZE in *. lia.
      + left. right. exists (1, ff2, fp2). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite fsz_1. clear. lia.
      + left. left. cbn [fst snd]. clear - NU SIDE. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      + right. cbn [fst snd]. split; [clear; lia | reflexivity].
    - exact (flag0_of_tbl _ fp2 m' HL).
  Qed.

  Lemma rel1 : forall ff1 fp1 spa ff2 fp2 m m', qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    as_RFS H ((1, ff1, fp1) :: LF) m -> munch (LbB_PqK2.QW3 sp ff1 fp1 spa) m m' -> wmono asegs m m' ->
    ftbl (W2' ff1 fp1 spa ff2 fp2) fp1 m' LTZ -> as_RFS H LF m'.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 m m' G1 G2 FR1 FR2 RF MU WM HL.
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU. pose proof (djs2 ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & _).
    pose proof (ah_release H HHb _ m m' _ 1 ff1 fp1 RF (or_introl eq_refl) MU WM) as KR. rewrite lf_remove_head in KR. apply KR.
    - unfold LbB_PqK2.QW3. rewrite !Z.add_assoc, LbB_PqK.shb1_eq.
      repeat apply Forall_cons; try apply Forall_nil.
      + left. left. cbn [fst snd]. clear - NU. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      + left. left. cbn [fst snd]. clear - NU. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      + left. right. exists (1, ff1, fp1). split; [left; reflexivity|]. cbn [ff_addr ff_class fst snd]. rewrite fsz_1. clear. lia.
      + left. left. cbn [fst snd]. clear - NU SIDE. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE. lia.
      + right. cbn [fst snd]. split; [clear; lia | reflexivity].
    - exact (flag0_of_tbl _ fp1 m' HL).
  Qed.

  Record pq_st4 (ff1 fp1 spa ff2 fp2 : Z) (R : bvmap 5 word) (m : mem) : Prop := PQ_ST4 {
    t4_g1 : qg1 H sp ds p n fl lo ff1 fp1 spa;
    t4_g2 : qg2 H ds ff1 fp1 ff2 fp2;
    t4_fr1 : fresh_frame H LF 1 ff1 fp1;
    t4_fr2 : fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2;
    t4_rf : rfull R;
    t4_rt : rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQ4;
    t4_ts : ftbl (W2' ff1 fp1 spa ff2 fp2) spz m TS0;
    t4_ta : ftbl (W2' ff1 fp1 spa ff2 fp2) spa m AT3;
    t4_tf1 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m FT2;
    t4_th1 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m HT2;
    t4_q1 : qf1 sp ds fl lo ff1 fp1 m;
    t4_mi : mem_inv asegs m;
    t4_rfs : as_RFS H ((1, ff1, fp1) :: LF) m;
    t4_fill : CRep.fld ASEGS m (ds + 256) 4 32;
    t4_w0 : CRep.fld ASEGS m (ds + 136) 8 0
  }.

  Record pq_fin (ff1 fp1 spa ff2 fp2 : Z) (Wb : list (Z * Z)) (mb : mem) (R : bvmap 5 word) (m : mem) : Prop := PQ_FIN {
    tf_rf : rfull R;
    tf_rt : rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQF;
    tf_q1 : qf1 sp ds fl lo ff1 fp1 m;
    tf_mi : mem_inv asegs m;
    tf_rfs : as_RFS H LF m;
    tf_fill : CRep.fld ASEGS m (ds + 256) 4 32;
    tf_w0 : CRep.fld ASEGS m (ds + 136) 8 0;
    tf_mu : munch Wb mb m;
    tf_wm : wmono asegs mb m
  }.

  Lemma pq_tail : forall ff1 fp1 spa ff2 fp2 R m, pq_st4 ff1 fp1 spa ff2 fp2 R m ->
    evt asegs (fun msx => exists R' m', msx = MS R' F (Z_to_bv 64 APQ_RET) fc None m' (seg_rom asegs)
                            /\ pq_fin ff1 fp1 spa ff2 fp2 (LbB_PqK2.QW3 sp ff1 fp1 spa) m R' m')
      (MS R F (Z_to_bv 64 APQ_P4B) fc None m (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 R m ST. destruct ST as [G1 G2 FR1 FR2 RF HRT HTS HTA HTF1 HTH1 Q1 MI RFS1 FI W0m].
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU. pose proof (djs2 ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & XF1D & XP1D & SF1D & _).
    assert (HTL : ftbl (W2' ff1 fp1 spa ff2 fp2) fp1 m []) by constructor.
    eapply evt_cut.
    { eapply (q_p4b H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 m R m RF HRT HTS HTA HTF1 HTH1 HTL
                (conj Q1 (LbB_PqK2.P3x_refl sp ff1 fp1 spa m)) MI). }
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HTL1 & [_ PX] & MI1 & MU1 & WM1).
    pose proof (LbB_PqK2.q3_keep H sp ds p n fl lo ff1 fp1 spa G1 m m1 Q1 PX MI1) as Q1'.
    pose proof (rel1 ff1 fp1 spa ff2 fp2 m m1 G1 G2 FR1 FR2 RFS1 MU1 WM1 HTL1) as RFS0'.
    assert (OUTD : forall a, ds <= a < ds + 392 -> 0 <= a < 2 ^ 64 /\ outside (LbB_PqK2.QW3 sp ff1 fp1 spa) a).
    { intros a Ha. split; [clear - Ha NU; lia|]. unfold LbB_PqK2.QW3. rewrite !Z.add_assoc, LbB_PqK.shb1_eq. cbn [outside].
      clear - Ha NU SIDE XF1D XP1D. lia. }
    apply evt_done. exists R1, m1. split; [reflexivity|]. constructor; try assumption.
    - eapply (LbB_DRep.fld_ag m m1 (fun x => ds + 256 <= x < ds + 256 + 4)); [clear - NU; lia | clear - NU; lia | intros x Hx; exact Hx | | exact FI].
      intros a Ha. apply MU1. destruct (OUTD a ltac:(clear - Ha; lia)) as [A1 A2]. rewrite unsigned_lit by exact A1. exact A2.
    - eapply (LbB_DRep.fld_ag m m1 (fun x => ds + 136 <= x < ds + 136 + 8)); [clear - NU; lia | clear - NU; lia | intros x Hx; exact Hx | | exact W0m].
      intros a Ha. apply MU1. destruct (OUTD a ltac:(clear - Ha; lia)) as [A1 A2]. rewrite unsigned_lit by exact A1. exact A2.
  Qed.

  Lemma mk_st4 : forall ff1 fp1 spa ff2 fp2 R m m1, qg1 H sp ds p n fl lo ff1 fp1 spa -> qg2 H ds ff1 fp1 ff2 fp2 ->
    fresh_frame H LF 1 ff1 fp1 -> fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2 ->
    ftbl (W2' ff1 fp1 spa ff2 fp2) spz m TS0 -> ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m FT2 -> ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m HT2 ->
    qf1 sp ds fl lo ff1 fp1 m -> qx2 ff2 fp2 m -> as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m -> CRep.fld ASEGS m (ds + 256) 4 32 ->
    rfull R -> rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQ4 -> ftbl (W2' ff1 fp1 spa ff2 fp2) spa m1 AT3 -> ftbl (W2' ff1 fp1 spa ff2 fp2) ds m1 DT3 ->
    ftbl (W2' ff1 fp1 spa ff2 fp2) fp2 m1 LTZ -> (qf1 sp ds fl lo ff1 fp1 m /\ qx2 ff2 fp2 m) /\ LbB_PqK2.P2x ds spa ff2 fp2 m m1 -> mem_inv asegs m1 ->
    munch (LbB_PqK2.QW2 ds spa ff2 fp2) m m1 -> wmono asegs m m1 ->
    pq_st4 ff1 fp1 spa ff2 fp2 R m1.
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 R m m1 G1 G2 FR1 FR2 HTS HTF1 HTH1 Q1 Q2 RFS2 FI RF HRT HTA HTD HTL QP MI1 MU WM.
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU. pose proof (djs2 ff1 fp1 spa ff2 fp2 G1 G2) as (SIDE & XF1D & XP1D & SF1D & XF2D & XP2D & SF2D & XF12 & XP12 & SF12).
    destruct (LbB_PqK2.q2_keep H sp ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 m m1 (conj Q1 Q2) (proj2 QP) MI1) as [Q1' _].
    pose proof (rel2 ff1 fp1 spa ff2 fp2 m m1 G1 G2 FR1 FR2 RFS2 MU WM HTL) as RFS1.
    unfold LbB_PqK2.QW2 in MU. rewrite !Z.add_assoc, LbB_PqK2.shb2_eq in MU.
    assert (D5 : forall A k, (A + k <= spa - 192 \/ spa + 88 <= A) -> (A + k <= ds + 136 \/ ds + 144 <= A) ->
                 (A + k <= ff2 \/ ff2 + 128 <= A) -> (A + k <= sh ff2 \/ sh ff2 + 16 <= A) -> (A + k <= fp2 \/ fp2 + 1 <= A) ->
                 disjoint_from [(spa + -192, spa + 88); (ds + 136, ds + 144); (ff2 + 0, ff2 + 128); (sh ff2, sh ff2 + 16); (fp2 + 0, fp2 + 1)] A k).
    { intros A k D1 D2 D3 D4 D5. cbn [disjoint_from]. clear - D1 D2 D3 D4 D5. lia. }
    constructor; try assumption.
    - eapply (ftbl_munch _ spz m m1 _ _ (-104) 0); [exact HTS | exact MU | exact WM | vm_compute; reflexivity |]. apply D5; clear - NU; lia.
    - eapply (ftbl_munch _ ff1 m m1 _ _ 0 128); [exact HTF1 | exact MU | exact WM | vm_compute; reflexivity |]. apply D5; clear - NU SIDE XF1D XF12; lia.
    - eapply (ftbl_munch _ (ff1 / 8) m m1 _ _ SHBASE (SHBASE + 16)); [exact HTH1 | exact MU | exact WM | vm_compute; reflexivity |].
      rewrite LbB_PqK.shb1_eq. replace (SHBASE + 16 - SHBASE) with 16 by (clear; lia). apply D5; clear - NU SIDE SF1D SF12; lia.
    - eapply (LbB_DRep.fld_ag m m1 (fun x => ds + 256 <= x < ds + 256 + 4)); [clear - NU; lia | clear - NU; lia | intros x Hx; exact Hx | | exact FI].
      intros a Ha. apply MU. rewrite unsigned_lit by (clear - Ha NU; lia). cbn [outside]. clear - Ha NU SIDE XF2D XP2D. lia.
    - apply (fld_of_ftbl _ ds m1 _ 136 8%nat (ELit 0) 0 HTD); [left; reflexivity | reflexivity].
  Qed.

  Lemma pq_z : n = 0 -> forall ff1 fp1 spa ff2 fp2 R m, pq_st2 ff1 fp1 spa ff2 fp2 R m ->
    evt asegs (fun msx => exists R' m', msx = MS R' F (Z_to_bv 64 APQ_RET) fc None m' (seg_rom asegs)
                            /\ pq_fin ff1 fp1 spa ff2 fp2 (WB ff1 fp1 ff2 fp2) m0 R' m')
      (MS R F (Z_to_bv 64 APQ_P3) fc None m (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros NZ ff1 fp1 spa ff2 fp2 R m ST. destruct ST as [G1 G2 FR1 FR2 RF HRT HTS HTA HTD HTF2 HTF1 HTH1 Q1 Q2 MI RFS2 FI MUB WMB].
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU.
    assert (HTH2 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff2 / 8) m []) by constructor.
    assert (HTL2 : ftbl (W2' ff1 fp1 spa ff2 fp2) fp2 m []) by constructor.
    eapply evt_cut.
    { eapply (q_p3z H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 NZ m R m RF HRT HTA HTD HTF2 HTH2 HTL2
                (conj (conj Q1 Q2) (LbB_PqK2.P2x_refl ds spa ff2 fp2 m)) MI). }
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HTA1 & HTD1 & HTL1 & QP & MI1 & MU1 & WM1).
    pose proof (mk_st4 ff1 fp1 spa ff2 fp2 R1 m m1 G1 G2 FR1 FR2 HTS HTF1 HTH1 Q1 Q2 RFS2 FI RF1 HRT1 HTA1 HTD1 HTL1 QP MI1 MU1 WM1) as ST4.
    eapply evt_cut; [apply (pq_tail ff1 fp1 spa ff2 fp2 R1 m1 ST4)|].
    intros ms2 (R2 & m2 & -> & FIN). destruct FIN as [RF2 HRT2 Q12 MI2 RFS0' FI2 W02 MU2 WM2].
    apply evt_done. exists R2, m2. split; [reflexivity|]. constructor; try assumption.
    - eapply munch_trans; [exact MUB|]. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of;
        unfold LbB_PqK2.QW2, LbB_PqK2.QW3, WB; rewrite !Z.add_assoc, ?LbB_PqK2.shb2_eq, ?LbB_PqK.shb1_eq.
      + apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (ds + 136, ds + 144); split; [do 9 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff2, ff2 + 128); split; [do 7 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff2, sh ff2 + 16); split; [do 8 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp2, fp2 + 1); split; [do 6 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil.
      + apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (ff1, ff1 + 128); split; [do 3 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff1, sh ff1 + 16); split; [do 4 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp1, fp1 + 1); split; [do 2 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil.
    - eapply wmono_trans; [exact WMB|]. eapply wmono_trans; [exact WM1 | exact WM2].
  Qed.

  Record pq_stb (ff1 fp1 spa ff2 fp2 : Z) (R : bvmap 5 word) (m : mem) : Prop := PQ_STB {
    tb_g1 : qg1 H sp ds p n fl lo ff1 fp1 spa;
    tb_g2 : qg2 H ds ff1 fp1 ff2 fp2;
    tb_fr1 : fresh_frame H LF 1 ff1 fp1;
    tb_fr2 : fresh_frame H ((1, ff1, fp1) :: LF) 1 ff2 fp2;
    tb_rf : rfull R;
    tb_rt : rtbl (W2' ff1 fp1 spa ff2 fp2) R RTQXR;
    tb_ts : ftbl (W2' ff1 fp1 spa ff2 fp2) spz m TS0;
    tb_ta : ftbl (W2' ff1 fp1 spa ff2 fp2) spa m AT3;
    tb_td : ftbl (W2' ff1 fp1 spa ff2 fp2) ds m DT3;
    tb_tf2 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff2 m FT3;
    tb_th2 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff2 / 8) m HT3;
    tb_tf1 : ftbl (W2' ff1 fp1 spa ff2 fp2) ff1 m FT2;
    tb_th1 : ftbl (W2' ff1 fp1 spa ff2 fp2) (ff1 / 8) m HT2;
    tb_q1 : qf1 sp ds fl lo ff1 fp1 m;
    tb_q2 : qx2 ff2 fp2 m;
    tb_mi : mem_inv asegs m;
    tb_rfs : as_RFS H ((1, ff2, fp2) :: (1, ff1, fp1) :: LF) m;
    tb_fill : CRep.fld ASEGS m (ds + 256) 4 32
  }.
  Definition WC (ff1 fp1 spa ff2 fp2 : Z) : list (Z * Z) :=
    [(spz - 16384, spz); (ds + 136, ds + 144); (ff2, ff2 + 128); (sh ff2, sh ff2 + 16); (fp2, fp2 + 1); (ff1, ff1 + 128); (sh ff1, sh ff1 + 16); (fp1, fp1 + 1)].

  Lemma pq_b : forall ff1 fp1 spa ff2 fp2 R m, pq_stb ff1 fp1 spa ff2 fp2 R m ->
    evt asegs (fun msx => exists R' m', msx = MS R' F (Z_to_bv 64 APQ_RET) fc None m' (seg_rom asegs)
                            /\ pq_fin ff1 fp1 spa ff2 fp2 (WC ff1 fp1 spa ff2 fp2) m R' m')
      (MS R F (Z_to_bv 64 APQ_XSRA) fc None m (seg_rom asegs)).
  Proof.
    clearbody Ha0 Ha1 Ha2 REP0 DSV DSin PN STK CEIL LO SP16 SPHI SPDS MI0 AC0 LV0 TP RFS0 LFn RH0.
    intros ff1 fp1 spa ff2 fp2 R m ST. destruct ST as [G1 G2 FR1 FR2 RF HRT HTS HTA HTD HTF2 HTH2 HTF1 HTH1 Q1 Q2 MI RFS2 FI].
    pose proof (nums2 ff1 fp1 spa ff2 fp2 G1 G2 FR1 FR2) as NU.
    assert (HTL2 : ftbl (W2' ff1 fp1 spa ff2 fp2) fp2 m []) by constructor.
    eapply evt_cut.
    { eapply (q_p4a H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ds p n fl lo ff1 fp1 spa G1 ff2 fp2 G2 m R m RF HRT HTA HTD HTF2 HTH2 HTL2
                (conj (conj Q1 Q2) (LbB_PqK2.P2x_refl ds spa ff2 fp2 m)) MI). }
    intros ms1 (R1 & m1 & -> & RF1 & HRT1 & HTA1 & HTD1 & HTL1 & QP & MI1 & MU1 & WM1).
    pose proof (mk_st4 ff1 fp1 spa ff2 fp2 R1 m m1 G1 G2 FR1 FR2 HTS HTF1 HTH1 Q1 Q2 RFS2 FI RF1 HRT1 HTA1 HTD1 HTL1 QP MI1 MU1 WM1) as ST4.
    eapply evt_cut; [apply (pq_tail ff1 fp1 spa ff2 fp2 R1 m1 ST4)|].
    intros ms2 (R2 & m2 & -> & FIN). destruct FIN as [RF2 HRT2 Q12 MI2 RFS0' FI2 W02 MU2 WM2].
    apply evt_done. exists R2, m2. split; [reflexivity|]. constructor; try assumption.
    - eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]]; apply sub_fp_of;
        unfold LbB_PqK2.QW2, LbB_PqK2.QW3, WC; rewrite !Z.add_assoc, ?LbB_PqK2.shb2_eq, ?LbB_PqK.shb1_eq.
      + apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (ds + 136, ds + 144); split; [right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (ff2, ff2 + 128); split; [do 2 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff2, sh ff2 + 16); split; [do 3 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp2, fp2 + 1); split; [do 4 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil.
      + apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (spz - 16384, spz); split; [left; reflexivity | cbn; clear - NU; lia]|].
        apply Forall_cons; [exists (ff1, ff1 + 128); split; [do 5 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (sh ff1, sh ff1 + 16); split; [do 6 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_cons; [exists (fp1, fp1 + 1); split; [do 7 right; left; reflexivity | cbn; clear; lia]|].
        apply Forall_nil.
    - eapply wmono_trans; [exact WM1 | exact WM2].
  Qed.

End PQ.
