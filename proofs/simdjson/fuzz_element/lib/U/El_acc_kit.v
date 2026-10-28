From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim STree Malloc Monad Stdio StrFun SjModel AtpModel ElModel Target Prog AtpImpl.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit Sj_new Sj_new_t2 Sj_h_kit Atp_defs Atp_kitu El_defs.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition acc_post (FR : Z) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(q - FR, q)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'.

Definition acc_post_r (FR r : Z) (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom usegs)
    /\ munch [(q - FR, q); (r, r + 24)] m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo q /\ frm0 fc'
    /\ exists jr' : list byte, rw_cells usegs m' r [CB 24 jr'].


Ltac acc_fin :=
  apply evt_done;
  lazymatch goal with |- acc_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ ?F _ ?fc _ ?mx _) =>
    unfold acc_post; do 15 eexists; exists F, fc, mx; split; [atp_st_eq_goal|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption| assumption]
  end.

Ltac acc_fin_r :=
  apply evt_done;
  lazymatch goal with |- acc_post_r _ ?r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MS _ ?F _ ?fc _ ?mx _) =>
    unfold acc_post_r; do 15 eexists; exists F, fc, mx; split; [atp_st_eq_goal|];
    split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
    lazymatch goal with H : rw_cells usegs mx r ?cs |- _ =>
      let jj := fresh "jj" in let HJ := fresh "HJ" in
      destruct (rw_cells_forget _ _ _ _ H) as [jj HJ]; cbn [cells_size csize Nat.add] in HJ; exists jj; exact HJ
    end
  end.

Ltac acc_tix E RA :=
  lazymatch goal with |- evt _ _ (MS _ ?F _ ?fc _ ?mx _) =>
    eapply (tix_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mx (ae_DOC E) (ae_TAPE E) 1 RA [C8 (Z_to_bv 64 (ae_SBUF E))]);
    [eassumption| lia| lia| lia| lia| assumption| lia| lia| reflexivity| lia| reflexivity|];
    intros ? ? ? ?
  end.

Ltac acc_ret RA FR MU WM MI FRM ST MU2 WM2 MI2 FC2 ST2 :=
  replace (ret_pc (Z_to_bv 64 RA)) with (Z_to_bv 64 RA) by (symmetry; apply ret_pc_even; [lia| reflexivity]);
  let FRn := fresh "FRn" in let MUn := fresh "MUn" in let WMn := fresh "WMn" in
  pose proof (rw_cells_transport _ _ _ _ _ _ FR MU2 WM2 ltac:(cbn; lia)) as FRn;
  lazymatch type of MU with munch ?W ?m0 _ => lazymatch type of MU2 with munch _ _ ?m2 =>
    assert (MUn : munch W m0 m2)
      by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MU2]; unfold sub_fp; cbn [outside]; intros ? ?; lia)
  end end;
  pose proof (wmono_trans _ _ _ _ WM WM2) as WMn;
  clear FR MU WM MU2 WM2 MI FRM ST; rename FRn into FR, MUn into MU, WMn into WM, MI2 into MI, FC2 into FRM, ST2 into ST.

Ltac acc_tr H MU2 WM2 :=
  let Hn := fresh "Hn" in pose proof (rw_cells_transport _ _ _ _ _ _ H MU2 WM2 ltac:(cbn; lia)) as Hn; clear H; rename Hn into H.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma acc_shl8_shr8 : forall x, 0 <= x < 2^64 -> Z.shiftr ((Z.shiftl x 8) mod 2^64) 8 = tval x.
Proof.
  intros x Hx. unfold tval. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  change (2^64) with (2^56 * 2^8). rewrite Zmult_mod_distr_r. rewrite Z.div_mul by lia. reflexivity.
Qed.
Notation ae_T E := (Tf (ae_tws E)).
Notation ae_S E := (Tf (ae_sbs E)).
Notation ae_n E := (Z.of_nat (length (ae_tws E))).
Notation ae_sn E := (Z.of_nat (length (ae_sbs E))).

Lemma tix_tail : forall Q (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (D TAPE i : Z) (rest : list cell),
  rw_cells usegs m D (C8 (Z_to_bv 64 TAPE) :: rest) -> 0 < TAPE -> 0 <= i -> TAPE + 8 * i < 2^63 -> i < 2^60 -> TAPE mod 8 = 0 ->
  0 <= D -> D + 8 < 2^64 ->
  (forall (xa1 xa2 xa3 xa4 : word),
     evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 (TAPE + 8 * i)) xa1 xa2 xa3 xa4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m (seg_rom usegs))) ->
  evt usegs Q (MS (mkR ra sp gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 ATP_TIX) fc None m (seg_rom usegs)).
Proof.
  intros until rest. intros DC T0 I0 TI I60 T8 D0 D64 HK.
  unfold ATP_TIX.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl usegs m) as WM.

  step. astep. astep. astep. astep.
  replace (0 <? TAPE) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (TAPE + 8 * i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  step. if_false.

  astep. astep. astep. astep. rewrite tix_shr61 by lia.
  step. if_lia.

  step. if_lia. step. if_lia. astep. rewrite tix_land7 by lia. step. if_lia.
  step.
  eapply evt_eq; [| eapply HK]. atp_st_eq.
Qed.

Lemma acc_bytes_read1 : forall m a (bs : list byte) k, bytes_at usegs m a bs -> 0 <= k -> (Z.to_nat k < length bs)%nat ->
  exists b, ov_read_bytes usegs m (wa (a + k)) 1 = Some [b].
Proof.
  intros m a bs k HB Hk Hl. destruct (nth_error bs (Z.to_nat k)) as [b|] eqn:EN; [| apply nth_error_None in EN; lia].
  exists b. rewrite (bytes_at_read usegs m a bs k 1 HB Hk ltac:(lia)). f_equal.
  apply nth_error_split in EN as (l1 & l2 & -> & L). rewrite skipn_app, <- L, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Lemma acc_word_small : forall (w : word) k, bv_unsigned w < k -> exists e, w = Z_to_bv 64 e /\ 0 <= e < k.
Proof.
  intros w k H. exists (bv_unsigned w). split; [symmetry; apply Z_to_bv_bv_unsigned|].
  pose proof (bv_unsigned_in_range 64 w). lia.
Qed.

Lemma acc_jt_read : forall m A (l : list Z), mem_inv usegs m -> 0 <= A -> A + 4 <= 2^64 -> length l = 4%nat ->
  ro_bytes_b usegs A (map (Z_to_bv 8) l) = true -> ov_read_bytes usegs m (wa A) 4 = Some (map (Z_to_bv 8) l).
Proof.
  intros m A l MI A0 A4 L RB.
  assert (LM : length (map (Z_to_bv 8) l) = 4%nat) by (rewrite length_map; exact L).
  pose proof (ro_bytes_at usegs m A (map (Z_to_bv 8) l) MI A0 ltac:(rewrite LM; lia) (ro_bytes_b_sound usegs _ _ RB)) as B.
  pose proof (bytes_at_read usegs m A _ 0 4 B ltac:(lia) ltac:(rewrite LM; lia)) as R.
  rewrite Z.add_0_r in R. rewrite R. f_equal. cbn [Z.to_nat skipn]. apply firstn_all2. rewrite LM. lia.
Qed.

Section Facts.
  Variable E : aenv.
  Hypothesis OK : aenv_ok E.

  Lemma acc_facts : forall s m, RHEAP s (ae_LB E) m ->
    (0 < ae_TAPE E /\ ae_TAPE E + 8 * ae_n E <= alloc_ceiling /\ ae_TAPE E mod 8 = 0)
    /\ (0 < ae_SBUF E /\ ae_SBUF E + ae_sn E <= alloc_ceiling)
    /\ (2 < ae_n E < 2^32 /\ 0 <= ae_sn E < 2^56)
    /\ (alloc_ceiling <= ae_lo E /\ ae_DOC E + 24 <= ae_B E /\ ae_B E < 2^63 /\ ae_DOC E mod 8 = 0)
    /\ 0 <= ae_T E 1 < 2^64
    /\ elem (ae_T E) (ae_S E) (ae_sn E) ck_any TAPE_MAX_DEPTH 1 (ae_n E - 1).
  Proof.
    intros s m HEAP. pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L BT BS BP P0 [CEIL GLO] B63 [DL DB] [D8 T8]].
    pose proof (aenv_ranges E s m OK HEAP) as (TR & SR & PR).
    pose proof (el_root_elem E OK) as [EL NR].
    assert (SN : 0 <= ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (elem_word_range _ _ _ _ _ _ EL ltac:(lia) ltac:(lia) ltac:(lia)) as TIR.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact TIR| exact EL].
  Qed.

  Lemma acc_root_str : ttype (ae_T E 1) = t_str ->
    0 <= tval (ae_T E 1) /\ tval (ae_T E 1) + 4 < ae_sn E /\ Z.land (ae_T E 1) 72057594037927935 = tval (ae_T E 1).
  Proof.
    intros TS. pose proof OK as OK'. destruct OK' as [WF _ _ _ _ _ _ _ _ _ _ _].
    pose proof (el_root_elem E OK) as [EL NR].
    assert (SN : ae_sn E < 2^56) by (destruct WF as (_ & ? & _); lia).
    pose proof (el_elem_cases E _ _ _ OK EL) as CASES. cbv zeta in CASES.
    destruct CASES as [[_ [W|[W|W]]]|[[_ [W|[W|W]]]|[(_ & STR & _)|(e & cv & IE & EJ & CV & [W|W])]]];
      try (rewrite W in TS; first [rewrite ttype_tword in TS by lia| rewrite ttype_cword in TS by (unfold CNT_MAX in *; lia)];
           unfold t_str, t_true, t_false, t_null, t_i64, t_u64, t_dbl, t_arr, t_obj in TS; lia).
    destruct (is_str_read _ _ _ SN _ STR) as [_ (l & SA)].
    pose proof (str_at_bounds _ _ SN _ _ SA) as (O0 & L0 & OL & _ & _).
    pose proof (key_word_range _ _ _ _ STR SN) as (_ & KM & _).
    split; [lia|]. split; [lia| exact KM].
  Qed.

  Lemma acc_reget : forall s m mX node lo hi,
    AINV E m -> el_root E m node -> RHEAP s (ae_LB E) m ->
    munch [(lo, hi)] m mX -> wmono usegs m mX -> alloc_ceiling <= lo -> hi <= node -> hi <= ae_DOC E ->
    AINV E mX /\ el_root E mX node /\ RHEAP s (ae_LB E) mX.
  Proof.
    intros s m mX node lo hi AI RT HP MU WM L1 L2 L3. split; [| split].
    - eapply AINV_agree; [exact AI| eapply agree_on_of_munch; [exact MU| exact WM]| | | exact OK].
      + intros a Ha. pose proof (blocks_below _ _ _ a HP Ha). cbn [outside]. lia.
      + intros a Ha. cbn [outside]. lia.
    - unfold el_root in *. eapply rw_cells_transport; [exact RT| exact MU| exact WM| cbn; lia].
    - eapply LH_frame; [exact HP| exact MU| exact WM|]. constructor; [apply W_ok_stack; lia| constructor].
  Qed.
End Facts.

End WithCeiling0.
