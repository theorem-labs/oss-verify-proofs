(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import InflateGarbBase InflateInvTab.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateGarbFast InflateInv InflateInvKit InflateInvRun InflateInvFastC.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe IfShape.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflArmLib6d InflNeed6 InflDec6
     InffastCtx IfSpec IfSpec6 InflA_Len3.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent bkv sbv.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Lemma arm_LEN_dec1' : forall s c r,
  ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r ->   (* 1.4: the fast path also needs bits < 8 *)
  arm_LEN ivar_ref (mkW s c r)
  = match DECODE1 (is_lencode s) (is_lenbits s) (mkW (iset_back s 0) c r) with
    | ARun last w1 => len_after1 (iset_back s 0) last w1 | ALeave w1 => ALeave w1 | ARet rc w1 => ARet rc w1 end.
Proof.
  intros s c r Hl. unfold arm_LEN. mstep1 (@gr_eq iregs).
  replace (iv_fast ivar_ref && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false.
  2:{ symmetry. destruct Hl as [Hl|[Hl|Hl]]; [replace (6 <=? ir_have r) with false by (symmetry; apply Z.leb_gt; exact Hl)
                                        | replace (258 <=? ir_left r) with false by (symmetry; apply Z.leb_gt; exact Hl)
                                        | replace (ir_bits r <? 8) with false by (symmetry; apply Z.ltb_ge; exact Hl)];
      rewrite ?Bool.andb_false_r; reflexivity. }
  cbv iota. rewrite abind_run, set_back_eq. cbn [iv_aux ivar_ref sbv]. mstep1 (@gs_eq inflate_state). rewrite abind_run.
  destruct s; reflexivity.
Qed.

Lemma arm_LEN_fast : forall s c r,
  6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  arm_LEN ivar_ref (mkW s c r)
  = let w1 := LOAD (inflate_fast (RESTORE (mkW s c r))) in
    if is_mode (w_s w1) =? TYPE then ARun tt (mkW (iset_back (w_s w1) (-1)) (w_c w1) (w_r w1)) else ARun tt w1.
Proof.
  intros s c r Hh Hl Hb. unfold arm_LEN. mstep1 (@gr_eq iregs).
  replace (iv_fast ivar_ref && (6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with true
    by (symmetry; rewrite (proj2 (Z.leb_le _ _) Hh), (proj2 (Z.leb_le _ _) Hl), (proj2 (Z.ltb_lt _ _) Hb); reflexivity).
  cbv iota. unfold amodify. rewrite abind_run.
  destruct (LOAD (inflate_fast (RESTORE (mkW s c r)))) as [s1 c1 r1]. cbn [w_s w_c w_r].
  mstep1 (@gs_eq inflate_state).
  destruct (is_mode s1 =? TYPE); [rewrite set_back_eq; cbn [iv_aux ivar_ref sbv]; reflexivity | reflexivity].
Qed.

Definition lf_tower (v : icv) (s : inflate_state) (r : iregs) (M : word -> option byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (zw (cv_ZP v)) (Z_to_le_bytes 8 (cv_I0 v + ir_next r)))
    (zw (cv_ZP v + 8)) (Z_to_le_bytes 4 (ir_have r)))
    (zw (cv_ZP v + 24)) (Z_to_le_bytes 8 (cv_P0 v + ir_put r)))
    (zw (cv_ZP v + 32)) (Z_to_le_bytes 4 (ir_left r)))
    (zw (cv_S v + 96)) (Z_to_le_bytes 8 (ir_hold r)))
    (zw (cv_S v + 104)) (Z_to_le_bytes 4 (ir_bits r)).

Definition LOADl (w : iw) (lf : Z) : iw :=
  mkW (w_s w) (w_c w) (mkIR (ic_next_in (w_c w)) (ic_avail_in (w_c w)) (ic_next_out (w_c w)) lf
                           (is_hold (w_s w)) (is_bits (w_s w)) (ir_in (w_r w)) (ir_out (w_r w)) (ir_ret (w_r w))).



Definition mbyte (M : word -> option byte) (a : Z) : Z :=
  match M (zw a) with Some b => bv_unsigned b | None => 0 end.
Definition mem_ob (M : word -> option byte) (P0 NO : Z) : arr := arr_init NO (fun i => mbyte M (P0 + i)).

Lemma mem_ob_len : forall M P0 NO, arr_len (mem_ob M P0 NO) = NO.
Proof. intros. reflexivity. Qed.
Lemma mem_ob_get : forall M P0 NO i, arr_get (mem_ob M P0 NO) i = mbyte M (P0 + i).
Proof. intros. unfold mem_ob, arr_init, arr_get. cbn. destruct ((0 <=? i) && (i <? NO)); [| reflexivity]. rewrite FMapPositive.PositiveMap.gempty. reflexivity. Qed.
Lemma mbyte_range : forall M a, 0 <= mbyte M a < 256.
Proof. intros. unfold mbyte. destruct (M (zw a)) as [b|]; [| lia]. pose proof (u8_range b). lia. Qed.

Lemma mem_ob_cells : forall M P0 NO, mapped M P0 NO -> 0 <= P0 -> P0 + NO <= 2 ^ 64 ->
  cells s6u_segs M P0 1 1 NO (arr_get (mem_ob M P0 NO)).
Proof.
  intros M P0 NO Hmap HP0 HPN i Hi. rewrite mem_ob_get. unfold cell, mbyte. cbn [rdn Z_to_le_bytes].
  replace (P0 + 1 * i) with (P0 + i) by lia.
  pose proof (Hmap (zw (P0 + i)) ltac:(rewrite u_zw_small by lia; lia)) as Hx.
  destruct (M (zw (P0 + i))) as [b|] eqn:E; [| exfalso; exact (Hx eq_refl)].
  cbn. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma mem_ob_prefix : forall M P0 NO put f, cells s6u_segs M P0 1 1 put f -> (forall i, 0 <= i < put -> 0 <= f i < 256) ->
  mapped M P0 NO -> put <= NO -> 0 <= P0 -> P0 + NO <= 2 ^ 64 ->
  forall i, 0 <= i < put -> arr_get (mem_ob M P0 NO) i = f i.
Proof.
  intros M P0 NO put f Hc Hf Hmap Hput HP0 HPN i Hi. rewrite mem_ob_get. unfold mbyte.
  pose proof (Hc i Hi) as X. unfold cell in X. cbn [rdn Z_to_le_bytes] in X. replace (P0 + 1 * i) with (P0 + i) in X by lia.
  pose proof (Hmap (zw (P0 + i)) ltac:(rewrite u_zw_small by lia; lia)) as Hx.
  destruct (M (zw (P0 + i))) as [b|]; [| exfalso; exact (Hx eq_refl)]. cbn in X.
  injection X as ->. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. pose proof (Hf i Hi). rewrite Z.mod_small; [reflexivity | lia].
Qed.


Lemma cell1_same : forall (M M' : word -> option byte) a v,
  cell s6u_segs M a 1 v -> cell s6u_segs M' a 1 v -> M (zw a) <> None -> M' (zw a) <> None -> M' (zw a) = M (zw a).
Proof.
  intros M M' a v H1 H2 Hs Hs'. unfold cell in *. cbn [rdn Z_to_le_bytes] in H1, H2.
  destruct (M (zw a)) as [b|]; [| exfalso; exact (Hs eq_refl)].
  destruct (M' (zw a)) as [b'|]; [| exfalso; exact (Hs' eq_refl)].
  cbn in H1, H2. injection H1 as H1. injection H2 as H2. rewrite <- H2 in H1. congruence.
Qed.

Lemma icset_cursors_facts : forall c nx hv pt lf,
  let c' := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c pt) lf) nx) hv in
  ic_next_in c' = nx /\ ic_avail_in c' = hv /\ ic_next_out c' = pt /\ ic_avail_out c' = lf
  /\ ic_input c' = ic_input c /\ ic_outbuf c' = ic_outbuf c /\ ic_msg c' = ic_msg c
  /\ ic_total_in c' = ic_total_in c /\ ic_total_out c' = ic_total_out c /\ ic_adler c' = ic_adler c /\ ic_data_type c' = ic_data_type c.
Proof. intros. destruct c. repeat split; reflexivity. Qed.


Definition ffok_stmt : Prop := forall (NI NO WN TOT0 : Z) s c r ob,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
  arr_len ob = NO -> (forall i, 0 <= i < ir_put r -> arr_get ob i = arr_get (ic_outbuf c) i) ->
  (forall i, 0 <= i < NO -> 0 <= arr_get ob i < 256) ->
  ff_ok (iset_bits (iset_hold s (ir_hold r)) (ir_bits r))
        (icset_outbuf (icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) ob) r = true.
Definition fastok_stmt : Prop := forall (NI NO WN TOT0 : Z) s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
  gFAST (mkW s c r) = true /\ pinv NI NO WN TOT0 (LOAD (inflate_fast (RESTORE (mkW s c r))))
  /\ ir_bits (w_r (LOAD (inflate_fast (RESTORE (mkW s c r))))) < 8.
Definition gfast_ob_stmt : Prop := forall s c ob r, arr_len ob = arr_len (ic_outbuf c) ->
  (forall i, 0 <= i < ic_next_out c -> arr_get ob i = arr_get (ic_outbuf c) i) ->
  ffG (mkW s (icset_outbuf c ob) r) = ffG (mkW s c r).
Definition fframe_stmt : Prop := forall s c r,
  let w1 := inflate_fast (mkW s c r) in
  ic_next_out c <= ic_next_out (w_c w1)
  /\ arr_len (ic_outbuf (w_c w1)) = arr_len (ic_outbuf c)
  /\ (forall i, (i < ic_next_out c \/ ic_next_out (w_c w1) <= i) -> arr_get (ic_outbuf (w_c w1)) i = arr_get (ic_outbuf c) i).

Lemma pinv_LEN__LEN : forall NI NO WN TOT0 s c r,
  pinv NI NO WN TOT0 (mkW s c r) -> is_mode s = LEN_ -> pinv NI NO WN TOT0 (mkW (iset_mode s LEN) c r).
Proof.
  intros NI NO WN TOT0 s c r PI Hm.
  pose (w := mkW s c r). change (mkW s c r) with w in PI. change s with (w_s w) in Hm |- *. change c with (w_c w). change r with (w_r w).
  clearbody w. clear s c r.
  dworld w. cbn [w_s is_mode] in Hm. pinv_open PI. subst f_mode. sinv_triage. wred. pinv_auto.
Qed.

Section LenFast.
  Variable v : icv.
  Hypothesis C : ictx v.

  Hypothesis IFAST : inflate_fast_spec6.
  Hypothesis FFOK : ffok_stmt.
  Hypothesis FASTOK : fastok_stmt.
  Hypothesis GFAST_OB : gfast_ob_stmt.
  Hypothesis FFRAME : fframe_stmt.

  Ltac open_lfacts HD :=
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CI & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).

  Lemma lf_pre : forall s c r R M,
    len_facts v s c -> RINV (cv_NI v) (cv_NO v) r ->
    LMEM v (mkW s c r) M -> LFIXc v R -> getr R 13 = zw (cv_ZP v) -> LVARS v (mkW s c r) R ->
    6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
    exists R1,
      msteps s6u_segs (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) (mkst R1 (Z_to_bv 64 0x225ec) (lf_tower v s r M) s6u_rom)
      /\ getr R1 10 = zw (cv_ZP v) /\ getr R1 11 = zw (ir_out r) /\ getr R1 1 = zw 0x20a18 /\ getr R1 2 = zw (cv_sp v - 256)
      /\ (forall k : reg, reg_in k [1; 10; 11; 12]%bv = false -> getr R1 k = getr R k).
  Proof.
    intros s c r R M HD RI HM HF G13 HV Hh6 Hl258 HB8. open_lfacts HD.
    open_ictx C. open_lmem HM. open_fixc HF. open_vars HV. open_rinv RI. open_frame Mfr.
    pose proof G2 as P2. pose proof G27 as P27. pose proof G8 as P8. pose proof G24 as P24. pose proof G9 as P9. pose proof G22 as P22. pose proof G18 as P18. pose proof G25 as P25.
    unfold mapped in *.
    arm_symexP (@nil (Z * expr)) ilS 20%nat [false; false; false] [RVal (EVar 39%nat); RVal (EVar 42%nat)]
      ([(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (13, EVar 34%nat); (1, ELit 16209);
        (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat); (26, EAdd (EVar 43%nat) (EVar 44%nat))])
      (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: lazymatch goal with |- exists _, _ => idtac | _ => try arm_side end.
    all: match goal with |- ?G => idtac "LEFTP" G end.
    exists R1. split; [unfold lf_tower; by_run Hms1|].
    symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11. symex_reg HR1 (1%bv : reg) as Q1.
    split; [exact Q10|]. split; [exact Q11|]. split; [exact Q1|].
    split; [rewrite (Hfr1 (2%bv : reg) eq_refl); exact P2|].
    intros k Hk. apply Hfr1. revert Hk. eapply reg_in_sub. reflexivity.
  Qed.

  Lemma lf_call : forall s c r M R3,
    pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_mode s = LEN -> 6 <= ir_have r -> 258 <= ir_left r ->
    ir_bits r < 8 ->
    len_facts v s c -> LMEM v (mkW s c r) M -> RETC v (mkW s c r) M ->
    getr R3 1 = zw 0x20a18 -> getr R3 2 = zw (cv_sp v - 256) -> getr R3 10 = zw (cv_ZP v) -> getr R3 11 = zw (ir_out r) ->
    let w1 := inflate_fast (RESTORE (mkW s c r)) in
    exists R4 M4,
      msteps s6u_segs (mkst R3 (Z_to_bv 64 0x225ec) (lf_tower v s r M) s6u_rom) (mkst R4 (Z_to_bv 64 0x20a18) M4 s6u_rom)
      /\ getr R4 2 = zw (cv_sp v - 256)
      /\ (forall k : reg, In k if_kept -> getr R4 k = getr R3 k)
      /\ LMEM v (LOADl w1 (ir_left r)) M4 /\ RETC v (LOAD w1) M4
      /\ MFRAME v (ir_put r) (ir_put (w_r (LOAD w1))) M M4
      /\ w_r w1 = r /\ (is_mode (w_s w1) = LEN \/ is_mode (w_s w1) = TYPE \/ is_mode (w_s w1) = BAD)
      /\ 0 <= is_bits (w_s w1) < 8 /\ 0 <= is_hold (w_s w1) < 2 ^ is_bits (w_s w1)
      /\ pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (LOAD w1)
      /\ (same_blocks s (w_s w1) /\ is_wrap (w_s w1) = is_wrap s /\ is_wbits (w_s w1) = is_wbits s /\ is_flags (w_s w1) = is_flags s
          /\ is_havedict (w_s w1) = is_havedict s /\ (ic_msg (w_c w1) = ic_msg c \/ lf_msg_ok (Some (ic_msg (w_c w1))))).
  Proof.
    intros s c r M R3 HP Hmode Hh6 Hl258 HB8 HD HM HRC A1 A2 A10 A11.
    open_ictx C. pose proof HP as HP0. open_pinv HP0. open_rinv RI. open_cinv CI.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HNO : 0 < cv_NO v) by (clear - Rpt0 Rpl Hl258; lia).
    assert (HNI : 0 < cv_NI v) by (clear - Rnx0 Rnh Hh6; lia).
    pose proof (LMEM_restore v C s c r M (ir_hold r) (ir_bits r) HM Hput) as HM1. change (wbytes _ _ _) with (lf_tower v s r M) in HM1.
    set (sR := iset_bits (iset_hold s (ir_hold r)) (ir_bits r)) in *.
    set (cR := icset_avail_in (icset_next_in (icset_avail_out (icset_next_out c (ir_put r)) (ir_left r)) (ir_next r)) (ir_have r)) in *.
    destruct (icset_cursors_facts c (ir_next r) (ir_have r) (ir_put r) (ir_left r)) as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11).
    fold cR in K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11.
    set (M1 := lf_tower v s r M) in *.
    open_lmem HM1. open_frame Mfr. open_zs Mzs. unfold mapped in Mmap_P, Mmap_S, Mmap_Z, Mmap_f.
    rewrite K1, K2, K3, K4 in *. 
    set (ob := mem_ob M1 (cv_P0 v) (cv_NO v)).
    set (cM := icset_outbuf cR ob).
    pose proof (icset_outbuf_facts cR ob) as Fo. fold cM in Fo.
    destruct Fo as (Fo1 & Fo2 & Fo3 & Fo4 & Fo5 & Fo6 & Fo7 & Fo8 & Fo9 & Fo10 & Fo11).
    rewrite ?K1 in Fo1. rewrite ?K2 in Fo2. rewrite ?K3 in Fo3. rewrite ?K4 in Fo4. rewrite K5 in Fo5. rewrite K7 in Fo11. rewrite K8 in Fo7. rewrite K9 in Fo8. rewrite K10 in Fo9. rewrite K11 in Fo10.
    assert (Hobl : arr_len ob = cv_NO v) by (subst ob; apply mem_ob_len).
    assert (Hobb : forall i, 0 <= i < arr_len ob -> 0 <= arr_get ob i < 256) by (intros i Hi; subst ob; rewrite mem_ob_get; apply mbyte_range).
    assert (Hobc : cells s6u_segs M1 (cv_P0 v) 1 1 (arr_len ob) (arr_get ob)).
    { rewrite Hobl. subst ob. apply mem_ob_cells; [exact Mmap_P | clear - CP0; lia | clear - CP0; lia]. }
    assert (Hagree : forall i, 0 <= i < ir_put r -> arr_get ob i = arr_get (ic_outbuf c) i).
    { intros i Hi. subst ob. rewrite <- K6.
      apply (mem_ob_prefix M1 (cv_P0 v) (cv_NO v) (ir_put r) (arr_get (ic_outbuf cR)) Mout); [| exact Mmap_P | clear - Hput; lia | clear - CP0; lia | clear - CP0; lia | exact Hi].
      intros j Hj. rewrite K6. apply Coutb. clear - Hj Hput; lia. }
    destruct HD as (Hsane & Hwh & Hwn & Hwl & Hws & Hwb & CIc & (extL & TL & HextL) & Hlofs & (extD & TD & HextD) & Hdofs).
    pose proof SR as X; unfold SRNGq in X.
    destruct X as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Sws & Swh & Swn & _ & _ & _ & _ & _ & Slc & Sdc & Slb & Sdb & _ & _ & _ & _ & _ & (_ & _ & Scodes) & Ssane & _).
    destruct (tab_ok_root _ _ _ _ TL) as (RtL & _ & _). destruct (tab_ok_root _ _ _ _ TD) as (RtD & _ & _).
    assert (EsR : is_codes sR = is_codes s /\ is_window sR = is_window s /\ is_hold sR = ir_hold r /\ is_bits sR = ir_bits r
                  /\ is_wsize sR = is_wsize s /\ is_whave sR = is_whave s /\ is_wnext sR = is_wnext s
                  /\ is_lenbits sR = is_lenbits s /\ is_distbits sR = is_distbits s /\ is_sane sR = is_sane s
                  /\ is_lencode sR = is_lencode s /\ is_distcode sR = is_distcode s /\ is_mode sR = is_mode s)
      by (subst sR; destruct s; repeat split; reflexivity).
    destruct EsR as (Ecd & Ewin & Ehd & Ebi & Ews & Ewh & Ewn & Elb & Edb & Esa & Elc & Edc & Emd).
    unfold sep in CfZ, CfS, CfI, CfP, CfW, CZS, CZI, CZO, CZW, CSI, CSP, CSW, CIP, CIW, CPW.
    unfold offimg, IMG6_TOP in CoZ, CoS, CoI, CoP, CoW.
    pose proof if6_RO as HRO.
    assert (CS8 : cv_S v mod 8 = 0).
    { clear - CS. destruct CS as (_ & _ & H16). apply Z.mod_divide in H16; [|lia]. destruct H16 as [k Hk]. rewrite Hk.
      replace (k * 16) with ((k * 2) * 8) by lia. apply Z.mod_mul. lia. }
    assert (PRE : iff_pre s6u_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP M1 (cv_sp v - 416) (zw 0x20a18) sR cM r
                    (cv_ZP v) (cv_S v) (cv_I0 v) (cv_P0 v) (cv_WB v)).
    { constructor.
      all: rewrite ?Fo1, ?Fo2, ?Fo3, ?Fo4, ?Fo5, ?Fo6, ?Hobl, ?Cil, ?Ecd, ?Ewin, ?Ehd, ?Ebi, ?Ews, ?Ewh, ?Ewn, ?Elb, ?Edb, ?Esa, ?Elc, ?Edc, ?Hwl.
      all: try exact Hobc.
      all: try assumption.
      all: try (unfold sep).
      all: try (apply ret_ok_lit; [clear; lia | reflexivity]).
      all: try lazymatch goal with |- cell _ _ (cv_ZP v + 0) _ _ => exact Z0 end.
      all: try lazymatch goal with |- isl_scalars _ _ _ _ _ _ _ => rewrite <- is6_scalars_isl; exact Msc end.
      all: try lazymatch goal with |- cells _ _ (cv_WB v) 1 1 _ _ => destruct (Z.eq_dec (cv_WN v) 0) as [E0|E0]; [rewrite E0; intros i Hi; exfalso; clear - Hi; lia | exact (Mwin E0)] end.
      all: try exact Mrod.
      all: try lazymatch goal with |- mapped _ _ _ => intros x Hx; first [apply Mmap_f | apply Mmap_P | apply Mmap_Z | apply Mmap_S]; clear - Hx Csp; lia end.
      all: try lazymatch goal with |- match ?p with _ => _ end => first [exact Slc | exact Sdc] end.
      all: try (unfold ROD6_LO, ROD6_HI, IMG6_TOP, is6_LENFIX, is6_DISTFIX in *;
                first [ clear - Csp; lia | clear - CZP; lia | clear - CS; lia | clear - CI0 Cil; lia | clear - CP0; lia | clear - CWB; lia
                      | clear - CoZ; lia | clear - CoS; lia | clear - CoP; lia
                      | clear - CfZ Csp; lia | clear - CfS Csp; lia | clear - CfI Csp HNI; lia | clear - CfP Csp HNO; lia | clear - CfW Csp; lia
                      | clear - CZO; lia | clear - CSP HNO; lia | clear - CIP; lia | clear - CPW HNO; lia | clear - CZS; lia | clear - CZI; lia
                      | clear - CZW; lia | clear - CSI HNI; lia | clear - CSW; lia
                      | clear - Rnx0 Rhv0 Rnh PNI; lia | clear - Rpt0 Rlf0 Rpl; lia | clear - Rout Routp Rpt0 Rlf0 Rpl; lia | clear - Rout PNO; lia | clear - PNO; lia
                      | clear - Rhold; lia | clear - Rbits; lia | clear - Hwh Hwn Hws CWB; lia | clear - RtL RtD; lia | clear - Hsane; lia
                      | clear - CZP CS8; lia | clear - CWB Hwl; lia | clear - CWB Hwl CI0; lia ]). }

    pose proof (FFOK _ _ _ _ s c r ob HP Hmode Hh6 Hl258 Hobl Hagree ltac:(rewrite <- Hobl; exact Hobb)) as Hok.
    change (ff_ok sR cM r = true) in Hok.
    assert (Hmsg : cell s6u_segs M1 (cv_ZP v + 48) 8 (msg6_addr (ic_msg cM))) by (rewrite Fo11, <- K7; exact Z48).
    pose proof IFAST as IF. unfold inflate_fast_spec6, inflate_fast_spec_at in IF.
    destruct (IF M1 (cv_sp v - 416) (zw 0x20a18) sR cM r (cv_ZP v) (cv_S v) (cv_I0 v) (cv_P0 v) (cv_WB v) R3 PRE Hmsg
                ltac:(clear - Rout Rlf0 PNO; lia) A1 ltac:(replace (cv_sp v - 416 + 160) with (cv_sp v - 256) by (clear; lia); exact A2) A10 A11 Hok)
      as (R4 & m' & Hms & B2 & Bkept & POST). clear IF.
    unfold FPOST in POST. cbv zeta in POST.
    destruct POST as (Pr & Pin & (Pti & Pto & Pad & Pdt) & Plen & Pb & Pcells & Pz0 & Pz8 & Pz24 & Pz32 & Psc & Pmsg & Pag & Pgrow & Pnin & Pnout & Phold & Pbits).
    rewrite Fo6, Hobl in Plen, Pb, Pcells, Pnout, Pag. rewrite Fo5 in Pin, Pnin. rewrite Cil in Pnin.
    destruct (FASTOK _ _ _ _ s c r HP Hmode Hh6 Hl258 HB8) as (HG & HPI1 & Hb8).
    change (RESTORE (mkW s c r)) with (mkW sR cR r) in HPI1, Hb8 |- *.
    assert (HG' : ffG (mkW sR cM r) = true).
    { unfold cM. rewrite (GFAST_OB sR cR ob r ltac:(rewrite Hobl, K6, Col; reflexivity) ltac:(rewrite K3, K6; exact Hagree)). exact HG. }
    assert (Hceq : ceq cR cM).
    { unfold ceq, agree_below. rewrite Fo6, K3, K6, Hobl, Col. split; [reflexivity|]. split; [reflexivity|]. exact Hagree. }
    destruct (inflate_fast_rel sR cR cM r Hceq HG') as (Es & Er & Hceq' & Elen).
    destruct (lf_shape_msg sR cR r) as (fh & fb & om & ob1 & fi & fo & ai & ao & omsg & Hom & Homsg & Es1 & Er1 & Ec1).
    remember (inflate_fast (mkW sR cM r)) as w2 eqn:Ew2 in *.
    remember (inflate_fast (mkW sR cR r)) as w1 eqn:Ew1 in *.
    destruct w1 as [s1 c1 r1]. destruct w2 as [s2 c2 r2]. cbn [w_s w_c w_r] in *. subst r2 s2 r1.
    destruct Hceq' as [Ec2 [Elen2 Hag2]].
    pose proof (icset_outbuf_facts c1 (ic_outbuf c2)) as G. rewrite <- Ec2 in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
    rewrite G1 in Pz0, Pnin. rewrite G2 in Pz8. rewrite G3 in Pz24, Pnout. rewrite G4 in Pz32. rewrite G5 in Pin.
    rewrite G7 in Pti. rewrite G8 in Pto. rewrite G9 in Pad. rewrite G10 in Pdt. rewrite G11 in Pmsg.
    rewrite Fo7 in Pti. rewrite Fo8 in Pto. rewrite Fo9 in Pad. rewrite Fo10 in Pdt.
    assert (Eflds : is_lens s1 = is_lens s /\ is_work s1 = is_work s /\ is_codes s1 = is_codes s /\ is_window s1 = is_window s
                    /\ is_self_blk s1 = is_self_blk s /\ is_window_blk s1 = is_window_blk s /\ is_wbits s1 = is_wbits s
                    /\ is_hold s1 = fh /\ is_bits s1 = fb
                    /\ (is_mode s1 = LEN \/ is_mode s1 = TYPE \/ is_mode s1 = BAD)
                    /\ (is_wrap s1 = is_wrap s /\ is_flags s1 = is_flags s /\ is_havedict s1 = is_havedict s)).
    { rewrite Es1. clear - Hom Hmode. subst sR. destruct om as [md|].
      - assert (Hmd : md = TYPE \/ md = BAD) by (destruct Hom as [X|[X|X]]; [discriminate X | injection X as <-; left; reflexivity | injection X as <-; right; reflexivity]).
        destruct s; cbn; repeat split; try reflexivity. right; exact Hmd.
      - destruct s; cbn in Hmode |- *; repeat split; try reflexivity. left; exact Hmode. }
    destruct Eflds as (El1 & Ewk1 & Ecd1 & Ewin1 & Esb1 & Ewb1 & Ewbits1 & Efh & Efb & Hmd1 & (Ewr1 & Efl1 & Ehd1)).
    assert (Hmsg1 : ic_msg c1 = ic_msg c \/ lf_msg_ok (Some (ic_msg c1))).
    { rewrite Ec1. rewrite <- K7. clear - Homsg. destruct omsg as [mg|]; [right; match goal with |- lf_msg_ok (Some ?x) => replace x with mg by (destruct cR; reflexivity) end; exact Homsg | left; destruct cR; reflexivity]. }
    rewrite Efb in Pbits, Phold. rewrite Efh in Phold.
    assert (TA : forall a (w : nat) x, cell s6u_segs M1 a w x -> 0 <= a -> a + Z.of_nat w <= 2 ^ 64 ->
              (a + Z.of_nat w <= cv_sp v - 416 \/ cv_sp v - 256 <= a) ->
              (a + Z.of_nat w <= cv_P0 v \/ cv_P0 v + cv_NO v <= a) ->
              (a + Z.of_nat w <= cv_ZP v \/ cv_ZP v + 12 <= a) -> (a + Z.of_nat w <= cv_ZP v + 24 \/ cv_ZP v + 36 <= a) -> (a + Z.of_nat w <= cv_ZP v + 48 \/ cv_ZP v + 56 <= a) ->
              (a + Z.of_nat w <= cv_S v + 8 \/ cv_S v + 12 <= a) -> (a + Z.of_nat w <= cv_S v + 96 \/ cv_S v + 108 <= a) ->
              cell s6u_segs m' a w x).
    { clear - Pag. intros a w x Hc Ha Hw D1 D2 D3 D4 D5 D6 D7. apply (cell_agree_out s6u_segs _ M1 m' a w x Pag); [| exact Ha | exact Hw | exact Hc].
      intros y Hy. unfold FFall. cbn [in_franges]. lia. }
    assert (TAs : forall P st (w : nat) n f, cells s6u_segs M1 P st w n f -> Z.of_nat w <= st -> 0 <= P -> P + st * n <= 2 ^ 64 ->
              (P + st * n <= cv_sp v - 416 \/ cv_sp v - 256 <= P) ->
              (P + st * n <= cv_P0 v \/ cv_P0 v + cv_NO v <= P) ->
              (P + st * n <= cv_ZP v \/ cv_ZP v + 56 <= P) ->
              (P + st * n <= cv_S v + 8 \/ cv_S v + 108 <= P) ->
              cells s6u_segs m' P st w n f).
    { clear - Pag. intros P st w n f Hc Hwst HP HPn D1 D2 D3 D4. apply (cells_agree_out s6u_segs _ M1 m' P st w n f Pag); [| exact Hwst | exact HP | exact HPn | exact Hc].
      intros y Hy. unfold FFall. cbn [in_franges]. lia. }

    assert (EsR2 : is_lens sR = is_lens s /\ is_work sR = is_work s) by (subst sR; clear; destruct s; split; reflexivity).
    destruct EsR2 as [EsRl EsRw].
    pose proof (FFRAME sR cM r) as FR. cbv zeta in FR. rewrite <- Ew2 in FR. cbn [w_c] in FR. rewrite Fo3, Fo6 in FR.
    destruct FR as (FRle & FRlen & FRget). rewrite G3 in FRle, FRget.
    exists R4, m'.
    split; [unfold A6_INFLATE_FAST in Hms; exact Hms|].
    split; [replace (cv_sp v - 256) with (cv_sp v - 416 + 160) by (clear; lia); exact B2|].
    split; [exact Bkept|].
    split.
    { unfold LOADl. cbn [w_s w_c w_r]. constructor; cbn [w_s w_c w_r ir_put ir_out ir_left ir_ret].
      - intros x Hx. rewrite (Pag x); [exact (Mrod x Hx)|]. unfold FFall. cbn [in_franges]. unfold ROD6_LO, ROD6_HI in Hx.
        specialize (CoP HNO). clear - Hx Csp CoP CoZ CoS. lia.
      - rewrite is6_scalars_isl. unfold is6_LENFIX, is6_DISTFIX in Psc. exact Psc.
      - rewrite El1, <- EsRl. apply (TAs _ _ _ _ _ Mlens); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | clear - CfS; lia | specialize (CSP HNO); clear - CSP; lia | clear - CZS; lia | clear; lia].
      - rewrite Ewk1, <- EsRw. apply (TAs _ _ _ _ _ Mwork); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | clear - CfS; lia | specialize (CSP HNO); clear - CSP; lia | clear - CZS; lia | clear; lia].
      - rewrite Ecd1, <- Ecd. apply (TAs _ _ _ _ _ Mcodes); [cbn; clear; lia | clear - CS; lia | clear - CS; lia | clear - CfS; lia | specialize (CSP HNO); clear - CSP; lia | clear - CZS; lia | clear; lia].
      - intros HWN. rewrite Ewin1, <- Ewin. apply (TAs _ _ _ _ _ (Mwin HWN)); [cbn; clear; lia | clear - CWB; lia | clear - CWB; lia | clear - CfW HWN CWB; lia | specialize (CPW HNO); clear - CPW HWN CWB; lia | clear - CZW HWN CWB; lia | clear - CSW HWN CWB; lia].
      - rewrite Pin, <- K5. apply (TAs _ _ _ _ _ Minp); [cbn; clear; lia | clear - CI0; lia | clear - CI0; lia | specialize (CfI HNI); clear - CfI; lia | clear - CIP HNI; lia | clear - CZI HNI; lia | specialize (CSI HNI); clear - CSI; lia].
      - intros i Hi. rewrite <- (Hag2 i Hi). apply Pcells. clear - Hi Pnout. lia.
      - unfold izs6. rewrite Pti, Pto, Pad, <- K8, <- K9, <- K10.
        split; [exact Pz0|]. split; [exact Pz8|].
        split; [apply (TA _ _ _ Z16); specialize (CfZ); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        split; [exact Pz24|]. split; [exact Pz32|].
        split; [apply (TA _ _ _ Z40); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        split; [exact Pmsg|].
        split; [apply (TA _ _ _ Z56); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        split; [apply (TA _ _ _ Z64); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        split; [apply (TA _ _ _ Z72); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        split; [apply (TA _ _ _ Z80); clear - CZP CfZ CZO CZS HNO; cbn; lia|].
        apply (TA _ _ _ Z96); clear - CZP CfZ CZO CZS HNO; cbn; lia.
      - unfold iframe6. unfold INF_FRAME.
        split.
        { intros rg o Hro. pose proof (Fsv rg o Hro) as X. cbn in Hro.
          assert (Ho : 152 <= o /\ o + 8 <= 256)
            by (clear -Hro; destruct Hro as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-; lia). clear Hro.
          apply (TA _ _ _ X); specialize (CfP HNO); clear - Csp CfP CfZ CfS Ho; cbn; lia. }
        rewrite ?Z.add_0_r.
        repeat match goal with |- _ /\ _ => split end;
          (eapply TA; [eassumption | | | | | | | | |]; specialize (CfP HNO); clear - Csp CfP CfZ CfS; cbn; lia).
      - apply (TA _ _ _ Moutc); specialize (CfP HNO); clear - Csp CfP CfZ CfS; cbn; lia.
      - apply (TA _ _ _ Mleftc); specialize (CfP HNO); clear - Csp CfP CfZ CfS; cbn; lia.
      - intros x Hx. apply Pgrow. apply Mmap_f. exact Hx.
      - intros x Hx. apply Pgrow. apply Mmap_Z. exact Hx.
      - intros x Hx. apply Pgrow. apply Mmap_S. exact Hx.
      - intros x Hx. apply Pgrow. apply Mmap_P. exact Hx.
      - intros HWN x Hx. apply Pgrow. apply (Mmap_W HWN). exact Hx. }
    assert (HF1 : MFRAME v (ir_put r) (ir_put r) M M1).
    { unfold M1, lf_tower.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r)); [| clear; lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply MFRAME_refl. }
    split.
    { assert (HRC1 : RETC v (mkW sR cR r) M1).
      { unfold M1, lf_tower. apply (RETC_regs v (mkW s c r)); [| reflexivity].
        do 6 (apply (RETC_other v C); [| clear - CS CZP; lia | rewrite length_Z_to_le_bytes; clear - CS CZP; cbn; lia
                                       | rewrite length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; clear - CfS CS CfZ CZP; lia]).
        exact HRC. }
      unfold RETC, LOAD, wset_r in HRC1 |- *. cbn [w_r ir_ret] in HRC1 |- *. unfold INF_FRAME in HRC1 |- *.
      apply (TA _ _ _ HRC1); specialize (CfP HNO); clear - Csp CfP CfZ CfS; cbn; lia. }
    split.
    { unfold LOAD, wset_r. cbn [w_r ir_put].
      destruct HF1 as (_ & Hg1 & HE1). unfold INF_FRAME, INF_SCRATCH in HE1. cbn [w_c].
      split; [exact FRle|]. split; [intros x Hx; apply Pgrow, Hg1, Hx|].
      unfold INF_FRAME, INF_SCRATCH. intros x N1 N2 N3 N4.
      destruct (Z_lt_le_dec (bv_unsigned x) (cv_P0 v)) as [Hlo|Hlo]; [| destruct (Z_lt_le_dec (bv_unsigned x) (cv_P0 v + cv_NO v)) as [Hin|Hhi]].
      - rewrite (Pag x); [apply HE1; [assumption | assumption | assumption | clear; lia]|]. unfold FFall. cbn [in_franges]. clear - Hlo N1 N2 N3. lia.
      - set (i := bv_unsigned x - cv_P0 v).
        assert (Hi : 0 <= i < cv_NO v /\ (i < ir_put r \/ ic_next_out c1 <= i)) by (subst i; clear - Hlo Hin N4; lia).
        rewrite <- (HE1 x N1 N2 N3 ltac:(clear; lia)).
        assert (Ex : x = zw (cv_P0 v + 1 * i)) by (subst i; symmetry; rewrite Z.mul_1_l, Zplus_minus; apply zw_u).
        rewrite Ex. apply (cell1_same M1 m' (cv_P0 v + 1 * i) (arr_get ob i)).
        + exact (Hobc i ltac:(rewrite Hobl; exact (proj1 Hi))).
        + rewrite <- (FRget i (proj2 Hi)). exact (Pcells i (proj1 Hi)).
        + apply Mmap_P. rewrite u_zw_small by (clear - Hi CP0; lia). clear - Hi; lia.
        + apply Pgrow, Mmap_P. rewrite u_zw_small by (clear - Hi CP0; lia). clear - Hi; lia.
      - rewrite (Pag x); [apply HE1; [assumption | assumption | assumption | clear; lia]|]. unfold FFall. cbn [in_franges]. clear - Hhi N1 N2 N3. lia. }
    split; [reflexivity|]. split; [exact Hmd1|]. rewrite Efb, Efh. split; [exact Pbits|]. split; [exact Phold|].
    split; [exact HPI1|].
    unfold same_blocks. rewrite Esb1, Ewb1, Ewbits1, Ewr1, Efl1, Ehd1.
    split; [repeat split; reflexivity|]. do 4 (split; [reflexivity|]). exact Hmsg1.
  Qed.
  Definition ret_pins : list (Z * expr) := [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat)].

  Local Ltac ret_run mode_lit dirs rds R4 M4 r' R5 HR5 Hfr5 Hms5 :=
    arm_symexP (@nil (Z * expr)) ilS 30%nat dirs
      ([RVal (ELit 16209); RVal (EAdd (EVar 43%nat) (EVar 44%nat)); RVal (EVar 36%nat); RVal (EAdd (EVar 37%nat) (EVar 38%nat)); RVal (EVar 39%nat);
        RVal (ELit mode_lit); RVal (EVar 40%nat); RVal (EVar 41%nat); RVal (EVar 35%nat)] ++ rds)
      ret_pins (@nil (nat * Z)) v r' (@nil Z) NoVals F0
      (mkst R4 (Z_to_bv 64 0x20a18) M4 s6u_rom) R5 HR5 Hfr5 Hms5.

  Lemma lf_ret : forall s1 c1 (r : iregs) R4 M4,
    let w1 := LOAD (mkW s1 c1 r) in
    LMEM v (LOADl (mkW s1 c1 r) (ir_left r)) M4 -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w1 ->
    (is_mode s1 = LEN \/ is_mode s1 = TYPE \/ is_mode s1 = BAD) -> 0 <= is_bits s1 < 8 ->
    getr R4 2 = zw (cv_sp v - 256) -> getr R4 8 = zw (cv_S v) -> getr R4 18 = zw (cv_ZP v) ->
    getr R4 3 = getr (cv_R0 v) 3 -> getr R4 4 = getr (cv_R0 v) 4 ->
    let w' := if is_mode s1 =? TYPE then mkW (iset_back s1 (-1)) c1 (w_r w1) else w1 in
    let ML := wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ic_avail_out c1)) in
    let M' := if is_mode s1 =? TYPE then wbytes ML (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (-1)) else ML in
    exists R',
      msteps s6u_segs (mkst R4 (Z_to_bv 64 0x20a18) M4 s6u_rom) (mkst R' (Z_to_bv 64 (arm6_pc (is_mode s1))) M' s6u_rom)
      /\ LFIX v R' /\ LVARS v w' R' /\ getr R' 27 = zw (-3)
      /\ LMEM v w' M'.
  Proof.
    intros s1 c1 r R4 M4. cbv zeta. intros HM HP Hmd Hb8 A2 A27 A8 A3 A4.
    open_ictx C. pose proof HP as HP0. open_pinv HP0. open_rinv RI. open_cinv CI.
    unfold LOAD, LOADl, wset_r in *. cbn [w_s w_c w_r ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in *.
    pose proof HM as HM0. open_lmem HM. open_frame Mfr. open_zs Mzs. unfold mapped in *.
    pose proof (is6_mode _ _ _ _ Msc) as C8. pose proof (is6_hold _ _ _ _ Msc) as C80. pose proof (is6_bits _ _ _ _ Msc) as C88.
    assert (Hput : 0 <= ic_next_out c1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    set (r' := mkIR (ic_next_in c1) (ic_avail_in c1) (ic_next_out c1) (ic_avail_out c1) (is_hold s1) (is_bits s1) (ir_in r) (ir_out r) (ir_ret r)) in *.
    set (rl := mkIR (ic_next_in c1) (ic_avail_in c1) (ic_next_out c1) (ir_left r) (is_hold s1) (is_bits s1) (ir_in r) (ir_out r) (ir_ret r)) in *.
    change (ic_next_in c1) with (ir_next r') in Z0. rewrite Z.add_0_r in Z0. change (ic_avail_in c1) with (ir_have r') in Z8.
    change (ic_next_out c1) with (ir_put r') in Z24. change (ic_avail_out c1) with (ir_left r') in Z32.
    change (is_hold s1) with (ir_hold r') in C80. change (is_bits s1) with (ir_bits r') in C88.
    change (ir_out r) with (ir_out r') in Moutc.
    assert (B36 : 0 <= ir_have r' < 2 ^ 31) by (subst r'; cbn; clear - Rhv0 Rnh Rnx0 CI0; lia).
    assert (B38 : 0 <= ir_put r' < 2 ^ 31) by (subst r'; cbn; clear - Rpt0 Rpl Rlf0 CP0; lia).
    assert (B39 : 0 <= ir_left r' < 2 ^ 31) by (subst r'; cbn; clear - Rpt0 Rpl Rlf0 CP0; lia).
    assert (B40 : 0 <= ir_hold r' < 2 ^ 64) by (subst r'; cbn; clear - Rhold64; exact Rhold64).
    assert (B41 : 0 <= ir_bits r' < 64) by (subst r'; cbn; clear - Hb8; lia).
    assert (B42 : 0 <= ir_out r' < 2 ^ 31) by (subst r'; cbn; clear - Rout Rlf0 CP0; lia).
    assert (B44 : 0 <= ir_next r' < 2 ^ 31) by (subst r'; cbn; clear - Rnx0 Rnh Rhv0 CI0; lia).
    assert (HML : LMEM v (mkW s1 c1 r') (wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r')))).
    { apply (LMEM_store_leftc v C s1 c1 rl r' M4 HM0); [exact Hput | reflexivity | clear - B39; subst r'; cbn in *; lia | reflexivity]. }
    destruct Hmd as [Hm|[Hm|Hm]]; rewrite Hm in C8 |- *.
    2:{
      change (TYPE =? TYPE) with true. cbv iota.
      ret_run 16191 [true] [RVal (EAdd (EVar 33%nat) (ELit 7160))] R4 M4 r' R5 HR5 Hfr5 Hms5.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTR1" G end.
      set (ML := wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r'))) in *.
      set (M5 := wbytes ML (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (-1))) in *.
      assert (HM5 : LMEM v (mkW (iset_back s1 (-1)) c1 r') M5).
      { apply (LMEM_store_scalar v C s1 c1 r' _ ML 7164 _ HML); [clear; lia | cbn; clear; lia | exact Hput | | | | | ]; try (destruct s1; reflexivity).
        apply (is6_upd_back ML (cv_S v) _ s1 (-1) (lm_sc _ _ _ HML)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      symex_reg HR5 (26%bv : reg) as Q25. symex_reg HR5 (23%bv : reg) as Q24. symex_reg HR5 (9%bv : reg) as Q9.
      symex_reg HR5 (25%bv : reg) as Q22. symex_reg HR5 (19%bv : reg) as Q18. symex_reg HR5 (1%bv : reg) as Q1.
      symex_reg HR5 (13%bv : reg) as Q13. symex_reg HR5 (11%bv : reg) as Q11.
      assert (Q2 : getr R5 2 = zw (cv_sp v - 256)) by (rewrite (Hfr5 (2%bv : reg) eq_refl); exact A2).
      assert (Q27 : getr R5 8 = zw (cv_S v)) by (rewrite (Hfr5 (8%bv : reg) eq_refl); exact A27).
      assert (Q8 : getr R5 18 = zw (cv_ZP v)) by (rewrite (Hfr5 (18%bv : reg) eq_refl); exact A8).
      assert (Q3 : getr R5 3 = getr (cv_R0 v) 3) by (rewrite (Hfr5 (3%bv : reg) eq_refl); exact A3).
      assert (Q4 : getr R5 4 = getr (cv_R0 v) 4) by (rewrite (Hfr5 (4%bv : reg) eq_refl); exact A4).
      clear Hfr5 HR5.
      destruct (disp6u v (iset_back s1 (-1)) c1 r' R5 M5 C HM5 Q2 Q27 ltac:(replace (is_mode (iset_back s1 (-1))) with TYPE by (rewrite <- Hm; destruct s1; reflexivity); cbv [HEAD TYPE]; lia))
        as (R' & Hms & G26 & Hfr).
      replace (is_mode (iset_back s1 (-1))) with TYPE in Hms by (rewrite <- Hm; destruct s1; reflexivity).
      exists R'. split; [eapply msteps_trans; [subst M5 ML; by_run Hms5 | subst M5 ML; by_run Hms]|].
      split; [unfold LFIX, INF_FRAME; regs_via Hfr|].
      split; [unfold LVARS; cbn [w_r]; regs_via Hfr|].
      split; [exact G26|].
      exact HM5. }
    -
      change (LEN =? TYPE) with false. cbv iota.
      ret_run 16200 [false] (@nil (option expr)) R4 M4 r' R5 HR5 Hfr5 Hms5.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTR3" G end.
      set (ML := wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r'))) in *.
      symex_reg HR5 (26%bv : reg) as Q25. symex_reg HR5 (23%bv : reg) as Q24. symex_reg HR5 (9%bv : reg) as Q9.
      symex_reg HR5 (25%bv : reg) as Q22. symex_reg HR5 (19%bv : reg) as Q18. symex_reg HR5 (1%bv : reg) as Q1.
      symex_reg HR5 (13%bv : reg) as Q13. symex_reg HR5 (11%bv : reg) as Q11.
      assert (Q2 : getr R5 2 = zw (cv_sp v - 256)) by (rewrite (Hfr5 (2%bv : reg) eq_refl); exact A2).
      assert (Q27 : getr R5 8 = zw (cv_S v)) by (rewrite (Hfr5 (8%bv : reg) eq_refl); exact A27).
      assert (Q8 : getr R5 18 = zw (cv_ZP v)) by (rewrite (Hfr5 (18%bv : reg) eq_refl); exact A8).
      assert (Q3 : getr R5 3 = getr (cv_R0 v) 3) by (rewrite (Hfr5 (3%bv : reg) eq_refl); exact A3).
      assert (Q4 : getr R5 4 = getr (cv_R0 v) 4) by (rewrite (Hfr5 (4%bv : reg) eq_refl); exact A4).
      clear Hfr5 HR5.
      destruct (disp6u v s1 c1 r' R5 ML C HML Q2 Q27 ltac:(rewrite Hm; cbv [HEAD LEN BAD]; lia)) as (R' & Hms & G26 & Hfr).
      rewrite Hm in Hms.
      exists R'. split; [eapply msteps_trans; [subst ML; by_run Hms5 | subst ML; by_run Hms]|].
      split; [unfold LFIX, INF_FRAME; regs_via Hfr|].
      split; [unfold LVARS; cbn [w_r]; regs_via Hfr|].
      split; [exact G26|].
      exact HML.
    -
      change (BAD =? TYPE) with false. cbv iota.
      ret_run 16209 [false] (@nil (option expr)) R4 M4 r' R5 HR5 Hfr5 Hms5.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTR5" G end.
      set (ML := wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r'))) in *.
      symex_reg HR5 (26%bv : reg) as Q25. symex_reg HR5 (23%bv : reg) as Q24. symex_reg HR5 (9%bv : reg) as Q9.
      symex_reg HR5 (25%bv : reg) as Q22. symex_reg HR5 (19%bv : reg) as Q18. symex_reg HR5 (1%bv : reg) as Q1.
      symex_reg HR5 (13%bv : reg) as Q13. symex_reg HR5 (11%bv : reg) as Q11.
      assert (Q2 : getr R5 2 = zw (cv_sp v - 256)) by (rewrite (Hfr5 (2%bv : reg) eq_refl); exact A2).
      assert (Q27 : getr R5 8 = zw (cv_S v)) by (rewrite (Hfr5 (8%bv : reg) eq_refl); exact A27).
      assert (Q8 : getr R5 18 = zw (cv_ZP v)) by (rewrite (Hfr5 (18%bv : reg) eq_refl); exact A8).
      assert (Q3 : getr R5 3 = getr (cv_R0 v) 3) by (rewrite (Hfr5 (3%bv : reg) eq_refl); exact A3).
      assert (Q4 : getr R5 4 = getr (cv_R0 v) 4) by (rewrite (Hfr5 (4%bv : reg) eq_refl); exact A4).
      clear Hfr5 HR5.
      destruct (disp6u v s1 c1 r' R5 ML C HML Q2 Q27 ltac:(rewrite Hm; cbv [HEAD LEN BAD]; lia)) as (R' & Hms & G26 & Hfr).
      rewrite Hm in Hms.
      exists R'. split; [eapply msteps_trans; [subst ML; by_run Hms5 | subst ML; by_run Hms]|].
      split; [unfold LFIX, INF_FRAME; regs_via Hfr|].
      split; [unfold LVARS; cbn [w_r]; regs_via Hfr|].
      split; [exact G26|].
      exact HML.
  Qed.

  Local Ltac bk3 s1 Hmd :=
    unfold bk_ok; clear - Hmd; destruct s1; cbn in Hmd |- *; split; intros EQ; exfalso;
    destruct Hmd as [E|[E|E]]; rewrite E in EQ; discriminate.

  Lemma lenF_core : forall s c r R M,
    pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) (mkW s c r) -> is_mode s = LEN -> len_facts v s c ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> LFIXc v R -> getr R 13 = zw (cv_ZP v) -> LVARS v (mkW s c r) R ->
    6 <= ir_have r -> 258 <= ir_left r -> ir_bits r < 8 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x209d4) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_LEN ivar_ref (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M HP Hmode HD HM HRC HX HF G13 HV Hh6 Hl258 HB8.
    rewrite (arm_LEN_fast s c r Hh6 Hl258 HB8). cbv zeta.
    pose proof HP as HP0. open_pinv HP0.
    open_ictx C. open_lx HX. pose proof HF as HF0. open_fixc HF0.
    destruct (lf_pre s c r R M HD RI HM HF G13 HV Hh6 Hl258 HB8) as (R1 & Hms1 & A10 & A11 & A1 & A2 & Hfr1).
    destruct (lf_call s c r M R1 HP Hmode Hh6 Hl258 HB8 HD HM HRC A1 A2 A10 A11)
      as (R4 & M4 & Hms2 & B2 & Bkept & HM4 & HRC4 & HF4 & Er & Hmd & Hb8 & Hhold & HP4 & (Hsb & Ewr & Ewb & Efl & Ehd & Hmsg)).
    remember (inflate_fast (RESTORE (mkW s c r))) as w1 eqn:Ew1. destruct w1 as [s1 c1 r1]. cbn [w_s w_c w_r] in *. subst r1.
    assert (KR : forall k : reg, In k if_kept -> reg_in k [1; 10; 11; 12]%bv = false -> getr R4 k = getr R k)
      by (intros k Hk Hk'; rewrite (Bkept k Hk); exact (Hfr1 k Hk')).
    destruct (lf_ret s1 c1 r R4 M4 HM4 HP4 Hmd Hb8 B2
                ltac:(rewrite (KR (8%bv : reg)); [exact G27 | cbn; clear; tauto | reflexivity])
                ltac:(rewrite (KR (18%bv : reg)); [exact G8 | cbn; clear; tauto | reflexivity])
                ltac:(rewrite (KR (3%bv : reg)); [exact G3 | cbn; clear; tauto | reflexivity])
                ltac:(rewrite (KR (4%bv : reg)); [exact G4 | cbn; clear; tauto | reflexivity]))
      as (R' & Hms3 & HF' & HV' & G26' & HM').
    unfold LOAD, LOADl, wset_r in HV', HM', HRC4, HF4, HP4 |- *. cbn [w_s w_c w_r ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret] in HV', HM', HRC4, HF4, HP4 |- *.
    assert (Hmsg' : -1 <= ic_msg c1 <= 27).
    { destruct Hmsg as [E | [E|[E|[E|E]]]]; [rewrite E; exact Xmsg | discriminate E | injection E as E | injection E as E | injection E as E];
        rewrite E; cbv; split; discriminate. }
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hlive : live_mode (is_mode s1)) by (destruct Hmd as [E|[E|E]]; rewrite E; live_mode_tac).
    destruct Hsb as (S1 & S2 & S3).
    unfold RETC in HRC4 |- *. cbn [w_r ir_ret] in HRC4 |- *.
    assert (HRCL : cell s6u_segs (wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ic_avail_out c1))) (cv_sp v - INF_FRAME + 64) 8 (ir_ret r)).
    { apply (cell_write_other _ _ _ _ _ _ _ HRC4); rewrite ?length_Z_to_le_bytes; cbn; unfold INF_FRAME in *; clear - Csp; lia. }
    destruct (is_mode s1 =? TYPE) eqn:ET.
    -
      exists R', (wbytes (wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ic_avail_out c1))) (zw (cv_S v + 7164)) (Z_to_le_bytes 4 (-1))), (arm6_pc (is_mode s1)).
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      cbn [arm_post w_s w_r ir_put]. replace (is_mode (iset_back s1 (-1))) with (is_mode s1) by (destruct s1; reflexivity).
      split; [reflexivity|]. split; [| split].
      + split; [exact HM'|]. split; [| split].
        * cbn [w_r ir_ret]. apply (cell_write_other _ _ _ _ _ _ _ HRCL); rewrite ?length_Z_to_le_bytes; cbn; unfold sep, INF_FRAME, INF_SCRATCH in *; clear - Csp CS CfS; lia.
        * apply (LX_step0 v s c r _ c1 _ HX NH NB); cbn [ir_in ir_ret];
            [ destruct s1; exact Ewr | destruct s1; exact Ewb | destruct s1; exact Efl
            | replace (is_mode (iset_back s1 (-1))) with (is_mode s1) by (destruct s1; reflexivity); exact Hlive
            | reflexivity | exact Xret | exact Hmsg' | destruct s1; exact Ehd | bk3 s1 Hmd ].
        * split; [exact HF'|]. split; [exact HV'|]. intros _; exact G26'.
      + unfold same_blocks in *. destruct s1; cbn in S1, S2, S3 |- *. split; [exact S1 | split; [exact S2 | exact S3]].
      + apply (MFRAME_store v (ir_put r) (ic_next_out c1) (ic_next_out c1)); [| clear; lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ic_next_out c1) (ic_next_out c1) M M4); [exact HF4 | clear; lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
    -
      exists R', (wbytes M4 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ic_avail_out c1))), (arm6_pc (is_mode s1)).
      split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
      cbn [arm_post w_s w_r ir_put].
      split; [reflexivity|]. split; [| split].
      + split; [exact HM'|]. split; [| split].
        * cbn [w_r ir_ret]. exact HRCL.
        * apply (LX_step0 v s c r _ c1 _ HX NH NB); cbn [ir_in ir_ret];
            [ exact Ewr | exact Ewb | exact Efl | exact Hlive | reflexivity | exact Xret | exact Hmsg' | exact Ehd | bk3 s1 Hmd ].
        * split; [exact HF'|]. split; [exact HV'|]. intros _; exact G26'.
      + exact (conj S1 (conj S2 S3)).
      + apply (MFRAME_store v (ir_put r) (ic_next_out c1) (ic_next_out c1) M M4); [exact HF4 | clear; lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
  Qed.
End LenFast.
End FXG.
