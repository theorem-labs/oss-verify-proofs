(* reloc-zl14c *)
(* [U14] inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.U1A Require Import ItA_base ItA_ldefs ItA_switch ItA_here ItA_fill ItA_cnt2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

(* [comment removed for export] *)
Ltac trip_facts TOK :=
  pose proof (trip_ok_facts _ 288 320 1444 _ TOK) as (Fsym & Flen & Fdrop & Fcurr & Fhuff & Fnext & Fused & Fmin & Fw & Fwm & Ffit & Flook & Fcont);
  cbn [x_ty x_max x_lens x_lens_ofs x_table x_root x_mask itm_ctx] in Fsym, Flen, Fdrop, Fcurr, Fhuff, Fnext, Fused, Fmin, Fw, Fwm, Ffit, Flook, Fcont;
  rewrite <- ?NE_ext_len in Fwm; rewrite ?Z.shiftl_1_l in Ffit; box Fwm; box Flook; box Fcont.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top : Z) (m1 : amem).
  Variables (ty : codetype) (lf wf cf : Z -> Z) (lo codes nx bits : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis C : itc ty lf lo codes nx bits cf wf.

  Notation LP := (S + 168 + 2 * lo).
  Notation cntAr := (cntA lf lo codes).
  Notation mx := (mxA lf lo codes).
  Notation mn := (mnA lf lo codes).
  Notation rt := (rootA lf lo codes bits).
  Notation work1Ar := (work1A lf lo codes wf).
  Notation w1 := (arr_get (work1A lf lo codes wf)).
  Notation X := (itm_ctx ty (lensA lf) lo nx rt mx).
  Notation MST := (mst SP SPA S F PB LP gp tp FR fc rt mx).
  Notation MINV := (fun m st => minv SPA S F PB m1 m ty rt nx bits lf w1 st).
  Notation SHPB := (Z_to_bv 64 (Z.shiftr PB 3 + 2147450880)).
  (* [comment removed for export] *)
  Notation UST st x1 x5 x6 x7 x10 x11 x16 x17 x25 x28 x29 pc m :=
    (bst SP SPA S F PB LP gp tp FR fc x1 x5 x6 x7 x10 x11 SHPB (Z_to_bv 64 rt) (Z_to_bv 64 mx) (Z_to_bv 64 (tr_len X st)) x16 x17
         (Z_to_bv 64 (tr_huff st)) x25 x28 x29 (Z_to_bv 64 (S + 1384 + 4 * t_next st)) (Z_to_bv 64 (tr_sym st)) pc m).

  (* [comment removed for export] *)
  (* [U14] the 1.3.1 register homes of ALL moved to 1.4 by tools/regmap_text_gr.py (t0>a7 t1>t2 t2>t1 a7>t0) *)
  (* [P14] the sub / currsz / link blocks' own 1.4 register homes (unc14.dis 0x960b8 .. 0x96254 against
     unc131.dis 0x95c0c .. 0x95dac, instruction by instruction): drop t4 -> ra (0x96130 mv ra,a3 / mv ra,a7), the loop index
     t0 -> a7 (0x9614c mv a7,a5), curr / count t1 -> t2, low t2 -> t1 (0x960c0 and t1,s8,a0), the constant 1 t3 -> s9 (0x96140
     sllw a1,s9,t2; 1.4 has no li t3,1 before 0x9619c), and t4 keeps match (it_reenter needs it).  In link the used sum stays
     in a7 (0x961a4 addw a7,a1,a7) and the next pointer moves t0 -> a7 (0x961e8); the re-entry sets a7 := ra (drop). *)
  Definition currsz_post (st : ItSt) (cv : Z) (m : amem) (x5 x6 : word) : machine_state -> Prop :=
    fun ms' => exists (q10 q16 q17 q28 : word),
      ms' = UST st (Z_to_bv 64 rt) x5 x6 (Z_to_bv 64 cv) q10 (Z_to_bv 64 (2 ^ cv)) q16 q17 (Z_to_bv 64 1) q28
                (Z_to_bv 64 (it_match ty)) 0x961d8 m.

  Lemma it_curr_loop : forall (k : nat) (curr lft n : Z) (cnt : arr) (st : ItSt) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (of wfx cfx : Z -> Z) (next bitsw : word)
      (x5 x6 x10 x16 x28 : word),
    mx - (curr + rt) <= Z.of_nat k -> Z.of_nat k < n -> 1 <= mx <= 15 -> 1 <= rt <= 15 ->
    1 <= curr -> curr + rt < mx -> 0 < lft <= 2 ^ curr ->
    (forall j, 0 <= j < 16 -> 0 <= arr_get cnt j < 65536) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (arr_get cnt) of lf wfx cfx next bitsw ->
    evtF asegs RNG (currsz_post st (fst (loopZ n (curr_body cnt rt mx) (curr, lft))) m x5 x6)
      (UST st (Z_to_bv 64 rt) x5 x6 (Z_to_bv 64 (mx - rt)) x10 (Z_to_bv 64 lft) x16 (Z_to_bv 64 (curr + rt)) (Z_to_bv 64 1) x28
           (Z_to_bv 64 (it_match ty)) 0x96188 m).
  Proof using All.
    induction k as [|k IH]; intros curr lft n cnt st m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 of wfx cfx next bitsw
      x5 x6 x10 x16 x28 Hk Hn Hmx RT Hc1 Hcm Hl HCR INV; [exfalso; lia|].
    pose proof INV as INV0. open_ctx CX. open_inv INV. unfold bst.
    assert (P14 : 2 ^ curr <= 2 ^ 13) by (apply Z.pow_le_mono_r; lia). change (2 ^ 13) with 8192 in P14.
    pose proof (HCR (curr + rt) ltac:(lia)) as HCc.
    zs. zs. setreg 10 (Z_to_bv 64 (2 * (curr + rt))) ltac:(rewrite zext32_x2 by lia; reflexivity).
    zs. do 4 zs.
    pose proof (f16arr_read asegs m (F + 32) 16 _ (curr + rt) _ CNT ltac:(lia) eq_refl) as RD.
    zs. rewrite (zx16_small (arr_get cnt (curr + rt))) by lia. clear RD.
    zs. setreg 11 (Z_to_bv 64 (lft - arr_get cnt (curr + rt))) ltac:(rewrite swrap32_small by lia; reflexivity).
    zs. zbr0 KL.
    - (* [comment removed for export] *)
      zs. setreg 7 (Z_to_bv 64 curr) ltac:(rewrite swrap32_small by lia; f_equal; lia).
      zs. setreg 11 (Z_to_bv 64 (2 ^ curr)) ltac:(rewrite sllw_1 by lia; reflexivity).   (* [P14] no li t3,1 at 1.4 *)
      apply evtF_done. unfold currsz_post. do 4 eexists.
      rewrite curr_stop_le by lia. cbn [fst]. reflexivity.
    - zs. setreg 17 (Z_to_bv 64 (curr + rt + 1)) ltac:(rewrite swrap32_small by lia; reflexivity).
      zs. setreg 11 (Z_to_bv 64 (2 * (lft - arr_get cnt (curr + rt)))) ltac:(rewrite shl1_2x; reflexivity).
      zs. zbr0 KM.
      + (* [comment removed for export] *)
        rewrite curr_more by lia. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
        replace ((lft - arr_get cnt (curr + rt)) * 2) with (2 * (lft - arr_get cnt (curr + rt))) by lia.
        replace (curr + rt + 1) with (curr + 1 + rt) by lia.
        eapply (IH (curr + 1) (2 * (lft - arr_get cnt (curr + rt))) (n - 1) cnt st); try eassumption; try lia.
        rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. lia.
      + zs. zs. setreg 11 (Z_to_bv 64 (2 ^ (mx - rt))) ltac:(rewrite sllw_1 by lia; reflexivity).   (* [P14] no li t3,1 at 1.4 *)
        apply evtF_done. unfold currsz_post. do 4 eexists.
        rewrite curr_more by lia. rewrite curr_stop_ge by lia. cbn [fst]. replace (curr + 1) with (mx - rt) by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma it_currsz : forall (st : ItSt) (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 : word) (of wfx cfx : Z -> Z) (next bitsw : word)
      (x5 x6 x7 x10 x11 x16 x17 x28 : word),
    1 <= mx <= 15 -> 1 <= rt <= 15 -> 1 <= tr_len X st <= 15 -> rt < tr_len X st -> tr_drop X st = rt ->
    (forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536) ->
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 (arr_get (tr_count st)) of lf wfx cfx next bitsw ->
    evtF asegs RNG (currsz_post st (tr_curr X st) m x5 x6)
      (UST st (Z_to_bv 64 rt) x5 x6 x7 x10 x11 x16 x17 (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x96174 m).
  Proof using All.
    intros until x28. intros Hmx RT TLR RTL HDR HCr1 INV.
    set (c0 := tr_len X st - rt). assert (Ec0 : c0 = tr_len X st - rt) by reflexivity.
    pose proof (pow2_le15 c0 ltac:(lia)) as PC0.
    assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
    { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
      fold c0. rewrite Z.shiftl_1_l, swrap32_id by lia. reflexivity. }
    pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (CR1 & CR2 & CR3).
    rewrite <- ETC in CR1, CR2, CR3.
    unfold bst.
    zs. setreg 7 (Z_to_bv 64 c0) ltac:(rewrite swrap32_small by lia; f_equal; lia).
    zs. setreg 11 (Z_to_bv 64 (2 ^ c0)) ltac:(rewrite sllw_1 by lia; reflexivity).
    zs. zbr0 KG.
    - (* [comment removed for export] *)
      assert (ETC0 : tr_curr X st = c0) by (apply CR3; lia).
      apply evtF_done. unfold currsz_post. do 4 eexists. rewrite ETC0. reflexivity.
    - zs. setreg 7 (Z_to_bv 64 (mx - rt)) ltac:(rewrite swrap32_small by lia; f_equal; lia).
      zs.
      rewrite ETC.
      pose proof (it_curr_loop 15%nat c0 (2 ^ c0) 16 (tr_count st) st m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 of wfx cfx next bitsw
                    x5 x6 x10 x16 x28 ltac:(lia) ltac:(lia) Hmx RT ltac:(lia) ltac:(lia) ltac:(lia) HCr1 INV) as HL.
      replace (c0 + rt) with (tr_len X st) in HL by lia. exact HL.
  Qed.

  Notation HEAD := (head_post FR fc gp tp SP SPA S F PB m1 ty lf wf lo codes nx bits).
  Notation RET1 cfx := (ret_pre SP SPA S F PB LP gp tp FR fc m1 1 lf w1 cfx (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits)).

  Lemma ne_facts : (isL ty = 0 \/ isL ty = 1) /\ (isD ty = 0 \/ isD ty = 1) /\ isL ty + isD ty <= 1 /\
    (forall u, it_not_enough ty u = (if isL ty =? 1 then 852 <? u else if isD ty =? 1 then 592 <? u else false)).
  Proof. destruct ty; cbn; repeat split; try lia; intros; reflexivity. Qed.
  Lemma lxor1_b2z : forall b, Z.lxor (Z.b2z b) 1 = Z.b2z (negb b).
  Proof. destruct b; reflexivity. Qed.
  Lemma land1_b2z : forall b, Z.land 1 (Z.b2z b) = Z.b2z b.
  Proof. destruct b; reflexivity. Qed.

  Notation SPU := (spure work1Ar rt nx).
  Lemma spure_st1 : forall st, SPU st -> SPU (tr_st1 X st).
  Proof.
    intros st HP. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st1].
    split; [exact WK|]. split; [exact LOWR|]. split; [exact DROPR|]. split; [exact NX0|]. split; [exact NX1|].
    split; [apply tr_count_range0; exact HCr|]. split; [apply tr_tbl1_range; exact HTr|].
    split; [unfold tr_count; rewrite arr_len_set; exact CL | rewrite it_fill_len_tr; exact TL].
  Qed.
  Lemma spure_st3 : forall st, SPU st -> 0 <= tr_low X st < 32768 -> tr_drop X st = rt -> t_next st <= tr_next st -> SPU (tr_st3 X st).
  Proof.
    intros st HP HL HD HN. open_spure HP. unfold spure. cbn [t_work t_low t_drop t_next t_count t_tbl tr_st3].
    split; [exact WK|]. split; [unfold BOX; right; exact HL|]. split; [unfold BOX; right; exact HD|]. split; [lia|]. split; [lia|].
    split; [apply tr_count_range0; exact HCr|]. split; [apply tr_tbl2_range; exact HTr|].
    split; [unfold tr_count; rewrite arr_len_set; exact CL | unfold tr_tbl2; rewrite arr_len_set, it_fill_len_tr; exact TL].
  Qed.
  Lemma tr_huff_range : forall st, 1 <= t_len st <= 15 -> 0 <= t_huff st < 65536 -> 0 <= tr_huff st < 65536 + 16384.
  Proof.
    intros st Flen Fhuff. unfold tr_huff. pose proof (pow2_le15 (t_len st - 1) ltac:(lia)) as PL1.
    pose proof (incr_range (t_huff st) 32 (shl32 1 (t_len st - 1)) ltac:(rewrite shl32_1 by lia; lia)) as IR.
    rewrite <- it_incr_back_eq in IR. fold (tr_incr2 st) in IR. rewrite shl32_1 in IR by lia.
    assert (2 ^ (t_len st - 1) <= 16384) by (change 16384 with (2 ^ 14); apply Z.pow_le_mono_r; lia).
    destruct (Z.eqb_spec (tr_incr2 st) 0); cbn [negb]; [lia|].
    assert (0 <= Z.land (t_huff st) (tr_incr2 st - 1) <= t_huff st) by (split; [apply Z.land_nonneg; lia | apply land_le_l; lia]). lia.
  Qed.

  (* [comment removed for export] *)
  Definition link_post (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (HEAD (tr_st3 X st) v0 v96 v104 v112 of ms' /\ it_not_enough ty (tr_used X st) = false /\ SPU (tr_st3 X st))
               \/ (RET1 (arr_get (tr_tbl1 X st)) ms' /\ it_not_enough ty (tr_used X st) = true).

  Lemma it_link : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x5 x10 x16 x17 x28 : word),
    MINV m (tr_st1 X st) v0 v96 v104 v112 of -> SPU st ->
    1 <= rt <= 15 -> 1 <= tr_curr X st <= 15 -> 0 <= t_used st < 65536 -> 0 <= t_curr st <= 15 ->
    0 <= tr_low X st < 32768 -> (it_not_enough ty (tr_used X st) = false -> 0 <= nx + tr_low X st < 1444) -> tr_drop X st = rt ->
    0 <= nx -> nx <= t_next st -> t_next st < 1444 -> arr_len (tr_tbl1 X st) = 1444 ->
    evtF asegs RNG (link_post st v0 v96 v104 v112 of)
      (UST st (Z_to_bv 64 rt) x5 (Z_to_bv 64 (tr_low X st)) (Z_to_bv 64 (tr_curr X st)) x10 (Z_to_bv 64 (2 ^ tr_curr X st)) x16 x17
           (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x961d8 m).
  Proof using All.
    intros until x28. intros INV HSPU RT HCU Fused Fcurr HLOW Flow3 HDR Hnx NX1 Hroom TL1.
    pose proof (pow2_le15 (tr_curr X st) ltac:(lia)) as PC3. pose proof (pow2_le15 (t_curr st) ltac:(lia)) as PC.
    assert (EU : tr_used X st = t_used st + 2 ^ tr_curr X st).
    { unfold tr_used. rewrite Z.shiftl_1_l. apply wrap32_small. lia. }
    assert (ENX : tr_next st = t_next st + 2 ^ t_curr st) by (unfold tr_next, tr_fill; rewrite shl32_1 by lia; reflexivity).
    pose proof ne_facts as (IL & ID & ILD & NE').
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_used t_low t_curr t_count t_tbl tr_st1] in *.
    unfold bst.
    zs. zs. setreg 17 (Z_to_bv 64 (tr_used X st)) ltac:(rewrite EU, swrap32_small by lia; f_equal; lia).   (* [P14] a7 at both versions (0x961a4) *)
    assert (FAIL : forall (mm : amem) (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y24 y25 y28 y29 y30 y31 : word)
                          (u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 : word) (cnt ofx : Z -> Z),
              itb_inv SPA S F PB m1 mm u0 u8 u16 u24 u32 u40 u48 u56 u64 u72 u80 u88 u96 u104 u112 cnt ofx lf w1 (arr_get (tr_tbl1 X st))
                      (Z_to_bv 64 (S + 1384 + 4 * nx)) (Z_to_bv 64 bits) ->
              it_not_enough ty (tr_used X st) = true ->
              link_post st v0 v96 v104 v112 of
                (bst SP SPA S F PB LP gp tp FR fc y1 y17 y7 y6 (Z_to_bv 64 1) y11 y12 y13 y14 y15 y16 y5 y24 y25 y28 y29 y30 y31 0x96348 mm)).
    { intros. right. split; [|assumption]. unfold ret_pre. exists mm. do 17 eexists. do 15 eexists. exists cnt, ofx. split; [reflexivity | eassumption]. }
    (* [comment removed for export] *)
    assert (JD : forall (y11 y16 : word), (isL ty = 1 -> tr_used X st < 853) ->
              evtF asegs RNG (link_post st v0 v96 v104 v112 of)
                (UST st (Z_to_bv 64 rt) x5 (Z_to_bv 64 (tr_low X st)) (Z_to_bv 64 (tr_curr X st)) (Z_to_bv 64 1) y11 y16 (Z_to_bv 64 (tr_used X st))
                     (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x961f8 m)).
    { intros y11 y16 HLok. unfold bst.
      zs. zs. setreg 11 (Z_to_bv 64 (Z.b2z (593 <=? tr_used X st))) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
      zs. zs.
      assert (LINK : it_not_enough ty (tr_used X st) = false ->
                forall (z11 z16 : word), evtF asegs RNG (link_post st v0 v96 v104 v112 of)
                  (UST st (Z_to_bv 64 rt) x5 (Z_to_bv 64 (tr_low X st)) (Z_to_bv 64 (tr_curr X st)) (Z_to_bv 64 1) z11 z16 (Z_to_bv 64 (tr_used X st))
                       (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x9620c m)).
      { intros HNE z11 z16. specialize (Flow3 HNE). unfold bst.
        zs.                                   (* [comment removed for export] *)
        zs. zs. zs.                           (* [comment removed for export] *)
        zs. zs.                               (* [comment removed for export] *)
        zs. zs. setreg 10 (Z_to_bv 64 (S + 1384 + 4 * (nx + tr_low X st))) ltac:(rewrite shl2_4x; f_equal; lia).
        f32_open_at CDS (nx + tr_low X st) D ED CH CC.
        do 4 zs. zs.                          (* [comment removed for export] *)
        zs. do 4 zs. zs.                      (* [comment removed for export] *)
        zs. do 4 zs.                          (* [comment removed for export] *)
        zs. zs. zs. setreg 11 (Z_to_bv 64 (4 * 2 ^ t_curr st)) ltac:(rewrite zext32_x4 by lia; reflexivity).
        zs. setreg 30 (Z_to_bv 64 (S + 1384 + 4 * tr_next st)) ltac:(rewrite ENX; f_equal; lia).
        zs. zs. setreg 11 (Z_to_bv 64 (tr_next st - nx))
                  ltac:(replace (S + 1384 + 4 * tr_next st - (S + 1384 + 4 * nx)) with ((tr_next st - nx) * 2 ^ 2) by lia;
                        rewrite Z.shiftr_div_pow2 by lia; rewrite Z.div_mul by lia; reflexivity).
        zs.                                   (* [comment removed for export] *)
        f32_close_at CH CC ED (code_pack (wrap8 (tr_curr X st)) rt (tr_next st - nx)) CDS; [apply entry_bytes; lia|]. subst D.
        assert (HIDX : 0 <= nx + tr_low X st < arr_len (tr_tbl1 X st)) by (rewrite TL1; lia).
        assert (W8 : wrap8 (tr_curr X st) = tr_curr X st) by (rewrite wrap8_mod; apply Z.mod_small; lia).
        rewrite W8 in CDS.
        apply (fun H => f32arr_ext asegs _ _ _ _ (arr_get (tr_tbl2 X st)) H
                          (fun j _ => fupd_arr_set (tr_tbl1 X st) (nx + tr_low X st) (code_pack (tr_curr X st) rt (tr_next st - nx)) j HIDX)) in CDS.
        zs. zs.                               (* [comment removed for export] *)
        (* [U14] it_reenter now pins s9 = 1 and t4 = match (1.4) *)
        pose proof (fun mm u0 u64 u80 u96 u104 u112 ofx y1 y10 y11 y16 y17 y28 =>
                      it_reenter RNG FR fc gp tp SP SPA S F PB top m1 ty lf wf cf lo codes nx bits CX C (tr_st3 X st)
                                 mm u0 u64 u80 u96 u104 u112 ofx y1 y10 y11 y16 y17 y28) as HR.
        unfold mst in HR. cbn [t_drop t_len t_huff t_next t_sym t_curr t_low t_used t_count t_tbl tr_st3] in HR.
        rewrite HDR, (lowS_small (tr_low X st)) in HR by lia.
        eapply evtF_mono; [eapply HR|].
        - lia.
        - right. lia.
        - unfold itb_inv, itb_W, frm15. do 10 (split; [eassumption|]). eassumption.
        - intros ms' HP. left. split; [exact HP|]. split; [exact HNE|]. apply spure_st3; [exact HSPU | exact HLOW | exact HDR | lia]. }
      destruct ID as [ID0|ID1].
      - setreg 11 (Z_to_bv 64 0) ltac:(rewrite ID0; reflexivity).
        zs. eapply LINK.
        rewrite NE'. destruct (Z.eqb_spec (isL ty) 1) as [E1|]; [apply Z.ltb_ge; specialize (HLok E1); lia|]. rewrite ID0. reflexivity.
      - setreg 11 (Z_to_bv 64 (Z.b2z (593 <=? tr_used X st))) ltac:(rewrite ID1, land1_b2z; reflexivity).
        zs. zbr0 KD.
        + apply evtF_done. eapply FAIL; [unfold itb_inv, itb_W, frm15; do 10 (split; [eassumption|]); eassumption|].
          rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_lt.
          lia.
        + eapply LINK. rewrite NE'. destruct (Z.eqb_spec (isL ty) 1); [lia|]. rewrite ID1. cbn [Z.eqb]. apply Z.ltb_ge.
          lia. }
    zs. zs. setreg 10 (Z_to_bv 64 (Z.b2z (853 <=? tr_used X st))) ltac:(rewrite lxor1_b2z, <- Z.leb_antisym; reflexivity).
    zs. zs.
    destruct IL as [IL0|IL1].
    - setreg 11 (Z_to_bv 64 0) ltac:(rewrite IL0; reflexivity).
      zs. zs. eapply JD. intros; lia.
    - setreg 11 (Z_to_bv 64 (Z.b2z (853 <=? tr_used X st))) ltac:(rewrite IL1, land1_b2z; reflexivity).
      zs. zs. zbr0 KL.
      + apply evtF_done. eapply FAIL; [unfold itb_inv, itb_W, frm15; do 10 (split; [eassumption|]); eassumption|].
        rewrite NE', IL1. cbn [Z.eqb]. apply Z.ltb_lt. lia.
      + eapply JD. intros _. lia.
  Qed.

  (* [comment removed for export] *)
  Definition sub_post (st : ItSt) (v0 v96 v104 v112 : word) (of : Z -> Z) : machine_state -> Prop :=
    fun ms' => (HEAD (tr_st1 X st) v0 v96 v104 v112 of ms' /\ tr_sub X st = false)
               \/ (link_post st v0 v96 v104 v112 of ms' /\ tr_sub X st = true).

  Lemma it_sub : forall (st : ItSt) (m : amem) (v0 v96 v104 v112 : word) (of : Z -> Z)
      (x1 x6 x7 x10 x11 x16 x17 x28 : word),
    MINV m (tr_st1 X st) v0 v96 v104 v112 of -> spure work1Ar rt nx st -> it_trip_ok X 288 320 1444 st = true ->
    tr_brk X st = false -> 1 <= mx ->
    (* [P14] 1.4 enters with the constant 1 in s9 and match in t4 (cnt2's post) *)
    evtF asegs RNG (sub_post st v0 v96 v104 v112 of)
      (MST (tr_st1 X st) x1 x6 x7 x10 x11 x16 x17 (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x960f0 m).
  Proof using All.
    intros until x28. intros INV HP TOK Hbrk Hmx.
    pose proof C as C'. open_itc C'. open_spure HP. clear HtyC HtyD Hcf Hwf Hlens15.
    pose proof (mx_range cntAr) as MXR. fold mx in MXR. pose proof (rt_facts lf lo codes bits Hmx) as (RT1 & RT2 & RT3).
    trip_facts TOK. clear Fwm.
    pose proof (pow2_le15 rt ltac:(lia)) as PRT.
    assert (TLR : 1 <= tr_len X st <= 15).
    { unfold tr_len. cbn [x_max x_lens x_lens_ofs itm_ctx].
      destruct (Z.eqb_spec (tr_c st) 0) as [E0|NE0]; [|cbn [andb]; lia].
      destruct (Z.eqb_spec (t_len st) mx) as [EM|NEM]; cbn [andb negb]; [lia|].
      unbox Flook. destruct (Flook E0 NEM) as (W1 & W2 & W3 & W4).
      replace (tr_sym st) with (t_sym st + 1) by (unfold tr_sym; symmetry; apply wrap32_small; lia). rewrite lensA_get in W4 |- *. exact W4. }
    clear Flook.
    pose proof (tr_huff_range st Flen Fhuff) as HHF.
    assert (HLOW : 0 <= tr_low X st < 32768).
    { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia.
      split; [apply Z.land_nonneg; lia|]. eapply Z.le_lt_trans; [apply land_le_r; lia | lia]. }
    assert (ELOW : Z.land (tr_huff st) (2 ^ rt - 1) = tr_low X st).
    { unfold tr_low. cbn [x_mask itm_ctx]. rewrite itm_used_pow2 by lia. reflexivity. }
    assert (HDR : tr_drop X st = rt).
    { unfold tr_drop. cbn [x_root itm_ctx]. unbox DROPR. destruct DROPR as [D0|D1]; rewrite D0 || rewrite D1; [reflexivity|].
      destruct (Z.eqb_spec rt 0); lia. }
    pose proof INV as INV0. open_ctx CX. unfold minv in INV. open_inv INV. cbn [t_used t_low t_curr t_count t_tbl tr_st1] in *.
    unfold mst, bst. cbn [t_drop t_len t_huff t_next t_sym tr_st1].
    zs. zbr0 KR.
    - (* [comment removed for export] *)
      apply evtF_done. left. split.
      + unfold head_post. exists m. do 9 eexists. split; [unfold mst, bst; cbn [t_drop t_len t_huff t_next t_sym tr_st1]; reflexivity | exact INV0].
      + unfold tr_sub. cbn [x_root itm_ctx]. replace (rt <? tr_len X st) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
    - zs. zs. setreg 6 (Z_to_bv 64 (tr_low X st)) ltac:(rewrite ELOW; reflexivity).
      zs.
      (* [comment removed for export] *)
      assert (J68 : tr_sub X st = true -> forall (y10 : word),
                evtF asegs RNG (sub_post st v0 v96 v104 v112 of)
                  (UST st x1 x17 (Z_to_bv 64 (tr_low X st)) x6 y10 x11 x16 (Z_to_bv 64 (t_drop st)) (Z_to_bv 64 1) x28
                       (Z_to_bv 64 (it_match ty)) 0x96168 m)).
      { intros Hsub y10.
        assert (RTL : rt < tr_len X st).
        { unfold tr_sub in Hsub. apply andb_prop in Hsub as [H1 _]. cbn [x_root itm_ctx] in H1. apply Z.ltb_lt in H1. exact H1. }
        assert (HCr1 : forall j, 0 <= j < 16 -> 0 <= arr_get (tr_count st) j < 65536) by (apply tr_count_range0; exact HCr).
        assert (AT4 : forall (y17 : word), evtF asegs RNG (sub_post st v0 v96 v104 v112 of)
                  (UST st (Z_to_bv 64 rt) x17 (Z_to_bv 64 (tr_low X st)) x6 y10 x11 x16 y17 (Z_to_bv 64 1) x28 (Z_to_bv 64 (it_match ty)) 0x96174 m)).
        { intros y17.
          eapply evtF_cut; [eapply (it_currsz st m); try eassumption; lia|].
          cbv beta. intros ms1 (q10 & q16 & q17 & q28 & ->).
          set (c0 := tr_len X st - rt).
          assert (ETC : tr_curr X st = fst (loopZ 16 (curr_body (tr_count st) rt mx) (c0, 2 ^ c0))).
          { unfold tr_curr. rewrite HDR. cbn [x_max itm_ctx]. rewrite it_subtable_curr_eq. rewrite (wrap32_small (tr_len X st - rt)) by lia.
            fold c0. rewrite Z.shiftl_1_l, swrap32_id by (pose proof (pow2_le15 c0 ltac:(unfold c0; lia)); lia). reflexivity. }
          pose proof (curr_result_range (tr_count st) rt mx 16 c0 (2 ^ c0) ltac:(unfold c0; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold c0; lia)) as (CR1 & CR2 & CR3).
          rewrite <- ETC in CR1, CR2, CR3.
          assert (HCU : 1 <= tr_curr X st <= 15).
          { destruct (Z_le_gt_dec (c0 + rt) mx) as [LE|GT]; [specialize (CR2 LE); unfold c0 in *; lia | rewrite (CR3 ltac:(lia)); unfold c0; lia]. }
          eapply evtF_mono; [eapply (it_link st m v0 v96 v104 v112 of); [exact INV0 | exact HP | lia | exact HCU | lia | lia | exact HLOW | | exact HDR | lia | exact NX1 | | ] |].
          - (* [comment removed for export] *)
            intros HNE.
            assert (HST3 : it_step X st = ItCont (tr_st3 X st)).
            { rewrite it_step_eq. rewrite Hbrk, Hsub. cbn [x_ty itm_ctx]. rewrite HNE. reflexivity. }
            unbox Fcont. destruct (Fcont (tr_st3 X st) HST3) as (Flow3 & Fcurr3 & Fnext3).
            { right. cbn [t_next tr_st3]. unfold tr_next, tr_fill. rewrite shl32_1 by lia. pose proof (pow2_le15 (t_curr st) ltac:(lia)). lia. }
            cbn [t_low tr_st3] in Flow3. exact Flow3.
          - pose proof (pow2_le15 (t_len st - t_drop st) ltac:(lia)).
            assert (2 ^ (t_len st - t_drop st) <= 2 ^ t_curr st) by (apply Z.pow_le_mono_r; lia).
            assert (0 <= Z.shiftr (t_huff st) (t_drop st)) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]). lia.
          - rewrite it_fill_len_tr. exact TL.
          - intros ms' HP'. right. split; [exact HP' | exact Hsub]. }
        unfold bst. zs.
        unbox DROPR. destruct DROPR as [D0|D1].
        - rewrite D0. zs. eapply AT4.
        - zs. zbr KD0. zs. rewrite D1. eapply AT4. }
      unbox LOWR. destruct LOWR as [LM|LSM].
      + (* [comment removed for export] *)
        rewrite LM. change (lowS 4294967295) with (-1).
        zs. zbr KQ. zs. eapply J68.
        unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, LM.
        replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.eqb_spec (tr_low X st) 4294967295); [lia | reflexivity].
      + rewrite (lowS_small (t_low st)) by lia.
        zs. zbr0 KQ.
        * (* [comment removed for export] *)
          apply evtF_done. left. split.
          -- unfold head_post. exists m. do 9 eexists. split; [unfold mst, bst; cbn [t_drop t_len t_huff t_next t_sym tr_st1]; reflexivity | exact INV0].
          -- unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW, KQ, Z.eqb_refl. cbn [negb]. apply Bool.andb_false_r.
        * zs. eapply J68.
          unfold tr_sub. cbn [x_root x_mask itm_ctx]. rewrite itm_used_pow2 by lia. rewrite ELOW.
          replace (rt <? tr_len X st) with true by (symmetry; apply Z.ltb_lt; lia).
          destruct (Z.eqb_spec (tr_low X st) (t_low st)); [lia | reflexivity].
  Qed.
End P.
End CANSEC1.
