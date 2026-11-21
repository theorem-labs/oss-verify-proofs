(** * LkHdr — the header segment (M_TABLE -> M_LEN), GOOD-ONLY
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Mirrors of g1's dynsel SelStages three stage lemmas and the DynSel
    chain (zr_table_chain_sel_holds) with EVERY leave/fuel arm killed:

      - stage 1's NEEDBITS(14) starve -> K1 against the strict header
        reads' own 14-bit floor;
      - stage 2's 3-bit-loop starve -> LkClKill.lk_ll_go_no_starve;
        its CODES-build fuel -> GtItTotal.it_model_total (the 3-bit
        values bound the lens);
      - stage 3's read-loop leave/fuel -> LkClKill.lk_cl_loop_exits
        (+ cl_loop_noBad for the BAD arm, as the _sel already did);
        both LENS/DISTS build fuels -> it_model_total (lens bounded by
        the loop's own <=15 export);
      - the chain emits NO disjunction: its conclusion is
        ZrTableChainSel's good arm verbatim.

    PA-EXPORTS: lk_tbl_stage1_good, lk_ll_stage2_good,
    lk_cdl_stage3_good, lk_table_chain_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff Inftrees DeflateSpec
  InflateFast Inflate InflateThy StepReach ItGTblCover InftreesBridge
  ItGModelExt DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproL0E ZReproQ6A ZReproQ6K Q6HuffResidue ItGTblSortWin
  Q6TblChainCore Q6TblChain GtCodesRes W2Stream GtBrAlign GtItTotal.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import StrictExtract ClNoBad.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkNb LkClKill.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* Walled-tree levels, as Q6TblChain :383-384 / SelStages / DynSel. *)
#[local] Strategy opaque [it_pre ll_go ll_zero cl_loop inf_fetch_go].
#[local] Strategy 1000 [inf_LENLENS inf_CODELENS inf_table it_model].

(** Stage 1, good-only: the 32-bit-free header read cannot starve
    under the strict decoder's own 14-bit floor. *)
Lemma lk_tbl_stage1_good : forall c q,
  br_wf (q_br q) ->
  h_mode (s_hdr (q_st q)) = M_TABLE ->
  (forall b, inf_nb 14 (q_br q) = NBOk b ->
     br_bits_of 5 b + 257 <= 286
     /\ br_bits_of 5 (br_dropbits 5 b) + 1 <= 30) ->
  (14 <= Z.of_nat (length (br_stream (q_br q)))) ->
  exists b qA,
        inf_nb 14 (q_br q) = NBOk b
        /\ br_bits_of 5 b + 257 <= 286
        /\ br_bits_of 5 (br_dropbits 5 b) + 1 <= 30
        /\ inf_step c q = inf_LENLENS c qA
        /\ q_br qA = br_dropbits 4 (br_dropbits 5 (br_dropbits 5 b))
        /\ b_ncode (s_bld (q_st qA))
           = br_bits_of 4 (br_dropbits 5 (br_dropbits 5 b)) + 4
        /\ b_nlen (s_bld (q_st qA)) = br_bits_of 5 b + 257
        /\ b_ndist (s_bld (q_st qA)) = br_bits_of 5 (br_dropbits 5 b) + 1
        /\ b_have (s_bld (q_st qA)) = 0
        /\ t_codes (s_tab (q_st qA)) = t_codes (s_tab (q_st q))
        /\ q_ob qA = q_ob q
        /\ h_last (s_hdr (q_st qA)) = h_last (s_hdr (q_st q))
        /\ q_in qA = q_in q
        /\ q_out qA = q_out q
        /\ w_wsize (s_win (q_st qA)) = w_wsize (s_win (q_st q))
        /\ h_wrap (s_hdr (q_st qA)) = h_wrap (s_hdr (q_st q))
        /\ h_flags (s_hdr (q_st qA)) = h_flags (s_hdr (q_st q))
        /\ h_check (s_hdr (q_st qA)) = h_check (s_hdr (q_st q))
        /\ h_total (s_hdr (q_st qA)) = h_total (s_hdr (q_st q))
        /\ w_whave (s_win (q_st qA)) = w_whave (s_win (q_st q))
        /\ t_sane (s_tab (q_st qA)) = t_sane (s_tab (q_st q))
        /\ q_ret qA = q_ret q.
Proof.
  intros c q Hwf Hm Hcaps Hfloor.
  assert (Hqm : q_mode q = M_TABLE) by (unfold q_mode; exact Hm).
  assert (Hstep : inf_step c q = inf_TABLE c q)
    by (unfold inf_step; rewrite Hqm; reflexivity).
  unfold inf_TABLE in Hstep.
  destruct (inf_nb 14 (q_br q)) as [b|b] eqn:E14;
    cbv beta iota zeta in Hstep.
  2:{ exfalso.
      destruct (k1_nb_starve_short 14 (q_br q) b Hwf ltac:(lia) E14)
        as (Hshort & _ & _).
      lia. }
  destruct (Hcaps b eq_refl) as (Hcap1 & Hcap2).
  match type of Hstep with
  | context [if ?chk then _ else _] => destruct chk eqn:Echk
  end; cbv beta iota in Hstep.
  { exfalso.
    apply orb_prop in Echk.
    destruct Echk as [E|E]; apply Z.ltb_lt in E; lia. }
  match type of Hstep with
  | _ = inf_LENLENS c ?X => exists b, X
  end.
  split; [reflexivity|].
  split; [exact Hcap1|].
  split; [exact Hcap2|].
  split; [exact Hstep|].
  repeat split; reflexivity.
Qed.

(** Stage 2, good-only: the 3-bit loop cannot starve and the CODES
    build cannot fuel out. *)
Lemma lk_ll_stage2_good : forall c qA,
  br_wf (q_br qA) ->
  br_haligned (q_br qA) ->
  b_have (s_bld (q_st qA)) = 0 ->
  0 <= b_ncode (s_bld (q_st qA)) <= 19 ->
  (forall vals rest,
     read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
       (br_stream (q_br qA)) = Some (vals, rest) ->
     Gap7Strict.build_accepts_b CT_CODES (scatter_cl vals) 7 = true) ->
  (exists vals rest,
     read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
       (br_stream (q_br qA)) = Some (vals, rest)) ->
  exists b4 (ls2 : zarr) (vals : list nat) o qB,
        br_wf b4
        /\ br_haligned b4
        /\ read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
             (br_stream (q_br qA)) = Some (vals, br_stream b4)
        /\ arr_eq_on ls2 (zlens (scatter_cl vals)) 0 19
        /\ it_model CT_CODES ls2 19 7
             (fun i => t_codes (s_tab (q_st qA)) (0 + i)) = Some o
        /\ o_ret o = 0
        /\ inf_LENLENS c qA = inf_CODELENS c qB
        /\ q_br qB = b4
        /\ b_have (s_bld (q_st qB)) = 0
        /\ b_nlen (s_bld (q_st qB)) = b_nlen (s_bld (q_st qA))
        /\ b_ndist (s_bld (q_st qB)) = b_ndist (s_bld (q_st qA))
        /\ t_codes (s_tab (q_st qB))
           = codes_wb (t_codes (s_tab (q_st qA))) 0 (o_tbl o)
        /\ t_lencode (s_tab (q_st qB)) = TRcodes 0
        /\ t_lenbits (s_tab (q_st qB)) = o_bits o
        /\ tbl_of (q_st qB) (t_lencode (s_tab (q_st qB)))
           = (fun i => codes_wb (t_codes (s_tab (q_st qA))) 0 (o_tbl o) (0 + i))
        /\ q_ob qB = q_ob qA
        /\ h_last (s_hdr (q_st qB)) = h_last (s_hdr (q_st qA))
        /\ q_in qB = q_in qA
        /\ q_out qB = q_out qA
        /\ w_wsize (s_win (q_st qB)) = w_wsize (s_win (q_st qA))
        /\ h_wrap (s_hdr (q_st qB)) = h_wrap (s_hdr (q_st qA))
        /\ h_flags (s_hdr (q_st qB)) = h_flags (s_hdr (q_st qA))
        /\ h_check (s_hdr (q_st qB)) = h_check (s_hdr (q_st qA))
        /\ h_total (s_hdr (q_st qB)) = h_total (s_hdr (q_st qA))
        /\ w_whave (s_win (q_st qB)) = w_whave (s_win (q_st qA))
        /\ t_sane (s_tab (q_st qB)) = t_sane (s_tab (q_st qA))
        /\ q_ret qB = 0.
Proof.
  intros c qA HwfA HalA Hhv Hnc HaccC HrdP.
  remember (inf_LENLENS c qA) as RES eqn:Hstep.
  unfold inf_LENLENS in Hstep. cbv beta zeta in Hstep.
  rewrite Hhv in Hstep.
  match type of Hstep with
  | context [ll_go 19 ?nc 0 ?ls ?bb] =>
      pose proof (ll_go_agree 19 nc 0 ls bb HwfA ltac:(lia) ltac:(lia)
                    ltac:(lia)) as HLL;
      destruct (ll_go 19 nc 0 ls bb) as [hv1 ls1 b4|hv1 ls1 b4] eqn:Ell
  end; cbv beta iota in Hstep.
  2:{ exfalso.
      destruct HrdP as (vals0 & rest0 & Hrd0).
      refine (lk_ll_go_no_starve 19 (b_ncode (s_bld (q_st qA))) 0 _ _
                vals0 rest0 _ _ _ HwfA ltac:(lia) ltac:(lia) _ Ell).
      replace (b_ncode (s_bld (q_st qA)) - 0)
        with (b_ncode (s_bld (q_st qA))) by lia.
      exact Hrd0. }
  destruct HLL as (Hhv1 & Hwfb4 & vals & Hrd3 & Hlenv & Hvalk & Hfrv).
  destruct (ll_zero 19 hv1 ls1) as [hv2 ls2] eqn:EZ.
  cbv beta iota in Hstep.
  subst hv1.
  destruct (ll_zero_agree 19 (b_ncode (s_bld (q_st qA))) ls1 hv2 ls2
              ltac:(lia) ltac:(lia) EZ) as (Hhv2 & Hzk & Hzfr).
  replace (b_ncode (s_bld (q_st qA)) - 0)
    with (b_ncode (s_bld (q_st qA))) in Hrd3 by lia.
  replace (b_ncode (s_bld (q_st qA)) - 0)
    with (b_ncode (s_bld (q_st qA))) in Hlenv by lia.
  assert (Hwin19 : arr_eq_on ls2 (zlens (scatter_cl vals)) 0 19).
  { intros j Hj.
    apply (scatter_tie vals (b_ncode (s_bld (q_st qA))) ls2
             ltac:(lia)); [| | | lia].
    - exact Hlenv.
    - intros k Hk.
      rewrite (Hzfr (inf_order k))
        by (intros k' Hk' He;
            pose proof (inf_order_inj k k' ltac:(lia) ltac:(lia) He); lia).
      specialize (Hvalk k ltac:(lia)).
      replace (0 + k) with k in Hvalk by lia.
      exact Hvalk.
    - intros k Hk. apply Hzk. lia. }
  assert (Halb4 : br_haligned b4)
    by (exact (ll_go_align 19 _ 0 _ _ _ _ _ HwfA Ell HalA)).
  (* the CODES build cannot fuel out: the 3-bit values bound the lens *)
  assert (Hls2b : LensBounded ls2 19).
  { intros i Hi. rewrite (Hwin19 i Hi). unfold zlens.
    split; [lia|].
    pose proof (read_3bit_vals_bound _ _ _ _ Hrd3) as Hvb.
    pose proof (scatter_cl_bound vals Hvb) as Hsb.
    assert (Hin : In (nth (Z.to_nat i) (scatter_cl vals) 0%nat)
                    (scatter_cl vals))
      by (apply nth_In; rewrite scatter_cl_length; lia).
    pose proof (Hsb _ Hin). lia. }
  unfold inf_table in Hstep.
  cbn [set_lens set_have s_tab s_bld q_st] in Hstep.
  match type of Hstep with
  | context [it_model CT_CODES ?l ?cds ?rt ?t0] =>
      destruct (it_model CT_CODES l cds rt t0) as [o|] eqn:EMC
  end; cbv beta iota in Hstep.
  2:{ exfalso.
      exact (it_model_total CT_CODES ls2 19 7 _ ltac:(lia) Hls2b EMC). }
  destruct (Z.eqb (o_ret o) 0) eqn:Erc;
    cbn [negb] in Hstep; cbv beta iota in Hstep.
  2:{ exfalso.
      assert (Hor : o_ret o = 0).
      { apply (accepts_transport CT_CODES (scatter_cl vals) 7 ls2 19
                 (fun i => t_codes (s_tab (q_st qA)) (0 + i)) o
                 (HaccC vals (br_stream b4) Hrd3)).
        - rewrite scatter_cl_length. reflexivity.
        - lia.
        - exact Hwin19.
        - exact EMC. }
      apply Z.eqb_neq in Erc. exact (Erc Hor). }
  apply Z.eqb_eq in Erc.
  match type of Hstep with
  | _ = inf_CODELENS c ?X => exists b4, ls2, vals, o, X
  end.
  split; [exact Hwfb4|].
  split; [exact Halb4|].
  split; [exact Hrd3|].
  split; [exact Hwin19|].
  split; [exact EMC|].
  split; [exact Erc|].
  split; [exact Hstep|].
  repeat split. all: first [reflexivity | exact Erc].
Qed.

(** Stage 3, good-only: the read loop exits in Done (Bad is refuted by
    the strict success), both builds answer, and the dispatch reaches
    the LEN entry. *)
Lemma lk_cdl_stage3_good : forall c qB (cs0 T : ztbl) (nb0 : Z)
                                  (cl : list nat),
  zr_cflush_ok c ->
  br_wf (q_br qB) ->
  br_haligned (q_br qB) ->
  b_have (s_bld (q_st qB)) = 0 ->
  257 <= b_nlen (s_bld (q_st qB)) ->
  1 <= b_ndist (s_bld (q_st qB)) ->
  t_codes (s_tab (q_st qB)) = cs0 ->
  t_lenbits (s_tab (q_st qB)) = nb0 ->
  tbl_of (q_st qB) (t_lencode (s_tab (q_st qB))) = T ->
  0 < nb0 <= 15 ->
  (forall i, 0 <= i < 2 ^ nb0 -> 0 <= c_bits (T i) <= nb0) ->
  zr_codes_fetch_bridge cl T nb0 ->
  ValidLengths cl 7%nat ->
  (exists ls0 rest0,
      read_lengths cl
        (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
        (br_stream (q_br qB)) = Some (ls0, rest0)) ->
  (forall ls0 rest0,
      read_lengths cl
        (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
        (br_stream (q_br qB)) = Some (ls0, rest0) ->
      zlens ls0 256 <> 0) ->
  (forall ls0 rest0,
      read_lengths cl
        (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
        (br_stream (q_br qB)) = Some (ls0, rest0) ->
      Gap7Strict.build_accepts_b CT_LENS
        (firstn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls0) 9 = true) ->
  (forall ls0 rest0,
      read_lengths cl
        (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
        (br_stream (q_br qB)) = Some (ls0, rest0) ->
      Gap7Strict.build_accepts_b CT_DISTS
        (skipn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls0) 6 = true) ->
  exists s' (ls : list nat) o1 o2 qL,
        read_lengths cl
          (Z.to_nat (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB))))
          (br_stream (q_br qB))
        = Some (ls, br_stream (cl_br s'))
        /\ cl_have s' = Z.of_nat (length ls)
        /\ b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)) <= cl_have s'
        /\ arr_eq_on (cl_lens s') (zlens ls) 0 (cl_have s')
        /\ br_wf (cl_br s')
        /\ br_haligned (cl_br s')
        /\ (forall x, In x ls -> (x <= 15)%nat)
        /\ cl_lens s' 256 <> 0
        /\ it_model CT_LENS (cl_lens s') (b_nlen (s_bld (q_st qB))) 9
             (fun i => cs0 (0 + i)) = Some o1
        /\ o_ret o1 = 0
        /\ it_model CT_DISTS
             (fun i => cl_lens s' (i + b_nlen (s_bld (q_st qB))))
             (b_ndist (s_bld (q_st qB))) 6
             (fun i => codes_wb cs0 0 (o_tbl o1) ((0 + o_used o1) + i))
           = Some o2
        /\ o_ret o2 = 0
        /\ inf_CODELENS c qB = inf_LEN_ qL
        /\ t_lencode (s_tab (q_st qL)) = TRcodes 0
        /\ t_lenbits (s_tab (q_st qL)) = o_bits o1
        /\ t_distcode (s_tab (q_st qL)) = TRcodes (0 + o_used o1)
        /\ t_distbits (s_tab (q_st qL)) = o_bits o2
        /\ t_codes (s_tab (q_st qL))
           = codes_wb (codes_wb cs0 0 (o_tbl o1)) (0 + o_used o1) (o_tbl o2)
        /\ q_br qL = cl_br s'
        /\ q_ob qL = q_ob qB
        /\ h_last (s_hdr (q_st qL)) = h_last (s_hdr (q_st qB))
        /\ q_in qL = q_in qB
        /\ q_out qL = q_out qB
        /\ w_wsize (s_win (q_st qL)) = w_wsize (s_win (q_st qB))
        /\ h_wrap (s_hdr (q_st qL)) = h_wrap (s_hdr (q_st qB))
        /\ h_flags (s_hdr (q_st qL)) = h_flags (s_hdr (q_st qB))
        /\ h_check (s_hdr (q_st qL)) = h_check (s_hdr (q_st qB))
        /\ h_total (s_hdr (q_st qL)) = h_total (s_hdr (q_st qB))
        /\ w_whave (s_win (q_st qL)) = w_whave (s_win (q_st qB))
        /\ t_sane (s_tab (q_st qL)) = t_sane (s_tab (q_st qB))
        /\ q_ret qL = o_ret o2.
Proof.
  intros c qB cs0 T nb0 cl Hfl HwfB HalB Hhv Hnl257 Hnd1 Hcs Hnb HT Hnbb
    Hbits Hbr HVcl Hread Heob HaccL HaccD.
  assert (Htot0 : 0 <= b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)))
    by lia.
  remember (inf_CODELENS c qB) as RES eqn:Hstep.
  unfold inf_CODELENS in Hstep. cbv beta zeta in Hstep.
  rewrite HT, Hnb, Hhv in Hstep.
  match type of Hstep with
  | context [cl_loop ?n ?t ?nb ?tot ?s0] =>
      pose proof (cl_loop_read_lengths cl t nb tot s0 Hbr
                    ltac:(exact HwfB) ltac:(reflexivity) ltac:(lia)) as HCL;
      pose proof (cl_loop_align cl t nb n tot s0 Hbr Hnbb Hbits
                    ltac:(exact HwfB) ltac:(exact HalB)) as HALW;
      pose proof (cl_loop_noBad n cl t nb tot s0 [] Hbr
                    ltac:(exact HwfB) ltac:(reflexivity)
                    ltac:(intros x Hx; destruct Hx)
                    ltac:(intros i Hi; cbn [cl_have] in Hi; lia)) as HNB;
      pose proof (lk_cl_loop_exits n cl t nb tot s0 [] (Z.to_nat tot)
                    Hbr Hbits Hnbb HVcl ltac:(exact HwfB)
                    ltac:(reflexivity)
                    ltac:(intros x Hx; destruct Hx)
                    ltac:(intros i Hi; cbn [cl_have] in Hi; lia)
                    ltac:(destruct Hread as (ls0 & rest0 & Hrd0);
                          exists ls0, rest0;
                          unfold read_lengths in Hrd0;
                          cbn [cl_have cl_br];
                          replace (Z.to_nat (tot - 0))
                            with (Z.to_nat tot) by lia;
                          exact Hrd0)
                    ltac:(cbn [cl_have]; lia)) as HEX;
      destruct (cl_loop n t nb tot s0) as [[s'|s'|s' m'|s'|]|] eqn:ECL
  end; cbv beta iota in Hstep.
  1:{ (* ClCont: dead by the exits lemma *)
    exfalso.
    destruct HEX as (r & Ecl & Hr).
    injection Ecl as Er.
    rewrite <- Er in Hr. exact Hr. }
  2:{ (* ClBad: the read loop rejected — refuted by the strict success *)
    exfalso.
    destruct Hread as (ls0 & rest0 & Hrd).
    cbv beta iota in HNB.
    cbn [cl_have cl_br] in HNB.
    unfold read_lengths in Hrd.
    specialize (HNB (Z.to_nat (b_nlen (s_bld (q_st qB))
                               + b_ndist (s_bld (q_st qB))))).
    replace (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)) - 0)
      with (b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)))
      in HNB by lia.
    rewrite HNB in Hrd; [discriminate Hrd | lia]. }
  2:{ (* ClLeave: dead by the exits lemma *)
    exfalso.
    destruct HEX as (r & Ecl & Hr).
    injection Ecl as Er.
    rewrite <- Er in Hr. exact Hr. }
  2:{ (* ClFuel: dead by the exits lemma *)
    exfalso.
    destruct HEX as (r & Ecl & Hr).
    injection Ecl as Er.
    rewrite <- Er in Hr. exact Hr. }
  2:{ (* None: dead by the exits lemma *)
    exfalso.
    destruct HEX as (r & Ecl & Hr).
    discriminate Ecl. }
  (* ClDone: the decoded lengths *)
  destruct HCL as (ls & Hrdl & Hhave & Htot & Hwin' & HwfS & Hbnd15).
  cbn [cl_br cl_have cl_lens] in Hrdl.
  assert (Hlenls : length ls
                   = Z.to_nat (b_nlen (s_bld (q_st qB))
                               + b_ndist (s_bld (q_st qB)))).
  { unfold read_lengths in Hrdl.
    pose proof (read_lengths_fuel_length _ _ _ _ _ _ _ Hrdl) as HL.
    cbn [length] in HL. lia. }
  destruct (Z.eqb (cl_lens s' 256) 0) eqn:Eeob; cbv beta iota in Hstep.
  { exfalso.
    apply Z.eqb_eq in Eeob.
    assert (H256 : cl_lens s' 256 = zlens ls 256)
      by (apply Hwin'; lia).
    apply (Heob ls (br_stream (cl_br s')) Hrdl).
    rewrite <- H256. exact Eeob. }
  apply Z.eqb_neq in Eeob.
  (* both builds' lens are bounded by the loop's own export *)
  assert (HlbL : LensBounded (cl_lens s') (b_nlen (s_bld (q_st qB)))).
  { intros i Hi.
    rewrite (Hwin' i ltac:(lia)). unfold zlens.
    split; [lia|].
    assert (Hin : In (nth (Z.to_nat i) ls 0%nat) ls)
      by (apply nth_In; rewrite Hlenls; lia).
    pose proof (Hbnd15 _ Hin). lia. }
  assert (HlbD : LensBounded
                   (fun i => cl_lens s' (i + b_nlen (s_bld (q_st qB))))
                   (b_ndist (s_bld (q_st qB)))).
  { intros i Hi.
    rewrite (Hwin' (i + b_nlen (s_bld (q_st qB))) ltac:(lia)).
    unfold zlens.
    split; [lia|].
    assert (Hin : In (nth (Z.to_nat (i + b_nlen (s_bld (q_st qB)))) ls
                        0%nat) ls)
      by (apply nth_In; rewrite Hlenls; lia).
    pose proof (Hbnd15 _ Hin). lia. }
  unfold inf_table in Hstep.
  cbn [q_st qset_st qset_br qset_ret set_lens set_have set_codes set_next
       set_lenbits set_lencode set_distbits set_distcode s_tab s_bld
       t_codes] in Hstep.
  rewrite Hcs in Hstep.
  match type of Hstep with
  | context [it_model CT_LENS ?l ?cds ?rt ?t0] =>
      destruct (it_model CT_LENS l cds rt t0) as [o1|] eqn:EML
  end; cbv beta iota in Hstep.
  2:{ exfalso.
      exact (it_model_total CT_LENS (cl_lens s')
               (b_nlen (s_bld (q_st qB))) 9 _ ltac:(lia) HlbL EML). }
  destruct (Z.eqb (o_ret o1) 0) eqn:Erl;
    cbn [negb] in Hstep; cbv beta iota in Hstep.
  2:{ exfalso.
      assert (Hor : o_ret o1 = 0).
      { apply (accepts_transport CT_LENS
                 (firstn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls) 9
                 (cl_lens s') (b_nlen (s_bld (q_st qB)))
                 (fun i => cs0 (0 + i)) o1
                 (HaccL ls (br_stream (cl_br s')) Hrdl)).
        - rewrite length_firstn, Hlenls. lia.
        - lia.
        - intros j Hj.
          rewrite (zlens_firstn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls j
                     ltac:(lia)).
          apply Hwin'. lia.
        - exact EML. }
      apply Z.eqb_neq in Erl. exact (Erl Hor). }
  apply Z.eqb_eq in Erl.
  match type of Hstep with
  | context [it_model CT_DISTS ?l ?cds ?rt ?t0] =>
      destruct (it_model CT_DISTS l cds rt t0) as [o2|] eqn:EMD
  end; cbv beta iota in Hstep.
  2:{ exfalso.
      exact (it_model_total CT_DISTS _
               (b_ndist (s_bld (q_st qB))) 6 _ ltac:(lia) HlbD EMD). }
  destruct (Z.eqb (o_ret o2) 0) eqn:Erd;
    cbn [negb] in Hstep; cbv beta iota in Hstep.
  2:{ exfalso.
      assert (Hor : o_ret o2 = 0).
      { apply (accepts_transport CT_DISTS
                 (skipn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls) 6
                 (fun i => cl_lens s' (i + b_nlen (s_bld (q_st qB))))
                 (b_ndist (s_bld (q_st qB)))
                 (fun i => codes_wb cs0 0 (o_tbl o1) ((0 + o_used o1) + i))
                 o2
                 (HaccD ls (br_stream (cl_br s')) Hrdl)).
        - rewrite length_skipn, Hlenls. lia.
        - lia.
        - intros j Hj. cbv beta.
          rewrite (zlens_skipn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls j
                     ltac:(lia)).
          replace (j + Z.of_nat (Z.to_nat (b_nlen (s_bld (q_st qB)))))
            with (j + b_nlen (s_bld (q_st qB))) by lia.
          apply Hwin'. lia.
        - exact EMD. }
      apply Z.eqb_neq in Erd. exact (Erd Hor). }
  apply Z.eqb_eq in Erd.
  rewrite (zr_eqb_nT c Hfl) in Hstep. cbv beta iota in Hstep.
  match type of Hstep with
  | _ = inf_LEN_ ?X => exists s', ls, o1, o2, X
  end.
  split; [exact Hrdl|].
  split; [exact Hhave|].
  split; [exact Htot|].
  split; [exact Hwin'|].
  split; [exact HwfS|].
  split; [exact HALW|].
  split; [exact Hbnd15|].
  split; [exact Eeob|].
  split; [exact EML|].
  split; [exact Erl|].
  split; [exact EMD|].
  split; [exact Erd|].
  split; [exact Hstep|].
  repeat split. all: first [reflexivity | exact Erd].
Qed.

Set Printing Width 2000.
Print Assumptions lk_tbl_stage1_good.
Print Assumptions lk_ll_stage2_good.
Print Assumptions lk_cdl_stage3_good.
