(* the zlib 1.4 twin of LkChain, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkChain), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkChain — the header chain, GOOD-ONLY: strict success drives
    M_TABLE all the way into the LEN dispatch with NO absorbed arm
    (q7-decode leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Mirror of g1's DynSel.zr_table_chain_sel_holds (a working folder,
    ) with the stage calls swapped for LkHdr's good-only
    mirrors; the three new dischargers are the strict decoder's own
    footprint: the 14-bit floor (its header reads), the CL-read
    success (its read_cl_lengths), and ValidLengths of the CL code
    (accept_valid at the CODES build, as the landed chain derives).

    PA-EXPORT: lk_table_chain_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff Inftrees DeflateSpec
  InflateFast Inflate InflateThy StepReach ItGTblCover InftreesBridge
  ItGModelExt DynTblOkHolds.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproL0E ZReproQ6A ZReproQ6K Q6HuffResidue ItGTblSortWin
  Q6TblChainCore Q6TblChain GtCodesRes W2Stream GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7Strict.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import StrictExtract ClNoBad.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkHdr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkChain.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkHdr14 Q6TblChain14 Spec.PngModel.Inflate14.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

#[local] Strategy opaque [it_pre ll_go ll_zero cl_loop inf_fetch_go].
#[local] Strategy 1000 [inf_LENLENS14 inf_CODELENS14 inf_table it_model].

Theorem lk_table_chain_good14 :
  forall c q (lit dst : list nat) (r3 : list bool),
    zr_cflush_ok c ->
    br_wf (q_br q) ->
    W2Stream.br_haligned (q_br q) ->
    0 <= o_put (q_ob q) ->
    h_mode (s_hdr (q_st q)) = M_TABLE ->
    q_ret q = 0 ->
    decode_dynamic_tables_strict (br_stream (q_br q)) = Some (lit, dst, r3) ->
    (exists cw, code_for lit 15%nat 256%nat = Some cw) ->
    exists qL d,
        br_stream (q_br qL) = r3
        /\ br_wf (q_br qL)
        /\ W2Stream.br_haligned (q_br qL)
        /\ zr_len_dispatch14 c q qL lit dst d.
Proof.
  intros c q lit dst r3 Hfl Hwf Hal Hput Hm Hq0 Hstrict HcwE.
  destruct HcwE as (cw & Hcw).
  pose proof GtCodesRes.zr_codes_fetch_res_holds as Hres.
  destruct (strict_extract _ _ _ _ Hstrict)
    as (hlit & r1 & hdist & r2 & hclen & r3a & clS & r4S & lsS
        & E1 & E2 & E3 & E4 & G1a & G1b & E5 & Hlit & Hdst
        & Gvl & Gvd & Hl286 & Hl30 & GaccL & GaccD).
  (* the decoded list's exact length *)
  assert (HlenS : length lsS
                  = (Z.to_nat hlit + 257 + (Z.to_nat hdist + 1))%nat).
  { pose proof E5 as E5c. unfold read_lengths in E5c.
    pose proof (read_lengths_fuel_length _ _ _ _ _ _ _ E5c) as HL.
    cbn [length] in HL. lia. }
  assert (Hl286' : (Nat.min (Z.to_nat hlit + 257) (length lsS) <= 286)%nat)
    by (rewrite <- length_firstn, <- Hlit; exact Hl286).
  assert (Hl30' : (length lsS - (Z.to_nat hlit + 257) <= 30)%nat)
    by (rewrite <- length_skipn, <- Hdst; exact Hl30).
  (* ---------------- stage 1 ---------------- *)
  assert (Hcaps : forall b0, inf_nb 14 (q_br q) = NBOk b0 ->
            br_bits_of 5 b0 + 257 <= 286
            /\ br_bits_of 5 (br_dropbits 5 b0) + 1 <= 30).
  { intros b0 E14'.
    destruct (zr_table_reads (q_br q) b0 Hwf E14')
      as (RA & RB & RC & _ & _ & Rr1 & Rr2 & _).
    pose proof E1 as E1'. rewrite RA in E1'.
    injection E1' as Hh0 Hr0.
    pose proof E2 as E2'. rewrite <- Hr0, RB in E2'.
    injection E2' as Hh0' Hr0'.
    lia. }
  assert (Hfloor14 : 14 <= Z.of_nat (length (br_stream (q_br q)))).
  { pose proof (read_bits_length 5%nat _ _ _ E1) as HL1.
    pose proof (read_bits_length 5%nat _ _ _ E2) as HL2.
    pose proof (read_bits_length 4%nat _ _ _ E3) as HL3.
    lia. }
  destruct (lk_tbl_stage1_good14 c q Hwf Hm Hcaps Hfloor14) as
    (b & qA & E14 & Hcap1 & Hcap2 & Hstep1 & HqbrA & Hbnc & Hbnl & Hbnd
     & HbhvA & HtcA & HobA & HhlA & HinA & HoutA & HwszA
     & HwrA & HfgA & HckA & HtoA & HwvA & HsnA & HretA).
  (* ---------------- the header-read ties ---------------- *)
  destruct (zr_table_reads (q_br q) b Hwf E14)
    as (HrdA & HrdB & HrdC & Hwf3 & Hbits3 & Hh1 & Hh2 & Hh3).
  rewrite HrdA in E1. injection E1 as Hhlit Hr1.
  rewrite <- Hr1, HrdB in E2. injection E2 as Hhdist Hr2.
  rewrite <- Hr2, HrdC in E3. injection E3 as Hhclen Hr3a.
  destruct (inf_nb_ok 14 (q_br q) b Hwf ltac:(lia) E14)
    as (Hsb & Hwfb & Hb14).
  assert (HwfA : br_wf (q_br qA)) by (rewrite HqbrA; exact Hwf3).
  assert (HalA : br_haligned (q_br qA)).
  { rewrite HqbrA.
    assert (Hd1 : br_bits (br_dropbits 5 b) = br_bits b - 5)
      by apply dropbits_bits.
    assert (Hd2 : br_bits (br_dropbits 5 (br_dropbits 5 b))
                  = br_bits b - 10)
      by (rewrite dropbits_bits, Hd1; lia).
    apply br_haligned_dropbits; [lia|].
    apply br_haligned_dropbits; [lia|].
    apply br_haligned_dropbits; [lia|].
    exact (inf_nb_align 14 (q_br q) b Hwf ltac:(lia) E14 Hal). }
  assert (HncA : 0 <= b_ncode (s_bld (q_st qA)) <= 19) by (rewrite Hbnc; lia).
  assert (Hstream_qA : br_stream (q_br qA) = r3a)
    by (rewrite HqbrA; exact Hr3a).
  (* ---------------- the CL-read tie ---------------- *)
  unfold read_cl_lengths in E4.
  destruct (read_3bit_vals (Z.to_nat hclen + 4) r3a)
    as [[valsE rE]|] eqn:E4v; [|discriminate E4].
  injection E4 as HclS Hr4.
  assert (HncodeN : Z.to_nat (b_ncode (s_bld (q_st qA)))
                    = (Z.to_nat hclen + 4)%nat)
    by (rewrite Hbnc, Hhclen; lia).
  assert (HaccC : forall vals0 rest0,
            read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
              (br_stream (q_br qA)) = Some (vals0, rest0) ->
            Gap7Strict.build_accepts_b CT_CODES (scatter_cl vals0) 7 = true).
  { intros vals0 rest0 Hr.
    rewrite Hstream_qA, HncodeN, E4v in Hr.
    injection Hr as Hv0 Hre0.
    rewrite <- Hv0, HclS. exact G1b. }
  assert (HrdPA : exists vals0 rest0,
            read_3bit_vals (Z.to_nat (b_ncode (s_bld (q_st qA))))
              (br_stream (q_br qA)) = Some (vals0, rest0)).
  { exists valsE, rE. rewrite Hstream_qA, HncodeN. exact E4v. }
  (* ---------------- stage 2 ---------------- *)
  destruct (lk_ll_stage2_good14 c qA HwfA HalA HbhvA HncA HaccC HrdPA) as
    (b4 & ls2 & vals & o & qB & Hwfb4 & Halb4 & Hrd3 & Hwin19 & EMC & Erc
     & Hstep2 & HqbrB & HbhvB & HbnlB & HbndB & HtcB & HlcB & HnbB & HtblB
     & HobB & HhlB & HinB & HoutB & HwszB
     & HwrB & HfgB & HckB & HtoB & HwvB & HsnB & HretB).
  (* the machine's CL values ARE the strict decoder's *)
  assert (Hvals : valsE = vals /\ rE = br_stream b4).
  { pose proof Hrd3 as Hrd3t.
    rewrite Hstream_qA, HncodeN, E4v in Hrd3t.
    injection Hrd3t as Hv Hr. split; [exact Hv | exact Hr]. }
  destruct Hvals as (HvalsE & HrE).
  assert (Hb4S : br_stream b4 = r4S) by (rewrite <- HrE; exact Hr4).
  assert (HclV : scatter_cl vals = clS)
    by (rewrite <- HvalsE; exact HclS).
  (* rebase the stage-2 exports onto q's spellings *)
  rewrite Hbnc in Hrd3. rewrite HqbrA in Hrd3.
  rewrite HtcA in EMC, HtcB, HtblB.
  rewrite Hbnl in HbnlB. rewrite Hbnd in HbndB.
  assert (HwfB2 : br_wf (q_br qB)) by (rewrite HqbrB; exact Hwfb4).
  assert (Hstream_qB : br_stream (q_br qB) = r4S)
    by (rewrite HqbrB; exact Hb4S).
  assert (HtotN : Z.to_nat (b_nlen (s_bld (q_st qB))
                            + b_ndist (s_bld (q_st qB)))
                  = (Z.to_nat hlit + 257 + (Z.to_nat hdist + 1))%nat)
    by (rewrite HbnlB, HbndB, Hhlit, Hhdist; lia).
  assert (HnlN : Z.to_nat (b_nlen (s_bld (q_st qB)))
                 = (Z.to_nat hlit + 257)%nat)
    by (rewrite HbnlB, Hhlit; lia).
  (* the CODES pre-state decides the CODELENS table shape *)
  destruct (it_pre CT_CODES ls2 19 7
              (fun i => t_codes (s_tab (q_st q)) (0 + i)))
    as [ |temp| |c0 st0] eqn:EPC.
  { exfalso. unfold it_model in EMC. rewrite EPC in EMC.
    injection EMC as <-. cbn [o_ret] in Erc. lia. }
  { (* PreEmpty: an all-zero CL code cannot decode read_lengths *)
    exfalso.
    assert (Hmx0 : it_findmax 15%nat MAXBITS
                     (it_count (Z.to_nat 19) 0 ls2 zzero) = 0)
      by exact (it_pre_empty_findmax0 _ _ _ _ _ _ EPC).
    assert (Hcl_bnd : forall x, In x (scatter_cl vals) -> (x <= 7)%nat).
    { apply scatter_cl_bound.
      exact (read_3bit_vals_bound _ _ _ _ Hrd3). }
    assert (HC19 : CountsOf (it_cnt0 ls2 19) (scatter_cl vals) 15%nat).
    { apply counts_of_it_count_agree;
        [rewrite scatter_cl_length; reflexivity | exact Hwin19]. }
    assert (Hallz : forall x, In x (scatter_cl vals) -> x = 0%nat).
    { intros x Hin.
      destruct (Nat.eq_dec x 0) as [->|Hx0]; [reflexivity|].
      exfalso.
      pose proof (Hcl_bnd x Hin) as Hx7.
      pose proof (sw_findmax_15 (it_cnt0 ls2 19)) as [Hzhi _].
      assert (Hmx0' : it_findmax 15%nat MAXBITS (it_cnt0 ls2 19) = 0)
        by exact Hmx0.
      assert (Hcnt0 : it_cnt0 ls2 19 (Z.of_nat x) = 0).
      { apply Hzhi. rewrite Hmx0'. unfold MAXBITS. lia. }
      pose proof (HC19 x ltac:(lia)) as Hcc.
      rewrite Hcnt0 in Hcc.
      unfold count_len in Hcc.
      apply (count_occ_In Nat.eq_dec) in Hin. lia. }
    pose proof E5 as E5z. unfold read_lengths in E5z.
    replace (Z.to_nat hlit + 257 + (Z.to_nat hdist + 1))%nat
      with (S (Z.to_nat hlit + 256 + (Z.to_nat hdist + 1)))%nat
      in E5z by lia.
    cbn [read_lengths_fuel] in E5z.
    rewrite <- HclV in E5z.
    rewrite (hdecode_zeros (scatter_cl vals) r4S Hallz) in E5z.
    discriminate E5z. }
  { exfalso. unfold it_model in EMC. rewrite EPC in EMC.
    injection EMC as <-. cbn [o_ret] in Erc. lia. }
  (* PreGo: the live path *)
  assert (Hcl_len : length (scatter_cl vals) = 19%nat)
    by apply scatter_cl_length.
  assert (Hcl_bnd : forall x, In x (scatter_cl vals) -> (x <= 7)%nat).
  { apply scatter_cl_bound.
    exact (read_3bit_vals_bound _ _ _ _ Hrd3). }
  pose proof (Hres (scatter_cl vals) ls2 (t_codes (s_tab (q_st q))) o
                Hcl_len Hwin19 Hcl_bnd EMC Erc
                (ex_intro _ c0 (ex_intro _ st0 EPC))) as Hbr.
  assert (Htot0 : 0 <= b_nlen (s_bld (q_st qB)) + b_ndist (s_bld (q_st qB)))
    by (rewrite HbnlB, HbndB; lia).
  assert (HalB : br_haligned (q_br qB)) by (rewrite HqbrB; exact Halb4).
  assert (Hls2b : forall i, 0 <= i < 19 -> 0 <= ls2 i <= 15).
  { intros i Hi. rewrite (Hwin19 i Hi). unfold zlens.
    split; [lia|].
    assert (Hin : In (nth (Z.to_nat i) (scatter_cl vals) 0%nat)
                    (scatter_cl vals))
      by (apply nth_In; rewrite Hcl_len; lia).
    pose proof (Hcl_bnd _ Hin). lia. }
  assert (Hnbb : 0 < o_bits o <= 15).
  { pose proof (it_model_bits_range CT_CODES ls2 19 7 _ o
                  ltac:(lia) Hls2b ltac:(lia) EMC Erc). lia. }
  assert (Hbits : forall i, 0 <= i < 2 ^ (o_bits o) ->
            0 <= c_bits (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o)
                           (0 + i)) <= o_bits o).
  { intros i Hi.
    pose proof (it_covers_root_pos CT_CODES ls2 19 7 _ o
                  ltac:(lia) Hls2b ltac:(lia) EMC Erc i Hi) as Hc.
    unfold codes_wb.
    replace (Z.leb 0 (0 + i)) with true
      by (symmetry; apply Z.leb_le; lia).
    replace (0 + i - 0) with i by lia.
    cbv beta iota. lia. }
  (* the CL code is a VALID prefix code (accept_valid at the build) *)
  assert (HVcl : ValidLengths (scatter_cl vals) 7%nat).
  { apply valid_lengths_b_true.
    eapply (accept_valid CT_CODES ls2 (scatter_cl vals) 19 7 _ o 7%nat);
      [rewrite Hcl_len; reflexivity | exact Hwin19 | exact Hcl_bnd
      | lia | exact EMC | exact Erc]. }
  (* the strict-side premises of stage 3 *)
  assert (Hnl257 : 257 <= b_nlen (s_bld (q_st qB)))
    by (rewrite HbnlB; lia).
  assert (Hnd1 : 1 <= b_ndist (s_bld (q_st qB)))
    by (rewrite HbndB; lia).
  assert (HreadP : exists ls0 rest0,
            read_lengths (scatter_cl vals)
              (Z.to_nat (b_nlen (s_bld (q_st qB))
                         + b_ndist (s_bld (q_st qB))))
              (br_stream (q_br qB)) = Some (ls0, rest0)).
  { exists lsS, r3. rewrite Hstream_qB, HtotN, HclV. exact E5. }
  assert (HeobP : forall ls0 rest0,
            read_lengths (scatter_cl vals)
              (Z.to_nat (b_nlen (s_bld (q_st qB))
                         + b_ndist (s_bld (q_st qB))))
              (br_stream (q_br qB)) = Some (ls0, rest0) ->
            zlens ls0 256 <> 0).
  { intros ls0 rest0 Hr.
    rewrite Hstream_qB, HtotN, HclV, E5 in Hr.
    injection Hr as Hls0 Hrest0.
    rewrite <- Hls0.
    exact (code_for_256_lens lit lsS (Z.to_nat hlit + 257) cw Hlit
             ltac:(lia) Hcw). }
  assert (HaccLP : forall ls0 rest0,
            read_lengths (scatter_cl vals)
              (Z.to_nat (b_nlen (s_bld (q_st qB))
                         + b_ndist (s_bld (q_st qB))))
              (br_stream (q_br qB)) = Some (ls0, rest0) ->
            Gap7Strict.build_accepts_b CT_LENS
              (firstn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls0) 9 = true).
  { intros ls0 rest0 Hr.
    rewrite Hstream_qB, HtotN, HclV, E5 in Hr.
    injection Hr as Hls0 Hrest0.
    rewrite <- Hls0, HnlN, <- Hlit. exact GaccL. }
  assert (HaccDP : forall ls0 rest0,
            read_lengths (scatter_cl vals)
              (Z.to_nat (b_nlen (s_bld (q_st qB))
                         + b_ndist (s_bld (q_st qB))))
              (br_stream (q_br qB)) = Some (ls0, rest0) ->
            Gap7Strict.build_accepts_b CT_DISTS
              (skipn (Z.to_nat (b_nlen (s_bld (q_st qB)))) ls0) 6 = true).
  { intros ls0 rest0 Hr.
    rewrite Hstream_qB, HtotN, HclV, E5 in Hr.
    injection Hr as Hls0 Hrest0.
    rewrite <- Hls0, HnlN, <- Hdst. exact GaccD. }
  (* ---------------- stage 3 ---------------- *)
  destruct (lk_cdl_stage3_good14 c qB _ _ _ (scatter_cl vals) Hfl HwfB2 HalB
              HbhvB Hnl257 Hnd1 HtcB HnbB HtblB Hnbb Hbits Hbr HVcl
              HreadP HeobP HaccLP HaccDP) as
    (s' & ls & o1 & o2 & qL & Hrdl & Hhave & Htot & Hwin' & HwfS & HalS
     & Hbnd15 & Eeob & EML & Erl & EMD & Erd & Hstep3 & HlcL & HnbL & HdcL
     & HdbL & HtcL & HqbrL & HobL & HhlL & HinL & HoutL & HwszL
     & HwrL & HfgL & HckL & HtoL & HwvL & HsnL & HretL).
  (* THE AGREEMENT: tie the machine's decode to the strict decoder's *)
  assert (Hties : lsS = ls /\ r3 = br_stream (cl_br s')).
  { pose proof Hrdl as Hrdl2.
    rewrite Hstream_qB, HtotN, HclV in Hrdl2.
    rewrite E5 in Hrdl2.
    injection Hrdl2 as Hlseq Hr3eq.
    split; [exact Hlseq | exact Hr3eq]. }
  destruct Hties as (Hlseq & Hr3eq).
  (* rebase the stage-3 exports for the pure core *)
  rewrite HqbrB in Hrdl.
  rewrite HbnlB in Hrdl, Htot, EML, EMD.
  rewrite HbndB in Hrdl, Htot, EMD.
  destruct (tbl_pure_core (q_br q) b b4 (t_codes (s_tab (q_st q))) vals ls
              ls2 o s' o1 o2 HrdA HrdB HrdC Hh1 Hh2 Hh3 Hrd3 Hwin19 EMC Erc
              Hrdl Hhave Htot Hwin' Hbnd15 Eeob EML Erl EMD Erd) as
    (nlit & Hnlit & Hdec & Hlitlen & Hdstlen & HwfL & EML' & HwfD & EMD'
     & HpreL & HpreD).
  assert (HnlitN : nlit = (Z.to_nat hlit + 257)%nat) by lia.
  assert (Hlit' : lit = firstn nlit ls)
    by (rewrite Hlit, HnlitN, Hlseq; reflexivity).
  assert (Hdst' : dst = skipn nlit ls)
    by (rewrite Hdst, HnlitN, Hlseq; reflexivity).
  exists qL,
    (mkDynBuild (codes_wb (t_codes (s_tab (q_st q))) 0 (o_tbl o))
       (zlens ls) (br_bits_of 5 b + 257)
       (br_bits_of 5 (br_dropbits 5 b) + 1) o1 o2).
  split; [rewrite HqbrL; symmetry; exact Hr3eq|].
  split; [rewrite HqbrL; exact HwfS|].
  split; [rewrite HqbrL; exact HalS|].
  rewrite Hlit', Hdst'.
  unfold zr_len_dispatch14, db_acc.
  cbn [db_cs db_lens db_nlen db_ndist db_o1 db_o2].
  split.
  { rewrite Hstep1, Hstep2. exact Hstep3. }
  split.
  { split; [exact HwfL|].
    split; [exact EML'|].
    split; [exact Erl|].
    split; [exact HwfD|].
    split; [exact EMD'|].
    exact Erd. }
  split.
  { unfold db_installed.
    cbn [db_cs db_lens db_nlen db_ndist db_o1 db_o2].
    split; [exact HlcL|].
    split; [exact HnbL|].
    split; [exact HdcL|].
    split; [exact HdbL|].
    exact HtcL. }
  split.
  { rewrite (firstn_skipn nlit ls). reflexivity. }
  split; [lia|].
  split; [lia|].
  split; [exact Hcap1|].
  split; [exact Hcap2|].
  split; [exact HpreL|].
  split; [exact HpreD|].
  split; [rewrite HobL, HobB; exact HobA|].
  split; [rewrite HhlL, HhlB; exact HhlA|].
  split; [rewrite HinL, HinB; exact HinA|].
  split; [rewrite HoutL, HoutB; exact HoutA|].
  split; [rewrite HwszL, HwszB; exact HwszA|].
  split; [rewrite HretL; exact Erd|].
  split; [rewrite HwrL, HwrB; exact HwrA|].
  split; [rewrite HfgL, HfgB; exact HfgA|].
  split; [rewrite HckL, HckB; exact HckA|].
  split; [rewrite HtoL, HtoB; exact HtoA|].
  split; [rewrite HwvL, HwvB; exact HwvA|].
  rewrite HsnL, HsnB. exact HsnA.
Qed.

Set Printing Width 2000.
