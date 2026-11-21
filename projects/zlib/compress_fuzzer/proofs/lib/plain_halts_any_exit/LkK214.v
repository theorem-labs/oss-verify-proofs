(* the zlib 1.4 twin of LkK2, RT's inflate at 1.4. Cut: untainted top-level declarations (imported from LkK2), 1.3.1-only declarations no 1.4 consumer needs. *)
(** * LkK2 — K2: [ZrHuffFixedLegSelGood_STMT] discharged (q7-decode
    leavekill fork, 2026-08-22, OFF-TREE SCRATCH).

    Statement: the ratified Gap7LeaveKill.v (md5
    , byte-verbatim copy in this bed).

    MIRROR of g1's Gap7FixAsm.zr_huff_fixed_leg_sel_holds (the 3-arm
    fixed assembly, a working folder ) with the selection loop
    swapped for the GOOD-ONLY [LkLoopGood.lk_sym_loop_fix_good]: the
    M_LEN_ entry aliases through [qmode] exactly as the landed
    assembly's, the premise dischargers are the walk's own landed
    fixed-table constants (ZReproQ6R + GtDecHsel), and the statement's
    own declarative-success premises feed the loop.  No disjunction
    reaches the consumer.

    PA-EXPORT: k2_fixed_leg_good. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import
  ZReproQ6A ZReproQ6I ZReproQ6Q ZReproQ6R Q6HuffResidue ZReproL0E.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require ZReproQ6M.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require GtDecHsel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require W2Stream.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import GtBrAlign.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import Gap7LeaveKill.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkLoopGood.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import LkK2.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import A1trip14 Gap7LeaveKill14 LkLoopGood14 Spec.PngModel.Inflate14 Spec.PngModel.Inflate14Iter.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

Theorem k2_fixed_leg_good14 : ZrHuffFixedLegSelGood_STMT14.
Proof.
  unfold ZrHuffFixedLegSelGood_STMT14.
  intros c q syms r3 out Hc Hwf Hha Hbud Hput Hleft Htie Hcap Hwh Hsn
         Hm HpL HpLb HpD HpDb Hdec Hres Hroom.
  set (qm := qmode q M_LEN).
  assert (Hshm : GtDecHsel.lcode_root_opshape
            (tbl_of (q_st qm) (t_lencode (s_tab (q_st qm))))
            (t_lenbits (s_tab (q_st qm)))).
  { assert (Hviewl : tbl_of (q_st qm) (t_lencode (s_tab (q_st qm)))
                     = lenfix).
    { assert (HpLm : t_lencode (s_tab (q_st qm)) = TRlenfix) by exact HpL.
      rewrite HpLm. reflexivity. }
    assert (Hrootl : t_lenbits (s_tab (q_st qm)) = 9) by exact HpLb.
    rewrite Hviewl, Hrootl. exact GtDecHsel.lenfix_root_opshape. }
  assert (HAL : inf_step14 c q = inf_step14 c qm).
  { rewrite (zr_step14_at_len c qm ltac:(reflexivity)).
    unfold inf_step14, q_mode. rewrite Hm.
    unfold inf_LEN_14. reflexivity. }
  assert (Hviewl : tbl_of (q_st qm) (t_lencode (s_tab (q_st qm)))
                   = lenfix).
  { assert (HpLm : t_lencode (s_tab (q_st qm)) = TRlenfix) by exact HpL.
    rewrite HpLm. reflexivity. }
  assert (Hviewd : tbl_of (q_st qm) (t_distcode (s_tab (q_st qm)))
                   = distfix).
  { assert (HpDm : t_distcode (s_tab (q_st qm)) = TRdistfix) by exact HpD.
    rewrite HpDm. reflexivity. }
  assert (Hrootl : t_lenbits (s_tab (q_st qm)) = 9) by exact HpLb.
  assert (Hrootd : t_distbits (s_tab (q_st qm)) = 5) by exact HpDb.
  destruct (lk_sym_loop_fix_good14
              (S (length (br_stream (q_br qm)))) c qm
              zr_entl_fix zr_entd_fix syms r3 out
              ltac:(exact HpL) ltac:(exact HpLb)
              ltac:(exact HpD) ltac:(exact HpDb)
              fixed_lit_valid fixed_dist_valid
              ltac:(rewrite Hviewl, Hrootl; exact zr_ownl_fix)
              ltac:(rewrite Hviewd, Hrootd; exact zr_ownd_fix)
              ltac:(rewrite Hrootl; lia)
              ltac:(rewrite Hrootd; lia)
              zr_subl_fix zr_subd_fix zr_entsl_fix zr_entsd_fix
              Hshm
              ltac:(lia) Hwf Hput Hleft Htie Hcap Hwh Hsn
              ltac:(reflexivity) Hha Hbud
              Hdec Hres Hroom)
    as (k & q' & HI & HS & HR' & HM & C6 & C7 & C8 & C9 & C10 & C11
        & C12 & C13 & CF & CK & CT & C14 & C15 & C16 & CH).
  destruct k as [|k'].
  { exfalso. cbn [inf_iter14] in HI. injection HI as <-.
    assert (HmM : h_mode (s_hdr (q_st qm)) = M_LEN) by reflexivity.
    rewrite HmM in HM. discriminate. }
  exists (S k'), q'.
  split. { exact (inf_iter14_alias_S c q qm k' q' HAL HI). }
  split. { exact HS. }
  split. { exact C6. }
  split.
  { assert (Eob : q_ob qm = q_ob q) by reflexivity.
    rewrite Eob in HR'.
    rewrite Hres in HR'. injection HR' as E. exact (eq_sym E). }
  split. { exact C9. }
  split. { exact C7. }
  split. { exact C8. }
  split. { exact HM. }
  split. { exact C12. }
  assert (Hbud' : br_have (q_br q') + br_bits (q_br q') / 8
                  <= 4294967290).
  { pose proof (decode_symbols_shorter _ _ _ _ _ Hdec) as HLn.
    pose proof (br_budget_mono (q_br q) (q_br q') Hwf C6
                  ltac:(rewrite HS; lia)) as HBM.
    lia. }
  split.
  { split. { exact C15. }
    split. { exact C16. }
    split. { exact C14. }
    split. { rewrite C11. reflexivity. }
    split. { exact C13. }
    split. { exact CF. }
    split. { exact CK. }
    split. { exact CT. }
    split. { rewrite C11. reflexivity. }
    rewrite C10. reflexivity. }
  split. { exact CH. }
  exact Hbud'.
Qed.

Set Printing Width 2000.
