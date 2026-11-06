(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require Import UImg CJ_iface CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pv_update.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pv_update.F_strlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U Require CJ_pobject_E.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.U.CJ_pobject_E.CJ_pvalue_lemmas.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.

Lemma dpres_of_munch : forall LB SP W m1 m2,
  munch W m1 m2 -> wmono usegs m1 m2 -> (forall a, 0 <= a < 2^64 -> doc_addr LB SP a -> outside W a) -> dpres LB SP m1 m2.
Proof. intros. eapply magree_of_munch; eauto. Qed.

Theorem parse_wopts_from_wlopts : forall HI, parse_wlopts_stmt HI -> parse_wopts_stmt HI.
Proof.
  intros HI WLS. unfold parse_wopts_stmt. intros until errv.
  intros HL HD DV VN V0 BY NONUL LEN31 SLACK CJ ERR MI ST CEIL LO SPSPB SPB62 SPAL FRM TP A0 A1.
  unfold wz in A0, A1. subst a0 a1. unfold PARSE_WOPTS, wz.
  pose proof (bytes_at_bound _ _ _ _ BY) as BYB. rewrite length_app in BYB. cbn [length] in BYB.
  pose proof (lh_block_range HI _ _ _ _ _ _ HL HD) as (D1 & D2 & D3 & D4 & D5). try rewrite alloc_ceiling_eq in D4. unfold PIMG_LO, PIMG_HI in D5.
  try rewrite alloc_ceiling_eq in CEIL. unfold PARSE_DOC_STACK, PARSE_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold PERRNO in ERR.
  (* [comment removed for export] *)
  set (k := (- (V + Z.of_nat (length str) + 1)) mod 8) in *.
  assert (Hk : 0 <= k < 8 /\ V + Z.of_nat (length str) + 1 + k <= alloc_ceiling).
  { subst k. clear - DV VN D4. Z.div_mod_to_equations. lia. }
  assert (LK : length (firstn (Z.to_nat k) slack) = Z.to_nat k) by (rewrite length_firstn; lia).
  assert (BYk : bytes_at usegs m V (str ++ wb 0 :: firstn (Z.to_nat k) slack)).
  { rewrite <- (firstn_skipn (Z.to_nat k) slack) in BY.
    rewrite (app_assoc str [wb 0] _ : str ++ wb 0 :: firstn (Z.to_nat k) slack ++ skipn (Z.to_nat k) slack = (str ++ [wb 0]) ++ _) in BY.
    rewrite (app_assoc (str ++ [wb 0]) (firstn (Z.to_nat k) slack) (skipn (Z.to_nat k) slack)) in BY.
    apply bytes_at_app in BY. rewrite <- app_assoc in BY. exact (proj1 BY). }
  clear BY.
  eapply scps_step_evt; [eapply (lh_mok HI); exact HL|].
  zstep. if_cases KV; zify_cond KV; [exfalso; lia|].
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  zstep. carve_frame 32%nat ST. do 4 zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply strlen_spec with (str := str) (slack := firstn (Z.to_nat k) slack); rewrite ?unsigned_lit by lia; [exact BYk| exact NONUL| rewrite LK; lia| exact MI]. }
  intros ms' PO. destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & _).
  apply munch_nil_eq in MU2. subst m2.
  replace (ret_pc (Z_to_bv 64 0x138a4)) with (Z_to_bv 64 0x138a4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  do 4 zstep. do 4 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  release_frame FR ST (bv_unsigned sp).
  zstep. apply evt_done.
  assert (HL1 : LHEAP HI SPB LB m1 mo).
  { eapply (lh_frame HI); [exact HL| exact MU| exact WM|]. constructor; [|constructor]. right; left. cbn. try rewrite alloc_ceiling_eq. lia. }
  assert (CJ1 : CJST m1).
  { eapply CJST_frame; [exact CJ| exact MU| exact WM|]. intros lo' hi' [E|[]]. inversion E; subst. unfold PDATA_LO, PIMG_HI. lia. }
  assert (BY1 : bytes_at usegs m1 V (str ++ [wb 0])).
  { rewrite (app_assoc str [wb 0] _ : str ++ wb 0 :: firstn (Z.to_nat k) slack = (str ++ [wb 0]) ++ _) in BYk. apply bytes_at_app in BYk. exact (proj1 BYk). }
  eapply scps_mono.
  { pose proof WLS as WS. unfold parse_wlopts_stmt in WS.
    eapply WS with (D := D) (n := n) (lo := lo) (bs := str ++ [wb 0]) (CA := V) (blen := Z.of_nat (length str) + 1); clear WS;
      first [ exact HL1 | exact HD | exact BY1 | exact CJ1 | exact ERR | exact MI | exact ST | exact SPAL | exact FRM | exact TP | reflexivity
            | rewrite length_app; cbn [length]; lia | unfold PARSE_DOC_STACK, PARSE_STACK; rewrite ?alloc_ceiling_eq; lia
            | unfold wz; f_equal; lia ]. }
  cbv beta. intros ms2 mo2 DP. unfold parse_doc_post in *.
  destruct DP as (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & F' & fc' & m' & r & LB' & errv'
                  & E & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  do 15 eexists. exists F', fc', m', r, LB', errv'.
  repeat (split; [eassumption|]). split; [| exact H11].
  eapply dpres_trans; [| exact H10]. eapply dpres_of_munch; [exact MU| exact WM|]. intros a Ha [[Hs|[[Hd _]|(A' & n' & Hin & Hr)]] _]; cbn; [lia| unfold PDATA_LO, PIMG_HI in Hd; lia|].
  pose proof (lh_block_range HI _ _ _ _ _ _ HL Hin) as (_ & _ & _ & R4 & _). try rewrite alloc_ceiling_eq in R4. lia.
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac zs_wrap e ::= rewrite (unsigned_lit_wrap e).
Ltac zs_wrap_in e H ::= rewrite (unsigned_lit_wrap e) in H.
Ltac zs_idioms ::=
  match goal with
  | |- context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e)
  | |- context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) by (first [lia | zrange_nonneg])
  end.
Ltac zs_idioms_in H ::=
  match type of H with
  | context [Z_to_bv 64 (?e mod 18446744073709551616)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z_to_bv 64 (?e mod 2^64)%Z] => rewrite (Z_to_bv_mod64 e) in H
  | context [Z.shiftr ((Z.shiftl ?x ?k) mod 2^64) ?k] => rewrite (zb_shl_shr x k) in H by (first [lia | zrange_nonneg])
  end.
