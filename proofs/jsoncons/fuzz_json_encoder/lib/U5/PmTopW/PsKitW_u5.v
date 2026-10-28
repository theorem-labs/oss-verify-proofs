(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5
  PmLibSpecsW_u5 PmRef_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 PsBase_u5.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PKW.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tokc (P a : Z) : Prop := (P + 148 <= a < P + 156) \/ a = P + 220.
Lemma rm_match_xfer : forall (K : Z -> Prop) c (M M' : mem) P ps st mo stk w,
  PMR.rm_match c M P ps -> TK.samem K M M' -> 0 <= P < 2 ^ 60 -> (forall a, tokc P a -> K a) ->
  st = ps_st ps -> mo = ps_more ps -> stk = ps_stack ps ->
  PMR.rm_match c M' P (PSB.ps_upd ps st mo stk w).
Proof.
  intros K c M M' P ps st mo stk w (H1 & H2 & H3) AG HP HK -> -> ->.
  split; [destruct ps; exact H1|]. split.
  - intros Hs. destruct (H2 ltac:(destruct ps; exact Hs)) as (A1 & A2 & A3 & A4 & A5 & t & Ht & Rt).
    split; [destruct ps; exact A1|]. split; [destruct ps; exact A2|]. split; [destruct ps; exact A3|].
    split; [intros Hr; apply (TK2.u32_x K M M' AG); [lia | intros i Hi; apply HK; unfold tokc; lia | exact (A4 Hr)]|].
    split; [intros Hr; apply (TK2.u32_x K M M' AG); [lia | intros i Hi; apply HK; unfold tokc; lia | exact (A5 Hr)]|].
    exists t. split; [|exact Rt]. apply (TK2.u8_x K M M' AG); [lia | intros i Hi; apply HK; unfold tokc; lia | exact Ht].
  - intros Hn. destruct (H3 ltac:(destruct ps; exact Hn)) as (B1 & B2). split; [destruct ps; exact B1 | destruct ps; exact B2].
Qed.
(* [comment removed for export] *)
Lemma rm_match_nontok : forall c (M : mem) P ps,
  PMR.rm_core c ps -> ps_st ps <> ST_STRING -> ps_st ps <> ST_NUMBER -> PMR.rm_match c M P ps.
Proof. intros c M P ps H NS NN. split; [exact H|]. split; intros X; contradiction. Qed.
Lemma rm_core_upd_same : forall c ps w, PMR.rm_core c ps -> PMR.rm_core c (PSB.ps_upd ps (ps_st ps) (ps_more ps) (ps_stack ps) w).
Proof. intros c ps w H. destruct ps; exact H. Qed.
(* [comment removed for export] *)
Lemma rm_core_pop : forall c ps rest x w, PMR.rm_core c ps -> ps_stack ps = rest ++ [x] ->
  PMR.rm_core (PMR.set_st (PMR.pop c) (PMR.top c)) (PSB.ps_upd ps x (ps_more ps) rest w).
Proof.
  intros c ps rest x w (H1 & H2 & H3 & H4 & H5) HS. unfold PMR.rm_core, PMR.set_st, PMR.pop, PMR.top, PMR.set_stack. cbn [PMR.c_st PMR.c_more PMR.c_done PMR.c_level PMR.c_stack].
  rewrite H5, HS. rewrite last_last, removelast_last. destruct ps; cbn; repeat split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u8_eq : forall (M : mem) a x y, L5.u8_at RSEGS M a x -> L5.u8_at RSEGS M a y -> 0 <= x < 256 -> 0 <= y < 256 -> x = y.
Proof.
  intros M a x y Hx Hy Rx Ry. unfold L5.u8_at in *. rewrite Hx in Hy.
  assert (E : bv_unsigned (Z_to_bv 8 x) = bv_unsigned (Z_to_bv 8 y)) by (apply (f_equal (fun o : option (list byte) => match o with Some (b :: _) => bv_unsigned b | _ => 0 end)) in Hy; exact Hy).
  rewrite !Z_to_bv_unsigned in E. change (bv_wrap 8 x) with (x mod 2 ^ 8) in E. change (bv_wrap 8 y) with (y mod 2 ^ 8) in E.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.
(* [comment removed for export] *)
Lemma win_byte : forall (M M' : mem) ps p e w q b (K : Z -> Prop),
  PMW.win_bytes M ps w -> ps_win ps = Some (p, e) -> TK.samem K M M' -> (forall a, p <= a < e -> K a) -> 0 <= p -> e < 2 ^ 63 ->
  p <= q < e -> L5.u8_at RSEGS M' q b -> 0 <= b < 256 -> b = nth (Z.to_nat (q - p)) w 0.
Proof.
  intros M M' ps p e w q b K WB HW AG HK Hp He Hq Cb Rb. unfold PMW.win_bytes in WB. rewrite HW in WB. destruct WB as (BA & LEN & RG).
  assert (Hi : (Z.to_nat (q - p) < length w)%nat) by lia.
  pose proof (BA (Z.to_nat (q - p)) Hi) as X. rewrite Z2Nat.id in X by lia. replace (p + (q - p)) with q in X by lia.
  pose proof (proj1 (Forall_nth _ _) RG (Z.to_nat (q - p)) 0 Hi) as R. cbn beta in R.
  apply (u8_eq M' q); [exact Cb | | lia | lia]. apply (TK.u8_samem K M M' q _ AG); [lia | apply HK; lia | exact X].
Qed.
(* [comment removed for export] *)
Lemma win_bytes_move : forall (M M' : mem) ps p e w q (K : Z -> Prop) st mo stk,
  PMW.win_bytes M ps w -> ps_win ps = Some (p, e) -> TK.samem K M M' -> (forall a, p <= a < e -> K a) -> 0 <= p -> e < 2 ^ 63 -> p <= q <= e ->
  PMW.win_bytes M' (PSB.ps_upd ps st mo stk (Some (q, e))) (skipn (Z.to_nat (q - p)) w).
Proof.
  intros M M' ps p e w q K st mo stk WB HW AG HK Hp He Hq. unfold PMW.win_bytes in *. rewrite HW in WB. destruct WB as (BA & LEN & RG).
  replace (ps_win (PSB.ps_upd ps st mo stk (Some (q, e)))) with (Some (q, e)) by (destruct ps; reflexivity).
  split; [|split; [rewrite length_skipn; lia | apply Forall_forall; intros x Hx; apply (proj1 (Forall_forall _ _) RG x); apply In_nth with (d := 0) in Hx as (n & Hn & <-);
                                                       rewrite nth_skipn; apply nth_In; rewrite length_skipn in Hn; lia]].
  intros i Hi. rewrite length_skipn in Hi. rewrite nth_skipn.
  pose proof (BA (Z.to_nat (q - p) + i)%nat ltac:(lia)) as X. replace (p + Z.of_nat (Z.to_nat (q - p) + i)) with (q + Z.of_nat i) in X by lia.
  apply (TK.u8_samem K M M' _ _ AG); [lia | apply HK; lia | exact X].
Qed.
Lemma win_bytes_len : forall (M : mem) ps p e w, PMW.win_bytes M ps w -> ps_win ps = Some (p, e) -> Z.of_nat (length w) = e - p.
Proof. intros M ps p e w WB HW. unfold PMW.win_bytes in WB. rewrite HW in WB. exact (proj1 (proj2 WB)). Qed.
(* [comment removed for export] *)
Lemma win_bytes_same : forall (M M' : mem) ps p e w (K : Z -> Prop) st mo stk,
  PMW.win_bytes M ps w -> ps_win ps = Some (p, e) -> TK.samem K M M' -> (forall a, p <= a < e -> K a) -> 0 <= p -> e < 2 ^ 63 ->
  PMW.win_bytes M' (PSB.ps_upd ps st mo stk (Some (p, e))) w.
Proof.
  intros M M' ps p e w K st mo stk WB HW AG HK Hp He.
  pose proof (win_bytes_len M ps p e w WB HW) as L. pose proof (win_bytes_move M M' ps p e w p K st mo stk WB HW AG HK Hp He ltac:(lia)) as X. rewrite Z.sub_diag in X. exact X.
Qed.
Lemma win_bytes_none : forall (M : mem) ps w, PMW.win_bytes M ps w -> ps_win ps = None -> w = [].
Proof. intros M ps w WB HW. unfold PMW.win_bytes in WB. rewrite HW in WB. exact WB. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forallb_firstn_S : forall (f : Z -> bool) n (w : list Z), (n < length w)%nat ->
  forallb f (firstn (S n) w) = forallb f (firstn n w) && f (nth n w 0).
Proof.
  intros f n. induction n as [|n IH]; intros [|x r] H; cbn [length] in H; try lia.
  - cbn. destruct (f x); reflexivity.
  - cbn [firstn forallb nth]. rewrite (IH r) by lia. destruct (f x); [reflexivity | reflexivity].
Qed.
Lemma forallb_all_firstn : forall (f : Z -> bool) (w : list Z), forallb f (firstn (length w) w) = forallb f w.
Proof. intros f w. rewrite firstn_all. reflexivity. Qed.
(* [comment removed for export] *)
Lemma forallb_fail_at : forall (f : Z -> bool) n (w : list Z), (n < length w)%nat -> f (nth n w 0) = false -> forallb f w = false.
Proof.
  intros f n w Hn Hf. destruct (forallb f w) eqn:X; [|reflexivity]. exfalso.
  rewrite forallb_forall in X. rewrite (X (nth n w 0) (nth_In w 0 Hn)) in Hf. discriminate Hf.
Qed.
(* [comment removed for export] *)
Lemma pcd_ok : forall c w, forallb PMR.is_ws w = true -> PMW.rm_step PMR.the_rm PMW.FCheckDone c w = PMW.CR c [] (Z.of_nat (length w)) 0 0.
Proof.
  intros c w H. cbn [PMW.rm_step PMR.the_rm PMR.rstep]. unfold PMR.pcheck_done. rewrite H. unfold PMR.r_of, PMR.ret. cbn [PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code length].
  f_equal. change (Z.of_nat 0) with 0. lia.
Qed.
Lemma pcd_err : forall c w, forallb PMR.is_ws w = false -> PMW.rm_step PMR.the_rm PMW.FCheckDone c w = PMW.CR (PMR.set_more c false) [] 0 PMR.E_EXTRA_CHAR 0.
Proof.
  intros c w H. cbn [PMW.rm_step PMR.the_rm PMR.rstep]. unfold PMR.pcheck_done. rewrite H. unfold PMR.r_of, PMR.err. cbn [PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code].
  f_equal. lia.
Qed.
(* [comment removed for export] *)
Lemma w_after_CR : forall (cc : PMR.ctrl) evs used code al w, PMW.w_after PMR.the_rm (PMW.CR cc evs used code al) w = skipn (Z.to_nat used) w.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma is_ws_spec : forall b, PMR.is_ws b = true <-> In b [9; 10; 13; 32].
Proof.
  intros b. unfold PMR.is_ws. rewrite !Bool.orb_true_iff, !Z.eqb_eq. cbn [In]. clear. split; intros H; lia.
Qed.
(* [comment removed for export] *)
Lemma ss_facts : forall n c w, (length w <= n)%nat ->
  (exists m, snd (PMR.skip_space c w) = skipn m w) /\
  (forall b2 r2, snd (PMR.skip_space c w) = b2 :: r2 -> PMR.is_ws b2 = false /\ fst (PMR.skip_space c w) = c).
Proof.
  induction n as [|n IH]; intros c w Hn.
  - destruct w; [|cbn in Hn; lia]. cbn. split; [exists 0%nat; reflexivity|]. intros b2 r2 X. discriminate X.
  - destruct w as [|b r]; [cbn; split; [exists 0%nat; reflexivity|]; intros b2 r2 X; discriminate X|]. cbn [length] in Hn.
    cbn [PMR.skip_space]. fold PMR.skip_space.
    destruct ((b =? 32) || (b =? 9) || (b =? 10)) eqn:W3.
    + destruct (IH c r ltac:(lia)) as [(m & Hm) Hh]. split; [exists (S m); rewrite Hm; reflexivity | exact Hh].
    + destruct (Z.eqb_spec b 13) as [->|NB].
      * destruct r as [|b2 r2].
        -- cbn [fst snd]. split; [exists 1%nat; reflexivity|]. intros b3 r3 X. discriminate X.
        -- destruct (Z.eqb_spec b2 10) as [->|NB2].
           ++ destruct (IH c r2 ltac:(cbn [length] in Hn; lia)) as [(m & Hm) Hh]. split; [exists (S (S m)); rewrite Hm; reflexivity | exact Hh].
           ++ destruct (IH c (b2 :: r2) ltac:(lia)) as [(m & Hm) Hh]. split; [exists (S m); rewrite Hm; reflexivity | exact Hh].
      * cbn [fst snd]. split; [exists 0%nat; reflexivity|]. intros b2 r2 X. injection X as <- <-. split; [|reflexivity].
        unfold PMR.is_ws. rewrite W3. cbn [orb]. apply Z.eqb_neq. exact NB.
Qed.
Lemma skipn_canon : forall {A} m (w : list A), skipn m w = skipn (length w - length (skipn m w)) w.
Proof.
  intros A m w. rewrite length_skipn. destruct (Nat.le_gt_cases m (length w)) as [L|L].
  - f_equal. lia.
  - rewrite (skipn_all2 (n:=m) w ltac:(lia)). replace (length w - (length w - m))%nat with (length w) by lia. symmetry. apply skipn_all.
Qed.
Lemma ss_suffix : forall c w, snd (PMR.skip_space c w) = skipn (length w - length (snd (PMR.skip_space c w))) w.
Proof. intros c w. destruct (proj1 (ss_facts (length w) c w ltac:(lia))) as (m & Hm). rewrite Hm at 2. rewrite <- skipn_canon. exact Hm. Qed.
Lemma ss_head : forall c w b2 r2, snd (PMR.skip_space c w) = b2 :: r2 -> PMR.is_ws b2 = false /\ fst (PMR.skip_space c w) = c.
Proof. intros c w b2 r2 H. exact (proj2 (ss_facts (length w) c w ltac:(lia)) b2 r2 H). Qed.
(* [comment removed for export] *)
Lemma sw_nil : forall c, PMR.skip_whitespace c [] = (c, []).
Proof. intros c. reflexivity. Qed.
Lemma sw_stop : forall c b r, PMR.c_st c <> ST_CR -> PMR.is_ws b = false -> PMR.skip_whitespace c (b :: r) = (c, b :: r).
Proof.
  intros c b r NC NW. cbn [PMR.skip_whitespace]. rewrite (proj2 (Z.eqb_neq _ _) NC). cbn [fst snd]. rewrite NW. reflexivity.
Qed.
Lemma sw_space : forall c b r, PMR.c_st c <> ST_CR -> PMR.is_ws b = true -> PMR.skip_whitespace c (b :: r) = PMR.skip_space c (b :: r).
Proof.
  intros c b r NC W. cbn [PMR.skip_whitespace]. rewrite (proj2 (Z.eqb_neq _ _) NC). cbn [fst snd]. rewrite W. reflexivity.
Qed.
Lemma sw_after_ss : forall c b r, PMR.c_st c <> ST_CR -> PMR.is_ws b = true ->
  PMR.skip_whitespace (fst (PMR.skip_space c (b :: r))) (snd (PMR.skip_space c (b :: r))) = PMR.skip_whitespace c (b :: r).
Proof.
  intros c b r NC W. rewrite (sw_space c b r NC W).
  destruct (snd (PMR.skip_space c (b :: r))) as [|b2 r2] eqn:S2.
  - rewrite sw_nil. rewrite <- S2. symmetry. apply surjective_pairing.
  - destruct (ss_head c (b :: r) b2 r2 S2) as [NW2 FC]. rewrite FC. rewrite sw_stop; [| rewrite <- FC in NC at 1; rewrite FC in NC; exact NC | exact NW2].
    rewrite <- S2, <- FC at 1. symmetry. apply surjective_pairing.
Qed.
Lemma sw_cr_step : forall c b r rest x, PMR.c_st c = ST_CR -> PMR.c_stack c = rest ++ [x] -> x <> ST_CR ->
  PMR.skip_whitespace (PMR.set_st (PMR.pop c) (PMR.top c)) (if b =? 10 then r else b :: r) = PMR.skip_whitespace c (b :: r).
Proof.
  intros c b r rest x HC HS NX.
  assert (TOP : PMR.top c = x) by (unfold PMR.top; rewrite HS; apply last_last).
  assert (ST' : PMR.c_st (PMR.set_st (PMR.pop c) (PMR.top c)) = x) by (rewrite TOP; reflexivity).
  cbn [PMR.skip_whitespace]. rewrite HC, Z.eqb_refl. cbv zeta.
  destruct (if b =? 10 then r else b :: r) as [|b1 r1] eqn:W1; cbn [fst snd].
  - reflexivity.
  - cbn [PMR.skip_whitespace]. rewrite ST'. rewrite (proj2 (Z.eqb_neq _ _) NX). cbn [fst snd]. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma ss_step : forall c w, PMW.rm_step PMR.the_rm PMW.FSkipSpace c w =
  PMW.CR (fst (PMR.skip_space c w)) [] (Z.of_nat (length w) - Z.of_nat (length (snd (PMR.skip_space c w)))) 0 0.
Proof. intros c w. cbn [PMW.rm_step PMR.the_rm PMR.rstep]. unfold PMR.skip_space_r, PMR.r_of, PMR.ret. cbn [PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code]. reflexivity. Qed.
Lemma ss_w_after : forall c w, PMW.w_after PMR.the_rm (PMW.rm_step PMR.the_rm PMW.FSkipSpace c w) w = snd (PMR.skip_space c w).
Proof.
  intros c w. rewrite ss_step, w_after_CR. set (s2 := snd (PMR.skip_space c w)). pose proof (ss_suffix c w) as SUF. fold s2 in SUF.
  assert (L : (length s2 <= length w)%nat) by (rewrite SUF, length_skipn; lia).
  transitivity (skipn (length w - length s2) w); [f_equal; lia | symmetry; exact SUF].
Qed.
Lemma sws_step : forall c w, PMW.rm_step PMR.the_rm PMW.FSkipWs c w =
  PMW.CR (fst (PMR.skip_whitespace c w)) [] (Z.of_nat (length w) - Z.of_nat (length (snd (PMR.skip_whitespace c w)))) 0 0.
Proof. intros c w. cbn [PMW.rm_step PMR.the_rm PMR.rstep]. unfold PMR.r_of, PMR.ret. cbn [PMR.q_c PMR.q_w PMR.q_evs PMR.q_al PMR.q_code]. reflexivity. Qed.
Lemma win_bytes_winlen : forall (M : mem) ps w, PMW.win_bytes M ps w -> Z.of_nat (length w) = winlen ps.
Proof.
  intros M ps w WB. unfold PMW.win_bytes, winlen in *. destruct (ps_win ps) as [[p e]|]; [exact (proj1 (proj2 WB)) | subst w; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma suffix_trans : forall (w1 w0 s : list Z) m, w1 = skipn (length w0 - length w1) w0 -> s = skipn m w1 -> s = skipn (length w0 - length s) w0.
Proof. intros w1 w0 s m H1 Hs. subst s. rewrite H1 at 1. rewrite skipn_skipn. rewrite (skipn_canon (m + (length w0 - length w1)) w0) at 1. rewrite <- skipn_skipn, <- H1. reflexivity. Qed.
End PKW.
