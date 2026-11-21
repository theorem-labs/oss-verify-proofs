(* the U1A twin of A-series
   W5A/A/ZA_itab_safe29.v (), over the spec/zmodel model (ItableModel, ItCov* ).
   1.4's inflate_table stores base = extra = 0 for CODES ("dummy value--not used"), so its table loop must never take the
   extra / base arm for CODES: every symbol the loop reads is below codes <= 19 < match = 20.  This text proves that about
   the model run (it_w20 / it_loop20 / it_safe20), from ItCovLoop's loop invariant IS and ItCovStep's W_range.
   LENS needs nothing here: spec/zmodel's lext_l already holds 1.4's entries (16, 71, 77), so the LENS arm reads the
   model's own table entry for every w - 257 < 31.  No model text is changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel InftreesCoverage.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ItCovBits ItCovPre ItCovMath ItCovStep ItCovLoop ItCovMain.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require IDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* the bound of one loop step: for CODES the symbol read is below 20 *)
Definition it_w20 (x : ItCtx) (st : ItSt) : bool :=
  if codetype_eqb (x_ty x) CODES then arr_get (t_work st) (t_sym st) <? 20 else true.

Fixpoint it_loop20 (k : nat) (x : ItCtx) (st : ItSt) : bool :=
  match k with
  | O => true
  | S k' => it_w20 x st && match it_step x st with ItCont st' => it_loop20 k' x st' | _ => true end
  end.

Lemma it_loop20_S : forall k x st,
  it_loop20 (S k) x st = it_w20 x st && match it_step x st with ItCont st' => it_loop20 k x st' | _ => true end.
Proof. reflexivity. Qed.

Lemma it_loop20_other : forall k x st, x_ty x <> CODES -> it_loop20 k x st = true.
Proof.
  induction k as [|k IH]; intros x st H; [reflexivity|].
  rewrite it_loop20_S. unfold it_w20.
  destruct (x_ty x) eqn:E; [exfalso; apply H; reflexivity| |]; cbn [codetype_eqb andb];
    destruct (it_step x st); try reflexivity; apply IH; rewrite E; discriminate.
Qed.

(* the table loop reads work[j] = znth j W, a symbol below codes *)
Lemma loop20_from : forall (ty : codetype) (lens : arr) (lens_ofs codes : Z)
    (Hcodes : 0 <= codes <= 288) (Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15)
    (Hmax : 1 <= max lens lens_ofs codes) (Hcomplete : kraft lens lens_ofs codes 15 = 2 ^ 15)
    (root : Z) (Hroot : min lens lens_ofs codes <= root <= 15) (table : Z) (HtyC : ty = CODES -> codes <= 19)
    (n : nat) (j : Z) (st : ItSt),
  0 <= j < N lens lens_ofs codes -> IS ty lens lens_ofs codes root table j st ->
  it_loop20 n {| x_ty := ty; x_lens := lens; x_lens_ofs := lens_ofs; x_table := table; x_root := root;
                 x_max := max lens lens_ofs codes; x_mask := 2 ^ root - 1 |} st = true.
Proof.
  intros ty lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot table HtyC.
  induction n as [|n IH]; intros j st Hj HIS; [reflexivity|].
  rewrite it_loop20_S.
  assert (W : it_w20 {| x_ty := ty; x_lens := lens; x_lens_ofs := lens_ofs; x_table := table; x_root := root;
                        x_max := max lens lens_ofs codes; x_mask := 2 ^ root - 1 |} st = true).
  { unfold it_w20. cbn [x_ty]. destruct (codetype_eqb ty CODES) eqn:EC; [|reflexivity].
    assert (ET : ty = CODES) by (destruct ty; cbn in EC; congruence).
    pose proof HIS as HIS0. unfold IS in HIS0. destruct HIS0 as (Hsym & _ & _ & _ & _ & Hwork & _).
    rewrite Hsym, (Hwork j Hj). pose proof (W_range lens lens_ofs codes Hcodes j Hj) as WR.
    pose proof (HtyC ET). apply Z.ltb_lt. lia. }
  rewrite W. cbn [andb].
  pose proof (trip ty lens lens_ofs codes Hcodes Hlens Hmax Hcomplete root Hroot table HtyC j st Hj HIS) as TP.
  destruct (it_step _ st) as [st'|st'|st']; unfold trip_post in TP; [| reflexivity | reflexivity].
  destruct TP as (HjN & _ & HIS' & _). exact (IH (j + 1) st' ltac:(lia) HIS').
Qed.

(* the shape of it_safe, keeping only what reaches the loop, with it_loop20 in place of it_loop_ok; true off CODES *)
Definition it_safe20 (ty : codetype) (lens : arr) (lens_ofs codes : Z)
           (tbl : arr) (table bits : Z) (work : arr) : bool :=
  if negb (codetype_eqb ty CODES) then true else
  let count := itm_count lens lens_ofs codes in
  let max := itm_max count in
  if max =? 0 then true
  else
  let min := itm_min count max in
  let root := itm_root bits max min in
  if itm_reject ty max (it_left_check count) then true
  else if it_not_enough ty (itm_used root) then true
  else it_loop20 (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max)
                 (itm_st0 min table root count tbl (itm_work lens lens_ofs codes (itm_offs count) work)).

(* ItCovMain.it_safe_true's path to the loop, for CODES (an incomplete CODES set is rejected) *)
Theorem it_safe20_true : forall (ty : codetype) (lens : arr) (lens_ofs codes : Z) (tbl : arr) (table bits : Z) (work : arr),
  0 <= codes <= 288 -> (forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15) ->
  (ty = CODES -> codes <= 19) -> 1 <= bits <= 15 -> codes <= arr_len work ->
  it_safe20 ty lens lens_ofs codes tbl table bits work = true.
Proof.
  intros ty lens lens_ofs codes tbl table bits work Hcodes Hlens HtyC Hbits Hwork.
  unfold it_safe20. destruct (codetype_eqb ty CODES) eqn:EC; [|reflexivity]. cbn [negb]. cbv zeta.
  change (itm_count lens lens_ofs codes) with (count lens lens_ofs codes).
  change (itm_max (count lens lens_ofs codes)) with (max lens lens_ofs codes).
  change (itm_min (count lens lens_ofs codes) (max lens lens_ofs codes)) with (min lens lens_ofs codes).
  destruct (Z.eqb_spec (max lens lens_ofs codes) 0) as [E0|E0]; [reflexivity|].
  rewrite (left_eq lens lens_ofs codes Hcodes Hlens).
  destruct (Z.ltb_spec (2 ^ 15) (kraft lens lens_ofs codes 15)) as [K|K]; [reflexivity|].
  unfold itm_reject. rewrite EC. cbn [orb].
  destruct (Z.ltb_spec 0 (2 ^ 15 - kraft lens lens_ofs codes 15)) as [K2|K2]; [reflexivity|]. cbn [andb].
  assert (HC : kraft lens lens_ofs codes 15 = 2 ^ 15) by lia.
  rewrite (used_eq lens lens_ofs codes bits Hcodes Hlens Hbits E0).
  destruct (it_not_enough ty (2 ^ itm_root bits (max lens lens_ofs codes) (min lens lens_ofs codes))) eqn:NE;
    [reflexivity|].
  rewrite (ctx_eq ty lens lens_ofs codes table bits Hcodes Hlens Hbits E0).
  pose proof (Hmax1 lens lens_ofs codes Hcodes Hlens E0) as M1.
  pose proof (CN lens lens_ofs codes Hcodes Hlens M1) as CN1.
  apply (loop20_from ty lens lens_ofs codes Hcodes Hlens M1 HC _ (Hroot lens lens_ofs codes bits Hcodes Hlens Hbits E0)
           table HtyC (Z.to_nat (codes + 1)) 0); [lia|].
  exact (IS0' ty lens lens_ofs codes tbl table bits work Hcodes Hlens Hbits Hwork E0 NE).
Qed.

(* it_safe20 from the ItA call context, as ItAPure.it_safe_ok gives it_safe *)
Lemma it_safe20_ok : forall (ty : codetype) (lf : Z -> Z) (lens_ofs codes nx bits : Z) (cf wf : Z -> Z),
  itc ty lf lens_ofs codes nx bits cf wf ->
  it_safe20 ty (lensA lf) lens_ofs codes (tblA cf) nx bits (workA wf) = true.
Proof.
  intros ty lf lens_ofs codes nx bits cf wf C.
  destruct C as [Hlf Hcf Hwf Hofs Hofs2 Hcodes Hcodes2 Hlens15 HtyC HtyD Hbits Hbits2 Hnx Hroom].
  apply it_safe20_true; unfold lensA, workA; rewrite ?arr_len_init.
  all: cbv [IDefs.N_WORK IDefs.N_LENS IDefs.N_CODES] in *; try lia.
  all: first [ intros s Hs; rewrite arr_get_init; pose proof (Hlf (lens_ofs + s) ltac:(lia)); pose proof (Hlens15 s Hs); lia
             | intros H; exact (proj1 (HtyC H)) ].
Qed.

(* the loop part of it_safe20, in the shape of ItableModel.it_safe_sort, for the walk *)
Lemma it_safe20_loop : forall ty lens lens_ofs codes tbl table bits work,
  it_safe20 ty lens lens_ofs codes tbl table bits work = true ->
  let count := itm_count lens lens_ofs codes in let max := itm_max count in
  let min := itm_min count max in let root := itm_root bits max min in
  max <> 0 -> itm_reject ty max (it_left_check count) = false -> it_not_enough ty (itm_used root) = false ->
  it_loop20 (Z.to_nat (codes + 1)) (itm_ctx ty lens lens_ofs table root max)
            (itm_st0 min table root count tbl (itm_work lens lens_ofs codes (itm_offs count) work)) = true.
Proof.
  intros ty lens lens_ofs codes tbl table bits work S count max min root NZ RJ NE.
  destruct (codetype_eqb ty CODES) eqn:EC.
  - unfold it_safe20 in S. rewrite EC in S. cbn [negb] in S. cbv zeta in S. fold count max min root in S.
    rewrite (proj2 (Z.eqb_neq max 0) NZ), RJ, NE in S. cbn iota in S. exact S.
  - apply it_loop20_other. unfold itm_ctx. cbn [x_ty]. intros E. subst ty. cbn in EC. discriminate.
Qed.

(* one step's bound in the form the walk uses *)
Lemma it_w20_codes : forall ty lens lens_ofs table root max st,
  it_w20 (itm_ctx ty lens lens_ofs table root max) st = true -> ty = CODES -> arr_get (t_work st) (t_sym st) < 20.
Proof.
  intros ty lens lens_ofs table root max st W ET. subst ty. unfold it_w20, itm_ctx in W. cbn [x_ty codetype_eqb] in W.
  apply Z.ltb_lt. exact W.
Qed.
