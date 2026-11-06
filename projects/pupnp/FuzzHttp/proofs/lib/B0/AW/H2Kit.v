(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import AWKit AWAuto AWAuto2 FakeKit.
Import ListNotations.
Open Scope Z_scope.

Ltac split_chunk FR n H1 H2 :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let cs1 := eval cbv beta iota delta [firstn skipn] in (firstn n cs) in
    let cs2 := eval cbv beta iota delta [firstn skipn] in (skipn n cs) in
    change (rw_cells segs m A (cs1 ++ cs2)) in FR;
    destruct (proj1 (rw_cells_app segs m A cs1 cs2) FR) as [H1 H2]; clear FR;
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul] in H2;
    try (lazymatch type of H2 with rw_cells _ _ (?a + ?b + ?c)%Z _ =>
           let v := eval vm_compute in (b + c)%Z in replace (a + b + c)%Z with (a + v)%Z in H2 by lia end)
  end.
Ltac recell FR i :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB 8 ?b) => change (rw_cells segs m A (pre ++ CB 8 b :: post)) in FR; apply (rw_cells_CB_C8 segs m A pre b post) in FR; cbn [app] in FR
    | Some (CB 4 ?b) => change (rw_cells segs m A (pre ++ CB 4 b :: post)) in FR; apply (rw_cells_CB_C4 segs m A pre b post) in FR; cbn [app] in FR
    end end.
Ltac splitcb FR i sizes :=
  lazymatch type of FR with rw_cells ?segs ?m ?A ?cs =>
    let pre := eval cbv beta iota delta [firstn skipn] in (firstn i cs) in
    let post := eval cbv beta iota delta [firstn skipn] in (skipn (S i) cs) in
    lazymatch eval cbv beta iota delta [firstn skipn nth_error] in (nth_error cs i) with
    | Some (CB ?n ?b) => change (rw_cells segs m A (pre ++ CB n b :: post)) in FR;
        apply (rw_cells_split_CB segs m A pre n b post sizes) in FR; [| reflexivity]; cbn [app mk_CB_cells] in FR
    end end.
Ltac name_junk FR :=
  repeat lazymatch type of FR with context [CB _ (firstn ?a ?b)] => let j := fresh "jk" in remember (firstn a b) as j in FR
                      | context [CB _ (skipn ?a ?b)] => let j := fresh "jk" in remember (skipn a b) as j in FR end;
  repeat match goal with E : _ = firstn _ _ |- _ => clear E | E : _ = skipn _ _ |- _ => clear E end.

Ltac fk_move H FKc WMc :=
  lazymatch type of H with rw_cells _ ?m ?A2 ?cs2 =>
    lazymatch type of FKc with fkeep ?FIx ?Wc ?stx m ?m' =>
      apply (rw_cells_fkeep FIx Wc stx m m' A2 cs2) in H; [ | exact FKc | exact WMc | solve_in_live | dj_solve ] end end.

Ltac chk8N r APP HS :=
  let HA' := fresh "ACCn" in pose proof (proj1 HS) as HA'; acc_chk0 r APP HA'; clear HA'; step; clear_shr.

Ltac chkbN r APP HS k SHR Hk :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (acc_load mm APP a (proj1 HS APP ltac:(lia)) ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.

Ltac chkwN r APP w HS k SHR Hk :=
  let a := reg_val r in
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (acc_loadw mm APP w a ltac:(lia) ltac:(lia) ltac:(lia) (proj1 HS (APP + w - 1) ltac:(lia)) ltac:(shadow_addr_tac)) as (k & SHR & Hk) end.

Ltac evalK K := repeat match type of K with
  | context [Z.land ?a ?b] => let v := eval vm_compute in (Z.land a b) in progress change (Z.land a b) with v in K
  | context [?a mod ?b] => let v := eval vm_compute in (a mod b) in progress change (a mod b) with v in K end.

Definition selw3 (i j k n : nat) (yi yj vk v : word) : word := if Nat.eqb n i then yi else if Nat.eqb n j then yj else if Nat.eqb n k then vk else v.
Ltac gen3v CONT pcnew i j k vk :=
  let v1 := reg_val 1 in let v2 := reg_val 2 in let v3 := reg_val 3 in let v4 := reg_val 4 in let v5 := reg_val 5 in let v6 := reg_val 6 in let v7 := reg_val 7 in let v8 := reg_val 8 in let v9 := reg_val 9 in let v10 := reg_val 10 in let v11 := reg_val 11 in let v12 := reg_val 12 in let v13 := reg_val 13 in let v14 := reg_val 14 in let v15 := reg_val 15 in let v16 := reg_val 16 in let v17 := reg_val 17 in let v18 := reg_val 18 in let v19 := reg_val 19 in let v20 := reg_val 20 in let v21 := reg_val 21 in let v22 := reg_val 22 in let v23 := reg_val 23 in let v24 := reg_val 24 in let v25 := reg_val 25 in let v26 := reg_val 26 in let v27 := reg_val 27 in let v28 := reg_val 28 in let v29 := reg_val 29 in let v30 := reg_val 30 in let v31 := reg_val 31 in
  lazymatch goal with |- evt ?sg ?P (MS _ ?F _ ?fc ?o ?mm ?ro) =>
    let T := constr:(forall yi yj : word, evt sg P (MS (mkR (selw3 i j k 1%nat yi yj vk v1) (selw3 i j k 2%nat yi yj vk v2) (selw3 i j k 3%nat yi yj vk v3) (selw3 i j k 4%nat yi yj vk v4) (selw3 i j k 5%nat yi yj vk v5) (selw3 i j k 6%nat yi yj vk v6) (selw3 i j k 7%nat yi yj vk v7) (selw3 i j k 8%nat yi yj vk v8) (selw3 i j k 9%nat yi yj vk v9) (selw3 i j k 10%nat yi yj vk v10) (selw3 i j k 11%nat yi yj vk v11) (selw3 i j k 12%nat yi yj vk v12) (selw3 i j k 13%nat yi yj vk v13) (selw3 i j k 14%nat yi yj vk v14) (selw3 i j k 15%nat yi yj vk v15) (selw3 i j k 16%nat yi yj vk v16) (selw3 i j k 17%nat yi yj vk v17) (selw3 i j k 18%nat yi yj vk v18) (selw3 i j k 19%nat yi yj vk v19) (selw3 i j k 20%nat yi yj vk v20) (selw3 i j k 21%nat yi yj vk v21) (selw3 i j k 22%nat yi yj vk v22) (selw3 i j k 23%nat yi yj vk v23) (selw3 i j k 24%nat yi yj vk v24) (selw3 i j k 25%nat yi yj vk v25) (selw3 i j k 26%nat yi yj vk v26) (selw3 i j k 27%nat yi yj vk v27) (selw3 i j k 28%nat yi yj vk v28) (selw3 i j k 29%nat yi yj vk v29) (selw3 i j k 30%nat yi yj vk v30) (selw3 i j k 31%nat yi yj vk v31)) F (Z_to_bv 64 pcnew) fc o mm ro)) in
    let T' := eval cbv beta iota delta [selw3 Nat.eqb] in T in
    assert (CONT : T') end.

Definition hid2 (X : Prop) : Prop := X.
Lemma munch_absorb : forall (W Ws : list ivl) (mb m m' : mem), munch W mb m -> munch Ws m m' -> sub_fp Ws W -> munch W mb m'.
Proof. intros W Ws mb m m' MU MUs SUB. eapply (munch_trans W mb m m' MU). eapply (munch_weaken Ws W m m' SUB MUs). Qed.
Ltac hideW MU WM := lazymatch type of MU with ?T => change (hid2 T) in MU end; lazymatch type of WM with ?T => change (hid2 T) in WM end.
Ltac absorbW MU WM MUs WMs SUB :=
  unfold hid2 in MU, WM;
  lazymatch type of MUs with munch ?Ws ?ma ?mf =>
  lazymatch type of MU with munch ?W ?mb0 _ =>
    let MUn := fresh "MUn" in let WMn := fresh "WMn" in
    pose proof (munch_absorb W Ws mb0 ma mf MU MUs SUB) as MUn; pose proof (wmono_trans asegs mb0 ma mf WM WMs) as WMn;
    clear MU WM; rename MUn into MU; rename WMn into WM end end.

Definition setb (bs : list byte) (k : nat) (b : byte) : list byte := firstn k bs ++ [b] ++ skipn (k + 1) bs.
Lemma setb_length : forall bs k b, (k < length bs)%nat -> length (setb bs k b) = length bs.
Proof. intros bs k b H. unfold setb. rewrite !length_app, firstn_length_le, length_skipn by lia. cbn. lia. Qed.
Lemma setb_same : forall bs k b, (k < length bs)%nat -> nth_error (setb bs k b) k = Some b.
Proof.
  intros bs k b H. unfold setb. rewrite nth_error_app2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le, Nat.sub_diag by lia. reflexivity.
Qed.
Lemma setb_other : forall bs k b i, (k < length bs)%nat -> i <> k -> nth_error (setb bs k b) i = nth_error bs i.
Proof.
  intros bs k b i H NE. unfold setb. destruct (Nat.lt_ge_cases i k).
  - rewrite nth_error_app1 by (rewrite firstn_length_le; lia). rewrite nth_error_firstn. destruct (Nat.ltb_spec i k); [reflexivity| lia].
  - rewrite nth_error_app2 by (rewrite firstn_length_le; lia). rewrite firstn_length_le by lia.
    change ([b] ++ skipn (k + 1) bs) with (b :: skipn (k + 1) bs). destruct (i - k)%nat as [|d] eqn:E; [lia|]. cbn [nth_error].
    rewrite nth_error_skipn. f_equal. lia.
Qed.
Lemma cb_split1 : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
  rw_cells asegs m X [CB n xs] -> nth_error xs k = Some b -> 0 <= X ->
  rw_cells asegs m X [CB k (firstn k xs)] /\ rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)].
Proof.
  intros m X n xs k b BLK Hb X0.
  assert (LXS : length xs = n) by (destruct BLK as [[W _] _]; cbn in W; LiaTuning.ctauto).
  pose proof (nth_error_lt _ _ _ Hb) as LT.
  apply (rw_cells_split_CB asegs m X [] n xs [] [k; 1%nat; (n - k - 1)%nat]) in BLK; [| cbn; lia].
  cbn [app mk_CB_cells] in BLK.
  lazymatch type of BLK with rw_cells _ _ _ [?c1; ?c2; ?c3] =>
    destruct (proj1 (rw_cells_app asegs m X [c1] [c2; c3]) BLK) as [BLK1 BLK23] end.
  cbn [cells_size csize] in BLK23. rewrite Nat.add_0_r in BLK23.
  assert (E1 : firstn 1 (skipn k xs) = [b]).
  { destruct (nth_error_split _ _ _ Hb) as (pre & post & E & Hlen). rewrite E at 1. rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity. }
  rewrite E1 in BLK23.
  replace (firstn (n - k - 1) (skipn 1 (skipn k xs))) with (skipn (k + 1) xs) in BLK23.
  2:{ rewrite skipn_skipn. replace (1 + k)%nat with (k + 1)%nat by lia. symmetry. apply firstn_all2. rewrite length_skipn. lia. }
  split; [exact BLK1| exact BLK23].
Qed.
Lemma cb_join1 : forall m X (n : nat) (xs : list byte) (k : nat) (b : byte),
  rw_cells asegs m X [CB k (firstn k xs)] -> rw_cells asegs m (X + Z.of_nat k) [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] ->
  (k < n)%nat -> length xs = n ->
  rw_cells asegs m X [CB n (setb xs k b)].
Proof.
  intros m X n xs k b BLK1 BLK23 LT LXS.
  pose proof (proj2 (rw_cells_app asegs m X [CB k (firstn k xs)] [CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)])) as J.
  cbn [cells_size csize Nat.add] in J. rewrite Nat.add_0_r in J. specialize (J (conj BLK1 BLK23)). cbn [app] in J.
  pose proof (rw_cells_merge asegs m X [] [CB k (firstn k xs); CB 1 [b]; CB (n - k - 1) (skipn (k + 1) xs)] []) as M.
  rewrite !app_nil_r in M. cbn [app cells_size csize cells_bytes cbytes Nat.add] in M.
  replace (k + Datatypes.S (n - k - 1 + 0))%nat with n in M by lia.
  pose proof (M J) as MJ. rewrite app_nil_r in MJ. exact MJ.
Qed.
