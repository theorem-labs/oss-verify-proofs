From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require StrLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_ContStmt LbB_WoBP.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_TablImg LbB_WoGen.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Fixpoint in_rngs (Wr : list (Z * Z)) (i : Z) : Prop :=
  match Wr with
  | [] => False
  | (lo, hi) :: Wr' => (lo <= i < hi) \/ in_rngs Wr' i
  end.

Fixpoint in_rngsb (Wr : list (Z * Z)) (i : Z) : bool :=
  match Wr with
  | [] => false
  | (lo, hi) :: Wr' => ((lo <=? i) && (i <? hi)) || in_rngsb Wr' i
  end.

Lemma in_rngsb_false : forall Wr i, in_rngsb Wr i = false -> ~ in_rngs Wr i.
Proof.
  induction Wr as [|[lo hi] Wr IH]; cbn; intros i E; [tauto|].
  apply orb_false_iff in E as [E1 E2]. intros [Hr|Hr]; [|exact (IH i E2 Hr)].
  apply andb_false_iff in E1 as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
Qed.

Lemma fldA1_mod : forall (m : mem) a v, fldA m a 1 v -> fldA m a 1 (v mod 256).
Proof.
  unfold fldA, fld. intros m a v F. rewrite StrLib.w1_bytes in F |- *.
  rewrite Z.mod_mod by lia. exact F.
Qed.

Definition shp_ok (bs bs' : list Z) (Wr WV : list (Z * Z)) : bool :=
  Nat.eqb (length bs') (length bs)
  && forallb (fun i =>
       if in_rngsb Wr (Z.of_nat i)
       then existsb (fun kv => (fst kv =? Z.of_nat i) && (snd kv mod 256 =? nth i bs' 0)) WV
       else (nth i bs' 0 =? nth i bs 0)) (seq 0 (length bs)).

Lemma bp_shad_set : forall ff L L' (m m' : mem) W Wr WV,
  bp_shad ff L m -> munch W m m' -> wmono asegs m m' ->
  shp_ok (wo_sh L) (wo_sh L') Wr WV = true ->
  (forall i, 0 <= i < Z.of_nat (length (wo_sh L)) -> ~ in_rngs Wr i -> outside W (sh ff + i)) ->
  Forall (fun kv => fldA m' (sh ff + fst kv) 1 (snd kv)) WV ->
  bp_shad ff L' m'.
Proof.
  intros ff L L' m m' W Wr WV SH MU WM OK OUT FV.
  unfold shp_ok in OK. apply andb_true_iff in OK as [LN AL]. apply Nat.eqb_eq in LN.
  rewrite forallb_forall in AL. rewrite Forall_forall in FV.
  unfold bp_shad, u8arr in *. destruct SH as ((B0 & B1 & BB) & WR).
  rewrite length_map in B1, BB, WR.
  split; [split; [exact B0|split]|].
  - rewrite length_map, LN. exact B1.
  - intros i Hi. rewrite length_map, LN in Hi.
    assert (HA : 0 <= sh ff + Z.of_nat i < 2 ^ 64) by lia.
    assert (IS : In i (seq 0 (length (wo_sh L)))) by (apply in_seq; lia).
    specialize (AL i IS).
    rewrite nth_error_map, (nth_error_nth' _ 0) by lia. cbn [option_map].
    destruct (in_rngsb Wr (Z.of_nat i)) eqn:E.
    + apply existsb_exists in AL as ([k v] & KV & KE). cbn [fst snd] in KE.
      apply andb_true_iff in KE as [K1 K2]. apply Z.eqb_eq in K1. apply Z.eqb_eq in K2.
      pose proof (FV _ KV) as F1. cbn [fst snd] in F1.
      rewrite K1 in F1. apply fldA1_mod in F1. rewrite K2 in F1.
      assert (V : 0 <= nth i (wo_sh L') 0 < 256) by (rewrite <- K2; apply Z.mod_pos_bound; lia).
      exact (LbB_TablImg.fld1_mrd m' _ _ F1 HA V).
    + apply Z.eqb_eq in AL.
      assert (HO : outside W (sh ff + Z.of_nat i)) by (apply OUT; [lia | apply in_rngsb_false; exact E]).
      specialize (BB i ltac:(lia)).
      rewrite nth_error_map, (nth_error_nth' _ 0) in BB by lia. cbn [option_map] in BB.
      rewrite AL, <- BB. unfold mrd. rewrite (MU (wa (sh ff + Z.of_nat i))); [reflexivity|].
      rewrite wa_unsigned by lia. exact HO.
  - rewrite length_map, LN. eapply wr_at_transport; [exact WR | exact WM].
Qed.

Lemma bp_shad_addr : forall ff L (m : mem) k n,
  bp_shad ff L m -> 0 <= ff -> ff mod 8 = 0 -> 0 <= k -> k mod 8 = 0 -> 0 <= n -> n mod 8 = 0 ->
  k / 8 + n / 8 <= Z.of_nat (length (wo_sh L)) ->
  firstn (Z.to_nat (n / 8)) (skipn (Z.to_nat (k / 8)) (wo_sh L)) = repeat 0 (Z.to_nat (n / 8)) ->
  addressable m (ff + k) n.
Proof.
  intros ff L m k n SH F0 F8 K0 K8 N0 N8 LEN Z0.
  unfold addressable, SHAD. split; [exact N0|]. split; [lia|]. split.
  { rewrite Z.add_mod by lia. rewrite F8, K8. reflexivity. }
  unfold shadow_of. rewrite N8. cbn [Z.eqb]. rewrite app_nil_r.
  assert (E1 : (ff + k) / 8 = ff / 8 + k / 8).
  { pose proof (Z.div_mod ff 8 ltac:(lia)) as Df. rewrite F8, Z.add_0_r in Df.
    rewrite Df at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
  replace (sh (ff + k)) with (sh ff + k / 8) by (unfold sh; rewrite E1; ring).
  unfold bp_shad in SH.
  assert (D0 : 0 <= k / 8) by (apply Z.div_pos; lia).
  assert (D1 : 0 <= n / 8) by (apply Z.div_pos; lia).
  pose proof (LbB_WoGen.u8arr_sub m (sh ff) _ (k / 8) (n / 8) SH D0 D1 ltac:(rewrite length_map; exact LEN)) as U.
  rewrite skipn_map, firstn_map, Z0, map_repeat in U. exact U.
Qed.
