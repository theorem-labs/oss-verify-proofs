(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Amb PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require ShapeAlg Shapi1s Nodes MmapSim AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AgentLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Li6dm Spec LibWbxd RefNodes D_Exvwg D_Stqgu D_Exit RefMocc D_Stmwg D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require AllocSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require MemSplit D_Kn21w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh SymAux RefPl89 D_TrRuns.

Module D_TrLib.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac StoreOk MemSplit SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Kn21w D_Knp98 D_Manqc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Mah0u.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Alu7n.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Tails.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require D_Wamxh D_TrRuns V_AKit V_CrcLib.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Knp98 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_TrRuns OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem Cells Step Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0.
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_fast_euclid.
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mrd_hw : forall segs m a, Mem.mrd segs m a = match m a with Some b => Some b | None => seg_rom segs a end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition rebase (vals : list word) (i : nat) (w : word) (R : bvmap 5 word) : list word :=
  (firstn i (firstn NB vals) ++ [w] ++ skipn (S i) (firstn NB vals)) ++ junk_vals R.

Lemma rebase_base_length : forall (vals : list word) i (w : word), (NB <= length vals)%nat -> (i < NB)%nat ->
  length (firstn i (firstn NB vals) ++ [w] ++ skipn (S i) (firstn NB vals)) = NB.
Proof.
  intros vals i w HL Hi. unfold NB in *. rewrite !length_app, length_firstn, length_skipn, !length_firstn. cbn [length]. lia.
Qed.

Lemma rebase_length : forall (vals : list word) i (w : word) R, (NB <= length vals)%nat -> (i < NB)%nat -> length (rebase vals i w R) = 70%nat.
Proof.
  intros vals i w R HL Hi. unfold rebase. rewrite length_app, junk_vals_length, rebase_base_length by assumption. reflexivity.
Qed.

Lemma rebase_lt : forall (vals : list word) i (w : word) R j, (NB <= length vals)%nat -> (i < NB)%nat -> (j < NB)%nat -> j <> i ->
  vals_ev (rebase vals i w R) j = vals_ev vals j.
Proof.
  intros vals i w R j HL Hi Hj Hne. unfold rebase, vals_ev. 
  rewrite (app_nth1 _ (junk_vals R)) by (rewrite rebase_base_length by assumption; exact Hj).
  unfold NB in *.
  destruct (Nat.lt_ge_cases j i) as [L1|L1].
  - rewrite app_nth1 by (rewrite !length_firstn; lia). rewrite !nth_firstn.
    apply Nat.ltb_lt in L1. rewrite L1. apply Nat.ltb_lt in Hj. rewrite Hj. reflexivity.
  - rewrite app_nth2 by (rewrite !length_firstn; lia). rewrite !length_firstn.
    replace (Nat.min i (Nat.min 38 (length vals))) with i by lia.
    cbn [app]. destruct (j - i)%nat as [|d] eqn:Ed; [lia|].
    cbn [nth]. rewrite nth_skipn, nth_firstn. replace (S i + d)%nat with j by lia. apply Nat.ltb_lt in Hj. rewrite Hj. reflexivity.
Qed.

Lemma rebase_at : forall (vals : list word) i (w : word) R, (NB <= length vals)%nat -> (i < NB)%nat -> vals_ev (rebase vals i w R) i = w.
Proof.
  intros vals i w R HL Hi. unfold rebase, vals_ev.
  rewrite (app_nth1 _ (junk_vals R)) by (rewrite rebase_base_length by assumption; exact Hi).
  unfold NB in *.
  rewrite app_nth2 by (rewrite !length_firstn; lia). rewrite !length_firstn.
  replace (i - Nat.min i (Nat.min 38 (length vals)))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma rebase_junk : forall (vals : list word) i (w : word) R, (NB <= length vals)%nat -> (i < NB)%nat ->
  junk_at (rebase vals i w R) R.
Proof.
  intros vals i w R HL Hi. unfold rebase. apply junk_at_app. apply rebase_base_length; assumption.
Qed.


(* [comment removed for export] *)
Lemma rdn_zone : forall (M M' : word -> option byte) (lo hi a : Z) n,
  (forall x : word, (lo <= bv_unsigned x < hi)%Z -> M' x = M x) ->
  (lo <= a)%Z -> (a + Z.of_nat n <= hi)%Z -> (0 <= lo)%Z -> (hi <= 2 ^ 64)%Z ->
  rdn RSEGS M' (Z_to_bv 64 a) n = rdn RSEGS M (Z_to_bv 64 a) n.
Proof.
  intros M M' lo hi a n AG Hlo Hhi H0 H64. symmetry. apply rdn_agree. intros j Hj.
  rewrite u_small by lia. symmetry. apply AG. rewrite u_small by lia. lia.
Qed.

Section P0.
  Context {Clg : Ceiling} {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="AI Clg"] Lemma no_seg_above : forall x : word, (0x63000 <= bv_unsigned x)%Z -> find_segment RSEGS (bv_unsigned x) 1 = None.
  Proof. intros x Hx. apply (as_find_segment_above (L:=LayoutP0)). cbn [al_image_hi LayoutP0]. exact Hx. Qed.

  (* [comment removed for export] *)
  Lemma stk_ok_of_win : forall vals ebs M kn iw (sp : word) K,
    know_ok RSEGS (Env (vals_ev vals) ebs) M kn ->
    nth_error kn iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608) ->
    (bv_unsigned (vals_ev vals 0) - 8388608 <= bv_unsigned sp - K)%Z -> (bv_unsigned sp <= bv_unsigned (vals_ev vals 0))%Z -> (0 <= K)%Z ->
    stk_ok RSEGS M sp K.
  Proof.
    intros vals ebs M kn iw sp K HK Hn H1 H2 HK0 a n Ha Hn2.
    pose proof (u64_range (vals_ev vals 0)) as H0. pose proof (u64_range a) as Hau.
    pose proof (kwr_store_ok RSEGS _ M kn iw (EVar 0) (-8388608) 8388608 (bv_unsigned a - bv_unsigned (vals_ev vals 0)) n HK Hn
                  ltac:(lia) ltac:(lia)) as ST.
    unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST.
    replace (bv_unsigned (vals_ev vals 0) + (bv_unsigned a - bv_unsigned (vals_ev vals 0)))%Z with (bv_unsigned a) in ST by lia.
    rewrite Z_to_bv_bv_unsigned in ST. exact ST.
  Qed.

  (* [comment removed for export] *)
  #[using="AI Clg"] Lemma stk_of_win : forall vals ebs M kn iw lo hi,
    know_ok RSEGS (Env (vals_ev vals) ebs) M kn ->
    nth_error kn iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608) ->
    (bv_unsigned (vals_ev vals 0) - 8388608 <= lo)%Z -> (lo <= hi)%Z -> (hi <= bv_unsigned (vals_ev vals 0))%Z -> (0x63000 <= lo)%Z ->
    Frame.stk RSEGS M lo hi.
  Proof.
    intros vals ebs M kn iw lo hi HK Hn H1 H2 H3 H4.
    pose proof (u64_range (vals_ev vals 0)) as H0.
    split; [lia|]. split; [lia|]. intros a Ha.
    pose proof (kwr_store_ok RSEGS _ M kn iw (EVar 0) (-8388608) 8388608 (a - bv_unsigned (vals_ev vals 0)) 1 HK Hn
                  ltac:(lia) ltac:(cbn; lia)) as ST.
    unfold adenot, v_addi in ST. cbn [a_base a_off edenot ev] in ST.
    replace (bv_unsigned (vals_ev vals 0) + (a - bv_unsigned (vals_ev vals 0)))%Z with a in ST by lia.
    destruct (store_ok_some_vis RSEGS M 1 (Z_to_bv 64 a) ST 0 ltac:(lia)) as [X|[sg X]];
      rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in X.
    - unfold Mem.wa. destruct (M (Z_to_bv 64 a)) as [b|] eqn:EM; [|congruence]. split.
      + unfold wview. rewrite EM. discriminate.
      + exists b. rewrite mrd_hw, EM. reflexivity.
    - exfalso. rewrite no_seg_above in X; [discriminate|]. rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma bytes_at_of_mem : forall M (a : Z) bs,
    (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
    (forall i, (i < length bs)%nat -> match M (Z_to_bv 64 (a + Z.of_nat i)) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat i)) end
                                       = nth_error bs i) ->
    Mem.bytes_at RSEGS M a bs.
  Proof. intros M a bs H0 H1 H. split; [lia|]. split; [lia|]. intros i Hi. unfold Mem.wa. rewrite mrd_hw. apply H. exact Hi. Qed.

  (* [comment removed for export] *)
  Definition ov_bytes (M : word -> option byte) (a : Z) (rom : list byte) : list byte :=
    map (fun i => match M (Z_to_bv 64 (a + Z.of_nat i)) with Some b => b | None => nth i rom (Z_to_bv 8 0) end) (seq 0 (length rom)).

  Lemma ov_bytes_length : forall M a rom, length (ov_bytes M a rom) = length rom.
  Proof. intros. unfold ov_bytes. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma bytes_at_ov : forall M a rom,
    (0 <= a)%Z -> (a + Z.of_nat (length rom) <= 2 ^ 64)%Z ->
    (forall i, (i < length rom)%nat -> seg_rom RSEGS (Z_to_bv 64 (a + Z.of_nat i)) = Some (nth i rom (Z_to_bv 8 0))) ->
    Mem.bytes_at RSEGS M a (ov_bytes M a rom).
  Proof.
    intros M a rom H0 H1 ROM. apply bytes_at_of_mem; rewrite ?ov_bytes_length; [lia| lia|].
    intros i Hi. unfold ov_bytes. rewrite nth_error_map, (nth_error_nth' (seq 0 (length rom)) 0%nat) by (rewrite length_seq; lia).
    rewrite seq_nth by lia. cbn [option_map Nat.add].
    destruct (M (Z_to_bv 64 (a + Z.of_nat i))) as [b|]; [reflexivity|]. apply ROM. exact Hi.
  Qed.

  (* [comment removed for export] *)
  Lemma rom_errno : forall i, (i < 4)%nat -> seg_rom RSEGS (Z_to_bv 64 (0x420b4 + Z.of_nat i)) = Some (nth i (repeat (Z_to_bv 8 0) 4) (Z_to_bv 8 0)).
  Proof. intros i Hi. destruct i as [|[|[|[|i]]]]; [vm_compute; reflexivity .. | lia]. Qed.
  Lemma rom_bss16 : forall i, (i < 16)%nat -> seg_rom RSEGS (Z_to_bv 64 (0x41830 + Z.of_nat i)) = Some (nth i (repeat (Z_to_bv 8 0) 16) (Z_to_bv 8 0)).
  Proof. intros i Hi. destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]; [vm_compute; reflexivity .. | lia]. Qed.

  Lemma wr_at_data : forall M (a : Z) n, (0x31000 <= a)%Z -> (a + n <= 0x63000)%Z -> Mem.wr_at RSEGS M a n.
  Proof.
    intros M a n H0 H1. split; [lia|]. split; [lia|]. intros i Hi.
    pose proof (kwr_data_ok (Env (vals_ev []) (blobs_ev [])) M) as KW. cbn [kentry_ok kwr_data] in KW. destruct KW as [_ ST].
    specialize (ST (a + i - 0x31000)%Z 1%nat ltac:(lia) ltac:(cbn; lia)).
    unfold estart in ST. cbn [a_base a_off edenot] in ST. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in ST.
    replace (0 + 0x31000 + (a + i - 0x31000))%Z with (a + i)%Z in ST by lia.
    cbn [store_ok] in ST. unfold Mem.wa. destruct (wview RSEGS M (Z_to_bv 64 (a + i))); [discriminate| discriminate].
  Qed.

  Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> Mem.le8 (le_bytes_to_word bs) = bs.
  Proof.
    intros bs Hl. unfold Mem.le8, word_to_le_bytes, le_bytes_to_word.
    pose proof (bytes_le_to_Z_nonneg bs) as H0. pose proof (bytes_le_to_Z_bound bs) as H1. rewrite Hl in H1.
    change (256 ^ Z.of_nat 8)%Z with 18446744073709551616%Z in H1.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z.
    rewrite Z.mod_small by lia. rewrite <- Hl. apply Z_to_le_bytes_roundtrip.
  Qed.

  Lemma rw_errno_any : forall M, exists e, Step.rw_cells RSEGS M 0x420b4 [Cells.C4 e].
  Proof.
    intros M. exists (le_bytes_to_word (ov_bytes M 0x420b4 (repeat (Z_to_bv 8 0) 4))). split.
    - split; [mem_side|]. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
      rewrite le4_of_bytes by (rewrite ov_bytes_length; reflexivity).
      apply bytes_at_ov; [lia| cbn; lia| apply rom_errno].
    - cbn [Cells.cells_size Cells.csize]. apply wr_at_data; lia.
  Qed.

  Lemma rw_bss_any : forall M, exists v1 v2, Step.rw_cells RSEGS M 0x41830 [Cells.C8 v1; Cells.C8 v2].
  Proof.
    intros M.
    set (bs := ov_bytes M 0x41830 (repeat (Z_to_bv 8 0) 16)).
    assert (HL : length bs = 16%nat) by (subst bs; rewrite ov_bytes_length; reflexivity).
    exists (le_bytes_to_word (firstn 8 bs)), (le_bytes_to_word (skipn 8 bs)). split.
    - split; [mem_side|]. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r.
      rewrite !le8_of_bytes by (rewrite ?length_firstn, ?length_skipn, HL; reflexivity).
      rewrite firstn_skipn. subst bs. apply bytes_at_ov; [lia| cbn; lia| apply rom_bss16].
    - cbn [Cells.cells_size Cells.csize]. apply wr_at_data; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_of_rdn : forall M n (a : Z) bs,
    rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> (0 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z ->
    Mem.bytes_at RSEGS M a bs.
  Proof.
    intros M n. induction n as [|n IH]; intros a bs Hr H0 H1.
    - cbn [rdn] in Hr. injection Hr as <-. apply Mem.bytes_at_nil. lia.
    - cbn [rdn] in Hr.
      destruct (match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b0|] eqn:E0; [|discriminate].
      replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) in Hr
        by (apply bv_eq; rewrite w_add_1, !Z_to_bv_unsigned, !bv_wrap64_mod; symmetry; apply Zplus_mod_idemp_l).
      destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [rest|] eqn:Er; [|discriminate]. injection Hr as <-.
      change (b0 :: rest) with ([b0] ++ rest). apply (proj2 (Mem.bytes_at_app RSEGS M a [b0] rest)). split.
      + split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i as [|i]; [|cbn in Hi; lia].
        unfold Mem.wa. rewrite mrd_hw, Z.add_0_r. exact E0.
      + cbn [length Z.of_nat Pos.of_succ_nat]. replace (a + 1)%Z with (a + 1)%Z by lia. apply IH; [exact Er| lia| lia].
  Qed.

  Lemma rw_guard : forall M g,
    rdn RSEGS M (Z_to_bv 64 0x623c8) 8 = Some (word_to_le_bytes 8 g) ->
    Step.rw_cells RSEGS M 0x623c8 [Cells.C8 g].
  Proof.
    intros M g Hr. split.
    - split; [mem_side|]. cbn [Cells.cells_bytes Cells.cbytes]. rewrite app_nil_r. unfold Mem.le8.
      apply (bytes_at_of_rdn M 8); [exact Hr| lia| lia].
    - cbn [Cells.cells_size Cells.csize]. apply wr_at_data; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bytes_at_block : forall M (p : Z) (bs : list byte),
    (0 <= p)%Z -> (p + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
    (forall i, (0 <= i < Z.of_nat (length bs))%Z -> M (Z_to_bv 64 (p + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
    Mem.bytes_at RSEGS M p bs.
  Proof.
    intros M p bs H0 H1 BY. apply bytes_at_of_mem; [lia| lia|]. intros i Hi.
    rewrite (BY (Z.of_nat i)) by lia. rewrite Nat2Z.id. symmetry. apply nth_error_nth'. exact Hi.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition bss16 (a : Z) : Prop := (0x41830 <= a < 0x41830 + 16)%Z.

  (* [comment removed for export] *)
  Definition lzone (x : word) : Prop :=
    (0x10000 <= bv_unsigned x < 0x41830)%Z \/ (0x41840 <= bv_unsigned x < 0x420b4)%Z
    \/ (0x420b8 <= bv_unsigned x < 0x62458)%Z \/ (0x62804 <= bv_unsigned x < 0x63000)%Z.

  Lemma lzone_ccall : forall A A' M M' md md' (sp : Z),
    ainv A M md -> ainv A' M' md' ->
    cframe LayoutP0 (owned A) (owned A') sp LIBW bss16 nowhere M M' ->
    (0x63000 + LIBW <= sp)%Z ->
    forall x : word, lzone x -> M' x = M x.
  Proof.
    (intros A A' M M' md md' sp AI0 AI1; (first [ intro dR_3; dand3 dR_3 as C1 C2 C3 | intros (C1 & C2 & C3) ]); intros Hsp x Hx). pose proof (u64_range x) as Hxr.
    unfold lzone in Hx.
    rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (C1 (bv_unsigned x)).
    - exact Hxr.
    - intros Ho. pose proof (owned_azone A M md _ AI0 Ho) as Z0. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in Z0. lia.
    - right. unfold in_image. cbn [al_image_lo al_image_hi LayoutP0]. lia.
    - unfold LIBW in *. lia.
    - unfold al_errno. cbn [al_tp LayoutP0]. rewrite u_small by lia. lia.
    - unfold bss16. lia.
  Qed.

  Lemma knL_lib_incl : kn_incl knL (kn_keep2 knL RS_lib VICT ++ [kwr_data]) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma knL_pf_incl : kn_incl knL (kn_keep2 knL RS_pf [] ++ [kwr_data]) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma knL_lib_kimg : kimg_within (kn_keep knL RS_lib) 0x10000 0x63000 = true.
  Proof. vm_compute. reflexivity. Qed.
  (* [comment removed for export] *)
  Definition knL_iw : nat := Eval vm_compute in match kindex (is_kwr_cov (EVar 0) (-8388608) 8388608) knL 0 with Some i => i | None => 0%nat end.
  Lemma knL_win : nth_error knL knL_iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608). Proof. vm_compute. reflexivity. Qed.
  Definition knL_dwi : nat := Eval vm_compute in match kindex (is_kwr_cov (ELit 0) 0x31000 0x32000) knL 0 with Some i => i | None => 0%nat end.   (* [comment removed for export] *)

  Lemma RS_lib_flat : forall vals ebs,
    (0x7fff80000000 <= bv_unsigned (vals_ev vals 0))%Z ->
    Forall (fun r : frange => match r with (ub, uk, un) => flat (Env (vals_ev vals) ebs) (SA ub uk) un end) RS_lib.
  Proof.
    intros vals ebs H0. pose proof (u64_range (vals_ev vals 0)).
    unfold RS_lib, LIBW, ERRNO_CELL, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK.
    repeat constructor; unfold estart; cbn [a_base a_off edenot ev]; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; try lia.
  Qed.

  Lemma RS_pf_flat : forall vals ebs,
    (0x7fff80000000 <= bv_unsigned (vals_ev vals 0))%Z ->
    Forall (fun r : frange => match r with (ub, uk, un) => flat (Env (vals_ev vals) ebs) (SA ub uk) un end) RS_pf.
  Proof.
    intros vals ebs H0. pose proof (u64_range (vals_ev vals 0)).
    unfold RS_pf.
    repeat constructor; unfold estart; cbn [a_base a_off edenot ev]; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma know_knL_lib : forall vals ebs A A' M M' md md',
    know_ok RSEGS (Env (vals_ev vals) ebs) M knL ->
    (0x7fff80000000 <= bv_unsigned (vals_ev vals 0))%Z ->
    ainv A M md -> ainv A' M' md' ->
    cframe LayoutP0 (owned A) (owned A') (bv_unsigned (vals_ev vals 0) - 208) LIBW bss16 nowhere M M' ->
    (alloc_ceiling + 8388608 <= bv_unsigned (vals_ev vals 0))%Z -> (bv_unsigned (vals_ev vals 0) <= 0x800000000000)%Z ->   (* [comment removed for export] *)
    know_ok RSEGS (Env (vals_ev vals) ebs) M' knL.
  Proof.
    intros vals ebs A A' M M' md md' HK H0 AI0 AI1 CF Hce Hsphi. (first [ pose proof (CF) as dR_1; dand3 dR_1 as C1 C2 C3 | pose proof CF as (C1 & C2 & C3) ]).
    pose proof (u64_range (vals_ev vals 0)) as Hsp. pose proof alloc_ceiling_val as CV.
    apply (know_ok_incl RSEGS _ M' knL _ knL_lib_incl).
    apply know_ok_app; [| constructor; [apply kwr_data_ok | constructor]].
    apply (know_ok_keep2_vis RSEGS _ M M' knL RS_lib VICT HK (RS_lib_flat vals ebs H0)).
    - intros x OUT VIS. pose proof (u64_range x) as Hx.
      assert (A1 := OUT (EVar 0) (-208 - LIBW)%Z LIBW ltac:(mem_side)).
      assert (A2 := OUT (ELit 0) ERRNO_CELL 4%Z ltac:(mem_side)).
      assert (A3 := OUT (ELit 0) 0x41830%Z 16%Z ltac:(mem_side)).
      assert (A4 := OUT (ELit 0) STATICS_LO (STATICS_HI - STATICS_LO)%Z ltac:(mem_side)).
      assert (A5 := OUT (ELit 0) HEAP_LO (HEAP_HI - HEAP_LO)%Z ltac:(mem_side)).
      assert (A6 := OUT (ELit 0) LOW_LO (LOW_HI - LOW_LO)%Z ltac:(mem_side)).
      assert (A7 := OUT (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(mem_side)).
      unfold estart in A1, A2, A3, A4, A5, A6, A7. cbn [a_base a_off edenot ev] in A1, A2, A3, A4, A5, A6, A7.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in A2, A3, A4, A5, A6.
      unfold ERRNO_CELL, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, LIBW, CSLACK in *.
      rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (C1 (bv_unsigned x)).
      + exact Hx.
      + intros Ho. pose proof (owned_azone A M md _ AI0 Ho) as Z0. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in Z0. lia.
      + destruct VIS as [V|[[sg V]|V]].
        * left. rewrite Z_to_bv_bv_unsigned. exact V.
        * right. destruct (Z_lt_le_dec (bv_unsigned x) 0x10000) as [L1|L1]; [| destruct (Z_lt_le_dec (bv_unsigned x) 0x63000) as [L2|L2]].
          -- exfalso. rewrite (as_find_segment_outside (L:=LayoutP0)) in V; [discriminate|]. unfold in_image. cbn [al_image_lo al_image_hi LayoutP0]. lia.
          -- unfold in_image. cbn [al_image_lo al_image_hi LayoutP0]. lia.
          -- exfalso. rewrite (as_find_segment_outside (L:=LayoutP0)) in V; [discriminate|]. unfold in_image. cbn [al_image_lo al_image_hi LayoutP0]. lia.
        * right. pose proof (kimg_within_cov _ _ _ _ knL_lib_kimg V) as W. unfold in_image. cbn [al_image_lo al_image_hi LayoutP0]. lia.
      + lia.
      + unfold al_errno. cbn [al_tp LayoutP0]. rewrite u_small by lia. lia.
      + unfold bss16. lia.
    - intros x OUT Hm. pose proof (u64_range x) as Hx.
      assert (A1 := OUT (ELit 0) 0%Z HEAP_HI ltac:(mem_side)).
      assert (A2 := OUT (EVar 0) (-8388608 - CSLACK)%Z CSLACK ltac:(mem_side)).
      unfold estart in A1, A2. cbn [a_base a_off edenot ev] in A1, A2. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in A1. unfold HEAP_HI, LIBW, CSLACK in *.
      destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (vals_ev vals 0) - 208 - 16384)) as [W|W];
        [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned (vals_ev vals 0) - 208)) as [W2|W2]].
      + rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hm |- *.
        assert (NO : ~ owned A (bv_unsigned x)).
        { intros Ho. pose proof (owned_azone A M md _ AI0 Ho) as Z0. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in Z0. lia. }
        rewrite (proj1 (C1 (bv_unsigned x) Hx NO (or_introl Hm) ltac:(lia) ltac:(unfold al_errno; cbn [al_tp LayoutP0]; rewrite u_small by lia; lia) ltac:(unfold bss16; lia))).
        exact Hm.
      + pose proof (C2 (bv_unsigned x - (bv_unsigned (vals_ev vals 0) - 208 - 16384))%Z ltac:(lia)) as MP.
        replace (bv_unsigned (vals_ev vals 0) - 208 - 16384 + (bv_unsigned x - (bv_unsigned (vals_ev vals 0) - 208 - 16384)))%Z
          with (bv_unsigned x) in MP by lia. rewrite Z_to_bv_bv_unsigned in MP. exact MP.
      + rewrite <- (Z_to_bv_bv_unsigned 64 x) in Hm |- *.
        assert (NO : ~ owned A (bv_unsigned x)).
        { intros Ho. pose proof (owned_azone A M md _ AI0 Ho) as Z0. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in Z0. lia. }
        rewrite (proj1 (C1 (bv_unsigned x) Hx NO (or_introl Hm) ltac:(lia) ltac:(unfold al_errno; cbn [al_tp LayoutP0]; rewrite u_small by lia; lia) ltac:(unfold bss16; lia))).
        exact Hm.
  Qed.

  (* [comment removed for export] *)
  Lemma know_knL_pf : forall vals ebs M M',
    know_ok RSEGS (Env (vals_ev vals) ebs) M knL ->
    (0x7fff80000000 <= bv_unsigned (vals_ev vals 0))%Z ->
    (forall x : word, outside_all (Env (vals_ev vals) ebs) RS_pf x -> M' x = M x) ->
    mem_grows M M' ->
    know_ok RSEGS (Env (vals_ev vals) ebs) M' knL.
  Proof.
    intros vals ebs M M' HK H0 OUT G.
    apply (know_ok_incl RSEGS _ M' knL _ knL_pf_incl).
    apply know_ok_app; [| constructor; [apply kwr_data_ok | constructor]].
    apply (know_ok_keep2 RSEGS _ M M' knL RS_pf [] HK (RS_pf_flat vals ebs H0) OUT).
    intros x _ Hm. apply G in Hm. exact Hm.
  Qed.

  (* [comment removed for export] *)
  Lemma knL_byte_incl : kn_incl knL (kn_keep2 knL [(ELit 0, 0x41804%Z, 1%Z)] [] ++ [kwr_data]) = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma know_knL_byte : forall vals ebs M b,
    know_ok RSEGS (Env (vals_ev vals) ebs) M knL ->
    know_ok RSEGS (Env (vals_ev vals) ebs) (wbytes M (Z_to_bv 64 0x41804) [b]) knL.
  Proof.
    intros vals ebs M b HK.
    apply (know_ok_incl RSEGS _ _ knL _ knL_byte_incl).
    apply know_ok_app; [| constructor; [apply kwr_data_ok | constructor]].
    apply (know_ok_keep2 RSEGS _ M _ knL [(ELit 0, 0x41804%Z, 1%Z)] [] HK).
    - repeat constructor; unfold estart; cbn [a_base a_off edenot ev]; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; try lia.
    - intros x OUT. pose proof (u64_range x) as Hx.
      assert (A1 := OUT (ELit 0) 0x41804%Z 1%Z ltac:(left; reflexivity)).
      unfold estart in A1. cbn [a_base a_off edenot ev] in A1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in A1.
      apply MemSplit.wbytes_outside; cbn [length]; rewrite u_small by lia; lia.
    - intros x _ Hm. apply (wbytes_grows [b] M (Z_to_bv 64 0x41804)). exact Hm.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma drv_client : forall (sp0 : word) A M M' md,
    (0x7fff80000000 <= bv_unsigned sp0)%Z ->
    (alloc_ceiling + 8388608 <= bv_unsigned sp0)%Z ->   (* [comment removed for export] *)
    ainv A M md -> Mem.mem_inv RSEGS M ->
    (forall x : word, ~ (bv_unsigned sp0 - 8388608 <= bv_unsigned x < bv_unsigned sp0)%Z ->
                      ~ (0x31458 <= bv_unsigned x < 0x623c8)%Z -> ~ (0x62804 <= bv_unsigned x < 0x63000)%Z -> M' x = M x) ->
    mem_grows M M' ->
    ainv A M' md /\ Mem.mem_inv RSEGS M'.
  Proof.
    intros sp0 A M M' md SPlo Hce AI0 MI OUT G. pose proof (u64_range sp0). pose proof alloc_ceiling_val as CV.
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    split.
    - apply (as_frame A M M' md md AI0).
      + intros a Ho. pose proof (owned_azone A M md a AI0 Ho) as ZZ. unfold azone, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI in ZZ.
        destruct (Z_lt_le_dec a 0) as [N|N]; [lia|]. destruct (Z_lt_le_dec a (2 ^ 64)) as [N2|N2].
        * apply OUT; rewrite u_small by lia; lia.
        * lia.
      + intros a Hs. cbn [al_shared LayoutP0] in Hs. unfold p0_shared in Hs. apply OUT; rewrite u_small by lia; lia.
      + intros p n i HL Hi. (first [ pose proof ((as_live_ok A M md p n AI0 HL)) as dR_2; dand7 dR_2 as _ _ _ _ _ MPp _ | destruct (as_live_ok A M md p n AI0 HL) as (_ & _ & _ & _ & _ & MPp & _) ]). apply G. apply MPp. exact Hi.
      + intros a [Ha Hni] Hm. unfold in_image in Hni. cbn [al_image_lo al_image_hi LayoutP0] in Hni.
        rewrite OUT in Hm; [exact Hm| rewrite u_small by lia; lia| rewrite u_small by lia; lia| rewrite u_small by lia; lia].
      + reflexivity.
      + exact Hh.
    - intros x v Hx. destruct (Mem.ro_addr RSEGS x) eqn:RO; [|reflexivity]. exfalso.
      pose proof (proj1 (as_ro_addr_iff (AI:=AI) x) RO) as RA. cbn [al_image_lo al_rw_lo LayoutP0] in RA.
      rewrite OUT in Hx by lia. pose proof (MI x v Hx) as RO'. rewrite RO' in RO. discriminate.
  Qed.

  Lemma rdn1_of : forall M (a : word) x, M a = Some x -> rdn RSEGS M a 1 = Some [x].
  Proof. intros M a x H. cbn [rdn]. rewrite H. reflexivity. Qed.
End P0.
End D_TrLib.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Amb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.ShapeAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Shapi1s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MmapSim.FileSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AgentLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec.Speco6o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Li6dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibWbxd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exvwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stqgu OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Exit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefMocc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Stmwg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Manqc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.AllocSim.Hoare OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u.D_MainA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Mah0u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Oobk0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Alu7n OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Tails.D_Dr084 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Wamxh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RefPl89 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_TrRuns OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_TrTail.D_TrLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutP0 DriverKit.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition knTL_iw : nat := Eval vm_compute in match kindex (is_kwr_cov (EVar 0) (-8388608) 8388608) knTL 0 with Some i => i | None => 0%nat end.
Lemma knTL_win : nth_error knTL knTL_iw = Some (KWr (SA (EVar 0) (-8388608)) 8388608). Proof. vm_compute. reflexivity. Qed.
Lemma knTL_free_incl : kn_incl knTL (kn_keep2 knTL (RS_call (-128) FREE_STACK) VICT ++ [kwr_data]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma know_knTL_free : forall E M',
  know_ok RSEGS E M' (kn_keep2 knTL (RS_call (-128) FREE_STACK) VICT) -> know_ok RSEGS E M' knTL.
Proof.
  intros E M' HK. apply (know_ok_incl RSEGS E M' knTL _ knTL_free_incl).
  apply know_ok_app; [exact HK | constructor; [apply kwr_data_ok | constructor]].
Qed.

Section Tail.
  Context {AMB : Amb} {Clg : Ceiling} {AI : AllocSpec LayoutP0} {DK : DriverKit LayoutP0 InitP0}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hvsp : valid_sp sp0.
  (* [comment removed for export] *)
  Hypothesis HCEIL : alloc_ceiling = (bv_unsigned sp0 - 8388608)%Z.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.

  (* [comment removed for export] *)
  Definition dzone (x : word) : Prop :=
    (0x10000 <= bv_unsigned x < 0x420b4)%Z \/ (0x420b8 <= bv_unsigned x < 0x62458)%Z \/ (0x62804 <= bv_unsigned x < 0x63000)%Z.

  #[using="HCEIL Hvsp"] Lemma dzone_acall : forall (O O' : Z -> Prop) vals (ebs : nat -> list byte) spk victim newb M M',
    vals_ev vals 0 = sp0 ->
    (forall a, O a -> azone a) -> (forall a, O' a -> azone a) ->
    (forall a, victim a -> azone a) -> (forall a, newb a -> azone a) ->
    frame_ok LayoutP0 O O' (bv_unsigned sp0 + spk) 8192 victim newb M M' ->
    (-8388608 + 8192 <= spk <= 0)%Z ->
    forall x : word, dzone x -> M' x = M x.
  Proof.
    intros O O' vals ebs spk victim newb M M' V0 HO HO' HV HN FR Hspk x Hx. pose proof (u64_range sp0).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. unfold sp_window_lo, sp_window_hi in *.
    destruct (frame_outside O O' (Env (vals_ev vals) ebs) spk 8192 victim newb M M' HO HO' HV HN) as [OUT _];
      cbn [ev]; rewrite ?V0; [exact FR| lia| lia| lia| lia| lia|].
    apply OUT. intros ub uk un Hin. unfold RS_call, ERRNO_CELL, STATICS_LO, STATICS_HI, HEAP_LO, HEAP_HI, LOW_LO, LOW_HI, CSLACK in Hin.
    unfold estart. cbn [a_base a_off].
    unfold dzone in Hx.
    repeat (destruct Hin as [Hin|Hin];
      [injection Hin as <- <- <-; cbn [edenot ev]; rewrite ?V0; try change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia|]).
    destruct Hin.
  Qed.

  Lemma file_clean_zone : forall M M' f wp rp,
    (forall x : word, dzone x -> M' x = M x) -> (0x31458 <= f)%Z -> (f + 232 <= 0x420b4)%Z ->
    file_clean M f wp rp -> file_clean M' f wp rp.
  Proof.
    (intros M M' f wp rp AG H1 H2; (first [ intro dR_4; dand5 dR_4 as A B C D E | intros (A & B & C & D & E) ])). unfold file_clean.
    rewrite !(rdn_zone M M' 0x10000 0x420b4) by (try (intros x Hx; apply AG; unfold dzone; lia); lia).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.

  Lemma stdout_pending_zone : forall M M' wb wp bufp bufsz rp1 can pending,
    (forall x : word, dzone x -> M' x = M x) -> (0x62804 <= wb)%Z ->
    stdout_pending M wb wp bufp bufsz rp1 can pending -> stdout_pending M' wb wp bufp bufsz rp1 can pending.
  Proof.
    intros M M' wb wp bufp bufsz rp1 can pending AG Hwb [L1 L2 L3 L4 L5 L6 L7 L8 L9 RG LEN MX BY SSP].
    split; try assumption;
      try (rewrite (rdn_zone M M' 0x10000 0x420b4) by (try (intros x Hx; apply AG; unfold dzone; lia); lia); assumption).
    - rewrite (rdn_zone M M' 0x62804 0x63000) by (try (intros x Hx; apply AG; unfold dzone; lia); lia). exact BY.
    - destruct SSP as [S1 S2]. split.
      + rewrite (rdn_zone M M' 0x10000 0x420b4) by (try (intros x Hx; apply AG; unfold dzone; lia); lia). exact S1.
      + rewrite (rdn_zone M M' 0x420b8 0x62458) by (try (intros x Hx; apply AG; unfold dzone; lia); lia). exact S2.
  Qed.

  (* [comment removed for export] *)
  Lemma atexit_st_zone : forall M M' reg,
    (forall x : word, dzone x -> M' x = M x) -> atexit_st M reg -> atexit_st M' reg.
  Proof.
    intros M M' reg AG AT. destruct reg; unfold atexit_st in AT |- *;
      rewrite !(rdn_zone M M' 0x420b8 0x62458) by (try (intros x Hx; apply AG; unfold dzone; lia); lia);
      [rewrite (rdn_zone M M' 0x10000 0x420b4) by (try (intros x Hx; apply AG; unfold dzone; lia); lia)|]; exact AT.
  Qed.

  (* [comment removed for export] *)
  #[using="Hvsp"] Lemma sr_cc_ok : forall vals R,
    length vals = 70%nat -> vals_ev vals 0 = sp0 -> junk_at vals R ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x42158 ->
    getr R 8 = vals_ev vals 24 -> getr R 9 = vals_ev vals 20 ->
    regs_ok (ENV a0s path rdraw vals) sr_cc R.
  Proof.
    intros vals R HL V0 HJ P2 P3 P4 P8 P9.
    pose proof (proj1 Hvsp) as SPlo. unfold sp_window_lo in SPlo. pose proof (u64_range sp0).
    apply regs_ok_by_index. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth sr_cc all_regs];
      try (lazymatch goal with |- _ = edenot _ (EVar ?n) =>
             change (edenot (ENV a0s path rdraw vals) (EVar n)) with (vals_ev vals n);
             first [ let i := eval vm_compute in (n - 38)%nat in
                     etransitivity; [| symmetry; exact (HJ i ltac:(lia))]; f_equal; apply bv_eq; reflexivity
                   | exact P8 | exact P9 ] end).
    - apply getr_zero.
    - rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. change (vals_ev vals 0) with (vals_ev vals 0). rewrite V0, P2. f_equal; lia.
    - exact P3.
    - exact P4.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="HCEIL Hvsp"] Theorem tail_free : forall vals R M (md : Model) A (b n0 v : Z) (wp2 rp2 : word) (pending : list byte) (areg : bool),
    base_ok sp0 a0s path envv tid vals -> regs_ok (ENV a0s path rdraw vals) srX1 R ->
    vals_ev vals 20 = Z_to_bv 64 b -> vals_ev vals 24 = Z_to_bv 64 v -> (0 <= v < 256)%Z ->
    know_ok RSEGS (ENV a0s path rdraw vals) M knTL ->
    ainv A M md -> a_live A b = Some n0 -> Mem.mem_inv RSEGS M ->
    file_clean M 0x315a8 wp2 rp2 -> atexit_st M areg ->
    ( (pending = [] /\ exists wp1 rp1, file_clean M 0x31698 wp1 rp1)
      \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
            stdout_pending M wb wp bufp bufsz rp1 can pending /\ (0x62804 <= wb)%Z
            /\ fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x22e84) M (seg_rom RSEGS)) md)
             (t_emit (W 1 pending) (t_exit (exit_code v) (m_fs md))).
  Proof.
    intros vals R M md A b n0 v wp2 rp2 pending areg HB HR V20 V24 Hv HK AI0 LIVE MI ERR AT OUT.
    (first [ pose proof (HB) as dR_1; dand5 dR_1 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    pose proof (proj1 Hvsp) as SPlo. pose proof (proj1 (proj2 Hvsp)) as SPhi. pose proof (proj2 (proj2 Hvsp)) as SPal.
    unfold sp_window_lo, sp_window_hi in *. pose proof (u64_range sp0) as Hsp.
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    assert (Hl : m_vm_lazy md = []) by (destruct (as_lazy_nil A M md AI0) as [X _]; exact X).
    assert (CH : callH vals (blobs_ev (blobs0 a0s path rdraw)) srX1 knTL b (-128) 0x17d60).
    { split; rewrite ?HL, ?V0; try reflexivity; try lia.
      - change (sr_get srX1 10) with (EVar 20). cbn [edenot ev]. exact V20.
      - exists knTL_iw. exact knTL_win. }
    apply (W_free_as vals (blobs_ev (blobs0 a0s path rdraw)) srX1 knTL R M md A b n0 (-128) 0x17d60 _ HR HK CH AI0 (or_intror LIVE) MI).
    clear HR HK. intros R1 M1 md1 A1 HR HK1 AI1 MI1 MF1 GONE1 OTHER1 _ _ FR1.   (* [comment removed for export] *)
    pose proof (know_knTL_free _ M1 HK1) as HK. clear HK1.
    assert (Hh1 : m_halted md1 = None) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [_ X]; exact X).
    assert (Hl1 : m_vm_lazy md1 = []) by (destruct (as_lazy_nil A1 M1 md1 AI1) as [X _]; exact X).
    rewrite HL in HR. change (sr_post srX1 70) with srX2_0 in HR.
    rewrite V0 in FR1.
    assert (DZ : forall x : word, dzone x -> M1 x = M x).
    { apply (dzone_acall (owned A) (owned A1) vals (blobs_ev (blobs0 a0s path rdraw)) (-128) (blk b n0) nowhere M M1 V0);
        try exact FR1; try lia.
      - intros a Ho. exact (owned_azone A M md a AI0 Ho).
      - intros a Ho. exact (owned_azone A1 M1 md1 a AI1 Ho).
      - intros a [_ Ha]. replace a with (b + (a - b))%Z by lia. eapply (live_azone A M md b n0); [exact AI0| exact LIVE| lia].
      - intros a Hn. destruct Hn. }
    set (vals1 := vals ++ junk_vals R1) in *.
    assert (HL1 : length vals1 = 102%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (AG1 : forall i, (i < 70)%nat -> vals_ev vals1 i = vals_ev vals i) by (intros i Hi; subst vals1; apply vals_ev_app_l; rewrite HL; exact Hi).
    (* [comment removed for export] *)
    run_block_gen FUEL_X STOPS_X (SCR [] [] []) 102%nat true.
    cbn [mem_denot] in EQM. subst M0.
    replace (m_fs md) with (m_fs md1).
    2:{ (first [ dand4 MF1 as _ _ FS _ | destruct MF1 as (_ & _ & FS & _) ]). unfold m_fs. rewrite FS. reflexivity. }
    apply (rz_conseq RSEGS _ (t_emit (W 1 pending) (t_exit (bv_and (Z_to_bv 64 v) (Z_to_bv 64 255)) (m_fs md1)))).
    2:{ rewrite exit_code_and_255 by exact Hv. apply t_eq_refl. }
    apply ref_exit_Z.
    pose proof (know_nth RSEGS _ _ knTL ltac:(let i := kidx knTL (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid. rewrite AG1 in Ktid by lia.
    exists (Z_to_bv 64 (bv_unsigned sp0 - 48)), (Z_to_bv 64 0x42158), (bv_unsigned (vals_ev vals 5)), wp2, rp2, areg.
    split; [|split; [exact (atexit_st_zone M M1 areg DZ AT)|split; [exact Hh1|split; [exact Hl1|]]]].
    - constructor.
      + regv HR (2 : reg). rewrite edenot_add_lit. unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite AG1 by lia. rewrite V0. f_equal; try lia.
      + regv HR (4 : reg). reflexivity.
      + regv HR (10 : reg). cbn [edenot ev ENV]. rewrite AG1 by lia. exact V24.
      + rewrite u_small by lia. lia.
      + rewrite u_small by lia. lia.
      + rewrite u_small by lia.
        pose proof (kwr_store_ok RSEGS _ _ knTL knTL_iw _ _ _ (-192) 144 HK knTL_win ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite AG1 in Hst by lia. rewrite V0 in Hst.
        replace (bv_unsigned sp0 - 48 - 144)%Z with (bv_unsigned sp0 + -192)%Z by lia. exact Hst.
      + lit_u; lia.
      + lit_u; lia.
      + lia.
      + lit_u. change (0x42158 - 168)%Z with 0x420b0%Z.
        let Htc := fresh in krd HK 0x420b0%Z 4%nat Htc; rewrite Htc; cbn [ev ENV]. rewrite AG1 by lia.
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia).
        rewrite Z_to_bv_bv_unsigned. reflexivity.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.
      + krd_solve HK.   (* [comment removed for export] *)
      + krd_solve HK.   (* [comment removed for export] *)
      + OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; krd_solve HK.
      + apply (file_clean_zone M M1); [exact DZ| lia| lia| exact ERR].
    - destruct OUT as [[-> (wp1 & rp1 & FC)] | (wb & wp & bufp & bufsz & rp1 & can & SP & Hwb & FD1)].
      + left. split; [reflexivity|]. exists wp1, rp1. apply (file_clean_zone M M1); [exact DZ| lia| lia| exact FC].
      + right. exists wb, wp, bufp, bufsz, rp1, can. split.
        * apply (stdout_pending_zone M M1); [exact DZ| exact Hwb| exact SP].
        * destruct MF1 as (FD & _). unfold m_fds. rewrite FD. exact FD1.
  Qed.

  (* [comment removed for export] *)
  #[using="HCEIL Hvsp"] Theorem tail_exit : forall vals R M (md : Model) A (b n0 v : Z) (wp2 rp2 : word) (pending : list byte) (areg : bool),
    base_ok sp0 a0s path envv tid vals -> junk_at vals R ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128) -> getr R 3 = Z_to_bv 64 0x10800 -> getr R 4 = Z_to_bv 64 0x42158 ->
    vals_ev vals 20 = Z_to_bv 64 b -> vals_ev vals 24 = Z_to_bv 64 v -> (0 <= v < 256)%Z ->
    getr R 8 = Z_to_bv 64 v -> getr R 9 = Z_to_bv 64 b ->
    know_ok RSEGS (ENV a0s path rdraw vals) M knTL ->
    ainv A M md -> a_live A b = Some n0 -> Mem.mem_inv RSEGS M ->
    file_clean M 0x315a8 wp2 rp2 -> atexit_st M areg ->
    ( (pending = [] /\ exists wp1 rp1, file_clean M 0x31698 wp1 rp1)
      \/ (exists (wb wp : Z) (bufp bufsz rp1 can : word),
            stdout_pending M wb wp bufp bufsz rp1 can pending /\ (0x62804 <= wb)%Z
            /\ fd_lookup (m_fds md) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1))) ) ->
    realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0x17d58) M (seg_rom RSEGS)) md)
             (t_emit (W 1 pending) (t_exit (exit_code v) (m_fs md))).
  Proof.
    intros vals R M md A b n0 v wp2 rp2 pending areg HB HJ P2 P3 P4 V20 V24 Hv P8 P9 HK AI0 LIVE MI ERR AT OUT.
    (first [ pose proof (HB) as dR_3; dand5 dR_3 as HL V0 V1 V2 V5 | pose proof HB as (HL & V0 & V1 & V2 & V5) ]).
    assert (Hh : m_halted md = None) by (destruct (as_lazy_nil A M md AI0) as [_ X]; exact X).
    assert (Hl : m_vm_lazy md = []) by (destruct (as_lazy_nil A M md AI0) as [X _]; exact X).
    pose proof (sr_cc_ok vals R HL V0 HJ P2 P3 P4 ltac:(rewrite V24; exact P8) ltac:(rewrite V20; exact P9)) as HR.
    clear HJ.
    run_block_gen FUEL_X STOPS_X (SCR [] [] []) 70%nat true.
    cbn [mem_denot] in EQM. subst M0.
    eapply (tail_free vals R0 M md A b n0 v wp2 rp2 pending areg); eassumption.
  Qed.
End Tail.
