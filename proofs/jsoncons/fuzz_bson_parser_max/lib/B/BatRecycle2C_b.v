(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatSecAlloc_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatCellEx_b BatImgCell_b BatSecAllocPost_b BatSecRSpec_b BatPoisonRun_b BatPoison3_b
     BatCls_b BatRecycle1_b BatRecycle2_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r3ef18_4052c_b Ba0_code_r719b0_719e8_b Ba0_code_r719f8_71a24_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_swap_remove {A : Type} (d : A) (i : nat) (l : list A) : list A :=
  map (fun j => nth (if (j =? i)%nat then (length l - 1)%nat else j) l d) (seq 0 (length l - 1)).

Lemma art_swap_remove_length : forall A (d : A) i l, length (art_swap_remove d i l) = (length l - 1)%nat.
Proof. intros. unfold art_swap_remove. rewrite length_map, length_seq. reflexivity. Qed.

Lemma art_swap_remove_nth : forall A (d : A) i l j, (j < length l - 1)%nat ->
  nth_error (art_swap_remove d i l) j = nth_error l (if (j =? i)%nat then (length l - 1)%nat else j).
Proof.
  intros A d i l j Hj. unfold art_swap_remove.
  rewrite nth_error_map, nth_error_seq. replace (j <? length l - 1)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj). cbn [option_map Nat.add].
  symmetry. apply nth_error_nth'. destruct (j =? i)%nat; lia.
Qed.

Lemma art_swap_remove_in : forall A (d : A) i l x, In x (art_swap_remove d i l) -> In x l.
Proof.
  intros A d i l x H. destruct (In_nth_error _ _ H) as (j & Hj).
  assert (Hjl : (j < length l - 1)%nat) by (rewrite <- (art_swap_remove_length A d i l); apply nth_error_Some; congruence).
  rewrite art_swap_remove_nth in Hj by exact Hjl. eapply nth_error_In. exact Hj.
Qed.

(* [comment removed for export] *)
Definition art_sec_cells (M : word -> option byte) (parr : Z) (bl : list (Z * Z)) : Prop :=
  cellA M 0x13c618 8 4096 /\ cellA M (0x13c618 + 8) 8 parr /\ cellA M (0x13c618 + 56) 8 (Z.of_nat (length bl)) /\ cellA M (0x13c618 + 616) 4 0
  /\ wrA M parr (8 * Z.of_nat (length bl))
  /\ (forall j b, nth_error bl j = Some b ->
        cellA M (parr + 8 * Z.of_nat j) 8 (fst b) /\ cellA M (fst b) 8 (fst b) /\ cellA M (fst b + 8) 8 (snd b) /\ cellA M (fst b + 24) 8 (Z.of_nat j)
        /\ wrA M (fst b) (snd b) /\ wrA M (SB + fst b / 8) (snd b / 8)).

Definition art_sec_geo (HI t ctx parr : Z) (bl : list (Z * Z)) : Prop :=
  0x696000 <= parr /\ parr + 8 * Z.of_nat (length bl) <= HI /\ Z.of_nat (length bl) < 2 ^ 20 /\ appmem parr (8 * Z.of_nat (length bl))
  /\ apart parr (8 * Z.of_nat (length bl)) t 4096 /\ apart parr (8 * Z.of_nat (length bl)) ctx 4096
  /\ (forall b, In b bl -> fst b mod 4096 = 0 /\ snd b mod 4096 = 0 /\ 4096 < snd b /\ 0x696000 <= fst b /\ fst b + snd b <= HI /\ appmem (fst b) (snd b)
                           /\ apart (fst b) (snd b) parr (8 * Z.of_nat (length bl)) /\ apart (fst b) (snd b) t 4096 /\ apart (fst b) (snd b) ctx 4096)
  /\ (forall i j b b', nth_error bl i = Some b -> nth_error bl j = Some b' -> i <> j -> apart (fst b) (snd b) (fst b') (snd b')).

Definition art_flush_events (mb ms : Z) : list aev :=
  if art_flush_beg mb <? art_flush_end mb ms then [AMadvise (art_flush_beg mb) (art_flush_end mb ms - art_flush_beg mb)] else [].

(* [comment removed for export] *)
Definition art_secd_fp (sp t parr idx last mb ms : Z) : list (Z * Z) :=
  [ (sp - 96, 96); (0x13c618 + 56, 568); (0x13c888 + 16, 16); (parr + 8 * idx, 8); (last + 24, 8); (t + 2800 + 88, 16); (SB + mb / 8, ms / 8); (mb, ms) ].

(* [comment removed for export] *)
Lemma art_layout_tr : forall W M M', art_agree W M M' ->
  art_gap W 0x1366c8 0x3000 -> art_gap W 0x13d438 (0x141480 - 0x13d438) -> art_gap W 0x1d1768 256 -> art_layout M -> art_layout M'.
Proof.
  intros W M M' A G1 G2 G3 L. unfold art_layout in *.
  zsplit;
  match goal with |- cell _ _ ?c ?m _ =>
    first [ apply (art_cell_tr W M M' c m _ A); [eapply art_gap_sub; [exact G1|cbn; lia|cbn; lia] | lia | cbn; lia | tauto]
          | apply (art_cell_tr W M M' c m _ A); [eapply art_gap_sub; [exact G2|cbn; lia|cbn; lia] | lia | cbn; lia | tauto]
          | apply (art_cell_tr W M M' c m _ A); [eapply art_gap_sub; [exact G3|cbn; lia|cbn; lia] | lia | cbn; lia | tauto] ] end.
Qed.

Lemma art_tsd_tr : forall W M M' tp key tsd ctx t, art_agree W M M' ->
  art_gap W 0x13f4a0 8 -> art_gap W (tp - 88) 8 -> art_gap W (tsd + 8 * key) 8 -> art_gap W (ctx + 152) 8 ->
  art_tsd M tp key tsd ctx t -> art_tsd M' tp key tsd ctx t.
Proof.
  intros W M M' tp key tsd ctx t A G1 G2 G3 G4 T. destruct T as (C1 & C2 & C3 & C4 & C5 & R). unfold art_tsd.
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia] | lia | cbn; lia | exact C1]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G1|lia|cbn; lia] | lia | cbn; lia | exact C2]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G2 | lia | cbn; lia | exact C3]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G3 | lia | cbn; lia | exact C4]|].
  split; [apply (art_cell_tr W M M' _ _ _ A); [exact G4 | lia | cbn; lia | exact C5]|].
  exact R.
Qed.

Lemma art_at_ecall_madvise : art_at_ecall ASEGS (0x8bcc4 : word).
Proof. exists W_8b8ac. split; [exact F_8b8ac | exact E_8b8ac]. Qed.
Lemma art_at_ecall_munmap : art_at_ecall ASEGS (0x8bc8c : word).
Proof. exists W_8b874. split; [exact F_8b874 | exact E_8b874]. Qed.

(* [comment removed for export] *)
Definition art_secd_fin_mem (Md : word -> option byte) (sp : Z) (raw : word) (t h ms x8 x9 x18 c88 c96 : Z) : word -> option byte :=
  Wn 4 (art_unmap (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) h ms) (sp - 36) 18446744072277895850.

(* [comment removed for export] *)
Lemma art_secd_fin_facts : forall (Md : word -> option byte) sp raw t h ms x8 x9 x18 c88 c96,
  96 <= sp -> sp < 2 ^ 64 -> 0 <= t -> t + 4096 < 2 ^ 64 -> 0 <= h -> 0 <= ms -> h + ms <= sp - 96 ->
  let M' := art_secd_fin_mem Md sp raw t h ms x8 x9 x18 c88 c96 in
  art_agree [(sp - 64, 64); (t + 2800 + 88, 16); (h, ms)] Md M'
  /\ (forall x : word, h <= U x < h + ms -> M' x = None)
  /\ (forall a n, 0 <= a -> a + n < 2 ^ 64 -> apart h ms a n -> wrA Md a n -> wrA M' a n).
Proof.
  intros Md sp raw t h ms x8 x9 x18 c88 c96 Hsp Hsp' Ht Ht' Hh Hms Hhs. cbv zeta. unfold art_secd_fin_mem, art_secd_d_mem. split; [|split].
  - eapply art_agree_sub; [zagree|]. zsub.
  - intros x Hx. rewrite Wn_outside by (cbn; lia). apply art_unmap_in. exact Hx.
  - intros a n Ha Hn A Wa. apply wr_Wn. apply wr_unmap_other; [exact Ha|exact Hn|exact A|]. repeat apply wr_Wn. exact Wa.
Qed.

(* [comment removed for export] *)
Lemma art_poisoned_facts : forall (M : word -> option byte) sp ra s0 s1 s2 s3 s4 s5 a k, 64 <= sp -> sp < 2 ^ 64 -> 0 <= a -> 0 <= k -> a + k < 2 ^ 64 ->
  let X := Wf (art_poison_frame M sp ra s0 s1 s2 s3 s4 s5) a (Z.to_nat k) 0 in
  mem_grows M X /\ art_agree [(sp - 64, 64); (a, k)] M X /\ (forall x : word, a <= U x < a + k -> X x = Some (Z_to_bv 8 0)).
Proof.
  intros M sp ra s0 s1 s2 s3 s4 s5 a k Hsp Hsp' Ha Hk Hak. cbv zeta. unfold art_poison_frame. split; [zgrows|]. split.
  - eapply art_agree_sub; [zagree|]. intros z Hz H. cbn [art_out app fst snd] in H |- *. rewrite ?Z2Nat.id in * by lia. repeat split; lia.
  - intros x Hx. replace x with (Z_to_bv 64 (a + (U x - a)) : word) by (replace (a + (U x - a)) with (U x) by lia; apply Z_to_bv_bv_unsigned).
    apply Wf_inside; [lia|rewrite Z2Nat.id by lia; lia|rewrite Z2Nat.id by lia; lia].
Qed.

Ltac inl := cbn [In]; repeat (first [left; reflexivity | right]).

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_secd_tail_aruns : forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (Md rom : word -> option byte) (raw : word)
    (sp HI tp key tsd ctx t h ms x8 x9 x18 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 32) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 ms -> ret_ok raw ->
  kHighMemBeg <= HI -> HI <= sp - 96 -> sp < 2 ^ 47 -> wrA Md (sp - 64) 64 ->
  0x696000 <= h -> h + ms <= HI -> 4096 < ms -> 0 <= x8 < 2 ^ 64 -> 0 <= x9 < 2 ^ 64 -> 0 <= x18 < 2 ^ 64 ->
  art_tsd Md tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> tp + 8 <= 0x696000 -> tsd + 1024 <= 0x696000 -> ctx + 4096 <= HI ->
  apart h ms t 4096 -> wrA Md t 4096 ->
  cellA Md (sp - 8) 8 (U raw) -> cellA Md (sp - 16) 8 x8 -> cellA Md (sp - 24) 8 x9 -> cellA Md (sp - 32) 8 x18 ->
  cellA Md h 8 h -> cellA Md (h + 8) 8 ms -> cellA Md 0x1374b0 8 0x1d1768 -> cellA Md (0x1d1768 + 144) 8 0 ->
  EVOK log (AMunmap h ms) ->
  (forall regs' c88 c96, 0 <= c88 < 2 ^ 64 -> 0 <= c96 < 2 ^ 64 -> cellA Md (t + 2800 + 88) 8 c88 -> cellA Md (t + 2800 + 96) 8 c96 ->
     getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp -> getr regs' 8 = Z_to_bv 64 x8 -> getr regs' 9 = Z_to_bv 64 x9 -> getr regs' 18 = Z_to_bv 64 x18 ->
     (forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
     Q (log ++ [AMunmap h ms]) (mkst regs' raw (art_secd_fin_mem Md sp raw t h ms x8 x9 x18 c88 c96) rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x54fc0 : word) Md rom).
Proof.
  intros Q log regs Md rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 H2 H4 H8 H18 Hret HHI Hsp Hsp' W Hh Hh' Hms Hx8 Hx9 Hx18 TSD Ht Ht' Hti Htp Htsd Hctx Aht Wt
    F1 F8 F9 F18 Chh Chms CF C144 EV HK.
  pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB.
  pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Rk & _).
  destruct (art_cell_exists Md (t + 2800 + 88) 8 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia|cbn; lia])) as (c88 & Hc88 & C88).
  destruct (art_cell_exists Md (t + 2800 + 96) 8 ltac:(lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) ltac:(eapply wr_sub; [exact Wt|lia|cbn; lia])) as (c96 & Hc96 & C96).
  pose proof (art_secd_d_fn regs Md rom raw sp HI tp key tsd ctx t h ms x8 x9 x18 c88 c96 H2 H4 H8 H18 ltac:(lia) Hsp ltac:(lia) W Hh ltac:(lia) ltac:(lia) Hx8 Hx9 Hx18 Hc88 Hc96
                TSD Ht Ht' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart in *; lia) Wt F1 F8 F9 F18 Chh Chms C88 C96) as RUNd.
  eapply ar_steps; [exact RUNd|]. clear RUNd.
  match goal with |- aruns _ _ _ _ _ (mkst ?R _ _ _) => set (Rd := R) end.
  assert (ARGS : art_munmap_args Rd h ms) by (unfold art_munmap_args, Rd; repeat split; gres; reflexivity).
  eapply (ar_munmap ASEGS EVOK GR Q log Rd (0x8bc8c : word) (0x8bc90 : word) _ rom h ms art_at_ecall_munmap ltac:(apply bv_eq; reflexivity) ARGS EV).
  (* [comment removed for export] *)
  assert (D1 : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (sp - 8) 8 (U raw)) by (unfold art_secd_d_mem; zcell).
  assert (D8 : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (sp - 16) 8 x8) by (unfold art_secd_d_mem; zcell).
  assert (D9 : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (sp - 24) 8 x9) by (unfold art_secd_d_mem; zcell).
  assert (D18 : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (sp - 32) 8 x18) by (unfold art_secd_d_mem; zcell).
  assert (DF : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) 0x1374b0 8 0x1d1768) by (unfold art_secd_d_mem; zcell).
  assert (D144 : cellA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (0x1d1768 + 144) 8 0) by (unfold art_secd_d_mem; zcell).
  assert (DW : wrA (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) (sp - 64) 64) by (unfold art_secd_d_mem; zwr).
  set (Mu := art_unmap (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) h ms).
  assert (U1 : cellA Mu (sp - 8) 8 (U raw)) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact D1]).
  assert (U8 : cellA Mu (sp - 16) 8 x8) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact D8]).
  assert (U9 : cellA Mu (sp - 24) 8 x9) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact D9]).
  assert (U18 : cellA Mu (sp - 32) 8 x18) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact D18]).
  assert (UF : cellA Mu 0x1374b0 8 0x1d1768) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact DF]).
  assert (U144 : cellA Mu (0x1d1768 + 144) 8 0) by (apply cell_unmap_other; [lia|cbn; lia|unfold apart; cbn; lia|exact D144]).
  assert (UW : wokA Mu (sp - 36) 4).
  { apply (wr_wok _ _ (sp - 64) 64); [|lia|cbn; lia]. apply wr_unmap_other; [lia|lia|unfold apart; lia|exact DW]. }
  pose proof (art_secd_e_fn (regupd Rd 10 (Z_to_bv 64 0)) Mu rom raw sp ms x8 x9 x18 ltac:(unfold Rd; gres; reflexivity) ltac:(unfold Rd; gres; reflexivity)
                ltac:(unfold Rd; gres; reflexivity) ltac:(gres; reflexivity) Hret ltac:(lia) ltac:(lia) ltac:(lia) Hx8 Hx9 Hx18 UW U1 U8 U9 U18 UF U144) as RUNe.
  eapply ar_steps; [exact RUNe|]. clear RUNe. apply ar_done.
  subst Mu. change (Wn 4 (art_unmap (art_secd_d_mem Md sp raw t ms x8 x9 x18 c88 c96) h ms) (sp - 36) 18446744072277895850) with (art_secd_fin_mem Md sp raw t h ms x8 x9 x18 c88 c96).
  apply (HK _ c88 c96 Hc88 Hc96 C88 C96); try (unfold Rd; gres; reflexivity).
  intros r Hr. cbn [In] in Hr. unfold Rd. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem art_secd_aruns : forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
    (sp HI tp key tsd ctx t parr mb ms : Z) (bl : list (Z * Z)) (idx : nat),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp ->
  getr regs 10 = Z_to_bv 64 0x13c618 -> getr regs 11 = Z_to_bv 64 0x13c888 -> getr regs 12 = Z_to_bv 64 (mb + 4096) ->
  kHighMemBeg <= HI -> HI <= sp - 96 -> sp < 2 ^ 47 -> wrA M (sp - 96) 96 ->
  nth_error bl idx = Some (mb, ms) -> art_sec_cells M parr bl -> art_sec_geo HI t ctx parr bl ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  4096 <= t -> t + 4096 <= HI -> appmem t 4096 -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> wrA M t 4096 ->
  4096 <= ctx -> ctx + 4096 <= HI -> appmem ctx 4096 -> (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x661b28 <= tp - 88 -> tp + 8 <= 0x696000 -> 0x661b28 <= tsd -> tsd + 1024 <= 0x696000 ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x137500 8 1 -> cellA M (0x1d1768 + 144) 8 0 ->
  art_evok_list EVOK log (art_flush_events mb ms ++ [AMunmap mb ms]) ->
  (forall regs' (M' : word -> option byte),
     getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp ->
     (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
     art_agree (art_secd_fp sp t parr (Z.of_nat idx) (fst (nth (length bl - 1) bl (0, 0))) mb ms) M M' ->
     (forall x : word, mb <= U x < mb + ms -> M' x = None) ->
     (forall x : word, SB + mb / 8 <= U x < SB + mb / 8 + ms / 8 -> M' x = Some (Z_to_bv 8 0)) ->
     (forall a n, 0 <= a -> a + n < 2 ^ 64 -> apart mb ms a n -> wrA M a n -> wrA M' a n) ->
     art_sec_cells M' parr (art_swap_remove (0, 0) idx bl) ->
     Q (log ++ art_flush_events mb ms ++ [AMunmap mb ms]) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x54ec0 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI tp key tsd ctx t parr mb ms bl idx H1 Hret H2 H4 H10 H11 H12 HHI Hsp Hsp' W Hnth SC GEO LAY TSD
    Ht Ht' APt Hti Wt Hctx Hctx' APc Hci Atc Htp Htp' Htsd Htsd' Cpc Cpg Cgot C144 EVS HK.
  pose proof (eq_refl : kHighMemBeg = 0x10007fff8000) as EHB. pose proof (eq_refl : SB = 2147450880) as ESB.
  destruct SC as (Cpage & Cparr & Cn & Clk & Wparr & CB).
  destruct GEO as (Hparr & Hparr' & Hlen & APp & Apt & Apc & GB & GP).
  assert (Hidx : (idx < length bl)%nat) by (apply nth_error_Some; congruence).
  set (n := Z.of_nat (length bl)) in *.
  assert (Hn1 : 1 <= n) by (unfold n; lia).
  (* [comment removed for export] *)
  destruct (CB idx (mb, ms) Hnth) as (Cslot & Chh & Chms & Chidx & Wblk & Wsh). cbn [fst snd] in Cslot, Chh, Chms, Chidx, Wblk, Wsh.
  destruct (GB (mb, ms) (nth_error_In _ _ Hnth)) as (Hmb4 & Hms4 & Hms & Hmbi & Hmbhi & APb & Abp & Abt & Abc). cbn [fst snd] in Hmb4, Hms4, Hms, Hmbi, Hmbhi, APb, Abp, Abt, Abc.
  (* [comment removed for export] *)
  destruct (nth_error bl (length bl - 1)) as [[lb lms]|] eqn:El; [|exfalso; apply nth_error_None in El; lia].
  assert (Elast : fst (nth (length bl - 1) bl (0, 0)) = lb) by (rewrite (nth_error_nth _ _ _ El); reflexivity). rewrite Elast in HK.
  destruct (CB _ _ El) as (Clslot & Clh & Clms & Clidx & Wlast & Wlsh). cbn [fst snd] in Clslot, Clh, Clms, Clidx, Wlast, Wlsh.
  destruct (GB (lb, lms) (nth_error_In _ _ El)) as (Hlb4 & Hlms4 & Hlms & Hlbi & Hlbhi & APl & Alp & Alt & Alc). cbn [fst snd] in Hlb4, Hlms4, Hlms, Hlbi, Hlbhi, APl, Alp, Alt, Alc.
  assert (SAME : (lb = mb /\ lms = ms) \/ apart lb lms mb ms).
  { destruct (Nat.eq_dec (length bl - 1) idx) as [E|NE]; [left; rewrite E in El; rewrite Hnth in El; inversion El; split; reflexivity | right; exact (GP _ _ _ _ El Hnth NE)]. }
  replace (Z.of_nat (length bl - 1)) with (n - 1) in Clslot, Clidx by (unfold n; lia).
  (* [comment removed for export] *)
  destruct (art_img_cell_exists M (0x13c618 + 80) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (nf & Hnf & Cnf). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hnf.
  destruct (art_img_cell_exists M (0x13c618 + 88) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (ca & Hca & Cca). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hca.
  destruct (art_img_cell_exists M (0x13c888 + 16) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (s16 & Hs16 & C16). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hs16.
  destruct (art_img_cell_exists M (0x13c888 + 24) 8 ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as (s24 & Hs24 & C24). change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hs24.
  assert (Hidxn : 0 <= Z.of_nat idx < n) by (unfold n; lia).
  (* [comment removed for export] *)
  pose proof (art_secd_a_fn regs M rom raw sp HI mb ms parr (Z.of_nat idx) n lb nf ca s16 s24 H1 H2 H10 H11 H12 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia]) Hmbi ltac:(lia) Hmb4 Hlbi ltac:(lia)
                ltac:(clear - SAME Hms Hlms; unfold apart in *; lia) Hparr ltac:(lia)
                ltac:(clear - Abp Hms; unfold apart in *; fold n; lia) ltac:(clear - Alp Hlms; unfold apart in *; fold n; lia)
                Hidxn Hlen ltac:(lia) Hnf Hca Hs16 Hs24 Cpage Clk Cparr Cn Cnf Cca C16 C24 Chh Chms Chidx Cslot Clslot
                ltac:(apply (wr_wok _ _ _ _ Wparr); [lia|cbn; fold n; lia]) ltac:(apply (wr_wok _ _ _ _ Wlast); [lia|cbn; lia])) as RUNa.
  eapply ar_steps; [exact RUNa|]. clear RUNa.
  match goal with |- aruns _ _ _ _ _ (mkst ?R _ _ _) => set (Ra := R) end.
  set (x8 := U (getr regs 8)). set (x9 := U (getr regs 9)). set (x18 := U (getr regs 18)).
  assert (Hx8 : 0 <= x8 < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr regs 8)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
  assert (Hx9 : 0 <= x9 < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr regs 9)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
  assert (Hx18 : 0 <= x18 < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (getr regs 18)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
  set (Wa := [(sp - 32, 32); (0x13c618 + 56, 568); (parr + 8 * Z.of_nat idx, 8); (lb + 24, 8); (0x13c888 + 16, 16)]).
  assert (FA : let Ma := art_secd_a_mem M sp raw regs ms parr (Z.of_nat idx) n lb nf ca s16 s24 in
               mem_grows M Ma /\ art_agree Wa M Ma
               /\ cellA Ma (sp - 8) 8 (U raw) /\ cellA Ma (sp - 16) 8 x8 /\ cellA Ma (sp - 24) 8 x9 /\ cellA Ma (sp - 32) 8 x18
               /\ cellA Ma 0x13c618 8 4096 /\ cellA Ma (0x13c618 + 8) 8 parr /\ cellA Ma (0x13c618 + 56) 8 (n - 1) /\ cellA Ma (0x13c618 + 616) 4 0
               /\ cellA Ma (parr + 8 * Z.of_nat idx) 8 lb /\ cellA Ma (lb + 24) 8 (Z.of_nat idx)).
  { cbv zeta. unfold art_secd_a_mem, art_flush_frame. fold x8 x9 x18.
    assert (AP1 : apart (lb + 24) 8 parr (8 * n)) by (clear - Alp Hlms; unfold apart in *; lia).
    clear - Hsp Hsp' HHI EHB Hparr Hparr' Hlbi Hlbhi Hlms Hidxn AP1 Hlen Cpage Cparr.
    split; [zgrows|]. split; [eapply art_agree_sub; [zagree|]; unfold Wa; zsub|].
    repeat split; try zcell.
    apply art_lock_word_release; [lia|lia|]. zcell. }
  cbv zeta in FA. destruct FA as (Ga & Aa & Fa1 & Fa8 & Fa9 & Fa18 & Capage & Caparr & Can & Calk & Caslot & Calidx).
  set (Ma := art_secd_a_mem M sp raw regs ms parr (Z.of_nat idx) n lb nf ca s16 s24) in *.
  assert (GAPimg : art_gap Wa 0x1366c8 0x3000 /\ art_gap Wa 0x13d438 (0x141480 - 0x13d438) /\ art_gap Wa 0x1d1768 256 /\ art_gap Wa 0x13f4a0 8 /\ art_gap Wa (tp - 88) 8
            /\ art_gap Wa (tsd + 8 * key) 8 /\ art_gap Wa 0x137500 8 /\ art_gap Wa 0x1cf6e0 8).
  { pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Rk & _). clear - Hsp HHI EHB Hparr Hlbi Htp Htp' Htsd Htsd' Rk. unfold Wa. repeat split; zarith_t. }
  destruct GAPimg as (GI1 & GI2 & GI3 & GI4 & GI5 & GI6 & GI7 & GI8).
  assert (GAPctx : art_gap Wa (ctx + 152) 8).
  { clear - Hsp HHI EHB Hctx Hctx' Hci Apc Alc Hidxn Hlms. unfold Wa. unfold apart in *. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GAPhdr : art_gap Wa mb 16).
  { clear - Hsp HHI EHB Hmbi Hmbhi Hms Abp SAME Hidxn Hlms. unfold Wa. unfold apart in *. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (LAYa : art_layout Ma) by (exact (art_layout_tr Wa M Ma Aa GI1 GI2 GI3 LAY)).
  assert (TSDa : art_tsd Ma tp key tsd ctx t) by (exact (art_tsd_tr Wa M Ma tp key tsd ctx t Aa GI4 GI5 GI6 GAPctx TSD)).
  assert (Cahh : cellA Ma mb 8 mb) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [eapply art_gap_sub; [exact GAPhdr|lia|cbn; lia]|lia|cbn; lia|exact Chh]).
  assert (Cahms : cellA Ma (mb + 8) 8 ms) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [eapply art_gap_sub; [exact GAPhdr|lia|cbn; lia]|lia|cbn; lia|exact Chms]).
  assert (Capc : cellA Ma 0x1374a0 8 0x1cf6e0) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [eapply art_gap_sub; [exact GI1|lia|cbn; lia]|lia|cbn; lia|exact Cpc]).
  assert (Capg : cellA Ma 0x1cf6e0 8 4096) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [exact GI8|lia|cbn; lia|exact Cpg]).
  assert (Cagot : cellA Ma 0x137500 8 1) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [exact GI7|lia|cbn; lia|exact Cgot]).
  assert (Ca144 : cellA Ma (0x1d1768 + 144) 8 0) by (apply (art_cell_tr Wa M Ma _ _ _ Aa); [eapply art_gap_sub; [exact GI3|lia|cbn; lia]|lia|cbn; lia|exact C144]).
  assert (Wa96 : wrA Ma (sp - 96) 96) by (exact (wr_grows _ _ _ _ _ Ga W)).
  assert (Wat : wrA Ma t 4096) by (exact (wr_grows _ _ _ _ _ Ga Wt)).
  assert (Wash : wrA Ma (SB + mb / 8) (ms / 8)) by (exact (wr_grows _ _ _ _ _ Ga Wsh)).
  (* [comment removed for export] *)
  pose proof (mod8_of_4096 mb Hmb4) as Hmb8. pose proof (mod8_of_4096 ms Hms4) as Hms8.
  assert (POK : art_poison_lo_ok mb ms \/ art_poison_hi_ok mb ms).
  { clear - APb Hmbi Hmbhi Hms Hsp Hsp' ESB EHB. unfold appmem, art_poison_lo_ok, art_poison_hi_ok, kHighMemEnd in *. cbn [fst snd] in *. lia. }
  assert (Hms61 : ms / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
  destruct (art_poison3_run Ra Ma rom (0x54fb4 : bv 64)%bv (sp - 32) mb ms 0 ltac:(unfold Ra; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold Ra; gres; reflexivity)
              ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(lia) ltac:(lia)
              ltac:(eapply wr_sub; [exact Wa96|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia) LAYa POK Hmb8 Hms8 ltac:(lia) ltac:(lia) ltac:(intros _; exact Hms61) Wash)
    as (rb & RUNb & B10 & B1 & B2 & B8 & B9 & B18 & _ & _ & _ & BK).
  eapply ar_steps; [exact RUNb|]. clear RUNb.
  (* [comment removed for export] *)
  assert (BLK : art_blk_ok mb ms) by (clear - APb Hmbi Hmbhi Hms Hsp Hsp' ESB EHB; unfold appmem, art_blk_ok, kHighMemEnd in *; cbn [fst snd] in *; lia).
  destruct (art_blk_shadow_range mb ms ltac:(lia) BLK) as (SD1 & SD2 & SD3).
  destruct (art_flush_range mb ms Hmb4 Hms4 ltac:(lia) ltac:(lia)) as (FR1 & FR2 & FR3 & FR4 & FR5 & FR6 & _ & _ & _).
  assert (Hsl0 : 0 <= ms / 8) by (apply Z.div_pos; lia).
  set (sa := SB + mb / 8) in *. set (sl := ms / 8) in *.
  assert (SHB : SB <= sa /\ sa + sl <= kHighMemBeg) by (clear - SD1 SD3 FR6 ESB EHB; unfold sa, sl; lia).
  destruct SHB as (SHB1 & SHB2).
  lazymatch goal with |- aruns _ _ _ _ _ (mkst _ _ (Wf (art_poison_frame _ _ ?ra ?s0 ?s1 ?s2 ?s3 ?s4 ?s5) _ _ _) _) =>
    pose proof (art_poisoned_facts Ma (sp - 32) ra s0 s1 s2 s3 s4 s5 sa sl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as FB end.
  cbv zeta in FB. destruct FB as (Gb & Ab & Zb).
  match goal with |- aruns _ _ _ _ _ (mkst _ _ ?X _) => remember X as Mb eqn:EMb in * end. clear EMb.
  assert (Ab' : art_agree [(sp - 96, 64); (sa, sl)] Ma Mb) by (eapply art_agree_sub; [exact Ab|]; clear; zsub).
  clear Ab.
  assert (E2 : getr rb 2 = Z_to_bv 64 (sp - 32)) by exact B2.
  assert (E8 : getr rb 8 = Z_to_bv 64 mb) by (rewrite B8; unfold Ra; gres; reflexivity).
  assert (E9 : getr rb 9 = Z_to_bv 64 mb) by (rewrite B9; unfold Ra; gres; reflexivity).
  assert (E18 : getr rb 18 = Z_to_bv 64 ms) by (rewrite B18; unfold Ra; gres; reflexivity).
  assert (EK : forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rb r = getr regs r).
  { intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [rewrite BK by (unfold art_poison_kept; repeat split; reg_neq_tac); unfold Ra; gres; reflexivity|]). destruct Hr. }
  assert (E4 : getr rb 4 = Z_to_bv 64 tp) by (rewrite EK by inl; exact H4).
  clear B10 B1 B2 B8 B9 B18 BK.
  (* [comment removed for export] *)
  assert (TAIL : forall rd (Md : word -> option byte) log',
            mem_grows Ma Md -> art_agree [(sp - 96, 64); (sa, sl)] Ma Md -> (forall x : word, sa <= U x < sa + sl -> Md x = Some (Z_to_bv 8 0)) ->
            getr rd 2 = Z_to_bv 64 (sp - 32) -> getr rd 4 = Z_to_bv 64 tp -> getr rd 8 = Z_to_bv 64 mb -> getr rd 18 = Z_to_bv 64 ms ->
            (forall r : reg, In r [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr rd r = getr regs r) ->
            EVOK log' (AMunmap mb ms) -> log' ++ [AMunmap mb ms] = log ++ art_flush_events mb ms ++ [AMunmap mb ms] ->
            aruns ASEGS EVOK GR Q log' (mkst rd (0x54fc0 : word) Md rom)).
  { intros rd Md log' Gd Ad Zd D2 D4 D8 D18 DK EVu ELOG.
    set (Wd := [(sp - 96, 64); (sa, sl)]) in *.
    pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Rk & _).
    assert (GAPd : art_gap Wd 0x1366c8 0x3000 /\ art_gap Wd 0x1d1768 256 /\ art_gap Wd 0x13f4a0 8 /\ art_gap Wd (tp - 88) 8 /\ art_gap Wd (tsd + 8 * key) 8
              /\ art_gap Wd (sp - 32) 32 /\ art_gap Wd 0x13c618 624).
    { clear - Hsp HHI EHB ESB SHB1 SHB2 Htp Htp' Htsd Htsd' Rk. unfold Wd. repeat split; zarith_t. }
    destruct GAPd as (GD1 & GD3 & GD4 & GD5 & GD6 & GD7 & GD8).
    assert (GDctx : art_gap Wd (ctx + 152) 8).
    { clear - Hsp HHI EHB ESB SHB1 SHB2 Hctx Hctx' APc. unfold Wd, appmem in *. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
    assert (GDhdr : art_gap Wd mb 16).
    { clear - Hsp HHI EHB ESB SHB1 SHB2 Hmbi Hmbhi Hms APb. unfold Wd, appmem in *. cbn [fst snd art_gap] in *. unfold apart. repeat split; try exact I; lia. }
    assert (TSDd : art_tsd Md tp key tsd ctx t) by (exact (art_tsd_tr Wd Ma Md tp key tsd ctx t Ad GD4 GD5 GD6 GDctx TSDa)).
    assert (Fd1 : cellA Md (sp - 8) 8 (U raw)) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD7|lia|cbn; lia]|lia|cbn; lia|exact Fa1]).
    assert (Fd8 : cellA Md (sp - 16) 8 x8) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD7|lia|cbn; lia]|lia|cbn; lia|exact Fa8]).
    assert (Fd9 : cellA Md (sp - 24) 8 x9) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD7|lia|cbn; lia]|lia|cbn; lia|exact Fa9]).
    assert (Fd18 : cellA Md (sp - 32) 8 x18) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD7|lia|cbn; lia]|lia|cbn; lia|exact Fa18]).
    assert (Cdhh : cellA Md mb 8 mb) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GDhdr|lia|cbn; lia]|lia|cbn; lia|exact Cahh]).
    assert (Cdhms : cellA Md (mb + 8) 8 ms) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GDhdr|lia|cbn; lia]|lia|cbn; lia|exact Cahms]).
    pose proof LAYa as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CaF & _).
    assert (CdF : cellA Md 0x1374b0 8 0x1d1768) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD1|lia|cbn; lia]|lia|cbn; lia|exact CaF]).
    assert (Cd144 : cellA Md (0x1d1768 + 144) 8 0) by (apply (art_cell_tr Wd Ma Md _ _ _ Ad); [eapply art_gap_sub; [exact GD3|lia|cbn; lia]|lia|cbn; lia|exact Ca144]).
    assert (Wd64 : wrA Md (sp - 64) 64) by (eapply wr_sub; [exact (wr_grows _ _ _ _ _ Gd Wa96)|lia|lia]).
    assert (Wdt : wrA Md t 4096) by (exact (wr_grows _ _ _ _ _ Gd Wat)).
    apply (art_secd_tail_aruns Q log' rd Md rom raw sp HI tp key tsd ctx t mb ms x8 x9 x18 D2 D4 D8 D18 Hret HHI Hsp Hsp' Wd64 Hmbi Hmbhi Hms Hx8 Hx9 Hx18 TSDd Ht Ht' Hti Htp' Htsd' Hctx' Abt Wdt
             Fd1 Fd8 Fd9 Fd18 Cdhh Cdhms CdF Cd144 EVu).
    intros regs' c88 c96 Hc88 Hc96 C88 C96 R1 R2 R8 R9 R18 RK.
    rewrite ELOG.
    destruct (art_secd_fin_facts Md sp raw t mb ms x8 x9 x18 c88 c96 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Af & Uf & Wf').
    set (M' := art_secd_fin_mem Md sp raw t mb ms x8 x9 x18 c88 c96) in *. clearbody M'.
    assert (Ar : art_agree (Wd ++ [(sp - 64, 64); (t + 2800 + 88, 16); (mb, ms)]) Ma M') by (exact (art_agree_trans _ _ _ _ _ Ad Af)).
    assert (P1 : art_agree (art_secd_fp sp t parr (Z.of_nat idx) lb mb ms) M M').
    { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ Aa Ar)|]. clear - Hsp. unfold Wa, Wd, art_secd_fp, sa, sl. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia. }
    assert (P3 : forall x : word, sa <= U x < sa + sl -> M' x = Some (Z_to_bv 8 0)).
    { intros x Hx. rewrite (Af x); [apply Zd; exact Hx|]. clear - Hx Hsp HHI EHB ESB SHB1 SHB2 APt APb Ht. unfold appmem in *. cbn [fst snd art_out] in *. repeat split; try exact I; lia. }
    assert (P4 : forall a k, 0 <= a -> a + k < 2 ^ 64 -> apart mb ms a k -> wrA M a k -> wrA M' a k).
    { intros a k Ha Hk A Wm. apply Wf'; [exact Ha|exact Hk|exact A|]. eapply wr_grows; [exact Gd|]. eapply wr_grows; [exact Ga|exact Wm]. }
    assert (P5 : art_sec_cells M' parr (art_swap_remove (0, 0) idx bl)).
    { set (Wr := Wd ++ [(sp - 64, 64); (t + 2800 + 88, 16); (mb, ms)]) in *.
      assert (GRimg : art_gap Wr 0x13c618 624).
      { clear - Hsp HHI EHB ESB SHB1 SHB2 Hti Hmbi. unfold Wr, Wd. cbn [app art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
      assert (GRslot : art_gap Wr (parr + 8 * Z.of_nat idx) 8).
      { clear - Hsp HHI EHB ESB SHB1 SHB2 Hparr Hparr' Hidxn APp Apt Abp. unfold Wr, Wd, appmem in *. cbn [app art_gap fst snd]. unfold apart in *. repeat split; try exact I; lia. }
      assert (GRlidx : apart lb lms mb ms -> art_gap Wr (lb + 24) 8).
      { intros ALM. clear - ALM Hsp HHI EHB ESB SHB1 SHB2 Hlbi Hlbhi Hlms APl Alt. unfold Wr, Wd, appmem in *. cbn [app art_gap fst snd] in *. unfold apart in *. repeat split; try exact I; lia. }
      unfold art_sec_cells. rewrite art_swap_remove_length.
      replace (Z.of_nat (length bl - 1)) with (n - 1) by (unfold n; lia).
      split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [eapply art_gap_sub; [exact GRimg|lia|cbn; lia]|lia|cbn; lia|exact Capage]|].
      split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [eapply art_gap_sub; [exact GRimg|lia|cbn; lia]|lia|cbn; lia|exact Caparr]|].
      split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [eapply art_gap_sub; [exact GRimg|lia|cbn; lia]|lia|cbn; lia|exact Can]|].
      split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [eapply art_gap_sub; [exact GRimg|lia|cbn; lia]|lia|cbn; lia|exact Calk]|].
      split. { apply P4; [lia|lia|clear - Abp Hn1; unfold apart in *; lia|eapply wr_sub; [exact Wparr|lia|lia]]. }
      intros j b Hjb.
      assert (Hj : (j < length bl - 1)%nat) by (rewrite <- (art_swap_remove_length _ (0, 0) idx bl); apply nth_error_Some; congruence).
      rewrite art_swap_remove_nth in Hjb by exact Hj.
      destruct (Nat.eqb_spec j idx) as [Ej|NEj].
      - subst j. rewrite El in Hjb. inversion Hjb; subst b. cbn [fst snd].
        assert (ALM : apart lb lms mb ms) by (apply (GP _ _ _ _ El Hnth); lia).
        destruct (art_sh_bounds lb lms Hlb4 Hlms4 ltac:(lia) ltac:(lia) ltac:(lia)) as (LS1 & LS2 & LS3 & LS4 & _).
        assert (GPhdr : art_gap (art_secd_fp sp t parr (Z.of_nat idx) lb mb ms) lb 16).
        { clear - ALM Hsp HHI EHB ESB SHB1 SHB2 Hlbi Hlbhi Hlms APl Alt Alp Hidxn. unfold art_secd_fp, appmem in *. fold sa sl. cbn [art_gap fst snd] in *. unfold apart in *. repeat split; try exact I; lia. }
        split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [exact GRslot|lia|cbn; lia|exact Caslot]|].
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [eapply art_gap_sub; [exact GPhdr|lia|cbn; lia]|lia|cbn; lia|exact Clh]|].
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [eapply art_gap_sub; [exact GPhdr|lia|cbn; lia]|lia|cbn; lia|exact Clms]|].
        split; [apply (art_cell_tr Wr Ma M' _ _ _ Ar); [exact (GRlidx ALM)|lia|cbn; lia|exact Calidx]|].
        split; [apply P4; [lia|lia|apply apart_sym; exact ALM|exact Wlast]|].
        apply P4; [lia|lia| |exact Wlsh]. clear - LS1 LS2 LS3 LS4 APb EHB ESB Hms. unfold appmem, art_shlo, art_shhi in *. cbn [fst snd] in *. unfold apart. lia.
      - destruct (CB j b Hjb) as (Cj1 & Cj2 & Cj3 & Cj4 & Wj1 & Wj2).
        destruct (GB b (nth_error_In _ _ Hjb)) as (Hb4 & Hbs4 & Hbs & Hbi & Hbhi & APbb & Abbp & Abbt & Abbc).
        assert (ABM : apart (fst b) (snd b) mb ms) by (apply (GP _ _ _ _ Hjb Hnth); exact NEj).
        assert (ABL : apart (fst b) (snd b) lb lms) by (apply (GP _ _ _ _ Hjb El); lia).
        destruct (art_sh_bounds (fst b) (snd b) Hb4 Hbs4 ltac:(lia) ltac:(lia) ltac:(lia)) as (BS1 & BS2 & BS3 & BS4 & _).
        assert (Hjn : 0 <= Z.of_nat j < n - 1) by (unfold n; lia).
        assert (GPslot : art_gap (art_secd_fp sp t parr (Z.of_nat idx) lb mb ms) (parr + 8 * Z.of_nat j) 8).
        { assert (Z.of_nat j <> Z.of_nat idx) by lia.
          clear - H Hjn Hsp HHI EHB ESB SHB1 SHB2 Hparr Hparr' Hidxn APp Apt Abp Alp Hlms Hms. unfold art_secd_fp, appmem in *. fold sa sl. cbn [art_gap fst snd] in *. unfold apart in *. repeat split; try exact I; lia. }
        assert (GPhdr : art_gap (art_secd_fp sp t parr (Z.of_nat idx) lb mb ms) (fst b) 32).
        { clear - ABM ABL Hsp HHI EHB ESB SHB1 SHB2 Hbi Hbhi Hbs APbb Abbt Abbp Hidxn Hlms Hms. unfold art_secd_fp, appmem in *. fold sa sl. cbn [art_gap fst snd] in *. unfold apart in *. repeat split; try exact I; lia. }
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [exact GPslot|lia|cbn; lia|exact Cj1]|].
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [eapply art_gap_sub; [exact GPhdr|lia|cbn; lia]|lia|cbn; lia|exact Cj2]|].
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [eapply art_gap_sub; [exact GPhdr|lia|cbn; lia]|lia|cbn; lia|exact Cj3]|].
        split; [apply (art_cell_tr _ M M' _ _ _ P1); [eapply art_gap_sub; [exact GPhdr|lia|cbn; lia]|lia|cbn; lia|exact Cj4]|].
        split; [apply P4; [lia|lia|apply apart_sym; exact ABM|exact Wj1]|].
        apply P4; [lia|lia| |exact Wj2]. clear - BS1 BS2 BS3 BS4 APb EHB ESB Hms. unfold appmem, art_shlo, art_shhi in *. cbn [fst snd] in *. unfold apart. lia. }
    apply HK; [exact R1 | exact R2 | | exact P1 | exact Uf | exact P3 | exact P4 | exact P5].
    intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|Hr]; [rewrite RK by inl; apply DK; inl|]. destruct Hr as [<-|Hr]; [rewrite RK by inl; apply DK; inl|].
    destruct Hr as [<-|Hr]; [rewrite R8; unfold x8; apply Z_to_bv_bv_unsigned|]. destruct Hr as [<-|Hr]; [rewrite R9; unfold x9; apply Z_to_bv_bv_unsigned|].
    destruct Hr as [<-|Hr]; [rewrite R18; unfold x18; apply Z_to_bv_bv_unsigned|].
    repeat (destruct Hr as [<-|Hr]; [rewrite RK by inl; apply DK; inl|]). destruct Hr. }
  (* [comment removed for export] *)
  set (Wd := [(sp - 96, 64); (sa, sl)]) in *.
  assert (GAPd : art_gap Wd 0x1366c8 0x3000 /\ art_gap Wd 0x13d438 (0x141480 - 0x13d438) /\ art_gap Wd 0x1d1768 256 /\ art_gap Wd 0x137500 8 /\ art_gap Wd 0x1cf6e0 8).
  { clear - Hsp HHI EHB ESB SHB1. unfold Wd. repeat split; zarith_t. }
  destruct GAPd as (GD1 & GD2 & GD3 & GD4 & GD5).
  assert (LAYb : art_layout Mb) by (exact (art_layout_tr Wd Ma Mb Ab' GD1 GD2 GD3 LAYa)).
  assert (Cbpc : cellA Mb 0x1374a0 8 0x1cf6e0) by (apply (art_cell_tr Wd Ma Mb _ _ _ Ab'); [eapply art_gap_sub; [exact GD1|lia|cbn; lia]|lia|cbn; lia|exact Capc]).
  assert (Cbpg : cellA Mb 0x1cf6e0 8 4096) by (apply (art_cell_tr Wd Ma Mb _ _ _ Ab'); [exact GD5|lia|cbn; lia|exact Capg]).
  assert (Cbgot : cellA Mb 0x137500 8 1) by (apply (art_cell_tr Wd Ma Mb _ _ _ Ab'); [exact GD4|lia|cbn; lia|exact Cagot]).
  assert (Wb32 : wrA Mb (sp - 32 - 32) 32) by (eapply wr_sub; [exact (wr_grows _ _ _ _ _ Gb Wa96)|lia|lia]).
  eassert (RUNc0 : msteps ASEGS (mkst rb (0x54fb4 : word) Mb rom) _).
  { zstep F_54b9c D_54b9c. zstep F_54ba0 D_54ba0. stepn F_54ba4 D_54ba4. apply mst_refl. }
  eapply ar_steps; [exact RUNc0|]. clear RUNc0.
  match goal with |- aruns _ _ _ _ _ (mkst ?R _ _ _) => set (Rc0 := R) end.
  assert (X1 : getr Rc0 1 = (0x54fc0 : bv 64)%bv) by (unfold Rc0; gres; bveq).
  assert (X2 : getr Rc0 2 = Z_to_bv 64 (sp - 32)) by (unfold Rc0; gres; exact E2).
  assert (X10 : getr Rc0 10 = Z_to_bv 64 mb) by (unfold Rc0; gres; reflexivity).
  assert (X11 : getr Rc0 11 = Z_to_bv 64 ms) by (unfold Rc0; gres; reflexivity).
  assert (XK : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rc0 r = getr rb r).
  { intros r Hr. cbn [In] in Hr. unfold Rc0. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr. }
  assert (Hraw' : ret_ok (0x54fc0 : bv 64)%bv) by (unfold ret_ok; bveq).
  pose proof (art_flush_mem_agree Mb (sp - 32) (0x54fc0 : bv 64)%bv Rc0 ltac:(lia) ltac:(lia)) as Ac.
  pose proof (art_flush_mem_grows Mb (sp - 32) (0x54fc0 : bv 64)%bv Rc0) as Gc.
  set (Mc := art_flush_mem Mb (sp - 32) (0x54fc0 : bv 64)%bv Rc0) in *.
  assert (Zc : forall x : word, sa <= U x < sa + sl -> Mc x = Some (Z_to_bv 8 0)).
  { intros x Hx. rewrite (Ac x) by (clear - Hx Hsp HHI EHB SHB2; cbn [art_out fst snd]; split; [lia|exact I]). apply Zb. exact Hx. }
  assert (Adc : art_agree Wd Ma Mc).
  { eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ Ab' Ac)|]. clear. unfold Wd. zsub. }
  destruct (art_flush_beg mb <? art_flush_end mb ms) eqn:ELT; unfold art_flush_events in EVS, TAIL; rewrite ELT in EVS, TAIL.
  - apply Z.ltb_lt in ELT. cbn [app art_evok_list] in EVS. destruct EVS as (EV1 & EV2 & _).
    destruct (art_flush_pre_run Rc0 Mb rom (0x54fc0 : bv 64)%bv (sp - 32) mb ms X1 X2 X10 X11 ltac:(lia) ltac:(lia) Wb32 ltac:(lia) BLK LAYb Cbpc Cbpg Cbgot ELT) as (rc & RUNc & ARGS & C1 & C2 & CK).
    eapply ar_steps; [exact RUNc|]. clear RUNc. fold Mc.
    eapply (ar_madvise ASEGS EVOK GR Q log rc (0x8bcc4 : word) (0x8bcc8 : word) Mc rom _ _ art_at_ecall_madvise ltac:(apply bv_eq; reflexivity) ARGS EV1).
    pose proof (art_flush_post_fn (regupd rc 10 (Z_to_bv 64 0)) (art_zfill Mc (art_flush_beg mb) (art_flush_end mb ms - art_flush_beg mb)) rom (0x54fc0 : bv 64)%bv
                  ltac:(gres; rewrite C1; bveq) Hraw' ltac:(gres; reflexivity)) as RUNp.
    eapply ar_steps; [exact RUNp|]. clear RUNp.
    apply TAIL.
    + eapply mem_grows_trans; [exact Gb|]. eapply mem_grows_trans; [exact Gc|]. apply art_zfill_grows.
    + eapply art_agree_sub; [exact (art_agree_trans _ _ _ _ _ Adc (art_agree_zfill Mc _ _))|]. clear - FR4 FR5 FR6. unfold Wd, sa, sl. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia.
    + intros x Hx. unfold art_zfill. destruct ((art_flush_beg mb <=? U x) && (U x <? art_flush_beg mb + (art_flush_end mb ms - art_flush_beg mb))); [reflexivity|apply Zc; exact Hx].
    + gres. exact C2.
    + gres. rewrite CK by inl. rewrite XK by inl. exact E4.
    + gres. rewrite CK by inl. rewrite XK by inl. exact E8.
    + gres. rewrite CK by inl. rewrite XK by inl. exact E18.
    + intros r Hr. assert (Hr' : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (clear - Hr; cbn [In] in Hr |- *; tauto).
      rewrite <- (EK r Hr), <- (XK r Hr'), <- (CK r Hr'). cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
    + exact EV2.
    + rewrite <- app_assoc. reflexivity.
  - apply Z.ltb_ge in ELT. cbn [app art_evok_list] in EVS. destruct EVS as (EV2 & _).
    destruct (art_flush_skip_run Rc0 Mb rom (0x54fc0 : bv 64)%bv (sp - 32) mb ms X1 Hraw' X2 X10 X11 ltac:(lia) ltac:(lia) Wb32 ltac:(lia) BLK LAYb Cbpc Cbpg ELT) as (rc & RUNc & C2 & CK).
    eapply ar_steps; [exact RUNc|]. clear RUNc. fold Mc.
    apply TAIL.
    + eapply mem_grows_trans; [exact Gb|]. exact Gc.
    + exact Adc.
    + exact Zc.
    + exact C2.
    + rewrite CK by inl. rewrite XK by inl. exact E4.
    + rewrite CK by inl. rewrite XK by inl. exact E8.
    + rewrite CK by inl. rewrite XK by inl. exact E18.
    + intros r Hr. assert (Hr' : In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv) by (clear - Hr; cbn [In] in Hr |- *; tauto).
      rewrite <- (EK r Hr), <- (XK r Hr'). apply CK. exact Hr'.
    + exact EV2.
    + reflexivity.
Qed.
End Spec.
