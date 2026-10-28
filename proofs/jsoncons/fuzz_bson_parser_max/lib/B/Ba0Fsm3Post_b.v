(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MemSplit. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0RegionPoisoned_b Ba0FakeStackGC_b Ba0Fsm3Core_b Ba0FakeStackGCC_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation CLS := 3%Z.

(* [comment removed for export] *)
Lemma gc_post_nogc_3 : forall gb (mem0 Mj : word -> option byte) lo hi fs,
  mem_grows mem0 Mj -> (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> Mj x = mem0 x) ->
  (0 <= fs)%Z -> (fs + 97 <= 2 ^ 64)%Z -> (fs + 97 <= lo \/ hi <= fs + 96)%Z -> rdn ASEGS mem0 (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb] ->
  gc_postb gb mem0 Mj lo hi fs (fun _ _ => False).
Proof.
  intros gb mem0 Mj lo hi fs G O F1 F2 D C. split; [exact G|]. split; [intros x Hx _ _; apply O; exact Hx|]. split; [intros c i _ []|].
  rewrite <- C. apply rdn_ext; [rewrite u64_lit by lia; cbn [Z.of_nat Pos.to_nat]; lia|].
  intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. apply O. lia.
Qed.

(* [comment removed for export] *)
Definition fsm3_fp (fs pos ff : Z) (col : Z -> Z -> Prop) (a : Z) : Prop :=
  (fs + 24 <= a < fs + 24 + 8)%Z \/ a = (fs + 96)%Z \/ a = gc_fl fs CLS pos \/ (ff + 24 <= a < ff + 32)%Z \/ (ff + 504 <= a < ff + 504 + 8)%Z
  \/ (SB + ff / 8 <= a < SB + ff / 8 + 64)%Z
  \/ (exists c i, gc_valid c i /\ col c i /\ (a = gc_fl fs c i \/ gc_insh fs c i a)).
(* [comment removed for export] *)
Definition fsm3_post (gb : Z) (mem0 Mf : word -> option byte) (lo hi s fs h j pos ff : Z) (col : Z -> Z -> Prop) : Prop :=
  mem_grows mem0 Mf
  /\ (forall x : word, (bv_unsigned x < lo \/ hi <= bv_unsigned x)%Z -> ~ fsm3_fp fs pos ff col (bv_unsigned x) -> Mf x = mem0 x)
  /\ rdn ASEGS Mf (Z_to_bv 64 (fs + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (h + j + 1)))                       (* [comment removed for export] *)
  /\ rdn ASEGS Mf (Z_to_bv 64 (fs + 96)) 1%nat = Some [Z_to_bv 8 gb]                                                   (* [comment removed for export] *)
  /\ rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs CLS pos)) 1%nat = Some [Z_to_bv 8 1]                                            (* [comment removed for export] *)
  /\ (forall c i, gc_valid c i -> col c i -> ~ (c = CLS /\ i = pos) -> rdn ASEGS Mf (Z_to_bv 64 (gc_fl fs c i)) 1%nat = Some [Z_to_bv 8 0])   (* [comment removed for export] *)
  /\ rdn ASEGS Mf (Z_to_bv 64 (ff + 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 s))                               (* [comment removed for export] *)
  /\ rdn ASEGS Mf (Z_to_bv 64 (ff + 504)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (gc_fl fs CLS pos)))             (* [comment removed for export] *)
  /\ (forall i, (0 <= i < 64)%Z -> Mf (Z_to_bv 64 (SB + ff / 8 + i)) = Some (Z_to_bv 8 0)).                             (* [comment removed for export] *)

Section POST3.
  Variables mem0 Mg : word -> option byte.
  Variables gb lo hi s fs h j pos ff : Z.
  Variable col : Z -> Z -> Prop.
  Hypothesis GP : gc_postb gb mem0 Mg lo hi fs col.
  Hypothesis Hfs : (0x696000 <= fs)%Z /\ (fs + 4096 + 32768 + 11 * 2 ^ 20 < 2 ^ 47)%Z.
  Hypothesis Happm : (fs + 4096 + 32768 + 11 * 2 ^ 20 <= 0x7fff7000 \/ 0x10007fff8000 <= fs)%Z.
  Hypothesis Hpos : (0 <= pos < 2048)%Z.
  Hypothesis Hff_def : ff = (fs + 4096 + 32768 + 3145728 + 512 * pos)%Z.

  #[local] Ltac pw e := let v := eval vm_compute in e in change e with v.
  #[local] Ltac pwin e H := let v := eval vm_compute in e in change e with v in H.
  #[local] Ltac lens := rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.to_nat].
  #[local] Ltac side := lens; rewrite ?u64_lit by lia; lia.
  #[local] Ltac peel_pt := repeat (rewrite wbytes_outside by side).
  #[local] Ltac peel_rd := repeat (rewrite rdn_wbytes_out by side).

  #[using="Type"] Lemma le8_zero_p : word_to_le_bytes 8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
  Proof. vm_compute. repeat (apply f_equal2; [apply bv_eq; reflexivity|]). reflexivity. Qed.

  #[using="GP Hfs Happm Hpos Hff_def"] Theorem core3_desc : fsm3_post gb mem0 (core3_mem Mg s fs h j pos ff) lo hi s fs h j pos ff col.
  Proof.
    unfold fsm3_post. destruct Hfs as [Fs1 Fs2]. pose proof (gc_shz_facts fs Fs1 Fs2 Happm) as (Z1 & Z2 & Z3 & Z4).
    assert (Vpos : gc_valid CLS pos) by (split; [lia | pw (2 ^ (14 - CLS))%Z; lia]).
    assert (Eff : gc_fr fs CLS pos = ff) by (unfold gc_fr; pw (2 ^ (6 + CLS))%Z; rewrite Hff_def; lia).
    assert (Efl : gc_fl fs CLS pos = (fs + 4096 + 28672 + pos)%Z) by (unfold gc_fl; pw (2 ^ (14 - CLS))%Z; lia).
    pose proof (gc_fr_range fs CLS pos Vpos) as [FRR1 FRR2]. rewrite Eff in FRR1, FRR2. pwin (2 ^ (6 + CLS))%Z FRR2.
    pose proof (gc_sh_range fs CLS pos Vpos) as [SHR1 SHR2]. unfold gc_sh in SHR1, SHR2. rewrite Eff in SHR1, SHR2. pwin (2 ^ (3 + CLS))%Z SHR2.
    destruct GP as (GG & GO & GPc & G96).
    assert (FPOS : forall c i, gc_valid c i -> col c i -> ~ (c = CLS /\ i = pos) -> gc_fl fs c i <> (fs + 4096 + 28672 + pos)%Z).
    { intros c i Vc Cc NE E. rewrite <- Efl in E. apply (gc_fl_inj fs c i CLS pos Vc Vpos) in E. exact (NE E). }
    unfold core3_mem, fsm3_fp. rewrite !Efl.
    set (sh := (SB + ff / 8)%Z) in *. clearbody sh. clear Eff Efl Hff_def Happm.
    split; [repeat (eapply mem_grows_trans; [|apply wbytes_grows]); exact GG|].
    split.
    { intros x Hx NF. pose proof (u64_range x) as Ux.
      assert (N1 : ~ (fs + 24 <= bv_unsigned x < fs + 24 + 8)%Z) by (intros X; apply NF; left; exact X).
      assert (N2 : bv_unsigned x <> (fs + 96)%Z) by (intros X; apply NF; right; left; exact X).
      assert (N3 : bv_unsigned x <> (fs + 4096 + 28672 + pos)%Z) by (intros X; apply NF; right; right; left; exact X).
      assert (N4 : ~ (ff + 24 <= bv_unsigned x < ff + 32)%Z) by (intros X; apply NF; right; right; right; left; exact X).
      assert (N5 : ~ (ff + 504 <= bv_unsigned x < ff + 504 + 8)%Z) by (intros X; apply NF; right; right; right; right; left; exact X).
      assert (N6 : ~ (sh <= bv_unsigned x < sh + 64)%Z) by (intros X; apply NF; right; right; right; right; right; left; exact X).
      assert (N7 : forall c i, gc_valid c i -> col c i -> bv_unsigned x <> gc_fl fs c i /\ ~ gc_insh fs c i (bv_unsigned x)).
      { intros c i Vc Cc. split; intros X; apply NF; do 6 right; exists c, i; (split; [exact Vc | split; [exact Cc|]]); [left | right]; exact X. }
      clear NF. peel_pt. apply GO; assumption. }
    split. { peel_rd. apply rdn_wbytes_hit8. side. }
    split.
    { peel_rd. exact G96. }
    split. { peel_rd. apply (rdn_wbytes_hit ASEGS [Z_to_bv 8 1]). side. }
    split.
    { intros c i Vc Cc NE. pose proof (FPOS c i Vc Cc NE) as NEQ. pose proof (gc_fl_range fs c i Vc) as FLc. pose proof (GPc c i Vc Cc) as P1.
      clear GO GPc FPOS. peel_rd. change [Z_to_bv 8 0] with (repeat (Z_to_bv 8 0) 1). apply MemSplit.rdn_const; [side|].
      intros x Hx. rewrite u64_lit in Hx by lia. cbn [Z.of_nat Pos.to_nat] in Hx. rewrite (word_of_u x (gc_fl fs c i)) by lia. exact P1. }
    split. { peel_rd. apply rdn_wbytes_hit8. side. }
    split. { peel_rd. apply rdn_wbytes_hit8. side. }
    intros i Hi. clear GO GPc FPOS.
    assert (D : (0 <= i < 8 \/ 8 <= i < 16 \/ 16 <= i < 24 \/ 24 <= i < 32 \/ 32 <= i < 40 \/ 40 <= i < 48 \/ 48 <= i < 56 \/ 56 <= i < 64)%Z) by lia.
    decompose [or] D; clear D; peel_pt; (rewrite wbytes_inside by side); rewrite le8_zero_p; f_equal; apply nth_repeat.
  Qed.
End POST3.
