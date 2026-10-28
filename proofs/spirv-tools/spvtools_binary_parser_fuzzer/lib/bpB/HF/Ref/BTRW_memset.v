(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BtoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
  u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof.
  intros segs m A n bs i k a ARR LEN (Hi & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m A bs i k a ARR); [lia | rewrite LEN; lia | exact Ha].
Qed.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
  u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
  mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
  ms_facts A n i k -> a = wa (A + i) ->
  u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
  filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
  length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
  mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
  wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
  intros segs m0 m A n bs cb Q i k a ARR FIL LEN MI MU WM MF Ha.
  assert (SOK : store_ok segs m a (length (repeat cb k)) = true).
  { rewrite repeat_length. eapply ms_store_ok; eauto. }
  destruct MF as (Hi & Hk & A0 & An). subst a.
  split; [|split; [|split; [|split; [|split]]]].
  - apply (u8arr_write_bytes segs m A bs i _ ARR); [lia|]. rewrite repeat_length, LEN. lia.
  - apply filled_updZ; [exact FIL | lia | rewrite LEN; lia].
  - rewrite upd_bytes_length; [exact LEN|]. rewrite repeat_length, LEN. lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | rewrite repeat_length; lia |]. cbn [inside]. left. rewrite repeat_length. lia.
  - apply wmono_write. exact WM.
Qed.

Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.

