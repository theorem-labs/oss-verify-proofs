(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.World Require Import Tgt_example_flush_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg StreamSim WsegFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require ZIface InflateState Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.IK Require Export ZSysLite ZCall ZCallL TSet ZArr ZRd ZRom.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.I6U Require Export i6u_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Abbreviation R := R_segs (only parsing).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition ROM_LO : Z := 65536.
Definition ROM_HI : Z := 180224.

Definition rom_ok (M : mem) : Prop := rom_okG ROM_LO ROM_HI M.

Lemma rom_ok_frame : forall M a bs,
  rom_ok M -> 0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  zdisj a (Z.of_nat (length bs)) ROM_LO (ROM_HI - ROM_LO) ->
  rom_ok (wbytes M (w64 a) bs).
Proof. intros. apply rom_okG_frame; assumption. Qed.

Lemma rom_is : forall M a bs,
  rom_ok M -> ROM_LO <= a -> a + Z.of_nat (length bs) <= ROM_HI ->
  rdn R_segs (fun _ => None) (w64 a) (length bs) = Some bs ->
  mem_is R_segs M a bs.
Proof. intros. eapply rom_isG; try eassumption; unfold ROM_LO, ROM_HI in *; lia. Qed.

Lemma rom_u64 : forall M a e,
  rom_ok M -> ROM_LO <= a -> a + 8 <= ROM_HI ->
  rdn R_segs (fun _ => None) (w64 a) 8 = Some (Z_to_le_bytes 8 e) -> mem_u64 R_segs M a e.
Proof. intros. unfold mem_u64. apply rom_is; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma rom_u32 : forall M a e,
  rom_ok M -> ROM_LO <= a -> a + 4 <= ROM_HI ->
  rdn R_segs (fun _ => None) (w64 a) 4 = Some (Z_to_le_bytes 4 e) -> mem_u32 R_segs M a e.
Proof. intros. unfold mem_u32. apply rom_is; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma rom_u16 : forall M a e,
  rom_ok M -> ROM_LO <= a -> a + 2 <= ROM_HI ->
  rdn R_segs (fun _ => None) (w64 a) 2 = Some (Z_to_le_bytes 2 e) -> mem_u16 R_segs M a e.
Proof. intros. unfold mem_u16. apply rom_is; rewrite ?length_Z_to_le_bytes'; assumption. Qed.
Lemma rom_u8 : forall M a e,
  rom_ok M -> ROM_LO <= a -> a + 1 <= ROM_HI ->
  rdn R_segs (fun _ => None) (w64 a) 1 = Some (Z_to_le_bytes 1 e) -> mem_u8 R_segs M a e.
Proof. intros. unfold mem_u8. apply rom_is; rewrite ?length_Z_to_le_bytes'; assumption. Qed.

End FXG.
Ltac rom_fact_tac :=
  lazymatch goal with
  | |- mem_u64 _ ?M _ _ => eapply rom_u64
  | |- mem_u32 _ ?M _ _ => eapply rom_u32
  | |- mem_u16 _ ?M _ _ => eapply rom_u16
  | |- mem_u8 _ ?M _ _ => eapply rom_u8
  | |- mem_is _ ?M _ _ => eapply rom_is
  end;
  [ match goal with H : rom_ok _ |- _ => exact H end
  | unfold ROM_LO; lia
  | unfold ROM_HI; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; zlen_norm; lia
  | lazymatch goal with
    | |- ?G => apply (@bool_decide_eq_true_1 G _);
              first [ assert_succeeds (vm_compute; reflexivity) | fail 1 "rom_fact: the image does not contain these bytes" ];
              vm_cast_no_check (@eq_refl bool true)
    end ].
Tactic Notation "rom_fact" constr(P) "as" ident(H) := assert (H : P) by rom_fact_tac.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma rom_ok_magree : forall M0 M lo1 hi1 lo2 hi2,
  rom_ok M0 -> magree M0 M lo1 hi1 lo2 hi2 -> (ROM_HI <= lo1 \/ hi1 <= ROM_LO) -> (ROM_HI <= lo2 \/ hi2 <= ROM_LO) -> rom_ok M.
Proof. intros. eapply rom_okG_magree; eassumption. Qed.
Lemma rom_ok_magreeL : forall M0 M rs,
  rom_ok M0 -> magreeL M0 M rs -> disj_all ROM_LO (ROM_HI - ROM_LO) rs -> rom_ok M.
Proof. intros. eapply rom_okG_magreeL; eassumption. Qed.
Lemma rom_ok_zzero : forall M a n,
  rom_ok M -> 0 <= a -> a + n < two64 -> 0 <= n -> (a + n <= ROM_LO \/ ROM_HI <= a) -> rom_ok (zzero M a n).
Proof. intros. apply rom_okG_zzero; assumption. Qed.
Lemma rom_ok_zunmap : forall M a n,
  rom_ok M -> 0 <= a -> a + n < two64 -> 0 <= n -> (a + n <= ROM_LO \/ ROM_HI <= a) -> rom_ok (zunmap M a n).
Proof. intros. apply rom_okG_zunmap; assumption. Qed.

End FXG.
Ltac zreattach_extra HA Mo Mn ::=
  try match goal with
  | H : rom_ok Mo |- _ =>
      first [ let H' := fresh in
              pose proof (rom_ok_magree Mo Mn _ _ _ _ H HA ltac:(unfold ROM_LO, ROM_HI; zlia) ltac:(unfold ROM_LO, ROM_HI; zlia)) as H';
              clear H; rename H' into H
            | idtac "zreattach: dropped rom_ok"; clear H ]
  end.
Ltac zreattachL_extra HA Mo Mn ::=
  try match goal with
  | H : rom_ok Mo |- _ =>
      first [ let H' := fresh in
              pose proof (rom_ok_magreeL Mo Mn _ H HA ltac:(unfold ROM_LO, ROM_HI; disj_all_tac)) as H';
              clear H; rename H' into H
            | idtac "zreattachL: dropped rom_ok"; clear H ]
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac zmem_transport_zero M a n ::=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_zzero_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_zzero_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_zzero_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_zzero_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_zzero_frame segs M a n a' bs') in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_zzero_frame segs M a n a' len) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_zzero_mono segs M a n a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_zzero M a n) in H; [| zlia | zlia | zlia | unfold ROM_LO, ROM_HI; zlia ]
            | idtac "WARNING: rom_ok dropped at zero-fill" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_transport_unmap M a n :=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_zunmap_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_zunmap_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_zunmap_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_zunmap_frame segs M a n a' e) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_zunmap_frame segs M a n a' bs') in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_zunmap_frame segs M a n a' len) in H; [|zdisj_tac|zlia] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      first [ apply (mem_wr_zunmap_frame segs M a n a' len) in H; [|zdisj_tac|zlia] | clear H ]
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_zunmap M a n) in H; [| zlia | zlia | zlia | unfold ROM_LO, ROM_HI; zlia ]
            | idtac "WARNING: rom_ok dropped at unmap" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Ltac zmem_post_unmap :=
  lazymatch goal with
  | |- realizes ?segs (zcfg _ ?pc ?R (zunmap ?M ?a ?n) ?MD) ?T =>
      zmem_transport_unmap M a n;
      let Mn := fresh "M" in
      set (Mn := zunmap M a n) in *;
      clearbody Mn; try clear M
  end.
Ltac zmem_transport M a bs ::=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_tac] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_frame segs M a bs a' len) in H; [|zdisj_tac]
            | let H1 := fresh "Zl" in let H2 := fresh "Zh" in
              destruct (mem_zero_split_store segs M a bs a' len H ltac:(zlia) ltac:(zlen_norm; zlia) ltac:(zlia) ltac:(zlia) ltac:(zlen_norm; zlia)) as [H1 H2];
              clear H;
              rewrite ?length_app, ?repeat_length, ?length_map, ?length_Z_to_le_bytes', ?Nat2Z.inj_add in H2;
              cbn [length] in H1, H2; znat_lits_in H1; znat_lits_in H2; zfold_in H1; zfold_in H2;
              znorm_zero_len H1; znorm_zero_len H2;
              try (lazymatch type of H1 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H1 end end);
              try (lazymatch type of H2 with mem_zero _ _ _ ?z => lazymatch z with 0 => clear H2 end end)
            | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rom_ok M |- _ =>
      first [ apply (rom_ok_frame M a bs) in H; [| zlia | zlen_norm; zlia | unfold ROM_LO, ROM_HI; zdisj_tac]
            | idtac "WARNING: rom_ok dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable ?Fr ?lo ?hi |- _ =>
      first [ apply (HS M a bs) in H; [|zlia|zlen_norm; zlia]
            | idtac "WARNING: framed fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stable2 ?Fr _ _ _ _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; zlia]
            | idtac "WARNING: framed2 fact dropped at store" a; clear H ]
  | H : framed ?Fr M, HS : wb_stableL ?Fr _ |- _ =>
      first [ apply (HS M a bs) in H; [|zlen_norm; in_some_tac]
            | idtac "WARNING: framedL fact dropped at store" a; clear H ]
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.











Definition lbase_bytes : list byte := [Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 163; Z_to_bv 8 0; Z_to_bv 8 195; Z_to_bv 8 0; Z_to_bv 8 227; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_lbase : forall M, rom_ok M -> mem_is R_segs M 75186 lbase_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 75186 lbase_bytes) as H. exact H. Qed.

Definition lext_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 71; Z_to_bv 8 0; Z_to_bv 8 77; Z_to_bv 8 0].
Lemma rom_lext : forall M, rom_ok M -> mem_is R_segs M 75248 lext_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 75248 lext_bytes) as H. exact H. Qed.

Definition dbase_bytes : list byte := [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 33; Z_to_bv 8 0; Z_to_bv 8 49; Z_to_bv 8 0; Z_to_bv 8 65; Z_to_bv 8 0; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 129; Z_to_bv 8 0; Z_to_bv 8 193; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 129; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 3; Z_to_bv 8 1; Z_to_bv 8 4; Z_to_bv 8 1; Z_to_bv 8 6; Z_to_bv 8 1; Z_to_bv 8 8; Z_to_bv 8 1; Z_to_bv 8 12; Z_to_bv 8 1; Z_to_bv 8 16; Z_to_bv 8 1; Z_to_bv 8 24; Z_to_bv 8 1; Z_to_bv 8 32; Z_to_bv 8 1; Z_to_bv 8 48; Z_to_bv 8 1; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_dbase : forall M, rom_ok M -> mem_is R_segs M 75310 dbase_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 75310 dbase_bytes) as H. exact H. Qed.

Definition dext_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 0].
Lemma rom_dext : forall M, rom_ok M -> mem_is R_segs M 75374 dext_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 75374 dext_bytes) as H. exact H. Qed.




Fixpoint allb (f : Z -> bool) (i : Z) (n : nat) : bool :=
  match n with O => true | S n' => f i && allb f (i + 1) n' end.
Lemma allb_spec : forall f n i, allb f i n = true -> forall j, i <= j < i + Z.of_nat n -> f j = true.
Proof.
  intros f n. induction n as [|n IH]; intros i H j Hj; [lia|].
  cbn [allb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec j i) as [->|Hne]; [exact H1|]. apply (IH (i + 1) H2). lia.
Qed.

  Definition lbase_f (i : Z) : Z := le_cell 2 lbase_bytes i.
Definition lext_f (i : Z) : Z := le_cell 2 lext_bytes i.
Definition dbase_f (i : Z) : Z := le_cell 2 dbase_bytes i.
Definition dext_f (i : Z) : Z := le_cell 2 dext_bytes i.
Lemma rom_lbase_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 75186 31 lbase_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 75186 31 _ (rom_lbase M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_lext_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 75248 31 lext_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 75248 31 _ (rom_lext M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_dbase_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 75310 32 dbase_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 75310 32 _ (rom_dbase M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_dext_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 75374 32 dext_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 75374 32 _ (rom_dext M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.

Lemma lbase_f_model : forall i, 0 <= i < 31 -> lbase_f i = ZIface.arr_get Inftrees.lbase_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => lbase_f i =? ZIface.arr_get Inftrees.lbase_a i) 31 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
Lemma lext_f_model : forall i, 0 <= i < 31 -> lext_f i = ZIface.arr_get Inftrees.lext_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => lext_f i =? ZIface.arr_get Inftrees.lext_a i) 31 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
Lemma dbase_f_model : forall i, 0 <= i < 32 -> dbase_f i = ZIface.arr_get Inftrees.dbase_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => dbase_f i =? ZIface.arr_get Inftrees.dbase_a i) 32 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
Lemma dext_f_model : forall i, 0 <= i < 32 -> dext_f i = ZIface.arr_get Inftrees.dext_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => dext_f i =? ZIface.arr_get Inftrees.dext_a i) 32 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.



End FXG.
