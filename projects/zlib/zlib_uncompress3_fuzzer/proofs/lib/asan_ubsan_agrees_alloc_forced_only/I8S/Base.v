(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg StreamSim WsegFast.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState Inftrees.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Export ZSysLite ZCall ZCallL TSet ZArr ZRd ZRom.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.I8S Require Export i8s_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Abbreviation R := R_segs (only parsing).
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Definition ROM_LO : Z := 65536.
Definition ROM_HI : Z := 135168.
Definition DATA_LO : Z := 139264.
Definition DATA_LEN : Z := 466944.
Definition BUF : Z := 208656.
Definition BUF_N : Z := 262144.
Definition A_MEMCPY : Z := 131564.
Definition A_ADLER32 : Z := 95836.
Definition A_ADLER32Z : Z := 94872.
Definition A_ZCALLOC : Z := 94848.
Definition A_ZCFREE : Z := 94864.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

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
Lemma rom_ok_of_hyp : forall M, (forall i, ROM_LO <= i < ROM_HI -> M (Z_to_bv 64 i) = None) -> rom_ok M.
Proof. intros. apply rom_okG_of_hyp; [unfold ROM_LO; lia | unfold ROM_HI; rewrite two64_eq; lia | assumption]. Qed.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

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
Section FXG. Context {fx : OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.PropExec.FPState}.

Lemma data_wseg : wseg_ok R_segs (Z_to_bv 64 DATA_LO) (Z.to_nat DATA_LEN) = true.
Proof. apply wseg_fast_sound. vm_cast_no_check (@eq_refl bool true). Qed.

Lemma data_writable : forall M, mem_wr R_segs M DATA_LO DATA_LEN.
Proof.
  intros M. apply mem_wr_of_range_writable_Z; [unfold DATA_LEN; lia|].
  unfold range_writable_b, w64. exact data_wseg.
Qed.

Lemma buf_writable : forall M, mem_wr R_segs M BUF BUF_N.
Proof. intros M. eapply mem_wr_sub; [apply data_writable | unfold BUF, DATA_LO; lia | unfold BUF, BUF_N, DATA_LO, DATA_LEN; lia]. Qed.

Lemma buf_store_ok : forall M, store_ok R_segs M (Z_to_bv 64 BUF) (Z.to_nat BUF_N) = true.
Proof.
  intros M. eapply store_ok_sub; [ | apply store_ok_wseg, data_wseg | | ];
  rewrite ?Z_to_bv_unsigned; unfold BUF, BUF_N, DATA_LO, DATA_LEN; apply Z.leb_le; vm_compute; reflexivity.
Qed.

Lemma wr_rd_R : wr_rd_ok R_segs.
Proof.
  assert (E : forallb (fun s => negb (seg_writable s) || seg_readable s) R_segs = true) by (vm_compute; reflexivity).
  intros seg Hin Hw. rewrite forallb_forall in E. specialize (E seg Hin). rewrite Hw in E. cbn in E. exact E.
Qed.

Lemma img_readable : forall M a n,
  DATA_LO <= a -> 0 <= n -> a + n <= DATA_LO + DATA_LEN ->
  exists bs, mem_is R_segs M a bs /\ Z.of_nat (length bs) = n.
Proof.
  intros M a n H1 H2 H3. apply (mem_wr_readable R_segs wr_rd_R); [| exact H2].
  eapply mem_wr_sub; [apply data_writable | lia | lia].
Qed.

Lemma out_arr_exists : forall M, exists f, mem_arr 1 R_segs M BUF BUF_N f /\ (forall i, 0 <= f i < 256).
Proof.
  intros M. apply (mem_wr_arr_exists R_segs wr_rd_R M BUF BUF_N (buf_writable M)); unfold BUF, BUF_N; rewrite ?two64_eq; lia.
Qed.

Definition mem_wr_arr_exists_R := mem_wr_arr_exists R_segs wr_rd_R.
Definition mem_wr_u32_exists_R := mem_wr_u32_exists R_segs wr_rd_R.
Definition mem_wr_u64_exists_R := mem_wr_u64_exists R_segs wr_rd_R.
Definition mem_wr_readable_R := mem_wr_readable R_segs wr_rd_R.


Definition order_addr : Z := 67132.
Definition order_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 15; Z_to_bv 8 0].
Lemma rom_order : forall M, rom_ok M -> mem_is R_segs M 67132 order_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67132 order_bytes) as H. exact H. Qed.

Definition lenfix_addr : Z := 67422.
Definition lenfix_bytes : list byte := [Z_to_bv 8 96; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 8; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 112; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 48; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 192; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 32; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 160; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 64; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 224; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 88; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 144; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 56; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 208; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 104; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 40; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 176; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 136; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 72; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 240; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 84; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 227; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 116; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 52; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 200; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 100; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 36; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 168; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 132; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 68; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 232; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 92; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 152; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 124; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 60; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 216; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 108; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 44; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 184; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 140; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 76; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 248; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 82; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 163; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 114; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 50; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 196; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 98; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 34; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 164; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 130; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 66; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 228; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 90; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 148; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 122; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 58; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 212; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 106; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 42; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 180; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 138; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 74; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 244; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 86; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 118; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 54; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 204; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 102; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 38; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 172; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 134; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 70; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 236; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 94; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 156; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 126; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 62; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 220; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 110; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 46; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 188; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 142; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 78; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 252; Z_to_bv 8 0; Z_to_bv 8 96; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 113; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 49; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 194; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 33; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 162; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 129; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 65; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 226; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 89; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 146; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 121; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 57; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 210; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 105; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 41; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 178; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 137; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 73; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 242; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 85; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 8; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 117; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 53; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 202; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 101; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 170; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 133; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 69; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 234; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 93; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 154; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 125; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 61; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 218; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 109; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 45; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 186; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 141; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 77; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 250; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 195; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 198; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 166; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 230; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 91; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 150; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 123; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 214; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 107; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 182; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 139; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 75; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 246; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 87; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 119; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 55; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 206; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 103; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 39; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 174; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 135; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 71; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 238; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 95; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 158; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 127; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 63; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 222; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 111; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 47; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 190; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 143; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 254; Z_to_bv 8 0; Z_to_bv 8 96; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 8; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 112; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 48; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 193; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 32; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 161; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 128; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 64; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 225; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 88; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 145; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 120; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 56; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 209; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 104; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 40; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 177; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 136; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 72; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 241; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 84; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 227; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 116; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 52; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 201; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 100; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 36; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 169; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 132; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 68; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 233; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 92; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 153; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 124; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 60; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 217; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 108; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 44; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 185; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 12; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 140; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 76; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 249; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 82; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 163; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 114; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 50; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 197; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 98; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 34; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 165; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 130; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 66; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 229; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 90; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 149; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 122; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 58; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 213; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 106; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 42; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 181; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 138; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 74; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 245; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 86; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 118; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 54; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 205; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 102; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 38; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 173; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 134; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 70; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 237; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 94; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 30; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 157; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 126; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 62; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 221; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 110; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 46; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 189; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 14; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 142; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 78; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 253; Z_to_bv 8 0; Z_to_bv 8 96; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 113; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 49; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 195; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 33; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 163; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 129; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 65; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 227; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 89; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 147; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 121; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 57; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 211; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 105; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 41; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 179; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 137; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 73; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 243; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 85; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 8; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 117; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 53; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 203; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 101; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 37; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 171; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 133; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 69; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 235; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 93; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 155; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 125; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 61; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 219; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 109; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 45; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 187; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 141; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 77; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 251; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 8; Z_to_bv 8 195; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 199; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 167; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 231; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 91; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 151; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 123; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 215; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 107; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 183; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 139; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 75; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 247; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 87; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 7; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 119; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 55; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 207; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 7; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 103; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 39; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 175; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 135; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 71; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 239; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 7; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 95; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 159; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 7; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 127; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 63; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 223; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 7; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 111; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 47; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 191; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 143; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 255; Z_to_bv 8 0].
Lemma rom_lenfix : forall M, rom_ok M -> mem_is R_segs M 67422 lenfix_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67422 lenfix_bytes) as H. exact H. Qed.

Definition distfix_addr : Z := 69470.
Definition distfix_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 19; Z_to_bv 8 5; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 16; Z_to_bv 8 17; Z_to_bv 8 5; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 4; Z_to_bv 8 21; Z_to_bv 8 5; Z_to_bv 8 65; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 64; Z_to_bv 8 16; Z_to_bv 8 5; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 2; Z_to_bv 8 20; Z_to_bv 8 5; Z_to_bv 8 33; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 32; Z_to_bv 8 18; Z_to_bv 8 5; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 8; Z_to_bv 8 22; Z_to_bv 8 5; Z_to_bv 8 129; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 5; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 5; Z_to_bv 8 129; Z_to_bv 8 1; Z_to_bv 8 19; Z_to_bv 8 5; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 24; Z_to_bv 8 17; Z_to_bv 8 5; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 6; Z_to_bv 8 21; Z_to_bv 8 5; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 96; Z_to_bv 8 16; Z_to_bv 8 5; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 3; Z_to_bv 8 20; Z_to_bv 8 5; Z_to_bv 8 49; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 48; Z_to_bv 8 18; Z_to_bv 8 5; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 5; Z_to_bv 8 1; Z_to_bv 8 12; Z_to_bv 8 22; Z_to_bv 8 5; Z_to_bv 8 193; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_distfix : forall M, rom_ok M -> mem_is R_segs M 69470 distfix_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 69470 distfix_bytes) as H. exact H. Qed.

Definition lbase_addr : Z := 67170.
Definition lbase_bytes : list byte := [Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 6; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 10; Z_to_bv 8 0; Z_to_bv 8 11; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 15; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 31; Z_to_bv 8 0; Z_to_bv 8 35; Z_to_bv 8 0; Z_to_bv 8 43; Z_to_bv 8 0; Z_to_bv 8 51; Z_to_bv 8 0; Z_to_bv 8 59; Z_to_bv 8 0; Z_to_bv 8 67; Z_to_bv 8 0; Z_to_bv 8 83; Z_to_bv 8 0; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 115; Z_to_bv 8 0; Z_to_bv 8 131; Z_to_bv 8 0; Z_to_bv 8 163; Z_to_bv 8 0; Z_to_bv 8 195; Z_to_bv 8 0; Z_to_bv 8 227; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_lbase : forall M, rom_ok M -> mem_is R_segs M 67170 lbase_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67170 lbase_bytes) as H. exact H. Qed.

Definition lext_addr : Z := 67232.
Definition lext_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 71; Z_to_bv 8 0; Z_to_bv 8 77; Z_to_bv 8 0].
Lemma rom_lext : forall M, rom_ok M -> mem_is R_segs M 67232 lext_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67232 lext_bytes) as H. exact H. Qed.

Definition dbase_addr : Z := 67294.
Definition dbase_bytes : list byte := [Z_to_bv 8 1; Z_to_bv 8 0; Z_to_bv 8 2; Z_to_bv 8 0; Z_to_bv 8 3; Z_to_bv 8 0; Z_to_bv 8 4; Z_to_bv 8 0; Z_to_bv 8 5; Z_to_bv 8 0; Z_to_bv 8 7; Z_to_bv 8 0; Z_to_bv 8 9; Z_to_bv 8 0; Z_to_bv 8 13; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 33; Z_to_bv 8 0; Z_to_bv 8 49; Z_to_bv 8 0; Z_to_bv 8 65; Z_to_bv 8 0; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 129; Z_to_bv 8 0; Z_to_bv 8 193; Z_to_bv 8 0; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 129; Z_to_bv 8 1; Z_to_bv 8 1; Z_to_bv 8 2; Z_to_bv 8 1; Z_to_bv 8 3; Z_to_bv 8 1; Z_to_bv 8 4; Z_to_bv 8 1; Z_to_bv 8 6; Z_to_bv 8 1; Z_to_bv 8 8; Z_to_bv 8 1; Z_to_bv 8 12; Z_to_bv 8 1; Z_to_bv 8 16; Z_to_bv 8 1; Z_to_bv 8 24; Z_to_bv 8 1; Z_to_bv 8 32; Z_to_bv 8 1; Z_to_bv 8 48; Z_to_bv 8 1; Z_to_bv 8 64; Z_to_bv 8 1; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_dbase : forall M, rom_ok M -> mem_is R_segs M 67294 dbase_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67294 dbase_bytes) as H. exact H. Qed.

Definition dext_addr : Z := 67358.
Definition dext_bytes : list byte := [Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 16; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 17; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 18; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 19; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 20; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 21; Z_to_bv 8 0; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 22; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 23; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 24; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 25; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 26; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 27; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 28; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 29; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 0; Z_to_bv 8 64; Z_to_bv 8 0].
Lemma rom_dext : forall M, rom_ok M -> mem_is R_segs M 67358 dext_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67358 dext_bytes) as H. exact H. Qed.

Definition jtab_addr : Z := 67008.
Definition jtab_bytes : list byte := [Z_to_bv 8 164; Z_to_bv 8 78; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 76; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 168; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 184; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 196; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 120; Z_to_bv 8 92; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 136; Z_to_bv 8 94; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 84; Z_to_bv 8 96; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 100; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 148; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 220; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 236; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 180; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 160; Z_to_bv 8 82; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 168; Z_to_bv 8 82; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 8; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 40; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 84; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 92; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 100; Z_to_bv 8 97; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 12; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 176; Z_to_bv 8 99; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 92; Z_to_bv 8 79; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 236; Z_to_bv 8 101; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 240; Z_to_bv 8 78; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 220; Z_to_bv 8 80; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 56; Z_to_bv 8 81; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 168; Z_to_bv 8 106; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 124; Z_to_bv 8 104; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 172; Z_to_bv 8 105; Z_to_bv 8 0; Z_to_bv 8 0].
Lemma rom_jtab : forall M, rom_ok M -> mem_is R_segs M 67008 jtab_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 67008 jtab_bytes) as H. exact H. Qed.

Definition mod31_addr : Z := 66928.
Definition mod31_bytes : list byte := [Z_to_bv 8 17; Z_to_bv 8 66; Z_to_bv 8 8; Z_to_bv 8 33; Z_to_bv 8 132; Z_to_bv 8 16; Z_to_bv 8 66; Z_to_bv 8 8].
Lemma rom_mod31 : forall M, rom_ok M -> mem_is R_segs M 66928 mod31_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 66928 mod31_bytes) as H. exact H. Qed.

Definition adlmag_addr : Z := 66920.
Definition adlmag_bytes : list byte := [Z_to_bv 8 205; Z_to_bv 8 197; Z_to_bv 8 47; Z_to_bv 8 13; Z_to_bv 8 225; Z_to_bv 8 0; Z_to_bv 8 15; Z_to_bv 8 0].
Lemma rom_adlmag : forall M, rom_ok M -> mem_is R_segs M 66920 adlmag_bytes.
Proof. intros M HR. rom_fact (mem_is R_segs M 66920 adlmag_bytes) as H. exact H. Qed.

Fixpoint allb (f : Z -> bool) (i : Z) (n : nat) : bool :=
  match n with O => true | S n' => f i && allb f (i + 1) n' end.
Lemma allb_spec : forall f n i, allb f i n = true -> forall j, i <= j < i + Z.of_nat n -> f j = true.
Proof.
  intros f n. induction n as [|n IH]; intros i H j Hj; [lia|].
  cbn [allb] in H. apply andb_prop in H as [H1 H2].
  destruct (Z.eq_dec j i) as [->|Hne]; [exact H1|]. apply (IH (i + 1) H2). lia.
Qed.

Definition order_f (i : Z) : Z := le_cell 2 order_bytes i.
Definition lenfix_f (i : Z) : Z := le_cell 4 lenfix_bytes i.
Definition distfix_f (i : Z) : Z := le_cell 4 distfix_bytes i.
Definition lbase_f (i : Z) : Z := le_cell 2 lbase_bytes i.
Definition lext_f (i : Z) : Z := le_cell 2 lext_bytes i.
Definition dbase_f (i : Z) : Z := le_cell 2 dbase_bytes i.
Definition dext_f (i : Z) : Z := le_cell 2 dext_bytes i.
Definition jtab_off (i : Z) : Z := le_cell 4 jtab_bytes i.
Definition jtab_f (i : Z) : Z := jtab_addr + bv_swrap 32 (jtab_off i).

Lemma rom_order_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 67132 19 order_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 67132 19 _ (rom_order M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_lenfix_arr : forall M, rom_ok M -> mem_arr 4 R_segs M 67422 512 lenfix_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 4 M 67422 512 _ (rom_lenfix M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_distfix_arr : forall M, rom_ok M -> mem_arr 4 R_segs M 69470 32 distfix_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 4 M 69470 32 _ (rom_distfix M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_lbase_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 67170 31 lbase_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 67170 31 _ (rom_lbase M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_lext_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 67232 31 lext_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 67232 31 _ (rom_lext M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_dbase_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 67294 32 dbase_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 67294 32 _ (rom_dbase M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_dext_arr : forall M, rom_ok M -> mem_arr 2 R_segs M 67358 32 dext_f.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 2 M 67358 32 _ (rom_dext M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.
Lemma rom_jtab_arr : forall M, rom_ok M -> mem_arr 4 R_segs M 67008 31 jtab_off.
Proof. intros M H. apply (mem_arr_of_bytes R_segs 4 M 67008 31 _ (rom_jtab M H)); try (cbn; lia); rewrite two64_eq; cbn; lia. Qed.

Lemma lenfix_f_model : forall i, 0 <= i < 512 -> lenfix_f i = ZIface.arr_get InflateState.lenfix_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => lenfix_f i =? ZIface.arr_get InflateState.lenfix_a i) 512 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
Lemma distfix_f_model : forall i, 0 <= i < 32 -> distfix_f i = ZIface.arr_get InflateState.distfix_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => distfix_f i =? ZIface.arr_get InflateState.distfix_a i) 32 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
Lemma order_f_model : forall i, 0 <= i < 19 -> order_f i = ZIface.arr_get InflateState.order_a i.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => order_f i =? ZIface.arr_get InflateState.order_a i) 19 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.
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

Lemma order_f_range : forall i, 0 <= i < 19 -> 0 <= order_f i <= 18.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => (0 <=? order_f i) && (order_f i <=? 18)) 19 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma lbase_f_range : forall i, 0 <= i < 31 -> 0 <= lbase_f i <= 258.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => (0 <=? lbase_f i) && (lbase_f i <=? 258)) 31 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma lext_f_range : forall i, 0 <= i < 31 -> 16 <= lext_f i <= 203.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => (16 <=? lext_f i) && (lext_f i <=? 203)) 31 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma dbase_f_range : forall i, 0 <= i < 32 -> 0 <= dbase_f i <= 24577.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => (0 <=? dbase_f i) && (dbase_f i <=? 24577)) 32 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.
Lemma dext_f_range : forall i, 0 <= i < 32 -> 16 <= dext_f i <= 64.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => (16 <=? dext_f i) && (dext_f i <=? 64)) 32 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply andb_prop in E as [A B]. apply Z.leb_le in A. apply Z.leb_le in B. lia.
Qed.

Definition jtab_targets : list Z := [87140; 87564; 87400; 87672; 87684; 90680; 91208; 91440; 91668; 87332; 87892; 87964; 87980; 87412; 88160; 88168; 87496; 87784; 87316; 91932; 91940; 87244; 92528; 87324; 93100; 87216; 87708; 87800; 94312; 93756; 94060].
Lemma jtab_f_targets : forall i, 0 <= i < 31 -> jtab_f i = nth (Z.to_nat i) jtab_targets 0.
Proof.
  intros i Hi. pose proof (allb_spec (fun i => jtab_f i =? nth (Z.to_nat i) jtab_targets 0) 31 0
    ltac:(vm_compute; reflexivity) i ltac:(lia)) as E. apply Z.eqb_eq in E. exact E.
Qed.

Lemma rom_mod31_u64 : forall M, rom_ok M -> mem_u64 R_segs M 66928 595056260442243601.
Proof. intros M HR. rom_fact (mem_u64 R_segs M 66928 595056260442243601) as H. exact H. Qed.
Lemma rom_adlmag_u64 : forall M, rom_ok M -> mem_u64 R_segs M 66920 4223091239536077.
Proof. intros M HR. rom_fact (mem_u64 R_segs M 66920 4223091239536077) as H. exact H. Qed.
End FXG.
