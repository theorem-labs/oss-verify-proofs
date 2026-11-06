(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Fs.ReadWrite.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SimInv ExitSim CatSim WallSim.

Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_StreamSim () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.Monad.outcome"; "LinuxProcessSemantics.LinuxProcessSem.State.SyscallEffect"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.iff"; "LinuxProcessSemantics.LinuxProcessSem.Specs.syscall_spec"; "LinuxProcessSemantics.LinuxProcessSem.Run.sys_input"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.ReadWrite.read_spec"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Syscall.fd32"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "LinuxProcessSemantics.LinuxProcessSem.State.fd_lookup"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fds"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.Some"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "M_loop"; "LinuxProcessSemantics.LinuxProcessSem.State.with_stdin"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.State.InputStream"; "LinuxProcessSemantics.LinuxProcessSem.State.stream_take"; "LinuxProcessSemantics.LinuxProcessSem.State.m_stdin"; "Corelib.Init.Datatypes.bool"; "wseg_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_aux"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_writable_byte"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "LinuxProcessSemantics.LinuxProcessSem.State.read_bytes_map"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.rw_bytes_max"; "LinuxProcessSemantics.LinuxProcessSem.State.in_wmem"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "Corelib.Init.Datatypes.fst"; "LinuxProcessSemantics.LinuxProcessSem.State.stream_take_z"; "LinuxProcessSemantics.LinuxProcessSem.State.rw_count_clamp"; "LinuxProcessSemantics.LinuxProcessSem.State.IEof"; "LinuxProcessSemantics.LinuxProcessSem.State.access_okb"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.check_result"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Fs.ReadWrite.check_read"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "LinuxProcessSemantics.LinuxProcessSem.Checks.Sys.Prelude.CheckOk"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Lists.ListDef.map"; "LinuxProcessSemantics.LinuxProcessSem.State.ReadEv"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Ok"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.Monad.Unmodeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.step_to"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "LinuxProcessSemantics.LinuxProcessSem.Run.sstep"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "LinuxProcessSemantics.LinuxProcessSem.Run.SNext"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "LinuxProcessSemantics.LinuxProcessSem.Run.apply_effect"; "chunks"; "Corelib.Init.Datatypes.app"; "LinuxProcessSemantics.LinuxProcessSem.Run.is_prefix"; "Stdlib.Lists.List.flat_map"; "iter_ev_ch"; "eof_tail"; "LinuxProcessSemantics.LinuxProcessSem.Fs.Fs"; "stream_traces_ch"; "stream_traces"; "OSSVerify.KrLib.ABoot.ExitSim.to_exit"; "Loop.to_wr"; "Loop.to_rd"; "Loop.ReadPend"; "LinuxProcessSemantics.LinuxProcessSem.Run.star"; "Loop.WrPend"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "iter_ev"; "LinuxProcessSemantics.LinuxProcessSem.State.m_fs"; "Corelib.Init.Peano.le"; "OSSVerify.KrLib.ABoot.CatSim.buf_modeled"; "OSSVerify.KrLib.ABoot.WallSim.to_wall_tail"; "Loop.lh_next"; "LinuxProcessSemantics.LinuxProcessSem.State.WriteEv"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_model"; "LinuxProcessSemantics.LinuxProcessSem.Run.cfg_ms"; "OSSVerify.KrLib.ABoot.ExitSim.on_path"; "Corelib.Numbers.BinNums.N"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "LinuxProcessSemantics.LinuxProcessSem.State.ProcInput"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.in_argv"; "LinuxProcessSemantics.LinuxProcessSem.State.in_envp"; "LinuxProcessSemantics.LinuxProcessSem.State.in_uid"; "LinuxProcessSemantics.LinuxProcessSem.State.in_hwcap"; "LinuxProcessSemantics.LinuxProcessSem.Run.obs_trace"; "LinuxProcessSemantics.LinuxProcessSem.Run.init_config"; "LinuxProcessSemantics.LinuxProcessSem.State.in_fs"; "LinuxProcessSemantics.LinuxProcessSem.State.in_stdin"; "LinuxProcessSemantics.LinuxProcessSem.Run.reaches_error"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_corun"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkEntry"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.never_errors"; "LinuxProcessSemantics.LinuxProcessSem.OmniRun.omni_cosafe"; "to_rd"; "LinuxProcessSemantics.EquivalenceDefinition.OmniEquivalence.omni_strong_equiv"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.modeled"; "LinuxProcessSemantics.LinuxProcessSem.Run.run"; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.equiv"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_arg1_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 1 = ms_gpr ms 1.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma syscall_spec_read : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Po,(5.$6.)P,(7.$8.(9.&40.R3.)+3?.)(:.(;.(<.R6.R5.R4.)R3.R2.)(=.(>.(?.R5.#0.))(?.R5.#1.)(?.R5.#2.)(<.R6.R5.R4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 model o Hno.
  unfold syscall_spec, dispatch.
  change (in_sysno (sys_input segs ms x8)) with x8.
  rewrite Hno. reflexivity.
Qed.

Lemma in_arg2_sys_input : forall segs ms x8,
  in_arg (sys_input segs ms x8) 2 = ms_gpr ms 2.
Proof. reflexivity. Qed.

Lemma in_wmem_sys_input : forall segs ms x8,
  in_wmem (sys_input segs ms x8) = ms_writable_byte segs ms.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma band0_255 : bv_and (Z_to_bv 64 0) (Z_to_bv 64 255) = Z_to_bv 64 0.
Proof.
  apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_fs_with_stdin : forall s m, m_fs (with_stdin s m) = m_fs m.
Proof. reflexivity. Qed.

Lemma m_halted_with_stdin : forall s m, m_halted (with_stdin s m) = m_halted m.
Proof. reflexivity. Qed.

Lemma m_fds_with_stdin : forall s m, m_fds (with_stdin s m) = m_fds m.
Proof. reflexivity. Qed.

Lemma m_vm_lazy_with_stdin : forall s m,
  m_vm_lazy (with_stdin s m) = m_vm_lazy m.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition M_loop (model : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "(10.(7.(11.$12.)(13.(14.O1.)(15.&40.=))(16.$12.(17.(15.&40.=))))(10.(7.(11.$12.)(13.(14.O1.)(15.&40.+1.))(16.$12.(17.(15.&40.+1.))))(10.(7.(11.(3.&40.))(18.O1.)(19.(3.&40.)))(7.(0.(1:.(3.&40.)(3.&40.)))(1;.O1.)(1<.(1:.(3.&40.)(3.&40.)))))))")
(* [comment removed for export] *).

Lemma init_M_loop : forall reserved brk0 mb sp lim inp,
  M_loop (init_model reserved brk0 mb sp lim inp).
Proof. intros reserved brk0 mb sp lim inp. repeat split. Qed.

(* [comment removed for export] *)
Lemma M_loop_take : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pk,$1=.Pmodel,$4.P,(1>.R1.)(1>.(1?.(20.(0.(3.&8.))$21.(22.(23.R2.)R3.))R2.))")
(* [comment removed for export] *).
Proof. intros k model (H0 & H1 & Hh & Hlazy). repeat split; assumption. Qed.

Lemma M_loop_fd1chan : forall model, M_loop model -> fd1chan model.
Proof. intros model (H0 & H1 & Hh & Hlazy). exact H1. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint wseg_ok (segs : list Segment) (a : word) (n : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match find_segment segs (bv_unsigned a) 1 with
      | Some seg =>
          (seg_writable seg
           && match segment_byte_at (seg_bytes seg)
                      (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) with
              | Some _ => true
              | None => false
              end
           && wseg_ok segs (a + 1) n')%bool
      | None => false
      end
  end.

Lemma wseg_ok_read_aux : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Psegs,(0.$1.)Pn,$1=.Pa,(3.&40.)Pms,$2.P,(7.$24.(25.R4.R2.R3.)$26.)(27.(0.(3.&8.))Lw,(0.(3.&8.))(7.(11.(0.(3.&8.)))(28.(29.R6.R3.)R4.R5.)(16.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs n; induction n as [|n IH]; intros a ms H.
  - exists []. reflexivity.
  - cbn [wseg_ok] in H.
    destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:Hseg; [|discriminate].
    apply andb_true_iff in H as [H Hrec].
    apply andb_true_iff in H as [Hwr Hbyte].
    destruct (segment_byte_at (seg_bytes seg)
                (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))) as [b|] eqn:Hb;
      [|discriminate].
    destruct (IH (a + 1) ms Hrec) as [w Hw].
    cbn [read_bytes_aux].
    assert (Hdef : exists b0, ms_writable_byte segs ms a = Some b0).
    { unfold ms_writable_byte, wview. destruct (ms_mem ms a) as [b'|].
      - eexists; reflexivity.
      - rewrite Hseg, Hwr, Hb. eexists; reflexivity. }
    destruct Hdef as [b0 Hb0]. rewrite Hb0, Hw. eexists; reflexivity.
Qed.

Lemma wseg_ok_wdef : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Psegs,(0.$1.)Pa,(3.&40.)Plen,(3.&40.)Pms,$2.P,(7.$24.(25.R4.R3.(2:.R2.))$26.)(27.(0.(3.&8.))Lw,(0.(3.&8.))(7.(11.(0.(3.&8.)))(2;.(29.R6.R3.)R5.R4.)(16.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros segs a len ms H. rewrite read_bytes_map_eq.
  apply wseg_ok_read_aux. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma read0_wmem1 : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pw,(0.(3.&8.))P,(7.(11.(0.(3.&8.)))(2;.(29.R4.R3.)(?.R3.#1.)R6.)(16.(0.(3.&8.))R1.))(27.(0.(3.&8.))Lw1,(0.(3.&8.))(7.(11.(0.(3.&8.)))(2;.(2?.(<.R6.R5.R4.))(?.R5.#1.)(15.&40.+1.))(16.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 w Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt (Z_to_bv 64 1) w);
    [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn; lia | exact Hw].
Qed.

(* [comment removed for export] *)
Lemma read0_wmem_need : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pw,(0.(3.&8.))Ps,$21.P,(7.(11.(0.(3.&8.)))(2;.(29.R5.R4.)(?.R4.#1.)R7.)(16.(0.(3.&8.))R2.))(27.(0.(3.&8.))Lwn,(0.(3.&8.))(7.(11.(0.(3.&8.)))(2;.(2?.(<.R7.R6.R5.))(?.R6.#1.)(30.(3.&8.)(31.(0.(3.&8.))$21.(32.R3.(33.R9.)))))(16.(0.(3.&8.))R1.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 w s Hw. rewrite in_wmem_sys_input.
  eexists. apply (read_bytes_map_prefix _ _ cnt _ w); [|exact Hw].
  rewrite stream_take_z_eq.
  pose proof (stream_take_length (Z.to_nat (rw_count_clamp cnt)) s) as Hlen.
  pose proof (rw_count_clamp_range cnt) as Hcl.
  unfold len_word. rewrite Z_to_bv_unsigned, bv_wrap_small;
    unfold bv_modulus, MAX_RW_COUNT in *; cbn [Z.of_N] in *;
    [ | pose proof (bv_unsigned_in_range 64 cnt) ]; unfold rw_count_clamp in *; lia.
Qed.

Lemma read0_check_eof : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pw,(0.(3.&8.))P,(7.$8.(9.&40.R3.)+3?.)P,(7.(11.$12.)(13.(14.R3.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.$21.(23.R4.)$34.)P,(7.(3.&40.)(?.R7.#0.)(15.&40.=))P,(7.(3.&40.)(?.R8.#2.)R;.)P,(7.(11.(0.(3.&8.)))(2;.(29.R:.R9.)(?.R9.#1.)R<.)(16.(0.(3.&8.))R6.))P,(7.$24.(35.(?.R:.#1.)(9.&40.R=.))$26.)(7.$36.(37.(<.R<.R;.R:.)(>.(?.R;.#0.))(?.R;.#1.)(?.R;.#2.)(38.(15.&40.=)(1<.(1:.(3.&40.)(0.(3.&8.))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.)))R9.)(3:.R9.(1<.$3;.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  rewrite Heof. cbv beta iota.
  unfold check_ret_only. rewrite bv_eqb_refl. reflexivity.
Qed.

Lemma read0_check_bytes : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pw,(0.(3.&8.))Pbs,(0.(3.&8.))P,(7.$8.(9.&40.R4.)+3?.)P,(7.(11.$12.)(13.(14.R4.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.(3.&40.)(?.R7.#0.)(15.&40.=))P,(7.(3.&40.)(?.R8.#2.)R;.)P,(7.(11.(0.(3.&8.)))(2;.(29.R:.R9.)(?.R9.#1.)R<.)(16.(0.(3.&8.))R6.))P,(7.$24.(35.(?.R:.#1.)(9.&40.R=.))$26.)P,(2=.+1.(3<.(3=.(3.&8.)R7.)))P,(2=.(3<.(3=.(3.&8.)R8.))(9.&40.R?.))P,(7.(0.(3.&8.))(31.(0.(3.&8.))$21.(22.(23.R;.)(3=.(3.&8.)R9.)))R9.)(7.$36.(37.(<.R?.R>.R=.)(>.(?.R>.#0.))(?.R>.#1.)(?.R>.#2.)(38.(30.(3.&8.)R:.)(3>.(1:.(3.&40.)(0.(3.&8.)))(3?.(3.&40.)(0.(3.&8.))(?.R>.#1.)R:.)(1<.(1:.(3.&40.)(0.(3.&8.)))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.)))R<.)(3:.(1?.(20.(0.(3.&8.))$21.(22.(23.R<.)(3=.(3.&8.)R:.)))R<.)(40.(3.&8.)$3;.(41.(15.&40.=))R:.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  unfold check_read.
  rewrite Hg0; norm_fd32; rewrite Hfd.
  cbv beta iota.
  change (negb (w_is0 (Z_to_bv 64 0))) with false. cbv beta iota.
  rewrite Hg2, Haok.
  cbn [negb]. cbv beta iota. rewrite Hcnt0. cbv beta iota.
  (* [comment removed for export] *)
  destruct (m_stdin model) as [|b0 s0] eqn:Hs.
  { exfalso. rewrite stream_take_nil_of_eof in Hpre. subst bs. cbn in Hlo. lia. }
  cbv beta iota.
  rewrite Hw1. cbv beta iota.
  rewrite Hwn. cbv beta iota.
  rewrite !bv_eqb_refl.
  rewrite (proj2 (Z.leb_le 1 (Z.of_nat (length bs))) Hlo).
  rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)).
  rewrite (proj2 (Z.leb_le (Z.of_nat (length bs)) (bv_unsigned cnt)) Hhi).
  rewrite (proj2 (listN_eqb_eq _ _) Hpre).
  rewrite <- (in_wmem_sys_input segs ms x8) in Hw.
  assert (Hlek : (bv_unsigned (len_word bs) <= bv_unsigned cnt)%Z).
  { unfold len_word. pose proof (bv_unsigned_in_range 64 cnt) as Hr.
    rewrite Z_to_bv_unsigned, bv_wrap_small; [exact Hhi | lia]. }
  rewrite (wmem_ok_of_full _ _ _ _ _ Hw Hlek).
  reflexivity.
Qed.

Lemma read0_ok_eof : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pw,(0.(3.&8.))P,(7.$8.(9.&40.R3.)+3?.)P,(7.(11.$12.)(13.(14.R3.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.$21.(23.R4.)$34.)P,(7.(3.&40.)(?.R7.#0.)(15.&40.=))P,(7.(3.&40.)(?.R8.#2.)R;.)P,(7.(11.(0.(3.&8.)))(2;.(29.R:.R9.)(?.R9.#1.)R<.)(16.(0.(3.&8.))R6.))P,(7.$24.(35.(?.R:.#1.)(9.&40.R=.))$26.)(;.(<.R<.R;.R:.)R9.(42.$6.(38.(15.&40.=)(1<.(1:.(3.&40.)(0.(3.&8.))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.)))R9.(1<.$3;.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Heof Hg0 Hg2 Hw Haok.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_eof; eassumption.
Qed.

Lemma read0_ok_bytes : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pw,(0.(3.&8.))Pbs,(0.(3.&8.))P,(7.$8.(9.&40.R4.)+3?.)P,(7.(11.$12.)(13.(14.R4.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.(3.&40.)(?.R7.#0.)(15.&40.=))P,(7.(3.&40.)(?.R8.#2.)R;.)P,(7.(11.(0.(3.&8.)))(2;.(29.R:.R9.)(?.R9.#1.)R<.)(16.(0.(3.&8.))R6.))P,(7.$24.(35.(?.R:.#1.)(9.&40.R=.))$26.)P,(2=.+1.(3<.(3=.(3.&8.)R7.)))P,(2=.(3<.(3=.(3.&8.)R8.))(9.&40.R?.))P,(7.(0.(3.&8.))(31.(0.(3.&8.))$21.(22.(23.R;.)(3=.(3.&8.)R9.)))R9.)(;.(<.R?.R>.R=.)R<.(42.$6.(38.(30.(3.&8.)R:.)(3>.(1:.(3.&40.)(0.(3.&8.)))(3?.(3.&40.)(0.(3.&8.))(?.R>.#1.)R:.)(1<.(1:.(3.&40.)(0.(3.&8.)))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.)))(1?.(20.(0.(3.&8.))$21.(22.(23.R<.)(3=.(3.&8.)R:.)))R<.)(40.(3.&8.)$3;.(41.(15.&40.=))R:.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model w bs Hno Hfd Hg0 Hg2 Hw Haok Hlo Hhi Hpre.
  apply (proj2 (syscall_spec_read _ _ _ _ _ Hno)).
  apply check_read_sound_ok. eapply read0_check_bytes; eassumption.
Qed.

(* [comment removed for export] *)
Lemma read0_ok_inv : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pbuf,(3.&40.)Pw,(0.(3.&8.))Peff,$6.Pmodel',$4.Pevs,(0.$3;.)P,(7.$8.(9.&40.R7.)+3?.)P,(7.(11.$12.)(13.(14.R7.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.(3.&40.)(?.R:.#0.)(15.&40.=))P,(7.(3.&40.)(?.R;.#1.)R8.)P,(7.(3.&40.)(?.R<.#2.)R?.)P,(7.(11.(0.(3.&8.)))(2;.(29.R>.R=.)R:.R10.)(16.(0.(3.&8.))R9.))P,(7.$24.(35.R;.(9.&40.R11.))$26.)P,(;.(<.R10.R?.R>.)R=.(42.$6.R:.R9.R8.))(43.(10.(7.$21.(23.R>.)$34.)(10.(7.$6.R;.(38.(15.&40.=)(1<.(1:.(3.&40.)(0.(3.&8.))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.))))(10.(7.$4.R:.R>.)(7.(0.$3;.)R9.(1<.$3;.)))))(27.(0.(3.&8.))Lbs,(0.(3.&8.))(10.(2=.+1.(3<.(3=.(3.&8.)R1.)))(10.(2=.(3<.(3=.(3.&8.)R1.))(9.&40.R14.))(10.(7.(0.(3.&8.))(31.(0.(3.&8.))$21.(22.(23.R?.)(3=.(3.&8.)R1.)))R1.)(10.(7.$6.R<.(38.(30.(3.&8.)R1.)(3>.(1:.(3.&40.)(0.(3.&8.)))(3?.(3.&40.)(0.(3.&8.))R>.R1.)(1<.(1:.(3.&40.)(0.(3.&8.)))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.))))(10.(7.$4.R;.(1?.(20.(0.(3.&8.))$21.(22.(23.R?.)(3=.(3.&8.)R1.)))R?.))(7.(0.$3;.)R:.(40.(3.&8.)$3;.(41.(15.&40.=))R1.)))))))))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model buf w eff model' evs
         Hno Hfd Hg0 Hg1 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w) as [w1 Hw1];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hw1.
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model)) as [wn Hwn];
    [rewrite Hg1; exact Hw|].
  rewrite Hg1 in Hwn.
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply check_read_complete_ok in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg1, Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  - (* [comment removed for export] *)
    apply check_ret_only_ok_iff in Hspec.
    destruct Hspec as (-> & -> & ->). left. auto.
  - (* [comment removed for export] *)
    rewrite Hw1 in Hspec. cbv beta iota in Hspec.
    rewrite Hwn in Hspec. cbv beta iota in Hspec.
    destruct eff as [ret ws zs us cs copyins].
    destruct ws as [|[a bs] [|w2 ws]]; [discriminate| |discriminate].
    destruct zs as [|z zs]; [|discriminate].
    destruct us as [|u us]; [|discriminate].
    destruct cs as [|c cs]; [|discriminate].
    destruct copyins as [|copyin copyins]; [|discriminate].
    destruct (bv_eqb a buf && bv_eqb ret (len_word bs)
              && (1 <=? Z.of_nat (length bs))%Z
              && (Z.of_nat (length bs) <=? rw_count_clamp cnt)%Z
              && listN_eqb (fst (stream_take (ICons b0 s0) (length bs))) bs
              && wmem_ok (sys_input segs ms x8) buf (len_word bs)) eqn:Hb;
      try rewrite Hb in Hspec; [|discriminate].
    inversion Hspec; subst.
    apply andb_true_iff in Hb as [Hb _].
    apply andb_true_iff in Hb as [Hb HE].
    apply andb_true_iff in Hb as [Hb HD].
    apply andb_true_iff in Hb as [Hb HC].
    apply andb_true_iff in Hb as [HA HB].
    apply bv_eqb_eq in HA; subst a.
    apply bv_eqb_eq in HB; subst ret.
    apply Z.leb_le in HC. apply Z.leb_le in HD.
    rewrite (rw_count_clamp_of_rw _ (proj2 Hcnt)) in HD.
    apply listN_eqb_eq in HE.
    right. exists bs. repeat split; try assumption; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma read0_no_unmodeled : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Px8,(3.&40.)Pmodel,$4.Pw,(0.(3.&8.))P,(7.$8.(9.&40.R3.)+3?.)P,(7.(11.$12.)(13.(14.R3.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.(3.&40.)(?.R6.#0.)(15.&40.=))P,(7.(3.&40.)(?.R7.#2.)R:.)P,(7.(11.(0.(3.&8.)))(2;.(29.R9.R8.)(?.R8.#1.)R;.)(16.(0.(3.&8.))R5.))P,(7.$24.(35.(?.R9.#1.)(9.&40.R<.))$26.)(44.(;.(<.R;.R:.R9.)R8.(45.$6.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms x8 model w Hno Hfd Hg0 Hg2 Hw Haok Hspec.
  destruct (read0_wmem1 cnt Hcnt segs ms x8 w Hw) as [w1 Hw1].
  destruct (read0_wmem_need cnt Hcnt segs ms x8 w (m_stdin model) Hw) as [wn Hwn].
  pose proof (w_is0_pos cnt (proj1 Hcnt)) as Hcnt0.
  apply (proj1 (syscall_spec_read _ _ _ _ _ Hno)) in Hspec.
  apply (check_read_complete_unmodeled _ _ _ _ _ (mkEffect (Z_to_bv 64 0) [] []))
    in Hspec.
  unfold check_read in Hspec.
  rewrite Hg0 in Hspec; norm_fd32; rewrite Hfd in Hspec.
  cbv beta iota in Hspec.
  change (negb (w_is0 (Z_to_bv 64 0))) with false in Hspec.
  cbv beta iota in Hspec.
  rewrite Hg2, Haok in Hspec.
  cbn [negb] in Hspec. cbv beta iota in Hspec. rewrite Hcnt0 in Hspec. cbv beta iota in Hspec.
  destruct (m_stdin model) as [|b0 s0] eqn:Hs; cbv beta iota in Hspec.
  { now apply check_ret_only_no_unmodeled in Hspec. }
  rewrite Hw1 in Hspec. cbv beta iota in Hspec.
  rewrite Hwn in Hspec. cbv beta iota in Hspec. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sstep_read_inv : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psegs,(0.$1.)Pms,$2.Pmodel,$4.Pbuf,(3.&40.)Px8,(3.&40.)Pw,(0.(3.&8.))Pevs,(0.$3;.)Pst,$46.P,(7.(11.(3.&40.))(18.R6.)(19.(3.&40.)))P,(7.(0.(1:.(3.&40.)(3.&40.)))(1;.R7.)(1<.(1:.(3.&40.)(3.&40.))))P,(7.(11.$12.)(13.(14.R8.)(15.&40.=))(16.$12.(17.(15.&40.=))))P,(7.(11.(3.&40.))(47.R:.)(16.(3.&40.)R7.))P,(7.$8.(9.&40.R8.)+3?.)P,(7.(3.&40.)(?.R<.#0.)(15.&40.=))P,(7.(3.&40.)(?.R=.#1.)R;.)P,(7.(3.&40.)(?.R>.#2.)R11.)P,(7.(11.(0.(3.&8.)))(2;.(29.R10.R?.)R=.R12.)(16.(0.(3.&8.))R;.))P,(7.$24.(35.R>.(9.&40.R13.))$26.)P,(48.R12.(49.R11.R10.)R<.R;.)(43.(10.(7.$21.(23.R11.)$34.)(10.(7.(0.$3;.)R=.(1<.$3;.))(7.$46.R<.(4:.(49.(4;.(4<.R12.(15.&40.=)))R11.)))))(27.(0.(3.&8.))Lbs,(0.(3.&8.))(10.(2=.+1.(3<.(3=.(3.&8.)R1.)))(10.(2=.(3<.(3=.(3.&8.)R1.))(9.&40.R16.))(10.(7.(0.(3.&8.))(31.(0.(3.&8.))$21.(22.(23.R12.)(3=.(3.&8.)R1.)))R1.)(10.(7.(0.$3;.)R>.(40.(3.&8.)$3;.(41.(15.&40.=))R1.))(7.$46.R=.(4:.(49.(4;.(4=.R13.(38.(30.(3.&8.)R1.)(3>.(1:.(3.&40.)(0.(3.&8.)))(3?.(3.&40.)(0.(3.&8.))R11.R1.)(1<.(1:.(3.&40.)(0.(3.&8.)))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.)))))(1?.(20.(0.(3.&8.))$21.(22.(23.R12.)(3=.(3.&8.)R1.)))R12.))))))))))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt segs ms model buf x8 w evs st
         Hh Hlazy Hfd Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0) |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(Hs & Heff & Hm & Hevs) | (bs & Hlo & Hhi & Hpre & Heff & Hm & Hevs)];
        subst eff model' evs0
    end.
    + match goal with
      | Hmat : materialize_model_accesses model _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat;
          inversion Hmat; subst model''
      end.
      left. rewrite apply_effect_no_write.
      split; [exact Hs | split; reflexivity].
    + match goal with
      | Hmat : materialize_model_accesses
                   (with_stdin ?s model) _ = Some ?model'' |- _ =>
          rewrite (materialize_model_accesses_no_lazy (with_stdin s model) _)
            in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy);
          inversion Hmat; subst model''
      end.
      right. exists bs. repeat split; try assumption; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      Hmat : materialize_model_accesses ?model' _ = None |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
      subst model';
      [ rewrite (materialize_model_accesses_no_lazy model _ Hlazy) in Hmat
      | rewrite (materialize_model_accesses_no_lazy
                   (with_stdin (snd (stream_take (m_stdin model) (length bs))) model) _)
          in Hmat by (rewrite m_vm_lazy_with_stdin; exact Hlazy) ];
      discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model'; [|rewrite m_halted_with_stdin in H6]; congruence
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model (Ok ?eff ?model' ?evs0),
      H6 : m_killed ?model' = Some ?sig |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      destruct (read0_ok_inv _ Hcnt segs ms x8 model (ms_gpr ms 1) w eff model' evs0
                  Hno Hfd Hg0 eq_refl eq_refl Hw Haok H3)
        as [(_ & _ & Hm & _) | (bs & _ & _ & _ & _ & Hm & _)];
        subst model';
        [ rewrite (m_killed_of_m_halted_none model Hh) in H6
        | rewrite (m_killed_of_m_halted_none _
                     (eq_trans (m_halted_with_stdin _ model) Hh)) in H6 ];
        discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H2 : ms_svc_pending ms = Some ?x,
      H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled |- _ =>
      assert (Hx : x = x8) by congruence; subst x;
      exact (read0_no_unmodeled _ Hcnt segs ms x8 model w Hno Hfd Hg0 eq_refl Hw
               Haok H3)
    end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive chunks (cnt : word) : InputStream -> list (list byte) -> InputStream -> Prop :=
| chunks_nil : forall s, chunks cnt s [] s
| chunks_cons : forall s bs blocks s'',
    (1 <= Z.of_nat (length bs))%Z ->
    (Z.of_nat (length bs) <= bv_unsigned cnt)%Z ->
    fst (stream_take s (length bs)) = bs ->
    chunks cnt (snd (stream_take s (length bs))) blocks s'' ->
    chunks cnt s (bs :: blocks) s''.

(* [comment removed for export] *)
Lemma chunks_app : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)Ps,$21.Pl1,(0.(0.(3.&8.)))Ps1,$21.Pl2,(0.(0.(3.&8.)))Ps2,$21.P,(4>.R6.R5.R4.R3.)P,(4>.R7.R4.R3.R2.)(4>.R8.R7.(4?.(0.(3.&8.))R6.R4.)R3.)")
(* [comment removed for export] *).
Proof.
  intros cnt s l1 s1 l2 s2 H1; revert l2 s2.
  induction H1 as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros l2 s2 H2; cbn [app]; [exact H2|].
  eapply chunks_cons; eauto.
Qed.

Lemma chunks_split : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)Pl1,(0.(0.(3.&8.)))Pl2,(0.(0.(3.&8.)))Ps,$21.Ps2,$21.P,(4>.R5.R2.(4?.(0.(3.&8.))R4.R3.)R1.)(27.$21.Ls1,$21.(10.(4>.R7.R4.R6.R1.)(4>.R7.R1.R5.R3.)))")
(* [comment removed for export] *).
Proof.
  intros cnt l1; induction l1 as [|bs l1 IH]; intros l2 s s2 H; cbn [app] in H.
  - exists s. split; [constructor | exact H].
  - inversion H as [|s0 bs0 blocks0 s3 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
    destruct (IH l2 _ _ HC) as (s1 & H1 & H2).
    exists s1. split; [eapply chunks_cons; eauto | exact H2].
Qed.

(* [comment removed for export] *)
Lemma chunks_single_inv : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)Ps,$21.Pbs,(0.(3.&8.))Ps',$21.P,(4>.R4.R3.(3>.(0.(3.&8.))R2.(1<.(0.(3.&8.))))R1.)(10.(2=.+1.(3<.(3=.(3.&8.)R3.)))(10.(2=.(3<.(3=.(3.&8.)R3.))(9.&40.R5.))(10.(7.(0.(3.&8.))(31.(0.(3.&8.))$21.(22.R4.(3=.(3.&8.)R3.)))R3.)(7.$21.R2.(20.(0.(3.&8.))$21.(22.R4.(3=.(3.&8.)R3.)))))))")
(* [comment removed for export] *).
Proof.
  intros cnt s bs s' H.
  inversion H as [|s0 bs0 blocks0 s2 Hlo Hhi Hpre HC Heq1 Heq2]; subst.
  inversion HC; subst.
  repeat split; assumption || reflexivity.
Qed.

(* [comment removed for export] *)
Definition iter_ev_ch (rch : word) (bs : list byte) : list event :=
  map (ReadEv rch) bs ++ map (WriteEv (Z_to_bv 64 1)) bs.

(* [comment removed for export] *)
Definition iter_ev (bs : list byte) : list event :=
  iter_ev_ch (Z_to_bv 64 0) bs.

(* [comment removed for export] *)
Definition eof_tail (s : InputStream) (fs : Fs.Fs) : list event :=
  match s with
  | IEof => [ExitEv (Z_to_bv 64 0) fs]
  | ICons _ _ => []
  end.

(* [comment removed for export] *)
Definition stream_traces_ch (rch : word) (cnt : word) (fs : Fs.Fs)
    (s : InputStream) (tr : list event) : Prop := ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "(27.(0.(0.(3.&8.)))Lblocks,(0.(0.(3.&8.)))(27.$21.Ls',$21.(10.(4>.O4.O2.R2.R1.)(50.$3;.O1.(4?.$3;.(51.(0.(3.&8.))$3;.(52.O5.)R2.)(53.R1.O3.))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition stream_traces (cnt : word) (fs : Fs.Fs) (s : InputStream)
    (tr : list event) : Prop :=
  stream_traces_ch (Z_to_bv 64 0) cnt fs s tr.

Lemma stream_traces_ch_prefix_closed : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Prch,(3.&40.)Pcnt,(3.&40.)Pfs,$54.Ps,$21.Ptr,(0.$3;.)Ptr',(0.$3;.)P,(55.R6.R5.R4.R3.R2.)P,(50.$3;.R2.R3.)(55.R8.R7.R6.R5.R3.)")
(* [comment removed for export] *).
Proof.
  intros rch cnt fs s tr tr' (blocks & s' & HC & Hp) Hp'.
  exists blocks, s'. split; [exact HC | eapply is_prefix_trans; eauto].
Qed.

Lemma stream_traces_prefix_closed : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)Pfs,$54.Ps,$21.Ptr,(0.$3;.)Ptr',(0.$3;.)P,(56.R5.R4.R3.R2.)P,(50.$3;.R2.R3.)(56.R7.R6.R5.R3.)")
(* [comment removed for export] *).
Proof. exact (stream_traces_ch_prefix_closed (Z_to_bv 64 0)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Loop.
Variable segs : list Segment.
Variable LH : machine_state -> Prop.
Variable cnt : word.
(* [comment removed for export] *)
Hypothesis Hcnt : (0 < bv_unsigned cnt <= rw_bytes_max)%Z.

(* [comment removed for export] *)
Definition lh_next (ms : machine_state) : Prop :=
  exists ms', msteps segs ms ms' /\ LH ms'.

(* [comment removed for export] *)
Definition WrPend (bs : list byte) (ms : machine_state) : Prop :=
  (1 <= length bs)%nat /\
  to_wall segs (Z_to_bv 64 1) ms bs lh_next.

(* [comment removed for export] *)
Inductive to_wr (bs : list byte) : machine_state -> Prop :=
| twr_here : forall ms, WrPend bs ms -> to_wr bs ms
| twr_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_wr bs ms' -> to_wr bs ms.

(* [comment removed for export] *)
Definition ReadPend (ms : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "(27.(3.&40.)Lbuf,(3.&40.)(27.(3.&40.)Lx8,(3.&40.)(10.(7.(11.(3.&40.))(47.O1.)(16.(3.&40.)R1.))(10.(7.$8.(9.&40.R1.)+3?.)(10.(7.(3.&40.)(?.O1.#0.)(15.&40.=))(10.(7.(3.&40.)(?.O1.#1.)R2.)(10.(7.(3.&40.)(?.O1.#2.)Vcnt,)(10.(27.(0.(3.&8.))Lw,(0.(3.&8.))(7.(11.(0.(3.&8.)))(2;.(29.Vsegs,O1.)R3.Vcnt,)(16.(0.(3.&8.))R1.)))(10.(7.$24.(35.R2.(9.&40.Vcnt,))$26.)(10.(57.Vsegs,(15.&40.=)(4;.(4<.O1.(15.&40.=))))Pbs,(0.(3.&8.))P,(2=.+1.(3<.(3=.(3.&8.)R1.)))P,(2=.(3<.(3=.(3.&8.)R2.))(9.&40.Vcnt,))(58.R3.(4;.(4=.O1.(38.(30.(3.&8.)R3.)(3>.(1:.(3.&40.)(0.(3.&8.)))(3?.(3.&40.)(0.(3.&8.))R5.R3.)(1<.(1:.(3.&40.)(0.(3.&8.)))))(1<.(1:.(3.&40.)(3.&40.)))(1<.(1:.(3.&40.)(3.&40.)))(1<.$39.)(1<.(1:.(3.&40.)$1=.))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma msteps_to_wr : forall bs ms ms',
  msteps segs ms ms' -> to_wr bs ms' -> to_wr bs ms.
Proof.
  intros bs ms ms' H; induction H; [auto|].
  intro Hwr. eapply twr_step; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma to_wr_wall_tail : forall bs ms,
  to_wr bs ms -> to_wall_tail segs (Z_to_bv 64 1) ms bs lh_next.
Proof.
  intros bs ms H; induction H as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - destruct HWP as [Hnb Hw]. apply twt_more; assumption.
  - eapply twt_step; eauto.
Qed.

Inductive to_rd : machine_state -> Prop :=
| trd_here : forall ms, ReadPend ms -> to_rd ms
| trd_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_rd ms' -> to_rd ms.

#[using="Type"] Lemma msteps_to_rd : forall ms ms',
  msteps segs ms ms' -> to_rd ms' -> to_rd ms.
Proof.
  intros ms ms' H; induction H; [auto|].
  intro Hrd. eapply trd_step; eauto.
Qed.

(* [comment removed for export] *)
Hypothesis H_LH : forall ms, LH ms -> to_rd ms.

#[using="H_LH"] Lemma lh_next_to_rd : forall ms, lh_next ms -> to_rd ms.
Proof.
  intros ms (ms' & Hm & HL). eapply msteps_to_rd; [exact Hm | apply H_LH, HL].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma to_rd_star : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pms,$2.Pmodel,$4.P,(7.(11.(3.&40.))(18.R1.)(19.(3.&40.)))P,(7.(0.(1:.(3.&40.)(3.&40.)))(1;.R2.)(1<.(1:.(3.&40.)(3.&40.))))P,(59.R4.)(27.$2.LmsR,$2.(10.(5:.R1.)(5;.Vsegs,(49.R6.R5.)(1<.$3;.)(49.R1.R5.))))")
(* [comment removed for export] *).
Proof.
  intros ms model Hh Hlazy Hrd.
  induction Hrd as [ms HRP | ms ms' Hsvc Hstep Hrd IH].
  - exists ms. split; [exact HRP | apply star_refl].
  - destruct IH as (msR & HRP & Hstar).
    exists msR. split; [exact HRP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

#[using="Type"] Lemma to_wr_star : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pbs,(0.(3.&8.))Pms,$2.Pmodel,$4.P,(7.(11.(3.&40.))(18.R1.)(19.(3.&40.)))P,(7.(0.(1:.(3.&40.)(3.&40.)))(1;.R2.)(1<.(1:.(3.&40.)(3.&40.))))P,(58.R5.R4.)(27.$2.LmsW,$2.(10.(5<.R7.R1.)(5;.Vsegs,(49.R6.R5.)(1<.$3;.)(49.R1.R5.))))")
(* [comment removed for export] *).
Proof.
  intros bs ms model Hh Hlazy Hwr.
  induction Hwr as [ms HWP | ms ms' Hsvc Hstep Hwr IH].
  - exists ms. split; [exact HWP | apply star_refl].
  - destruct IH as (msW & HWP & Hstar).
    exists msW. split; [exact HWP|].
    change ([] : list event) with (([] : list event) ++ []).
    eapply star_step; [apply (sstep_instr segs ms model ms' model) | exact Hstar];
      try assumption.
    rewrite (mi_account_step_no_lazy segs ms model Hlazy), Hstep. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma stream_star_admits : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Ps,$21.Pblocks,(0.(0.(3.&8.)))Ps',$21.P,(4>.Vcnt,R3.R2.R1.)Pms,$2.Pmodel,$4.P,(1>.R1.)P,(7.$21.(23.R2.)R7.)P,(59.R4.)(27.$5=.Lc,$5=.(5;.Vsegs,(49.R6.R5.)(4?.$3;.(51.(0.(3.&8.))$3;.$5>.R9.)(53.R8.(5?.R5.)))R1.))")
(* [comment removed for export] *).
Proof.
  intros s blocks s' HC.
  induction HC as [s | s bs blocks s'' Hlo Hhi Hpre HC IH];
    intros ms model HM Hst Hrd; pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
  - (* [comment removed for export] *)
    cbn [flat_map app].
    destruct s as [|b0 s0] eqn:Hs.
    + (* [comment removed for export] *)
      destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
      destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & _).
      destruct (to_exit_star_admits segs (Z_to_bv 64 0)
                  (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0))) model Hh Hlazy Hex)
        as [c Hstar2].
      exists c.
      assert (HssE : sstep segs (mkCfg msR model) []
                (SNext (mkCfg (advance_past_svc (set_gpr0 msR (Z_to_bv 64 0)))
                              model))).
      { rewrite <- (apply_effect_no_write msR (Z_to_bv 64 0)).
        apply (sstep_syscall segs msR model x8 (mkEffect (Z_to_bv 64 0) [] [])
                 model model []);
          [exact Hh | exact Hsvc | | exact Hh |].
        - rewrite <- Hg1 in Hw, Haok. eapply (read0_ok_eof cnt Hcnt); eassumption.
        - rewrite (materialize_model_accesses_no_lazy model _ Hlazy). reflexivity. }
      cbn [eof_tail].
      replace [ExitEv (Z_to_bv 64 0) (m_fs model)]
        with (([] : list event)
                ++ ([] ++ [ExitEv (bv_and (Z_to_bv 64 0) (Z_to_bv 64 255))
                             (m_fs model)]))
        by (rewrite band0_255; reflexivity).
      eapply star_trans; [exact Hstar0|].
      eapply star_step; [exact HssE | exact Hstar2].
    + (* [comment removed for export] *)
      cbn [eof_tail app]. exists (mkCfg ms model). apply star_refl.
  - (* [comment removed for export] *)
    destruct (to_rd_star ms model Hh Hlazy Hrd) as (msR & (buf & x8 & HRP) & Hstar0).
    destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
    pose proof (Hbytes bs Hlo Hhi) as Hwr.
    set (advB := advance_past_svc (apply_effect msR
                   (mkEffect (len_word bs) [(buf, bs)] []))) in *.
    set (model' := with_stdin (snd (stream_take s (length bs))) model).
    assert (Hh' : m_halted model' = None) by exact Hh.
    assert (HM' : M_loop model')
      by (unfold model'; rewrite <- Hst; apply M_loop_take; exact HM).
    assert (HssR : sstep segs (mkCfg msR model) (map (ReadEv (Z_to_bv 64 0)) bs)
              (SNext (mkCfg advB model'))).
    { apply (sstep_syscall segs msR model x8
               (mkEffect (len_word bs) [(buf, bs)] []) model' model'
               (map (ReadEv (Z_to_bv 64 0)) bs));
        [exact Hh | exact Hsvc | | exact Hh' |].
      - unfold model'. rewrite <- Hst. rewrite <- Hg1. rewrite <- Hg1 in Hw, Haok.
        eapply (read0_ok_bytes cnt Hcnt); try eassumption.
        rewrite Hst. exact Hpre.
      - rewrite (materialize_model_accesses_no_lazy model' _ (proj2 (proj2 (proj2 HM')))).
        reflexivity. }
    assert (Hfdc' : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model')
      by (apply fd1chan_fdchan; exact Hfd1).
    assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
    assert (Hst' : m_stdin model' = snd (stream_take s (length bs)))
      by reflexivity.
    assert (Hcont : forall ms', lh_next ms' ->
              exists c, star segs (mkCfg ms' model')
                (flat_map iter_ev blocks ++ eof_tail s'' (m_fs model')) c).
    { intros ms' Hlh.
      apply (IH ms' model' HM' Hst' (lh_next_to_rd ms' Hlh)). }
    destruct (to_wall_tail_star_admits segs (Z_to_bv 64 1) (Z_to_bv 64 1)
                fd32_1 advB bs lh_next (to_wr_wall_tail bs advB Hwr) Hbmbs
                model' _ Hh' (proj2 (proj2 (proj2 HM'))) Hfdc' Hcont) as [c Hstar1].
    exists c.
    change (m_fs model') with (m_fs model) in Hstar1.
    cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
    rewrite <- !app_assoc.
    replace (map (ReadEv (Z_to_bv 64 0)) bs
               ++ map (WriteEv (Z_to_bv 64 1)) bs
               ++ flat_map iter_ev blocks ++ eof_tail s'' (m_fs model))
      with (([] : list event)
              ++ (map (ReadEv (Z_to_bv 64 0)) bs
                    ++ (map (WriteEv (Z_to_bv 64 1)) bs
                          ++ (flat_map iter_ev blocks
                                ++ eof_tail s'' (m_fs model)))))
      by reflexivity.
    eapply star_trans; [exact Hstar0|].
    eapply star_step; [exact HssR | exact Hstar1].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma star_loop_only : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pc0,$5=.Ptr,(0.$3;.)Pc',$5=.P,(5;.Vsegs,R3.R2.R1.)Pms,$2.Pmodel,$4.P,(7.$5=.R6.(49.R2.R1.))P,(1>.R2.)(10.P,(59.R4.)(27.(0.(0.(3.&8.)))Lblocks,(0.(0.(3.&8.)))(27.$21.Ls',$21.(10.(4>.Vcnt,(23.R6.)R2.R1.)(50.$3;.R:.(4?.$3;.(51.(0.(3.&8.))$3;.$5>.R2.)(53.R1.(5?.R6.)))))))Pbs,(0.(3.&8.))P,(60.#1.(3=.(3.&8.)R1.))P,(61.R2.)P,(62.Vsegs,(15.&40.+1.)R7.R3.$63.)(27.(0.(0.(3.&8.)))Lblocks,(0.(0.(3.&8.)))(27.$21.Ls',$21.(10.(4>.Vcnt,(23.R9.)R2.R1.)(50.$3;.R=.(4?.$3;.(40.(3.&8.)$3;.(64.(15.&40.+1.))R6.)(4?.$3;.(51.(0.(3.&8.))$3;.$5>.R2.)(53.R1.(5?.R9.)))))))))")
(* [comment removed for export] *).
Proof.
  intros c0 tr c' Hstar.
  induction Hstar as [c | c1 evs c2 tr2 c3 Hss Hstar IH];
    intros ms model Heq HM; subst.
  - (* [comment removed for export] *)
    split.
    + intros _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
    + intros bs _ _ _. exists [], (m_stdin model).
      split; [constructor | apply is_prefix_nil].
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    split.
    + (* [comment removed for export] *)
      intro Hrd. destruct Hrd as [ms (buf & x8 & HRP) | ms ms' Hsvc Hstep Hrd'].
      * (* [comment removed for export] *)
        destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs (SNext c2)
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- (* [comment removed for export] *)
           destruct (to_exit_star_only segs (Z_to_bv 64 0)
                       (advance_past_svc (set_gpr0 ms (Z_to_bv 64 0))) model
                       Hh Hlazy Hex tr2 c3 Hstar) as [-> | ->].
           ++ exists [], (m_stdin model).
              split; [constructor | apply is_prefix_nil].
           ++ exists [], (m_stdin model).
              split; [constructor|].
              rewrite Hs, band0_255. cbn [flat_map app eof_tail].
              apply is_prefix_refl.
        -- (* [comment removed for export] *)
           assert (Hnb : (1 <= length bs)%nat) by lia.
           assert (Hbmbs : buf_modeled bs) by (unfold buf_modeled; lia).
           destruct (proj2 (IH _ _ eq_refl (M_loop_take (length bs) model HM)) bs
                       Hnb Hbmbs (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)))
             as (blocks & s' & HCb & Hp).
           exists (bs :: blocks), s'.
           split; [eapply chunks_cons; eassumption|].
           cbn [flat_map]. unfold iter_ev at 1; unfold iter_ev_ch.
           rewrite <- !app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* [comment removed for export] *)
        destruct (sstep_instr_inv segs ms model ms' evs (SNext c2)
                    Hlazy Hsvc Hstep Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj1 (IH _ model eq_refl HM) Hrd').
    + (* [comment removed for export] *)
      intros bs Hnb Hbm Hwt.
      inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* [comment removed for export] *)
        cbn in Hnb. lia.
      * (* [comment removed for export] *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext c2) Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & Hevs & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* [comment removed for export] *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           destruct (proj1 (IH _ model eq_refl HM)
                       (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)))
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite firstn_all.
           apply is_prefix_app_mono. exact Hp.
        -- (* [comment removed for export] *)
           assert (Hnb' : (1 <= length (skipn n bs))%nat)
             by (rewrite length_skipn; lia).
           destruct (proj2 (IH _ model eq_refl HM) (skipn n bs) Hnb'
                       (buf_modeled_skipn n bs Hbm) Hwt2)
             as (blocks & s' & HCb & Hp).
           exists blocks, s'. split; [exact HCb|].
           rewrite <- (firstn_skipn n bs) at 2.
           rewrite map_app, <- app_assoc.
           apply is_prefix_app_mono. exact Hp.
      * (* [comment removed for export] *)
        destruct (sstep_instr_inv segs ms model msS' evs (SNext c2)
                    Hlazy HsvcS HstepS Hss) as [Hevs Hc2].
        inversion Hc2; subst.
        exact (proj2 (IH _ model eq_refl HM) bs Hnb Hbm Hwt').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition sinv (c : config) : Prop := ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "(43.(10.(1>.(65.O1.))(43.(59.(66.O1.))(27.(0.(3.&8.))Lbs,(0.(3.&8.))(10.(60.#1.(3=.(3.&8.)R1.))(10.(61.R1.)(62.Vsegs,(15.&40.+1.)(66.O1.)R1.$63.))))))(67.Vsegs,(15.&40.=)O1.))")
(* [comment removed for export] *).

#[using="Hcnt H_LH"] Lemma sinv_step : forall c evs c',
  sinv c -> sstep segs c evs (SNext c') -> sinv c'.
Proof.
  intros [ms model] evs [ms' model'] Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs
                    (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(Hs & Hevs & Hc2) | (bs & Hlo & Hhi & Hpre & Hevs & Hc2)];
          inversion Hc2; subst.
        -- right. left. cbn. split; [exact Hh|].
           split; [exact Hlazy | exact Hex].
        -- left. cbn. split; [apply M_loop_take; exact HM|].
           right. exists bs. split; [lia|].
           split; [unfold buf_modeled; lia|].
           exact (to_wr_wall_tail bs _ (Hbytes bs Hlo Hhi)).
      * destruct (sstep_instr_inv segs ms model ms1 evs
                    (SNext (mkCfg ms' model')) Hlazy Hsvc Hstep Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM | left; exact Hrd'].
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * (* [comment removed for export] *)
        cbn in Hnb. lia.
      * (* [comment removed for export] *)
        destruct (sstep_to_wall_inv segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                    ms bs lh_next model evs (SNext (mkCfg ms' model'))
                    Hh Hlazy Hfdc Hbm Hwl Hss)
          as (n & Hn1 & Hn2 & _ & Hc2 & Hwt2).
        inversion Hc2; subst.
        set (adv := advance_past_svc (set_gpr0 ms (len_word (firstn n bs)))) in *.
        destruct (Nat.eq_dec n (length bs)) as [-> | Hne].
        -- (* [comment removed for export] *)
           rewrite skipn_all in Hwt2.
           destruct (to_wall_tail_nil_msteps segs (Z_to_bv 64 1) adv lh_next Hwt2)
             as (msL & HmL & HlhL).
           left. cbn. split; [exact HM|].
           left. exact (msteps_to_rd adv msL HmL (lh_next_to_rd msL HlhL)).
        -- (* [comment removed for export] *)
           left. cbn. split; [exact HM|].
           right. exists (skipn n bs).
           split; [rewrite length_skipn; lia|].
           split; [apply buf_modeled_skipn; exact Hbm | exact Hwt2].
      * destruct (sstep_instr_inv segs ms model msS' evs
                    (SNext (mkCfg ms' model')) Hlazy HsvcS HstepS Hss) as [_ Hc2].
        inversion Hc2; subst.
        left. cbn. split; [exact HM|].
        right. exists bs.
        split; [exact Hnb | split; [exact Hbm | exact Hwt']].
  - right. eapply on_path_step; eauto.
Qed.

#[using="Hcnt"] Lemma sinv_no_error : forall c evs, sinv c -> ~ sstep segs c evs SError.
Proof.
  intros [ms model] evs Hinv Hss.
  destruct Hinv as [[HM Hphase] | Hop]; cbn [cfg_ms cfg_model] in *.
  - pose proof HM as (Hfd0 & Hfd1 & Hh & Hlazy).
    assert (Hfdc : fdchan (Z_to_bv 64 1) (Z_to_bv 64 1) model)
      by (apply fd1chan_fdchan; exact Hfd1).
    destruct Hphase as [Hrd | (bs & Hnb & Hbm & Hwt)].
    + destruct Hrd as [ms (buf & x8 & HRP) | ms ms1 Hsvc Hstep Hrd'].
      * destruct HRP as (Hsvc & Hno & Hg0 & Hg1 & Hg2 & (w & Hw) & Haok & Hex & Hbytes).
        destruct (sstep_read_inv cnt Hcnt segs ms model buf x8 w evs SError
                    Hh Hlazy Hfd0 Hsvc Hno Hg0 Hg1 Hg2 Hw Haok Hss)
          as [(_ & _ & Hc2) | (bs & _ & _ & _ & _ & Hc2)]; discriminate.
      * destruct (sstep_instr_inv segs ms model ms1 evs SError
                    Hlazy Hsvc Hstep Hss) as [_ Hc2]. discriminate.
    + inversion Hwt as [msD kD HkD | msM restM kM HnbM Hwl
                       | msS msS' restS kS HsvcS HstepS Hwt']; subst.
      * cbn in Hnb. lia.
      * exact (to_wall_no_error_sstep segs (Z_to_bv 64 1) (Z_to_bv 64 1) fd32_1
                 ms bs lh_next model evs Hh Hlazy Hfdc Hbm Hwl Hss).
      * destruct (sstep_instr_inv segs ms model msS' evs SError
                    Hlazy HsvcS HstepS Hss) as [_ Hc2]. discriminate.
  - eapply on_path_no_error; eauto.
Qed.

#[using="Hcnt H_LH"] Lemma star_sinv : forall c tr c', sinv c -> star segs c tr c' -> sinv c'.
Proof. exact (star_inv segs sinv sinv_step). Qed.

#[using="Hcnt H_LH"] Lemma to_rd_no_error : forall ms model,
  M_loop model -> to_rd ms -> ~ reaches_error segs (mkCfg ms model).
Proof.
  intros ms model HM Hrd.
  apply (inv_no_reaches_error segs sinv sinv_step sinv_no_error).
  left; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma stream_obs_iff : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Ppc,$68.Pph,$69.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$6:.Plim,$8.Pinp,$6;.P,(59.(6<.Vsegs,R8.R7.R6.R3.(6=.R1.)(6>.R1.)(6?.R1.)(70.R1.)))Ptr,(0.$3;.)(:.(71.Vsegs,(72.Vsegs,R:.R9.R8.R7.R6.R5.R4.R3.)R1.)(56.Vcnt,(73.R3.)(74.R3.)R1.))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd tr.
  set (fs0 := in_fs inp) in *; set (stdin0 := in_stdin inp) in *.
  unfold init_config.
  set (ms0 := init_machine_state segs pc ph sp rnd (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) in *.
  pose proof (init_M_loop (segments_reserved segs) brk0 mb sp lim inp) as HM0.
  set (model0 := init_model (segments_reserved segs) brk0 mb sp lim inp) in *.
  assert (Hst0 : m_stdin model0 = stdin0) by reflexivity.
  assert (Hfs0 : m_fs model0 = fs0) by reflexivity.
  split.
  - intros (tr' & c & Hstar & Hp).
    destruct (proj1 (star_loop_only _ _ _ Hstar ms0 model0 eq_refl HM0) Hrd)
      as (blocks & s' & HC & Hp').
    rewrite Hst0 in HC. rewrite Hfs0 in Hp'.
    apply (stream_traces_prefix_closed cnt fs0 stdin0 tr'); [|exact Hp].
    exists blocks, s'. split; assumption.
  - intros (blocks & s' & HC & Hp).
    destruct (stream_star_admits stdin0 blocks s' HC ms0 model0 HM0 Hst0 Hrd)
      as [c Hstar].
    rewrite Hfs0 in Hstar.
    exists (flat_map iter_ev blocks ++ eof_tail s' fs0), c.
    split; assumption.
Qed.

#[using="Hcnt H_LH"] Lemma stream_no_error : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Ppc,$68.Pph,$69.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$6:.Plim,$8.Pinp,$6;.P,(59.(6<.Vsegs,R8.R7.R6.R3.(6=.R1.)(6>.R1.)(6?.R1.)(70.R1.)))(44.(75.Vsegs,(72.Vsegs,R9.R8.R7.R6.R5.R4.R3.R2.)))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd.
  apply to_rd_no_error; [apply init_M_loop | exact Hrd].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Hcnt H_LH"] Lemma to_rd_coexec : forall ms model,
  M_loop model -> to_rd ms -> OmniRun.coexec segs (mkCfg ms model) never_errors.
Proof.
  intros ms model HM Hrd.
  apply (inv_coexec segs sinv sinv_step sinv_no_error). left; cbn; auto.
Qed.

#[using="Hcnt H_LH"] Lemma stream_omni_corun : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Ppc,$68.Pph,$69.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$6:.Plim,$8.Pinp,$6;.P,(59.(6<.Vsegs,R8.R7.R6.R3.(6=.R1.)(6>.R1.)(6?.R1.)(70.R1.)))(76.(77.Vsegs,R9.R8.)R3.(78.R7.R6.R5.R4.)R2.$79.)")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_corun]. unfold init_config.
  apply to_rd_coexec; [apply init_M_loop | exact Hrd].
Qed.

#[using="Hcnt H_LH"] Lemma stream_omni_cosafe : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Ppc,$68.Pph,$69.Psp,(3.&40.)Pbrk0,(3.&40.)Pmb,(3.&40.)Prnd,$6:.Plim,$8.Pinp,$6;.P,(59.(6<.Vsegs,R8.R7.R6.R3.(6=.R1.)(6>.R1.)(6?.R1.)(70.R1.)))(7:.(77.Vsegs,R9.R8.)R3.(78.R7.R6.R5.R4.)R2.(56.Vcnt,(73.R2.)(74.R2.)))")
(* [comment removed for export] *).
Proof.
  intros pc ph sp brk0 mb rnd lim inp Hrd. cbn [omni_cosafe].
  apply cosafe_obs_iff.
  - intros t t' Ht Hp. eapply stream_traces_prefix_closed; eauto.
  - intros tr Hobs. apply (stream_obs_iff pc ph sp brk0 mb rnd lim inp Hrd). exact Hobs.
Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma stream_omni_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psource_segs,(0.$1.)PrLH,Px,$2.SpPrpc,$68.Prph,$69.Prsp,(3.&40.)Prbrk,(3.&40.)Prmb,(3.&40.)Prrnd,$6:.Ptarget_segs,(0.$1.)PaLH,Px,$2.SpPapc,$68.Paph,$69.Pasp,(3.&40.)Pabrk,(3.&40.)Pamb,(3.&40.)Parnd,$6:.Pinp,$6;.P,Pms,$2.P,A1.R11.R1.(7;.R13.R12.R15.R2.)P,Pms,$2.P,A1.R:.R1.(7;.R<.R;.R16.R2.)P,(7;.R13.R12.R15.(6<.R13.R11.R10.R?.R<.(6=.R3.)(6>.R3.)(6?.R3.)(70.R3.)))P,(7;.R<.R;.R16.(6<.R<.R:.R9.R8.R5.(6=.R4.)(6>.R4.)(6?.R4.)(70.R4.)))(7<.(77.R15.R13.R12.)(77.R=.R;.R:.)(78.R11.R10.R?.R>.)(78.R9.R8.R7.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd target_segs aLH apc aph asp abrk amb arnd
         inp HrLH HaLH Hr Ha.
  split.
  { cbn [img_segments].
    eapply coexec_conseq;
      [exact (stream_omni_corun source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd
                source_alloc_limit inp Hr) | apply never_errors_covered]. }
  right. split.
  - apply trace_equiv_iff_omni. intro tr. cbn.
    rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd source_alloc_limit inp Hr tr).
    rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha tr).
    reflexivity.
  - exact (stream_omni_corun target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd target_alloc_limit inp Ha).
Qed.

Lemma stream_strong_equiv : ltac2:(CDefT.buildp (gd_tbl_StreamSim ()) "Pcnt,(3.&40.)P,(10.(2<.=(9.&40.R1.))(2=.(9.&40.R1.)$2>.))Psource_segs,(0.$1.)PrLH,Px,$2.SpPrpc,$68.Prph,$69.Prsp,(3.&40.)Prbrk,(3.&40.)Prmb,(3.&40.)Prrnd,$6:.Prlim,$8.Ptarget_segs,(0.$1.)PaLH,Px,$2.SpPapc,$68.Paph,$69.Pasp,(3.&40.)Pabrk,(3.&40.)Pamb,(3.&40.)Parnd,$6:.Palim,$8.Pinp,$6;.P,Pms,$2.P,A1.R13.R1.(7;.R15.R14.R17.R2.)P,Pms,$2.P,A1.R;.R1.(7;.R=.R<.R18.R2.)P,(7;.R15.R14.R17.(6<.R15.R13.R12.R11.R>.(6=.R3.)(6>.R3.)(6?.R3.)(70.R3.)))P,(7;.R=.R<.R18.(6<.R=.R;.R:.R9.R6.(6=.R4.)(6>.R4.)(6?.R4.)(70.R4.)))(10.(7=.(7>.(77.R17.R15.R14.)R?.(78.R13.R12.R11.R10.)R5.))(7?.(7>.(77.R17.R15.R14.)R?.(78.R13.R12.R11.R10.)R5.)(7>.(77.R>.R<.R;.)R6.(78.R:.R9.R8.R7.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros cnt Hcnt source_segs rLH rpc rph rsp rbrk rmb rrnd rlim target_segs aLH apc aph asp abrk amb arnd alim
         inp HrLH HaLH Hr Ha.
  split.
  { apply no_error_run_modeled.
    apply (stream_no_error source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr). }
  right. split.
  - intro tr. cbn.
    rewrite (stream_obs_iff source_segs rLH cnt Hcnt HrLH rpc rph rsp rbrk rmb rrnd rlim inp Hr tr).
    rewrite (stream_obs_iff target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha tr).
    reflexivity.
  - cbn. apply (stream_no_error target_segs aLH cnt Hcnt HaLH apc aph asp abrk amb arnd alim inp Ha).
Qed.
