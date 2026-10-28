(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen StdioFiles Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

Theorem fwritex_stderr_proof : fwritex_stderr_stmt.
Proof.
  unfold fwritex_stderr_stmt, out_stmt. intros St B. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3 S47.
  destruct st as [buf st].
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ in *.
  change usegs with usegs in *.
  destruct SSP as [GOT GUARD]. change usegs with usegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  Local Ltac2 Set LiaHints.tbl := fun () => "0120?10040197249.79 11770142661.79 13035831593.95 14002117805.94 1451302806.79  15611898301.11717207757499.11521881176170.79 22700267513.11924407152425.95 24921050300.79 24953689962.77 25498651748.79 26525069896.79 27060004634.79 28040198754.11628575982988.10329158771112.71 29442969842.79 29637151233.10329871468903.94 30062733858.95 31551594020.94 33524217389.94 33534964791.79 33596307437.94 34238060565.94 36177465322.94 36602215619.10438040770411.79 39204446167.10140821674190.94 41596052879.95 41800319328.72 42150790724.94 43011251178.94 43420333474.94 43626705115.79 43888721210.79 45617647863.79 48059309399.10250095796337.94 52135615273.95 52148621422.79 55430152575.76 57615708368.10557622410744.11959589697707.79 59848878127.94 60157907995.79 60525951281.94 61096018436.95 6338470773.70  63664893543.95 64290478175.79 64305420869.94 65419876591.79 65945316889.79 66140160580.94 66234375369.94 67630005728.79 6966639082.76  8834461625.94  9218853494.95  953034770.79   9895822270.94  00000A00i01601?01M01Z02P02Q02`02m03>03K03^03o04?05606106206?06j07807n08d08m09609D09]09f0:80:D0:Y0:f0;_0;h0<50<>0<N0=;0=D0=R0=g0>30>@0>S0>\0>j0?b0?k0@90@B0@O0@P0@Y0AI0AU0Aa0B30BK0BT0Ba0Bn0C>0CK0CL0CM0CZS4BGLO3LSB3RA02LZS2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZS3GLO3LSB3RA0S3LSB3RA0S3LSB3RA04CMP'S3LEN3LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'FS3TOP3LSB3RA01HS3GLO3LSB3RA0S3BSL3LSB3RA03CMPS3LEN3LSB3RA0S3TOP5SEPS23LSB3RA0S4BGLO3LSB3RA02LZS3LEN3LSB3RA02LRS3LEN2LO3GLO3TOP4SEPB5SEPS15SEPS25SEPS33LSB3RA02LR4CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'1HSS3GLO3LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS33LSB3RA02LRS4BGLO3LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'S3LSB3RA0S3LSB3RA0S4SPHI3LSB3RA0S3TOP5SEPS15SEPS23LSB3RA0S3LSB3RA0S3LEN3LSB3RA04CMP'S2LO3LSB3RA0S4BGLO3GLO3LSB3RA02LZS3S473LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'S3LSB3RA0S3GLO3LSB3RA0S3LSB3RA0S3LEN3LSB3RA02LRS4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZS3LSB3RA0S4SPHI3LSB3RA0S4BGLO3GLO3LSB3RA02LZS2LO3LSB3RA0S3GLO3LSB3RA0S3TOP5SEPS13LSB3RA0S3LSB3RA0S3LSB3RA04CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'1HS3LSB3RA0S4BGLO3LSB3RA0S3LSB3RA0S3GLO3LSB3RA0FS3LSB3RA0S3TOP4SEPB3LSB3RA03LEN4BGLO2LO3GLO5SEPS32LR4CMP'S2BS3LSB3RA0S2BS3LSB3RA0S3BHI4BGLO3LSB3RA0S3LEN4BGLO3LSB3RA02LZ2LRS3LSB3RA0S3BHI3LSB3RA0S3GLO3LSB3RA0S3LEN3LSB3RA02LRS3BHI3LSB3RA0FFS3S473LSB3RA0".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  unfold zlength in *.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  pose proof BUF as BUF0.
  apply (rw_cells_split_CB usegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
  cbn [mk_CB_cells app] in BUF.
  rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
  rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
  apply (proj1 (rw_cells_app usegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
  unfold implM, OUT_stderr.
  destruct (80 - zlength buf <? zlength bs) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
    eapply impl_evt.
    { eapply fwx_nofit with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    unfold file_cells in FC.
    transport_after_call usegs m m1 MU1 WM1.
    unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
    eapply impl_ebind.
    { eapply (stdio_write_spec (St:=St)) with (B := B) (fd := 2) (Fp := 122104) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
        (wend := B + 80) (bufsize := 80) (mode := mode) (lbf := 0xffffffff) (tail := tail) (flags := flags) (wfn := F_STDIO_WRITE);
        try reflexivity.
      - exact FC.
      - apply (bytes_at_ext _ _ _ _ _ (rw_cells_bytes_at _ _ _ _ BUFa)). cbn [cells_bytes cbytes]. rewrite app_nil_r. reflexivity.
      - exact SRC.
      - lia.
      - exact ST1.
      - unfold STDIO_WRITE_DEPTH. lia.
      - unfold GLOBALS_TOP in *; lia.
      - split; [exact GOT | exact GUARD].
      - exact MI1.
      - lia. - lia.
      - unfold got_ssp. lia.
      - unfold ssp_guard. lia.
      - lia. - lia.
      - unfold zlength. lia.
      - lia.
      - lia.
      - unfold zlength. lia.
      - lia. - lia. - unfold zlength in *. lia.      (* [comment removed for export] *)
      - right. unfold zlength. lia.
      - right. unfold zlength, GLOBALS_TOP in *. split; lia. }
    cbv beta. intros [[] st'] ms' PO. cbn [fst snd] in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDIO_WRITE_DEPTH in MU2.
    apply impl_ret_ok. cbn [fst snd]. apply evt_done.
    (* [comment removed for export] *)
    pose proof (rw_cells_transport usegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport usegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
    unfold out_post, SR. do 16 eexists. split; [reflexivity|].
    split. { apply (munch_trans _ m m1 m2).
             - eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
             - eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
    split.
    { (* [comment removed for export] *)
      exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
      split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
      split; [exact BUF2|]. split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
    split; [exact SSP2 | exact SRC2].
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
    cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
    apply impl_ret_ok. cbn [fst snd].
    unfold file_cells in FC.
    eapply evt_mono.
    { eapply (fwx_fit_plain ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
        (Fp := 122104) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest);
        [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
        [exact ST | exact MI].
    }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
    unfold out_post, SR. do 16 eexists.
    split. { reflexivity. }
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    assert (GOT2 : rw_cells usegs m2 117944 [C8 (Z_to_bv 64 320152)]).
    { eapply (rw_cells_transport usegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
    assert (GUARD2 : rw_cells usegs m2 320152 [C8 canary]).
    { eapply (rw_cells_transport usegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
    assert (BUFa2 : rw_cells usegs m2 B [CB (length buf) (zb buf)]).
    { eapply (rw_cells_transport usegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
    split.
    { (* [comment removed for export] *)
      exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
      split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
      split; [exact FL32|]. split; [exact FL8|].
      split.
      { (* [comment removed for export] *)
        assert (J : rw_cells usegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
        { cbn [app]. apply (proj2 (rw_cells_app usegs _ _ [_] _)); split; [exact BUFa2|].
          cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
        replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
      split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
    split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
