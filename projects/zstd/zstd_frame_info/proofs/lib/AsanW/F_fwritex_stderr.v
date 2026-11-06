(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg MonadF RtCells.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import Shadow SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.
#[using="Type"] Lemma zb_length : forall a, length (zb a) = length a.
Proof. intros. unfold zb. apply length_map. Qed.

#[using="Type"] Theorem fwritex_stderr_proof : fwritex_stderr_stmt.
Proof.
  unfold fwritex_stderr_stmt, out_stmt. intros St B RB. intros until canary.
  intros SINK SRC BYT BSL -> -> ST LO GLO SPHI TOP SSP MI SEPF SEPB SEPS1 SEPS2 SEPS3.
  intros KH ENV RS1 IN1 RB1 INB RSTK RIMG RSRC RFP RBUF RSH1 RSH2 S47.
  pose proof (rclean_shclean _ _ RS1) as SH1. pose proof (rclean_lt _ _ RS1) as LT1. unfold inreg in IN1. destruct IN1 as [IN1a IN1b].
  pose proof (rclean_shclean _ _ RB1) as SH2. pose proof (rclean_lt _ _ RB1) as LT2. unfold inreg in INB. destruct INB as [INBa INBb].
  unfold rrng in RSH1, RSH2.
  destruct st as [buf st].
  destruct SINK as (flags & mode & tail & rest & FC & FL32 & FL8 & BUF & LEN & BHI & BGLO). cbn [fst] in FC, BUF, LEN.
  unfold OUT_DEPTH, GLOBALS_TOP, INTERNAL_BUFSIZ in *.
  change asegs with asegs in *.
  destruct SSP as [GOT GUARD]. change asegs with asegs in GOT, GUARD. unfold got_ssp, ssp_guard in GOT, GUARD.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BS. rewrite zb_length in BS.
  assert (LSB : length (zb bs) = length bs) by apply zb_length.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0.
  Local Ltac2 Set LiaHints.tbl := fun () => "01g0?10611404139.10210729357726.10410999467945.12011563010027.10211694973547.10211770142661.10412090737193.12012618137047.12714002117805.11914049017578.1191451302806.104 14651502089.11915321660364.10215611898301.14216016492470.10416900404843.10217207757499.14017395657067.10219475977055.10419988007508.10420091109937.11920774987436.10221217265228.10221881176170.10422700267513.14423032126699.10223049808277.10423170724940.10223545217228.10224921050300.10424953689962.1022633512555.102 26525069896.10427060004634.10428040198754.14128575982988.12829158771112.94 29442969842.10429637151233.12830062733858.12031386913421.10431551594020.11931990977881.10432769765461.10433039702827.10434037206704.10534065297888.10434238060565.11936602215619.12937585905868.10238040770411.104394700872.104  40069857996.10240569449706.11940821674190.11941596052879.12041800319328.95 41804464219.10442007380850.10442150790724.11942875407207.11943089771019.10243420333474.11943626705115.10443888721210.10444759514212.10444862470808.10445008699991.12645617647863.10446293961676.10246642331949.11946657274679.10447475043691.10250095796337.1195050558744.104 50746667550.10451085747889.10451363943620.10451978563788.10252148621422.10452225561217.10453730415077.10454886540492.10255430152575.10155667454156.1025600903253.104 57615708368.13057622410744.14458657744726.10459274971627.10259647585643.10259848878127.11960045862637.10560157907995.10461096018436.12061919421545.1196338470773.93  63664893543.12063695158123.10264290478175.10464305420869.11965393239372.10265419876591.10465545380009.12065945316889.10466140160580.11966233910611.11966234375369.11967012592138.10467085980385.11967150539009.1046855269461.104 6966639082.101 7315844459.102 7966424877.104 8008354764.102 9218853494.120 953034770.104  9895510799.6   00000900E00R00[00d01L01Y01n02702@02N02W02X02e02f02o03e03n03o04004=04>04?04@04O04X04e04f04g05805E05N05_05o06f07a07b07o08Z09P09Q0:G0:H0:I0:R0;I0;V0;o0<A0<B0<N0<O0<P0<Y0<f0=_0=h0>40>50>B0>P0>Y0>i0?V0?_0@20@C0@X0@f0@g0A00A90AB0AN0A\0Ah0B;0BG0BH0B[0Bl0Bm0Bn0C70C80C90CG0D?0DL0DU0D^0Dl0Dm0E60E70E@0EI0F90FB0FN0FZ0F[0Fm0G:0GR0G[0Gd0H10HF0HV0Hc0Hd0I40I=0IK0IL0IM0IN0IWS4BGLO2H1S3LSB3RA02LZS3GLO3LSB3RA0S4BGLO2H1S4BGLO2H1S2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZS3GLO3LSB3RA0S4BGLO3GLO3LSB3RA02LZS3LSB3RA0S3LSB3RA0S3LSB3RA04CMP'S3LSB3RA0SS3LEN3LSB3RA0FS4BGLO2H1S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'S4BGLO2H1FFS3GLO3LSB3RA0SSFS3TOP3LSB3RA01HS4BGLO2H1S3LT23LSB3RA0SSS3BSL3LSB3RA03CMPS3LEN3LSB3RA0S4BGLO2H1S4BGLO3LSB3RA02LZS3LEN3LSB3RA02LRS3LEN2LO3GLO3TOP4SEPB5SEPS15SEPS25SEPS33LSB3RA02LR4CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'1HSS3GLO3LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS33LSB3RA02LRS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'FS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'FFS3LSB3RA0S2LO3TOP4SEPB5SEPS15SEPS32KH4INBa4INBb3LSB3RA02H12H32ABS3GLO3LSB3RA0S3TOP5SEPS15SEPS23LSB3RA0S3LEN3LSB3RA04CMP'SS2LO3LSB3RA0FSS3LSB3RA0S3S473LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'S3LSB3RA0S3LSB3RA02LSFS3GLO3LSB3RA0S4BGLO3LSB3RA0S4BGLO2H1S3LEN3LSB3RA02LRS4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZS3LSB3RA0S3TOP5SEPS23LSB3RA0S4INBa3LSB3RA02LZS4BGLO3GLO3LSB3RA02LZS4SPHI3LSB3RA0SS3LSB3RA0S3LSB3RA0S4BGLO2H1S2LO3LSB3RA0S4IN1b3LSB3RA0S2LO3LSB3RA0S4INBb3LSB3RA04CMP'S2KH3LSB3RA0SS3TOP5SEPS13LSB3RA0S4BGLO3LSB3RA02LZFSS3LSB3RA0SFS3LSB3RA04CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'1HS3BSL3LSB3RA0S4BGLO2H1S4BGLO2H1S4BGLO3LSB3RA0SS3LSB3RA0FS3LSB3RA0S3LSB3RA0S3TOP4SEPB3LSB3RA03LEN4BGLO2LO3GLO5SEPS32LR4CMP'S4BGLO2H1S2BS3LSB3RA0S2BS3LSB3RA0SS3BHI4BGLO3LSB3RA0S3GLO3LSB3RA0S3LEN4BGLO3LSB3RA02LZ2LRS3LSB3RA0S3LSB3RA0S3BHI3LSB3RA0S3LSB3RA04CMP'3LEN2LRS3LEN3LSB3RA02LRS3LT13LSB3RA0FS3LEN3LSB3RA02LRS4BGLO2H1S4IN1a3LSB3RA0SFFS3S473LSB".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
  assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
  assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
  unfold zlength in *.
  set (S := bv_unsigned a0) in *.
  assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
  (* [comment removed for export] *)
  assert (SAFE : forall wpos l, B <= wpos -> 0 <= l -> ashsafe [(644112 + 40, 644112 + 48); (wpos, wpos + l)]).
  { intros wpos l H1 H2. unfold ashsafe; cbn [disjoint_from]. unfold GLOBALS_TOP in *. repeat split; lia. }
  assert (APW : forall wpos l, B <= wpos -> 0 <= l -> wpos + l <= B + 80 -> appW [(644112 + 40, 644112 + 48); (wpos, wpos + l)]).
  { intros wpos l H1 H2 H3. pose proof (shclean_app_blk _ _ _ _ _ SH2) as AB. unfold app_blk in AB.
    apply appW_cons; [left; cbn; unfold KLOW; lia|]. apply appW_cons; [cbn [fst snd]; unfold KLOW, KHIGH in *; lia|]. apply appW_nil. }
  (* [comment removed for export] *)
  pose proof BUF as BUF0.
  apply (rw_cells_split_CB asegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
  cbn [mk_CB_cells app] in BUF.
  rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
  rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
  apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
  cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
  unfold implAM, OUT_stderr.
  destruct (80 - zlength buf <? zlength bs) eqn:CMP.
  - (* [comment removed for export] *)
    pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
    eapply implF_evtF.
    { eapply (fwx_nofit RNG) with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia | exact RSTK | exact RFP]. }
    cbv beta. intros ms1 PO.
    destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
    unfold file_cells in FC.
    transport_after_call asegs m m1 MU1 WM1.
    unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
    eapply implF_ebind.
    { eapply (stdio_write_spec (St:=St) RNG) with (B := B) (fd := 2) (Fp := 644112) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
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
      - right. unfold zlength. lia.
      - right. unfold zlength, GLOBALS_TOP in *. split; lia.
      - solve_rng.
      - eapply rng_sub; [exact RFP| lia| lia].
      - eapply rng_sub; [exact RBUF| lia| unfold zlength in *; lia].
      - exact RSRC.
      - exact RIMG.
      - exact SPHI. - exact BHI. - clear - S47 BS LSB; unfold zlength in *; lia. }   (* [comment removed for export] *)
    cbv beta. intros [[] st'] RNG' ms' [-> PO]. cbn [fst snd] in PO.
    destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
    unfold STDIO_WRITE_DEPTH in MU2.
    apply implAM_retF. cbn [fst snd]. apply evtF_done.
    (* [comment removed for export] *)
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
    pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
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
    apply implAM_retF. cbn [fst snd].
    unfold file_cells in FC.
    eapply evtF_mono.
    { eapply (fwx_fit_plain RNG ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
        (Fp := 644112) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest)
        (SLO1 := r_lo rs) (SHI1 := r_hi rs) (RLO1 := r_rlo rs) (RHI1 := r_rhi rs) (SLO2 := r_lo RB) (SHI2 := r_hi RB) (RLO2 := r_rlo RB) (RHI2 := r_rhi RB);
        [ exact FC | exact BUFb | lia | exact SRC | rewrite LSB; reflexivity | exact EA0 | reflexivity | reflexivity | try lia .. ];
        first [ exact ST | exact MI | exact KH | exact ENV | exact SH1 | exact SH2 | exact RSTK | exact RIMG | exact RSRC | exact RFP | exact RSH1 | exact RSH2
              | apply SAFE; lia | apply APW; lia | eapply rng_sub; [exact RBUF| lia| lia] | solve_rng | lia ].
    }
    cbv beta. intros ms' PO.
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & DST2 & SRC2).
    unfold out_post, SR. do 16 eexists.
    split. { reflexivity. }
    split. { eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    assert (GOT2 : rw_cells asegs m2 629480 [C8 (Z_to_bv 64 6241872)]).
    { eapply (rw_cells_transport asegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
    assert (GUARD2 : rw_cells asegs m2 6241872 [C8 canary]).
    { eapply (rw_cells_transport asegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
    assert (BUFa2 : rw_cells asegs m2 B [CB (length buf) (zb buf)]).
    { eapply (rw_cells_transport asegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
    split.
    { (* [comment removed for export] *)
      exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
      split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
      split; [exact FL32|]. split; [exact FL8|].
      split.
      { (* [comment removed for export] *)
        assert (J : rw_cells asegs m2 B ([] ++ [CB (length buf) (zb buf); CB (length (zb bs)) (zb bs); CB (80 - length buf - length (zb bs))%nat (skipn (length (zb bs)) rest)] ++ [])).
        { cbn [app]. apply (proj2 (rw_cells_app asegs _ _ [_] _)); split; [exact BUFa2|].
          cbn [cells_size csize]. rewrite Nat.add_0_r. exact DST2. }
        apply rw_cells_merge in J. cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite app_nil_r in J.
        rewrite zb_app, <- app_assoc. rewrite LSB in J |- *.
        replace (length buf + (length bs + (80 - length buf - length bs + 0)))%nat with 80%nat in J by lia. exact J. }
      split; [| split; [exact BHI| exact BGLO]].
      unfold zlength. rewrite length_app, length_skipn, LSB. lia. }
    split; [split; [exact GOT2 | exact GUARD2] | exact SRC2].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
