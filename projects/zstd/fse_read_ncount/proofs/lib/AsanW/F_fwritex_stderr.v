(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import F_syscalls F_printf_iface F_stdio_write F_fwritex_gen StdioFiles Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import Stdio_kit.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg MonadF RtCells.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import Shadow SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

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
Local Ltac2 Set LiaHints.tbl := fun () => "01e0?10729357726.10411770142661.10413117980364.10214002117805.11914351919692.1021451302806.104 15281220940.10215611898301.14216016492470.10417160999041.10417207757499.14018712161643.10219475977055.10419988007508.10420060073676.10220998539757.10521881176170.10421964658124.10222700267513.14423049808277.10424643972459.10224921050300.10424953689962.10226253705737.11926426338985.12026525069896.10427060004634.10427518659881.12028040198754.14128575982988.12828831374955.10229158771112.94 29278655210.11929442969842.10429541024490.11929637151233.12830062733858.12031386913421.10431551594020.11931990977881.10432769765461.10434037206704.10534238060565.1193497153895.119 36558830692.10436602215619.12937320623921.11937718411980.10238040770411.10438270701015.127394700872.104  40821674190.11941363315541.10441596052879.12041800319328.95 41804464219.10441969970515.11942007380850.10442150790724.11942259035991.12643420333474.11943626705115.10443888721210.10444862470808.10445356344171.10245617647863.10445623019883.10247772741836.1024977323755.102 50095796337.1195026896395.102 5050558744.104 50746667550.10451085747889.10451363943620.10452041796075.10252148621422.10452262902476.10253318530508.10253730415077.10454790639785.12055430152575.10155769886059.10257615708368.13057622410744.14458657744726.10458900669612.10259622491616.10459848878127.11960157907995.10460717558860.10261096018436.12061816805580.10261919421545.1196338470773.93  63664893543.12063695158123.10264290478175.10464305420869.11964515086251.10465419876591.10465945316889.10466140160580.11966234375369.11967012592138.10467085980385.11967150539009.1046855269461.104 68706874987.10268711652331.1026966639082.101 7966424877.104 8279438381.119 8281273911.104 9218853494.120 953034770.104  9895510799.6   00000<00d00e00n00o01=01>01K01L01]02S02\02]02^02_02`02a02b03103>03G03X03e03n04;04L04\04i05`06[06d06e06n07;07D07o08e08f09\09]09^0:U0:n0;<0;O0;a0;n0;o0<;0<P0<Q0<^0<_0=X0=a0=m0>60>70>D0>Y0>i0?V0?_0@00@90@G0@P0@Q0@Z0@f0@o0A=0AI0A\0Ah0B10BD0BE0BF0BG0BT0B]0Bf0C40Cl0D90D:0DG0DU0D^0D_0D`0Da0Dj0E30Ec0El0F80FD0FM0F_0G70G@0GM0Gb0H20H?0H@0HI0HR0Hb0I00I90IB0IC0ID0IMS3LSB3RA02LZS2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZSS3LSB3RA0SS3LSB3RA04CMP'SS3LEN3LSB3RA0FS4BGLO3LSB3RA02LZS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'S4BGLO2H1FFSSFSS3TOP3LSB3RA01HS3LT23LSB3RA0S4BGLO2H1S3BSL3LSB3RA03CMPS3LEN3LSB3RA0S3LSB3RA0S3GLO3LSB3RA0S4BGLO3LSB3RA02LZS3LEN3LSB3RA02LRS3GLO3LSB3RA0S3LEN2LO3GLO3TOP4SEPB5SEPS15SEPS25SEPS33LSB3RA02LR4CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'1HS4BGLO2H1SS3LSB3RA0S3GLO3LSB3RA0S3LSB3RA0S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS33LSB3RA02LRS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'FS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'FFS2LO3TOP4SEPB5SEPS15SEPS32KH4INBa4INBb3LSB3RA02H12H32ABS3TOP5SEPS15SEPS23LSB3RA0S4BGLO3LSB3RA0S3TOP5SEPS23LSB3RA0S3LEN3LSB3RA04CMP'S3GLO3LSB3RA0SS2LO3LSB3RA0S4BGLO3GLO3LSB3RA02LZFS3S473LSB3RA0FS3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZ2LR4CMP'S3LSB3RA0S3LSB3RA02LSS3LSB3RA0FS3GLO3LSB3RA0S4BGLO3GLO3LSB3RA02LZS3LEN3LSB3RA02LRS4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LZS3LSB3RA0S4INBa3LSB3RA02LZS4BGLO2H1S4SPHI3LSB3RA0S4BGLO2H1SS4BGLO2H1S2LO3LSB3RA0S4BGLO2H1S4IN1b3LSB3RA0S2LO3LSB3RA0S4INBb3LSB3RA04CMP'S2KH3LSB3RA0S4BGLO2H1S3TOP5SEPS13LSB3RA0SSFS3GLO3LSB3RA0S3LSB3RA0S4BGLO2H1S3LSB3RA04CMP'S3LEN4BGLO2LO3GLO3TOP4SEPB5SEPS15SEPS33LSB3RA02LR4CMP'1HS3BSL3LSB3RA0SS3GLO3LSB3RA0S4BGLO3LSB3RA0S3LSB3RA0SFSS3LSB3RA0S3LSB3RA0S3TOP4SEPB3LSB3RA03LEN4BGLO2LO3GLO5SEPS32LR4CMP'S4BGLO2H1S2BS3LSB3RA0S2BS3LSB3RA0S3LSB3RA0S3BHI4BGLO3LSB3RA0S3LEN4BGLO3LSB3RA02LZ2LRS3LSB3RA0S3BHI3LSB3RA0S3LSB3RA04CMP'3LEN2LRS3LEN3LSB3RA02LRS3LT13LSB3RA0FS4BGLO2H1S4BGLO2H1S3LEN3LSB3RA02LRS4IN1a3LSB3RA0S3LSB3RA0S3LSB3RA0FFS3S473LSB".
assert (LZ : 0 <= zlength buf) by (unfold zlength; lia).
assert (LR : 0 <= zlength rest) by (unfold zlength; lia).
assert (LS : 0 <= zlength bs) by (unfold zlength; lia).
unfold zlength in *.
set (S := bv_unsigned a0) in *.
assert (EA0 : a0 = Z_to_bv 64 S) by (subst S; symmetry; apply Z_to_bv_bv_unsigned).
assert (SAFE : forall wpos l, B <= wpos -> 0 <= l -> ashsafe [(646456 + 40, 646456 + 48); (wpos, wpos + l)]).
{ intros wpos l H1 H2. unfold ashsafe; cbn [disjoint_from]. unfold GLOBALS_TOP in *. repeat split; lia. }
assert (APW : forall wpos l, B <= wpos -> 0 <= l -> wpos + l <= B + 80 -> appW [(646456 + 40, 646456 + 48); (wpos, wpos + l)]).
{ intros wpos l H1 H2 H3. pose proof (shclean_app_blk _ _ _ _ _ SH2) as AB. unfold app_blk in AB.
apply appW_cons; [left; cbn; unfold KLOW; lia|]. apply appW_cons; [cbn [fst snd]; unfold KLOW, KHIGH in *; lia|]. apply appW_nil. }
pose proof BUF as BUF0.
apply (rw_cells_split_CB asegs _ _ [] 80 (zb buf ++ rest) [] [length buf; 80 - length buf]%nat) in BUF; [| cbn; unfold zlength in *; lia].
cbn [mk_CB_cells app] in BUF.
rewrite firstn_app, zb_length, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 in BUF by (rewrite zb_length; lia).
rewrite skipn_app, zb_length, Nat.sub_diag, skipn_O, skipn_all2 in BUF by (rewrite zb_length; lia). cbn [app] in BUF.
apply (proj1 (rw_cells_app asegs _ _ [_] _)) in BUF. destruct BUF as [BUFa BUFb].
cbn [cells_size csize Nat.add] in BUFb. rewrite Nat.add_0_r in BUFb. rewrite ?firstn_all2 in BUFb by lia.
unfold implAM, OUT_stderr.
destruct (80 - zlength buf <? zlength bs) eqn:CMP.
-
pose proof (proj1 (Z.ltb_lt _ _) CMP) as CMP'. unfold zlength in CMP'.
eapply implF_evtF.
{ eapply (fwx_nofit RNG) with (lo := lo); [exact FC | exact EA0 | reflexivity | reflexivity | lia | lia | unfold zlength in *; lia | lia | lia | reflexivity | exact ST | lia | lia | exact MI | lia | exact RSTK | exact RFP]. }
cbv beta. intros ms1 PO.
destruct PO as (t0' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & -> & MU1 & WM1 & MI1 & ST1).
unfold file_cells in FC.
transport_after_call asegs m m1 MU1 WM1.
unfold INTERNAL_BUFSIZ. cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with true by (symmetry; exact CMP) end. cbv beta iota zeta.
eapply implF_ebind.
{ eapply (stdio_write_spec (St:=St) RNG) with (B := B) (fd := 2) (Fp := 646456) (buf := buf) (s := bs) (S := S) (lo := lo) (canary := canary)
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
- exact SPHI. - exact BHI. - clear - S47 BS LSB; unfold zlength in *; lia. }
cbv beta. intros [[] st'] RNG' ms' [-> PO]. cbn [fst snd] in PO.
destruct PO as (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & -> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2 & ->).
unfold STDIO_WRITE_DEPTH in MU2.
apply implAM_retF. cbn [fst snd]. apply evtF_done.
pose proof (rw_cells_transport asegs _ m1 m2 _ _ BUF0 MU2 WM2 ltac:(cbn; lia)) as BUF2.
pose proof (bytes_at_transport asegs _ m1 m2 _ _ SRC MU2 ltac:(cbn; rewrite LSB; lia)) as SRC2.
unfold out_post, SR. do 16 eexists. split; [reflexivity|].
split. { apply (munch_trans _ m m1 m2).
- eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]; intros; lia.
- eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
split; [eapply wmono_trans; [exact WM1 | exact WM2] |]. split; [exact MI2|]. split; [exact ST2|].
split.
{
exists flags, mode, tail, (zb buf ++ rest). cbn [fst].
split; [rewrite Z.add_0_r; exact FC2|]. split; [exact FL32|]. split; [exact FL8|].
split; [exact BUF2|]. split; [| split; [exact BHI| exact BGLO]].
unfold zlength. cbn [length]. rewrite length_app, zb_length. lia. }
split; [exact SSP2 | exact SRC2].
-
pose proof (proj1 (Z.ltb_ge _ _) CMP) as CMP'. unfold zlength in CMP'.
cbv beta iota zeta. match goal with |- context [if ?c then _ else _] => replace c with false by (symmetry; exact CMP) end. cbv beta iota zeta.
apply implAM_retF. cbn [fst snd].
unfold file_cells in FC.
eapply evtF_mono.
{ eapply (fwx_fit_plain RNG ra sp gp tp t0 t1 t2 s0 s1 a0) with (lo := lo) (cap := (80 - length buf)%nat) (src := zb bs) (S := S)
(Fp := 646456) (wend := B + 80) (wpos := B + Z.of_nat (length buf)) (junk := rest)
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
assert (GOT2 : rw_cells asegs m2 631824 [C8 (Z_to_bv 64 6247504)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GOT | exact MU2 | exact WM2 | cbn; lia]. }
assert (GUARD2 : rw_cells asegs m2 6247504 [C8 canary]).
{ eapply (rw_cells_transport asegs _ m m2); [exact GUARD | exact MU2 | exact WM2 | cbn; lia]. }
assert (BUFa2 : rw_cells asegs m2 B [CB (length buf) (zb buf)]).
{ eapply (rw_cells_transport asegs _ m m2); [exact BUFa | exact MU2 | exact WM2 | cbn; lia]. }
split.
{
exists flags, mode, tail, (skipn (length (zb bs)) rest). cbn [fst].
split. { unfold zlength. rewrite length_app, Nat2Z.inj_add, Z.add_assoc. exact FC2. }
split; [exact FL32|]. split; [exact FL8|].
split.
{
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
