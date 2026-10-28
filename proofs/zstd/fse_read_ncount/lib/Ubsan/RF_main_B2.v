(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ua := idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma rw_cells_CB0 : forall m A, 0 <= A <= 2^64 -> rw_cells usegs m A [CB 0%nat []].
Proof.
intros m A H. split; [split|].
- cbn. split; [reflexivity| exact I].
- cbn [cells_bytes cbytes app]. apply bytes_at_nil. exact H.
- cbn [cells_size csize Nat.add]. Local Ltac2 Set LiaHints.tbl := fun () => "0030=24938099585.440675941957.441283725690.600000300600:S1HS1HS2Hi".
split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma rw_cells_CB_join : forall m A n1 n2 (b1 b2 : list byte),
rw_cells usegs m A [CB n1 b1] -> rw_cells usegs m (A + Z.of_nat n1) [CB n2 b2] ->
rw_cells usegs m A [CB (n1 + n2)%nat (b1 ++ b2)].
Proof.
intros m A n1 n2 b1 b2 H1 H2.
assert (H : rw_cells usegs m A ([CB n1 b1] ++ [CB n2 b2])).
{ apply (proj2 (rw_cells_app _ _ _ _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r. exact H2. }
destruct H as [[Hwf HB] HW]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
split; [split|].
- cbn. rewrite length_app. Local Ltac2 Set LiaHints.tbl := fun () => "0020>26384963688.132888234679.13 00000700>S2L12L2S2L12L2".
split; [lia| exact I].
- cbn [cells_bytes cbytes app] in HB |- *. rewrite !app_nil_r in HB |- *. exact HB.
- replace (Z.of_nat (cells_size [CB (n1 + n2)%nat (b1 ++ b2)])) with (Z.of_nat (cells_size ([CB n1 b1] ++ [CB n2 b2]))) by (cbn; lia). exact HW.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section B2.
Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (arg0 arg1 : list byte) (TID : Z)
(J8 : list byte) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
Hypothesis VSP : dvalid_sp sp0 argv envp.
Hypothesis VARGV : valid_argv argv.
Hypothesis VENVP : valid_envp envp.
Hypothesis EARGV : argv = [arg0; arg1].
Hypothesis HT : 0 < TID < 4194304.
Hypothesis MALLOC : rmalloc_stmt.
Hypothesis FREE : rfree_stmt.
Hypothesis FPR : @fprintf_diag_stmt PState.
Hypothesis FWX : fwritex_stderr_stmt.
Hypothesis SWF : stdio_write_flush_stmt.
Hypothesis FWR : @fwrite_diag_stmt PState.
Hypothesis TOW : towrite_stmt.
Notation usp0 := (bv_unsigned sp0).
Notation gpv := (Z_to_bv 64 0x10800).
Notation tpv := (Z_to_bv 64 RATP).
Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
Notation POSTBODY' := (POSTBODY sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
#[using="arg0 VSP VARGV VENVP EARGV HT FPR FWX SWF"] Lemma rd_read_core : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a1 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem) (A CNT : Z) (DATA junk sj : list byte) (errv : word),
3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj ->
Z.of_nat (length DATA) < rd_cap st1 ->
CNT = (if 65536 <? rd_cap st1 - Z.of_nat (length DATA) then 65536 else rd_cap st1 - Z.of_nat (length DATA)) ->
FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
implM usegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
(GST 0x13164 x1 t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 65536) a1 (Z_to_bv 64 CNT) a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (Z.of_nat (length DATA))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until errv. intros FD HP1 HC BU SJ LT ECNT0 FR BA ERR FRM.
pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
destruct BU as (P0 & FA0 & SO0 & _ & BLK & [CAPR CAPK] & LENR & BR). pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts. pose proof PSTAGE_LEN_Z as PSTAGER.
pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
unfold MAX_INPUT in CAPR.
assert (CNTR : 1 <= CNT <= 65536 /\ CNT <= rd_cap st1 - Z.of_nat (length DATA)).
{ rewrite ECNT0. Local Ltac2 Set LiaHints.tbl := fun () => "01N0?10378964495.15210479223267.13410571041724.99 11805550483.15312571846664.15612723551514.12015091876170.14015188341087.1201533903831.99  15787415602.99 15802522775.12015975902217.15215975902217.15315988681662.13416075584073.12116075584458.12116145740187.15316147837319.13416431039697.12016583139070.98 16726501678.12017769516388.99 18198853898.1201824529279.119 18932035050.15121487896573.12023640171742.99 25299558642.14126492304053.11826591870389.95 26916898118.11728186272870.15328703860911.11929269309704.15230091987038.11730772704877.15331701494120.14033867879905.13434667073629.15235551827507.99 36833387915.15637734843123.99 38339826923.15339090096978.13339448547998.12041219967894.15341796544081.15142022055264.15442149587807.11942733996238.11942845074760.95 4306029353.152 43413452237.11944131240248.11844279961850.15245458496000.15146720414871.11946849733622.11849919069086.1515078321122.133 51551415527.11951791573024.15252098681508.99 52650796170.95 52695808289.11853908434000.11954133639715.15554268287127.11759017429902.11859206904098.15659209280777.12059308628179.1  59308628304.12259321100273.10 59321170897.12059409705057.13460517231664.11960897740723.14061563400992.1406167618490.140 62261235758.1176292924095.152 64014194870.13464070790100.15664146473546.99 66023885878.99 66030078099.12066136628136.18 66603335140.99 7209889221.120 8697535581.152 8828222487.120 8838740146.99  981144086.153  00000B00O00X00Y01501901?01C01I01J01K01a02702M02Z02g03403A03V03\03b03h04104F04o05005405<05=05@05A05N05O06:06I06]06c07507G07H07P07T07U07]07^07f08808E08N08O08U08k08l09@09A09I09M09f0::0:J0:S0:g0:h0;=0;M0;N0;V0;W0;X0;e0<20<60<A0<N0<`0=:0=O0=X0=i0>00>10>C0>K0>]0>^0>b0>f0?20?80?90?F0?G0?H0?]S4CNTR4ELEN3Hbs2BBS4CNTR3Hbs2BBS2SF4CNTRFS2SF3BR17PSTAGER4CNTR3Hbs2BBS2SFS4P1LOS2SFS4CNTRSSS3BR54CNTR4ELEN3Hbs2BBS3BR54CNTR4ELEN3Hbs2BBS3BR54CNTR4ELEN3Hbs2BBS4CNTR3Hbs2BBS4CNTR3Hbs2BBS4CNTR3Hbs2BBS4CNTR3Hbs2BBS2LT4CNTR4ELEN3Hbs2BBS4ELENS4CNTRS4CNTRS2SF4CNTRS2SF3BR17PSTAGER4CNTRS4CAPR3BR13BR43BR55ATOPR4CNTR4ELEN3Hbs2BBFS2FDS4P1HI1HFS1lSS4ELEN3Hbs2BBSS2LT3BR54CNTR4ELEN3Hbs2BB2SF3BR17PSTAGER2K1S2SF5ATOPR4CNTRS2SF3BR44CNTR3Hbs2BBS4SLK1S4CNTR4ELEN3Hbs2BBS4CNTR4ELEN3Hbs2BBSS3Hbs2BBS2SFFS3Hbs2BBFS3Hbs2BBS4LENZ4CNTR3Hbs2BBS4CNTR3Hbs2BBS2SF4CNTRFS2LT1nS3BR54CNTR4ELEN3Hbs2BBFS2LT2SF3BR13BR54ELENFS3Hbs2BBS2SFS2LT2SF3BR13BR54CNTR4ELENS2SF3BR44CNTR3Hbs2BBS2LT4CNTR3Hbs2BBS2SF4CNTRS2SF3BR44CNTR3Hbs2BBSS2SF3BR17PSTAGER4CNTRS2LT2SF3BR44ELENSS3Hbs2BBSFS4CAPR3Hbs2BBS4CAPR3Hbs2BBS2K0S3Hbs2BB2K1S2K03Hbs4CNTRS2SF3Hiv4CNTR4Hiv2S2SF3BR45ATOPR4CNTR3Hbs2BBS2SF3BR17PSTAGER4CNTRS2SF4P1LOS2SF4P1LO4P1HI2ILS5A1LENSS4CNTR4LEN03Hbs2BBS3Hbs2BBS4CNTR4ELEN3Hbs2BBSS2SFS2SFS2SF1H2H02H4S4CNTRSS4CNTR3Hbs2BBSSS2LT4CNTR4ELEN3Hbs2BB".
destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); lia. }
unfold rd_read_part. cbv zeta. rewrite LENZ, <- ECNT0.
unfold MFRAME in FR. unfold RERRNO in ERR. unfold STAGE, UREAD_STAGE in SJ.
unfold implM. iprefix.
zstep. zstep. zstep.
apply (rw_cells_split_CB usegs _ _ [] _ _ [] [Z.to_nat CNT; (PSTAGE_LEN - Z.to_nat CNT)%nat]) in SJ; [| cbn; lia].
cbn [mk_CB_cells app] in SJ.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in SJ. destruct SJ as [SJ1 SJ2]. cbn [cells_size csize Nat.add] in SJ2.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
set (LEN := Z.of_nat (length DATA)) in *.
assert (ELEN : LEN = Z.of_nat (length DATA)) by reflexivity. clearbody LEN. assert (LEN0 : 0 <= LEN) by lia.
eapply implM_bind.
{ set (w1 := Z_to_bv 64 UREAD_STAGE). unfold UREAD_STAGE in w1.
replace UREAD_STAGE with (bv_unsigned w1) by (subst w1; unfold UREAD_STAGE; rewrite unsigned_lit; lia).
eapply implM_of_enode.
eapply read_spec with (lo := usp0 - 8388608) (junk := firstn (Z.to_nat CNT) sj) (errv := errv); subst w1; unfold RATP;
rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit 126505) by lia; try reflexivity;
first [exact ST | exact SJ1 | exact ERR | exact MI | lia]. }
cbv beta. intros a s' ms' [PO ->].
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MUc & WMc & MI2 & ST2 & RES).
unfold RATP in MUc, RES. rewrite !unsigned_lit in MUc by lia. rewrite ?unsigned_lit in ST2 by lia. rewrite ?unsigned_lit in RES by lia.
change (192304 + -164) with 192140 in MUc, RES.
transport_after_call usegs mm m2 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x13170)) with (Z_to_bv 64 0x13170) by (symmetry; rpc).
rename ST2 into ST2'.
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 16, usp0 + -128); (126505, 126505 + Z.of_nat (Z.to_nat CNT)); (192140, 192140 + 4)]).
{ unfold WOK, LO, RERRNO, UREAD_STAGE. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; lia. }
assert (P2 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m2).
{ eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact P0].
intros iv [<-|[<-|[<-|[]]]]; cbn [fst snd]; intros Hiv Hiv2; exfalso; lia. }
assert (BA2 : BASE' m2) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI2| unfold LO; first [exact ST2' | replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2']]).
remember (firstn (PSTAGE_LEN - Z.to_nat CNT) (skipn (Z.to_nat CNT) sj)) as JR eqn:EJR. clear EJR.
clear MUc WMc BA WOKW.
destruct a as [e|bs]; cbn [read_ret] in *.
-
destruct RES as (SJ1' & ERR2 & He).
pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & TR3). pose proof RS3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
pose proof VARGV as (_ & _ & ARGLEN & NONUL & _).
destruct (argv_cstring sp0 argv envp uid hw draw m2 IMG3 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
as (p1 & slack1 & HP1' & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL.
rewrite HP1 in HP1'. assert (EP : Z_to_bv 64 P1v = Z_to_bv 64 p1) by congruence. rewrite EP. clear HP1' EP.
assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
unfold implM. iprefix.
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
cbn [io_diag Prog.io io_S].
eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF (DReadError (map bv_unsigned arg1)));
[| exact BA2| exact P2| exact SO0| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
unfold F_fmt_fp_lib.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|].
pose proof (IMGB_top sp0 argv envp uid hw draw VSP). lia.
- destruct RES as (SJ1' & ERR2 & Hbs).
pose proof (bytes_at_bound _ _ _ _ (proj2 (proj1 SJ1'))) as BB. cbn [cells_bytes cbytes app] in BB. rewrite !length_app, length_skipn in BB.
unfold implM. iprefix.
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0 Hbs CAPR LEN0 CNTR LENR; clear; intros; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. if_cases K1; zify_cond K1.
+
pose proof BA2 as (ST3 & MI3 & RS3 & AUX3 & IMG3 & SE3 & SOF3 & TR3). unfold LO in ST3.
apply (proj1 (rw_cells_app _ _ _ [CB (length bs) bs] _)) in SJ1'. destruct SJ1' as [SJa SJb]. cbn [cells_size csize Nat.add] in SJb.
pose proof (rw_cells_bytes_at _ _ _ _ SJa) as SRCB. cbn [cells_bytes cbytes app] in SRCB. rewrite app_nil_r in SRCB.
pose proof BLK as BLK2. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLK2. destruct BLK2 as [BLK1 BLK2].
cbn [cells_size csize Nat.add] in BLK2. replace (length DATA + 0)%nat with (length DATA) in BLK2 by lia.
apply (rw_cells_split_CB usegs _ _ [] _ _ [] [length bs; (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat]) in BLK2; [| cbn; lia].
cbn [mk_CB_cells app] in BLK2.
apply (proj1 (rw_cells_app _ _ _ [_] _)) in BLK2. destruct BLK2 as [BLK2 BLK3]. cbn [cells_size csize Nat.add] in BLK3.
zstep. zstep. zstep. zstep.
eapply evt_cut.
{ eapply memcpy_callv with (src := bs) (junk := firstn (length bs) junk);
[ unfold UREAD_STAGE; exact SRCB | lia | replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) by lia; replace (A + LEN) with (A + Z.of_nat (length DATA)) by lia; exact BLK2
| unfold UREAD_STAGE; lia | lia | unfold UREAD_STAGE; lia | lia | exact MI3 ]. }
cbv beta. intros ms'' PO.
destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MUd & WMd & MI4 & NB & _).
ua. transport_after_call usegs m2 m3 MUd WMd.
replace (ret_pc (Z_to_bv 64 0x13108)) with (Z_to_bv 64 0x13108) by (symmetry; rpc).
assert (WOKD : Forall (WOK sp0) [(A + LEN, A + LEN + Z.of_nat (length bs))]).
{ unfold WOK. constructor; [right; right; left; cbn [fst snd]; lia| constructor]. }
assert (P3 : RHEAP s [(rd_buf st1, A, rd_cap st1)] m3).
{ eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKD| exact MUd| exact WMd| | exact P2].
intros iv [<-|[]]. cbn [fst snd]. intros _ _. exists (rd_buf st1, A, rd_cap st1). split; [left; reflexivity|]. cbn [fst snd blk_addr blk_size]. lia. }
assert (BA3 : BASE' m3) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA2| exact WOKD| exact MUd| exact WMd| exact MI4| unfold LO; first [exact ST3 | replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3]]).
clear MUd WMd WOKD.
zstep. zstep.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
replace (length bs =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; intros E; rewrite E in K1; apply K1; reflexivity).
apply implM_ret. apply evt_done. cbn [POSTBODY]. unfold RDINV. cbn [rd_content rd_cap rd_buf].
assert (LEN' : zlength (rd_content st1 ++ u8s_of_bytes bs) = LEN + Z.of_nat (length bs)).
{ unfold zlength, u8s_of_bytes. rewrite length_app, length_map. unfold zlength in LENZ. lia. }
rewrite LEN'.
pose proof (rw_cells_CB_join _ _ _ _ _ _ BLK1 ltac:(replace (A + Z.of_nat (length DATA)) with (A + LEN) by lia; replace (length bs) with (Z.to_nat (Z.of_nat (length bs))) by lia; exact NB)) as BLK1'.
replace (Z.to_nat (Z.of_nat (length bs))) with (length bs) in BLK1' by lia.
assert (BLK' : rw_cells usegs m3 A [CB (length (DATA ++ bs)) (DATA ++ bs); CB (Z.to_nat (rd_cap st1 - Z.of_nat (length (DATA ++ bs)))) (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk))]).
{ apply (proj2 (rw_cells_app _ _ _ [CB (length (DATA ++ bs)) (DATA ++ bs)] _)). rewrite length_app. split; [exact BLK1'|]. cbn [cells_size csize Nat.add].
replace (A + Z.of_nat (length DATA + length bs + 0)) with (A + Z.of_nat (length DATA) + Z.of_nat (length bs + 0)) by lia.
replace (Z.to_nat (rd_cap st1 - Z.of_nat (length DATA + length bs))) with (Z.to_nat (rd_cap st1 - LEN) - length bs)%nat by lia. exact BLK3. }
pose proof (rw_cells_CB_join _ _ _ _ _ _ SJb ltac:(replace (126505 + Z.of_nat (length bs + 0) + Z.of_nat (Z.to_nat CNT - length bs)) with (126505 + Z.of_nat (Z.to_nat CNT + 0)) by lia; exact SJ2)) as SJc.
pose proof (rw_cells_CB_join _ _ _ _ _ _ SJa ltac:(replace (126505 + Z.of_nat (length bs)) with (126505 + Z.of_nat (length bs + 0)) by lia; exact SJc)) as SJ'.
do 17 eexists. exists F, fc, m3, A, (DATA ++ bs), (firstn (Z.to_nat (rd_cap st1 - LEN) - length bs) (skipn (length bs) junk)), (Z_to_bv 64 (bv_unsigned errv)).
exists (bs ++ (skipn (length bs) (firstn (Z.to_nat CNT) sj) ++ JR)), 0x13110.
split; [replace (Z.of_nat (length bs) + LEN) with (LEN + Z.of_nat (length bs)) by lia; reflexivity|].
split; [left; split; reflexivity|].
split; [rewrite HC; unfold u8s_of_bytes; rewrite map_app; reflexivity|].
split; [| split; [| split; [exact FR| split; [exact BA3| split; [| exact FRM]]]]].
3:{ replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned). exact ERR2. }
{ split; [exact P3|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact I|]. split; [exact BLK'|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [rewrite length_app; lia| exact BR]. }
{ unfold STAGE, UREAD_STAGE. replace PSTAGE_LEN with (length bs + (Z.to_nat CNT - length bs + (PSTAGE_LEN - Z.to_nat CNT)))%nat at 1 by lia. exact SJ'. }
+
assert (Ebs : bs = []) by (destruct bs; [reflexivity| cbn [length] in K1; exfalso; rewrite ?unsigned_lit in K1 by lia; lia]). subst bs.
cbn [length Nat.eqb]. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s (POSTBODY' fd P1v) msx) end.
apply implM_ret. apply evt_done.
cbn [POSTBODY]. unfold RDBRK.
do 17 eexists. exists F, fc, m2, A, (rd_cap st1), DATA, junk, (Z_to_bv 64 (bv_unsigned errv)).
split; [rewrite LENZ; cbn [Z.of_nat]; reflexivity|].
split; [exact HC|]. split; [| split; [exact FR| split; [exact BA2| split; [| exact FRM]]]].
2:{ replace (Z_to_bv 64 (bv_unsigned errv)) with errv by (symmetry; apply Z_to_bv_bv_unsigned). exact ERR2. }
split; [exact P2|]. split; [exact FA0|]. split; [exact SO0|]. split; [exact I|]. split; [rewrite <- ELEN; exact BLK|]. unfold MAX_INPUT. split; [split; [lia| exact CAPK]|]. split; [lia| exact BR].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="arg0 VSP VARGV VENVP EARGV HT FPR FWX SWF"] Lemma rd_read : forall (fd P1v : Z) (st1 : rd_st) (s : PState) x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (x23 : word) t3 t4 t5 t6
(F : bvmap 5 word) (fc : bv 32) (mm : mem) (A : Z) (DATA junk sj : list byte) (errv : word),
3 <= fd < 2^32 -> nth_error (argv_ptrs sp0 argv envp) 1 = Some (Z_to_bv 64 P1v) ->
rd_content st1 = map bv_unsigned DATA -> BUF mm s (rd_buf st1) A (rd_cap st1) DATA junk -> STAGE mm sj ->
Z.of_nat (length DATA) < rd_cap st1 ->
FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] -> frm0 fc ->
implM usegs (rd_read_part fd (map bv_unsigned arg1) st1) s (POSTBODY' fd P1v)
(GST 0x13154 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 (zlength (rd_content st1))) (Z_to_bv 64 fd) (Z_to_bv 64 (rd_cap st1)) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until errv. intros FD HP1 HC BU SJ LT FR BA ERR FRM.
pose proof BU as (_ & _ & _ & _ & _ & [CAPR CAPK] & LENR & _). unfold MAX_INPUT in CAPR.
pose proof BA as (_ & MI & _).
assert (LENZ : zlength (rd_content st1) = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
rewrite LENZ.
unfold implM. eapply impl_evt; [| intros ms' H; exact H].
Local Ltac2 Set LiaHints.tbl := fun () => "0040>16083456460.8323359244187.7767353306284.768929163403.76 00000900?00C00LS2LT4CAPRS2KW1nS2KWS2LT4CAPR".
zstep. zstep. zstep. if_cases KW; zify_cond KW.
-
apply evt_done.
replace (Z_to_bv 64 (rd_cap st1 + - Z.of_nat (length DATA))) with (Z_to_bv 64 (rd_cap st1 - Z.of_nat (length DATA))) by (f_equal; lia).
eapply (rd_read_core fd P1v st1 s); try eassumption.
replace (65536 <? rd_cap st1 - Z.of_nat (length DATA)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
-
zstep. apply evt_done.
eapply (rd_read_core fd P1v st1 s); try eassumption.
destruct (Z.ltb_spec0 65536 (rd_cap st1 - Z.of_nat (length DATA))); [reflexivity| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B2.
End CANSEC1.
