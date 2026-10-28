(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Namei.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3.
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
Section B4.
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
Notation GST pc x1 t0 t1 t2 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Notation RST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 P1v len fd cap x23 t3 t4 t5 t6 F fc mm :=
(GST pc x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 P1v) (Z_to_bv 64 len) (Z_to_bv 64 fd) (Z_to_bv 64 cap) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm).
Definition RDONE (bufp : bptr) (content : list Z) (s : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
(A cap P1v fd : Z) (DATA junk : list byte) (errv : word),
ms = RST 0x13184 x1 t0 t1 t2 (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7 P1v (zlength content) fd cap x23 t3 t4 t5 t6 F fc mm
/\ content = map bv_unsigned DATA
/\ BUF mm s bufp A cap DATA junk
/\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.
Definition POSTB (r : rd_result) (s : PState) (ms : machine_state) : Prop :=
match r with
| RdExit => pat_exit 2 s ms
| RdDone b c => RDONE b c s ms
end.
#[using="arg0 VSP VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR TOW"] Lemma main_read_all : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem),
FRAME' mm -> BASE' mm -> RHEAP (ps_init (reservedZ usegs) ATOP) [] mm -> rw_cells usegs mm RERRNO [C4 (Z_to_bv 64 0)] -> frm0 fc -> STG mm ->
implM usegs (read_all Prog.io raw_malloc raw_free UREAD_STAGE (map bv_unsigned arg1)) (ps_init (reservedZ usegs) ATOP) POSTB
(MS (mkR (Z_to_bv 64 0x14a68) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
(Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
(Z_to_bv 64 0x13088) (Z_to_bv 64 (envp_addr sp0 argv)) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
bvmap_empty (Z_to_bv 64 0x130b8) fc None mm (seg_rom usegs)).
Proof.
intros until mm. intros FR BA HP0 ERR FRM [sj SJ]. unfold UREAD_STAGE in SJ. pose proof PSTAGE_LEN_Z as PSTAGER.
pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF. pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL.
pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
pose proof VARGV as (_ & _ & ARGLEN & NONUL & NOSL).
Local Ltac2 Set LiaHints.tbl := fun () => "01K0?11137728426.99 12044146536.10312403971566.10312723747997.10312725794747.19212849358436.19213015508063.10117299057828.19217750081190.10119748150706.82 20779530377.10322247234669.12823642450812.13523655082585.17125069614349.10225075858987.19126920848961.10226922880999.19028814044093.13628816038556.13529503543536.10129503543536.82 30621155865.10331701493748.1013172561356.81  34225178517.10334251706946.10336795109372.82 37290294297.10337379514840.10338130064400.12639448744729.10339455086655.19239821076852.17139947486821.10339962185027.19240153421138.99 43355316238.13543550988785.19143676255486.1924399813457.82  45414017936.10246710210102.19146720742672.10248642648111.19149253891872.82 49364486404.99 53575814021.13556542611996.82 57788126167.10259308628179.1  59308628304.13659323410545.10059323410545.12759626803089.82 60236402904.10361249489534.1276167620902.101 62073034509.10562073034509.19362273608489.10262275639951.19062881816585.10263197076952.10364144461288.82 64148606157.17164783464057.10365512798732.13565620006582.19066024030770.19266026193812.10466026193812.12666026193812.82 66026193812.99 66030338737.17166136628136.18 66247985189.82 66698233360.99 67159604881.99 6749508636.81  68158015924.171693834101.102  8078416600.103 8700736953.192 8828483125.171 8838854326.192 8841017104.104 8841017104.126 8841017104.82  8841017104.99  9617299244.81  00000100700;00?00C00D00J00W00`00a00b00k01001501601701801901H01W01h02902:02@02A02J02K02Q02R02V02W02X02Y02]02^02_02d02e02f02j02n02o03303703803903=03>03G03H03L03T03\03`03a03m03n04504>04G04H04I04J04N04O04P04Y04Z04[04_04c04g04k04o05305?05C05D05E05F05G05O05S05]05^05_05`05a05b05c05dSS4P1LOS2SFS2SFS2SFSS4P1LOS2SF4LEN33BQ4S2SF4P1LOSSS7PSTAGERS3FDRS3FDRFFSSS3BR13BR45ATOPRS3BR13BR45ATOPRS2SF2IL4P1LO4P1HIS2SF2IL4P1LO4P1HISS4SLK1SS2SF4P1LOSS4P1LOSS2SFSFFS2SFFFS3FDRSSS2SFS2SFSS2SFS2SFFSS2SFSS2SF4P1LOSS2K0S3BR12K1S3FDR2K0S2K1SS7PSTAGER2SFSS5A1LENS2SF1H2H0S2SF1H2H0SSFS2SFSSS7PSTAGERSSS2SFS2SFS2SFS2SFS2SFS2SFS2SF1H2H02H4S2SFSSSSS4P1HI1HS2SFS4LEN33BQ5SSSSSSS".
destruct (argv_cstring sp0 argv envp uid hw draw mm IMG 1 arg1 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; Z.div_mod_to_equations; lia))
as (P1v & slack1 & HP1 & P1LO & P1HI & STR1 & SLK1). unfold str_base, struct_size, argc, envc in P1LO.
destruct (stack_pieces sp0 argv envp uid hw draw mm IMG) as (_ & ARGVP & _).
assert (A1NN : ~ In (Z_to_bv 8 0) arg1) by (rewrite EARGV in NONUL; inversion NONUL as [|? ? ? X]; inversion X; assumption).
assert (A1LEN : Z.of_nat (length arg1) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN as [|? ? ? X]; inversion X; assumption).
assert (A1NOSL : path_has_slash arg1 = false) by (rewrite EARGV in NOSL; cbn [tl] in NOSL; inversion NOSL as [|? ? [X _]]; exact X).
assert (STR1' : bytes_at usegs mm P1v (arg1 ++ [Z_to_bv 8 0])).
{ change (arg1 ++ Z_to_bv 8 0 :: slack1) with (arg1 ++ ([Z_to_bv 8 0] ++ slack1)) in STR1. rewrite app_assoc in STR1. apply bytes_at_app in STR1. destruct STR1 as [S1 _]. exact S1. }
pose proof (RHEAP_ssp _ _ _ HP0) as [G1 G2]. unfold got_ssp, ssp_guard in G1, G2.
unfold read_all. unfold implM. iprefix.
pose proof (u64ro_read usegs mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 1 (Z_to_bv 64 P1v) (Z_to_bv 64 (usp0 + 16))
ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP1) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
zstep. clear RD. zstep. zstep. zstep.
remember READ_FUEL as rf eqn:Erf. clear Erf.
apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm (ps_init (reservedZ usegs) ATOP) POSTB msx) end.
replace (map (Z_to_bv 8) (map bv_unsigned arg1)) with arg1 by (symmetry; apply zbytes_map_unsigned').
eapply implM_bind.
{ eapply implM_of_enode.
eapply open_spec with (lo := usp0 - 8388608) (errv := Z_to_bv 64 0) (canary := CAN);
[ rewrite (unsigned_lit (usp0 + -128)) by lia; exact ST
| rewrite (unsigned_lit P1v) by lia; exact STR1'
| unfold RATP; rewrite (unsigned_lit 192304) by lia; exact ERR
| exact G1 | exact G2 | exact MI | reflexivity | exact A1NN | exact A1NOSL | ..].
all: unfold RATP, F_syscalls.got_ssp, F_syscalls.ssp_guard; rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia; rewrite ?(unsigned_lit P1v) by lia; lia. }
cbv beta. intros r s' ms' [PO ->].
destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & ERR1 & _ & _ & _ & FDR).
unfold RATP in MUc, ERR1. rewrite ?(unsigned_lit 192304) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
rewrite ?(unsigned_lit (usp0 + -128)) in ST1 by lia. rewrite ?(unsigned_lit 192304) in ERR1 by lia. change (192304 + -164) with 192140 in MUc, ERR1.
transport_after_call usegs mm m1 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x130c8)) with (Z_to_bv 64 0x130c8) by (symmetry; rpc).
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 112, usp0 + -128); (192140, 192140 + 4)]).
{ unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (HP1' : RHEAP (ps_init (reservedZ usegs) ATOP) [] m1).
{ eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact HP0]. intros iv [<-|[<-|[]]]; cbn [fst snd]; atop_facts; intros; lia. }
assert (BA1 : BASE' m1) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA| exact WOKW| exact MUc| exact WMc| exact MI1| unfold LO; first [exact ST1| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1]]).
clear MUc WMc BA WOKW HP0 G1 G2. try clear ST. try clear MI. try clear RS. try clear AUX. try clear IMG. try clear SE. try clear SOF. try clear TR.
pose proof BA1 as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
unfold implM. iprefix.
destruct r as [e|fd]; cbn [open_ret open_errno] in *.
-
pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
zstep. if_cases K0; zify_cond K0; try (exfalso; revert K0; clear; intros K0; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm (ps_init (reservedZ usegs) ATOP) POSTB msx) end.
cbn [io_diag io_S].
eapply (fprintf_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FPR FWX SWF (DCannotOpen (map bv_unsigned arg1)));
[| exact BA1| exact HP1'| reflexivity| exact FRM| intros ms'' AE; apply implM_ret; apply evt_done; exact AE].
cbn [diag_args]. split; [reflexivity|]. exists slack1. rewrite unsigned_lit by lia.
unfold F_fmt_fp_lib.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
split; [exact STR1|]. split; [apply map_unsigned_pos; exact A1NN|]. split; [lia|].
split; [unfold FmtFp.INT_MAX; lia|]. split; [right; lia|]. split; [unfold GLOBALS_TOP; lia|].
pose proof (IMGB_top sp0 argv envp uid hw draw VSP). lia.
-
zstep. if_cases K0; zify_cond K0; try (exfalso; rewrite ?unsigned_lit in K0 by lia; lia). clear K0.
zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm (ps_init (reservedZ usegs) ATOP) POSTB msx) end.
eapply implM_bind.
{ unfold rmalloc_stmt in MALLOC.
eapply MALLOC with (lo := usp0 - 8388608) (B := usp0); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact HP1' | exact AUX | exact ST | exact ERR1 | exact MI | unfold RMALLOC_STACK; lia | lia ]. }
cbv beta. intros r s1 ms1 PO.
destruct PO as (v0 & v1 & v2 & ra0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & errv2 & -> & MI2 & ST2 & ERR2 & AUX2 & HPR & FAE & SOE & RR).
unfold RATP in ERR2. rewrite ?(unsigned_lit 192304) in ERR2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in ST2 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR by lia.
change (192304 + -164) with 192140 in ERR2.
replace (ret_pc (Z_to_bv 64 0x130dc)) with (Z_to_bv 64 0x130dc) by (symmetry; rpc).
assert (BA2 : BASE' m2) by (eapply (BASE_heap_pres sp0 argv envp uid hw draw TID); [exact BA1| exact HPR| exact MI2| unfold LO; first [exact ST2| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST2]| exact AUX2]).
assert (FR2 : FRAME' m2) by (unfold MFRAME; eapply rheap_pres_rw_cells; [exact HPR| exact FR| left; cbn; lia]).
assert (SJ2 : rw_cells usegs m2 126505 [CB PSTAGE_LEN sj]).
{ eapply rheap_pres_rw_cells; [exact HPR| exact SJ|]. right; left. cbn [cells_size csize Nat.add]. unfold RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP. lia. }
clear FR ST MI RS AUX IMG SE SOF ERR1 TR SJ.
pose proof BA2 as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST.
unfold implM. iprefix.
destruct r as [buf|].
2:{
destruct RR as [-> HEAP2].
pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
zstep. if_cases K1; zify_cond K1; try (exfalso; lia). clear K1.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 POSTB msx) end.
cbn [io_diag io_S].
eapply (fwrite_exit sp0 argv envp uid hw draw TID S8 S9 S10 S11 VSP HT FWR TOW);
[exact BA2| exact HEAP2| rewrite SOE; reflexivity| intros ms'' AE; apply implM_ret; apply evt_done; exact AE]. }
destruct RR as (A & junk & -> & BR & HEAP2 & BLK & HEXP).
pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
zstep. if_cases K1; zify_cond K1; try (exfalso; rewrite ?unsigned_lit in K1 by lia; lia). clear K1.
zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s1 POSTB msx) end.
eapply implM_bind.
{ apply (rd_loop sp0 argv envp uid hw draw arg0 arg1 TID J8 S4 S5 S6 S7 S8 S9 S10 S11 VSP VARGV VENVP EARGV HT MALLOC FREE FPR FWX SWF FWR TOW rf fd P1v); [lia| exact HP1|].
unfold RDINV. cbn [rd_content rd_cap rd_buf zlength length Z.of_nat].
do 17 eexists. exists bvmap_empty, fc, m2, A, [], junk, errv2, sj, 0x130f0.
split; [unfold UREAD_STAGE; reflexivity|]. split; [right; split; reflexivity|]. split; [reflexivity|].
split; [| split; [exact SJ2| split; [exact FR2| split; [exact BA2| split; [exact ERR2| exact FRM]]]]].
split; [exact HEAP2|]. split; [rewrite FAE; reflexivity|]. split; [rewrite SOE; reflexivity|]. split; [exact I|]. cbn [length Z.of_nat Z.sub].
split; [replace (Z.to_nat (65536 - 0)) with (Z.to_nat 65536) by reflexivity; apply (proj2 (rw_cells_app _ _ _ [CB 0%nat []] _)); split; [| cbn [cells_size csize Nat.add]; rewrite Z.add_0_r; exact BLK] |].
- apply rw_cells_CB0. lia.
- unfold MAX_INPUT. split; [split; [lia| exists 16; split; [lia| reflexivity]]|]. split; [lia| exact BR]. }
cbv beta. intros res s2 ms2 PO.
destruct res as [|b c]; cbn [POSTLOOP] in PO.
{ apply implM_ret. apply evt_done. exact PO. }
clear dependent m2.
destruct PO as (x1 & w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & x23 & F2 & fc2 & m3 & A3 & cap3 & DATA3 & junk3 & errv3
& -> & HC3 & BU3 & FR3 & BA3 & ERR3 & FRM3).
pose proof BA3 as (ST & MI & RS & AUX & IMG & SE & SOF & TR3). unfold LO in ST. unfold RERRNO in ERR3. unfold MFRAME in FR3.
pose proof BU3 as (P3 & FA3 & SO3 & HA3 & BLK3 & CAP3 & LEN3 & BRR3).
pose proof BRR3 as (BQ1 & BQ2 & BQ3 & BQ4 & BQ5). atop_facts.
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s2 POSTB msx) end.
eapply implM_bind.
{ eapply implM_of_enode.
eapply close_spec with (lo := usp0 - 8388608) (errv := errv3); try reflexivity; unfold RATP; rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact ST | exact ERR3 | exact MI | lia ]. }
cbv beta. intros r3 s3 ms3 [PO ->].
destruct PO as (y0 & y1 & y2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & y3 & y4 & y5 & y6 & m4 & -> & MUc & WMc & MI4 & ST4 & ERR4).
unfold RATP in MUc, ERR4. rewrite ?(unsigned_lit 192304) in MUc by lia. rewrite ?(unsigned_lit (usp0 + -128)) in MUc by lia.
rewrite ?(unsigned_lit (usp0 + -128)) in ST4 by lia. rewrite ?(unsigned_lit 192304) in ERR4 by lia. change (192304 + -164) with 192140 in MUc, ERR4.
transport_after_call usegs m3 m4 MUc WMc.
replace (ret_pc (Z_to_bv 64 0x13184)) with (Z_to_bv 64 0x13184) by (symmetry; rpc).
assert (WOKW : Forall (WOK sp0) [(usp0 + -128 - 32, usp0 + -128); (192140, 192140 + 4)]).
{ unfold WOK, LO, RERRNO. constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (P4 : RHEAP s2 [(b, A3, cap3)] m4).
{ eapply (RHEAP_munchW sp0 argv envp VSP); [exact WOKW| exact MUc| exact WMc| | exact P3]. intros iv [<-|[<-|[]]]; cbn [fst snd]; atop_facts; intros; lia. }
assert (BA4 : BASE' m4) by (eapply (BASE_munch sp0 argv envp uid hw draw TID VSP VARGV VENVP); [exact BA3| exact WOKW| exact MUc| exact WMc| exact MI4| unfold LO; first [exact ST4| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST4]]).
apply implM_ret. apply evt_done. cbn [POSTB]. unfold RDONE.
do 16 eexists. exists x23, F2, fc2, m4, A3, cap3, P1v, fd. exists DATA3, junk3, (close_errno r3 errv3).
split; [reflexivity|]. split; [exact HC3|]. split; [| split; [exact FR3| split; [exact BA4| split; [exact ERR4| exact FRM3]]]].
split; [exact P4|]. split; [exact FA3|]. split; [exact SO3|]. split; [exact HA3|]. split; [exact BLK3|]. split; [exact CAP3|]. split; [exact LEN3| exact BRR3].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End B4.
End CANSEC1.
