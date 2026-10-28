(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import UImgX F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.fse_read_ncount.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3 RF_main_B4.
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
#[using="Type"] Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. Local Ltac2 Set LiaHints.tbl := fun () => "0010=21381470951.3000003S1R".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition sx8 (c : Z) : Z := if c <? 128 then c else c - 256.
#[using="Type"] Lemma signed_byte : forall b : byte, bv_signed b = sx8 (bv_unsigned b).
Proof.
intros b. pose proof (byte_range b) as R. unfold bv_signed, sx8. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[bv_unsigned Z.modulo Z.add Z.sub Z.ltb Z.mul]. change (2 ^ 8 / 2) with 128. change (2 ^ 8) with 256.
destruct (Z.ltb_spec (bv_unsigned b) 128).
- Local Ltac2 Set LiaHints.tbl := fun () => "0040=13196258072.430779415313.458542802595.464471420465.4000001002007008SSS1R1HS".
rewrite Z.mod_small; lia.
- replace (bv_unsigned b + 128) with ((bv_unsigned b - 128) + 1 * 256) by lia. rewrite Z_mod_plus_full. rewrite Z.mod_small; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma list6 : forall (l : list byte), (6 <= length l)%nat -> exists d0 d1 d2 d3 d4 d5 r, l = d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: r.
Proof.
intros l H. Local Ltac2 Set LiaHints.tbl := fun () => "0070=57860607488.257860607488.357860607488.457860607488.557860607488.657860607488.757860607488.900000300600900<00?00B00CS1HS1HS1HS1HS1HS1HF".
destruct l as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 r]]]]]]; cbn in H; try lia. do 7 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma skipn4 : forall (l : list byte) n, (n + 4 <= length l)%nat -> exists q0 q1 q2 q3 r, skipn n l = q0 :: q1 :: q2 :: q3 :: r.
Proof.
intros l n H. pose proof (length_skipn n l) as L.
Local Ltac2 Set LiaHints.tbl := fun () => "0050>57860672516.1057860672516.5 57860672516.6 57860672516.7 57860672516.8 00000100600;00@00EFS1H1LS1H1LS1H1LS1H1L".
destruct (skipn n l) as [|q0 [|q1 [|q2 [|q3 r]]]]; cbn in L; try lia. do 5 eexists. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land15_mod : forall x, Z.land x 32767 = x mod 32768.
Proof. intros. change 32767 with (Z.ones 15). Local Ltac2 Set LiaHints.tbl := fun () => "0010=28717424086.2000001S".
rewrite Z.land_ones by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma land_shiftl_small : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.land (Z.shiftl b k) a = 0.
Proof.
intros a b k Hk Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020=51794598124.665501932176.6000004008S2HkS2Ha".
rewrite Z.shiftl_mul_pow2 by lia.
replace a with (Z.land a (Z.ones k)) by (rewrite Z.land_ones by lia; apply Z.mod_small; lia).
rewrite (Z.land_comm a), Z.land_assoc, Z.land_ones by lia. rewrite Z_mod_mult. apply Z.land_0_l.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_shiftl_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (Z.shiftl b k) a = a + b * 2^k.
Proof.
intros a b k Hk Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0030=43717872073.651794598124.665501932176.6000001005009SS2HkS2Ha".
rewrite <- Z.lxor_lor by (apply land_shiftl_small; lia).
rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_small; lia). rewrite Z.shiftl_mul_pow2 by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma lor_mul_add : forall a b k, 0 <= k -> 0 <= a < 2^k -> Z.lor (b * 2^k) a = a + b * 2^k.
Proof. intros a b k Hk Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0020=51794598124.665501932176.6000004008S2HkS2Ha".
rewrite <- Z.shiftl_mul_pow2 by lia. rewrite lor_shiftl_add by lia. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma le16_cons : forall d0 d1 (r : list byte), le16 (map bv_unsigned (d0 :: d1 :: r)) = bv_unsigned d0 + bv_unsigned d1 * 256.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma le32_cons : forall q0 q1 q2 q3 (r : list byte),
le32 (map bv_unsigned (q0 :: q1 :: q2 :: q3 :: r)) = bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma znth2_cons : forall d0 d1 d2 (r : list byte), znth (map bv_unsigned (d0 :: d1 :: d2 :: r)) 2 = bv_unsigned d2.
Proof. intros. reflexivity. Qed.
#[using="Type"] Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
intros c0 c1 H0 H1. Local Ltac2 Set LiaHints.tbl := fun () => "0010=28720314397.5000001S".
rewrite Z.testbit_eqb by lia. change (2 ^ 15) with 32768.
replace ((c0 + c1 * 256) / 32768) with (c1 / 128) by (Z.div_mod_to_equations; nia).
destruct (Z.leb_spec 128 c1).
- replace (c1 / 128) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
- replace (c1 / 128) with 0 by (Z.div_mod_to_equations; nia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma cfg15_Z : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
Z.lor (Z.shiftr (Z.land (Z.shiftl ((sx8 u1) mod 2^64) 57) 18446744073709551615) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
intros u0 u1 H0 H1.
change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "00A0>11030411325.5 11052527910.6 11607912823.6 27857570251.6 32245714760.6 34771708033.6 35497649709.5 51087801437.4151914555565.6 56121982141.5 59242254788.1363251886031.6 63374408857.6 7277063250.6  7701663367.6  8794636485.6  8931307546.6  00000100500600:00=00>00?00d00e00f01201801901:01;01?01ESS2H1SS2H1S1HSSS2H01E1H2H22H62H73H113H123H163H173H21SSS2H11H2H22H3S2H11HSSSS2H0S2H11H".
rewrite Z.land_ones by lia.
rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
rewrite land15_mod.
assert (E : (sx8 u1 mod 2 ^ 64 * 2 ^ 57) mod 2 ^ 64 / 2 ^ 49 = (u1 mod 128) * 2^8).
{ unfold sx8. destruct (Z.ltb_spec u1 128).
- rewrite (Z.mod_small u1) by lia. rewrite (Z.mod_small u1) by lia.
rewrite Z.mod_small by (split; [lia|]; change (2^64) with (2^7 * 2^57); apply Z.mul_lt_mono_pos_r; lia).
change (2^57) with (2^49 * 2^8). rewrite Z.mul_assoc, (Z.mul_comm u1), <- Z.mul_assoc. rewrite Z.mul_comm.
rewrite Z.div_mul by lia. lia.
- replace ((u1 - 256) mod 2^64) with (2^64 - 256 + u1) by (Z.div_mod_to_equations; nia).
replace ((2 ^ 64 - 256 + u1) * 2 ^ 57) with ((u1 - 128) * 2^57 + (2^57 - 1) * 2^64) by lia.
rewrite Z.mod_add by lia. rewrite Z.mod_small by lia.
replace (u1 mod 128) with (u1 - 128) by (Z.div_mod_to_equations; lia).
change (2^57) with (2^8 * 2^49). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. reflexivity. }
rewrite E. rewrite lor_mul_add by lia. Z.div_mod_to_equations. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section C.
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
Notation RDONE' := (RDONE sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
(MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
Definition RQEXIT (code : Z) (s : PState) : machine_state -> Prop := pat_exit code s.
Definition main_tail (buf : bptr) (cw cfg : Z) (payload : list Z) : M PState Z :=
status <- Prog.run cfg payload ;;
status' <- (if Z.testbit cw 15 then
n <- Prog.alloc_count ;; mret (if n <? COUNT_MAX then n else COUNT_MAX)
else mret status) ;;
raw_free buf ;;;
mret status'.
Definition main_rest (buf : bptr) (content : list Z) : M PState Z :=
let len := zlength content in
if len <? HDR_MIN then io_diag Prog.io DShortHdr ;;; raw_free buf ;;; mret 2
else
let cfg_word := le16 content in
let config_len := Z.land cfg_word 0x7fff in
if len <? HDR_MIN + config_len then io_diag Prog.io DCfgOverrun ;;; raw_free buf ;;; mret 2
else
let bitmap := le32 (skipn (Z.to_nat (2 + config_len)) content) in
let payload := skipn (Z.to_nat (6 + config_len)) content in
let cfg := if 0 <? config_len then znth content 2 else 0 in
Prog.alloc_init bitmap ;;; main_tail buf cfg_word cfg payload.
#[using="arg0 EARGV"] Lemma main_model_eq : main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv)
= (ra <- read_all Prog.io raw_malloc raw_free UREAD_STAGE (map bv_unsigned arg1) ;;
match ra with RdExit => mret 2 | RdDone buf content => main_rest buf content end).
Proof. unfold main_model, argv_Z. rewrite EARGV. reflexivity. Qed.
Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ rblock_range A cap
/\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
/\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
/\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).
Definition RUN0 (bufp : bptr) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (s : PState) (ms : machine_state) : Prop :=
exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
(junk : list byte) (errv : word),
ms = GST 0x131e8 x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm
/\ HDR A cap DATA cw L cfg sc
/\ RHEAP s [(bufp, A, cap)] mm /\ ps_so s = stdout_init
/\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
/\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.
#[using="VSP HT FREE FWR TOW"] Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z)
x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
s_diag (St:=PState) d = stderr_fwrite msg -> ro_bytes_b usegs PA (zbytes msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
0x10000 <= PA -> PA + 31 <= 0x1d000 ->
RHEAP s [(bufp, A, cap)] mm -> ps_so s = stdout_init -> FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] ->
implM usegs (s_diag d ;;; raw_free bufp ;;; mret 2) s RQEXIT
(GST 0x13278 x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0x1ebf0) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
Proof.
intros until errv. intros ED RO ML RNG LOA HIA P0 SO FR BA ERR.
pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. unfold RERRNO in ERR. unfold MFRAME in FR.
pose proof (RMalloc_ifaceP.RHEAP_block_range_proof _ _ _ (bufp, A, cap) P0 ltac:(left; reflexivity)) as BR. cbn [blk_addr blk_size fst snd] in BR.
pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
rewrite ED.
unfold implM. iprefix. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
eapply implM_bind.
{ Local Ltac2 Set LiaHints.tbl := fun () => "00N0?10898349623.13611126984331.11111561318432.87 13548026367.87 14357939516.87 22345614936.11424361825921.87 26772152872.11432059271057.87 40703369393.1094425429372.115 47854222187.87 49366584741.11549371035685.1115437840273.114 56323174152.87 57628696595.11257628696595.11360778449190.87 61249635161.13663468596703.87 66023801653.10966026048179.13666026193812.87 66028024501.1116669525048.114 6669525048.115 67174027184.11167560135324.87 8826078769.111 00000100200300;00C00G00K00O00P00Q00R00Z00^00b00i00m01101801C01D01I01M01Q01U01Y01]01a01b01k01lSSSS2ML3HIAS2ML3HIAS2SFS2SFS2SFSSSS2ML3HIAS2SFS2SFS2SF2HaS2SFS2HaS2SF2HaS2ML3HIA2SFSS3LOAS2SFS2SFS2SFS2SFS2HaS2HaSS3LOA3HIAS".
eapply (FWR) with (lo := usp0 - 8388608) (canary := CAN) (s := msg);
[exact TOW| apply stderr_file0_wfile0; exact SE| rewrite unsigned_lit by lia; apply rodata_bytes; [exact MI| exact RO| lia| lia]
| exact RNG | rewrite ML; lia| rewrite ML; reflexivity| reflexivity| reflexivity
| rewrite unsigned_lit by lia; exact ST
| rewrite unsigned_lit by lia; unfold FWRITE_DEPTH; lia| unfold GLOBALS_TOP; lia
| rewrite !unsigned_lit by lia; lia
| rewrite !unsigned_lit by lia; lia
| rewrite !unsigned_lit by lia; lia
| rewrite !unsigned_lit by lia; lia
| apply (RHEAP_ssp _ _ _ P0)| exact MI]. }
cbv beta. intros [] st' ms' PO.
destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & -> & MUc & WMc & MI1 & ST1 & SEW & SSP1 & ->).
ua. rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST1 by lia.
replace (ret_pc (Z_to_bv 64 0x1327c)) with (Z_to_bv 64 0x1327c) by (symmetry; rpc).
pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x1ebf0 <= a < 0x1ebf0 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1ebf0, 0x1ebf0 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
assert (OUT2 : forall a, (0x10000 <= a < 0x50000 /\ ~ (0x1ebf0 <= a < 0x1ebf0 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1ebf0, 0x1ebf0 + 232)] a0) a).
{ intros a Ha. cbn. lia. }
apply (rw_cells_magree usegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
apply (rw_cells_magree usegs _ _ _ _ _ AG) in ERR; [| intros a Ha; apply OUT2; cbn in Ha; lia].
assert (RS1 : RSTAT TID m1) by (eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS]).
assert (SOF1 : stdout_file m1 stdout_init) by (eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SOF]).
assert (AUX1 : rauxv_ok m1 usp0).
{ eapply rauxv_ok_frame; [exact AUX| exact MUc| exact WMc|]. unfold RAUXV_CELL, RLIBC in *.
constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia| constructor]. }
assert (P1 : RHEAP s [(bufp, A, cap)] m1).
{ eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact P0| exact MUc| exact WMc|].
constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia. }
clear MUc WMc AG OUT OUT2.
unfold implM. iprefix. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
eapply implM_bind.
{ unfold rfree_stmt in FREE.
eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
rewrite ?(unsigned_lit 192304) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
first [ exact P1 | left; reflexivity | exact AUX1 | exact ST1 | exact MI1 | exact ERR | unfold RFREE_STACK; lia | lia ]. }
cbv beta. intros [] s2 ms2 PO.
destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
replace (ret_pc (Z_to_bv 64 0x13284)) with (Z_to_bv 64 0x13284) by (symmetry; rpc).
cbn [lb_remove filter bptr_eqb fst snd] in HEAP3, HPR3.
apply implM_ret. change (RQEXIT 2 s2) with (pat_exit 2 s2).
eapply (main_return sp0 argv envp TID VSP HT 2 s2).
- unfold MFRAME. eapply rheap_pres_rw_cells; [exact HPR3| exact FR| left; cbn; lia].
- unfold LO. first [exact ST3| replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST3].
- eapply RSTAT_heap_pres; [exact HPR3| exact RS1].
- rewrite bptr_eqb_refl in HEAP3 || idtac. exact HEAP3.
- rewrite SOE3, SO. eapply stdout_file_heap_pres; [exact HPR3| exact SOF1].
- apply stderr_wfile0_file. eapply (stderr_wfile0_heap_pres); [exact HPR3| exact SEW].
- exact MI3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="VSP HT FREE FWR TOW"] Lemma phaseC : forall bufp content s ms,
RDONE' bufp content s ms ->
(forall DATA A cap cw L cfg sc s1 ms1, content = map bv_unsigned DATA -> RUN0 bufp A cap DATA cw L cfg sc s1 ms1 ->
implM usegs (main_tail bufp cw cfg (skipn (Z.to_nat (6 + L)) content)) s1 RQEXIT ms1) ->
implM usegs (main_rest bufp content) s RQEXIT ms.
Proof.
intros bufp content s ms RD K.
destruct RD as (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & x23 & F & fc & mm & A & cap & P1v & fd & DATA & junk & errv
& -> & HC & BU & FR & BA & ERR & FRM).
pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in SF.
pose proof BA as (ST & MI & RS & AUX & IMG & SE & SOF & TR). unfold LO in ST. pose proof ERR as ERR0. unfold RERRNO in ERR. pose proof FR as FR0. unfold MFRAME in FR.
pose proof BU as (P0 & FA0 & SO0 & HA & BLK & [CAPR CAPK] & LENR & BR). unfold MAX_INPUT in CAPR.
pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). atop_facts.
assert (LENZ : zlength content = Z.of_nat (length DATA)) by (rewrite HC; unfold zlength; rewrite length_map; reflexivity).
pose proof BLK as BLKB. apply (proj1 (rw_cells_app _ _ _ [CB (length DATA) DATA] _)) in BLKB. destruct BLKB as [BLKB _].
apply rw_cells_bytes_at in BLKB. cbn [cells_bytes cbytes app] in BLKB. rewrite app_nil_r in BLKB.
unfold main_rest. rewrite LENZ. unfold HDR_MIN.
remember (length DATA) as nD eqn:HnD.
pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
unfold implM. iprefix. zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00e0?10051342206.13010719523369.11411039251382.12114939502106.14015045294142.11115047375367.13017853067776.13020603750199.13020611481228.10121671956579.13022083353442.13022663147322.10123029066960.14428915217081.14128915217082.12129504615138.13129786644187.13030599421263.13031094199679.10131277540587.10131277540712.11432171981767.13036294664574.13136359080976.13139061230790.13141417907787.13041555686566.10141889083948.12942069433181.11442247747269.13142548581089.13142639358466.10147646126024.11452618908075.12054702042636.11454767043212.11455887575753.13156912929706.13057018341390.13058783042702.11459915138172.10159915138559.11463370214929.12765140884126.13065499920045.12865515440134.13066735321570.12467184189054.1516753474747.130 6755555970.111 8927294749.127 8927457312.129 8927457313.128 00000800=00B00C00H00M00V00[00c00h01901>01S01X01]01f01k02502:02?02D02N02U02^02e02j03203703K04104<04D04O04P04X04]04h04m05205:05I05[05`05h05m06206=06E06J06O06X06a06jS3HnD2RLS3HnDS3HnDFS3HnDS3HnDS3HnD3Rd2S3HnDS3HnD2K0S3HnDS3HnD3Rd03Rd13EcwS3HnDS3HnD4CAPR4LENR2RL2K1S3HnDS3HnDS3HnD3Rd1S3HnDS3HnD4LENRS3HnDS3HnDS3HnDS3HnD4CAPRS3HnD1HS3HnD3Rd1S3HnD1HS3HnDS3HnD2K0S3HnDS3HnD3Rd03Rd13Ecw2RLS3HnD4CAPR3BR13BR23Rd03Rd13Ecw1H2H02H4S3HnD3Rd11HS3HnD2K0S3HnD2RL2K1FS3HnD2K1S3HnDS3HnD3Rd11HS3HnDS3HnDS3HnD2K1S3HnD4CAPR4LENRS3HnD4CAPR4LENR2K0S3HnDS3HnD2K1S3HnDS3HnDS3HnD2RL2K1S3HnD2H0S3HnDS3HnDS3HnD3Rq1S3HnD3Rq3S3HnD3Rq2".
if_cases K0; zify_cond K0.
{
replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
cbn [io_diag io_S].
eapply (diagC_exit DShortHdr s_short S_SHORT); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
| unfold S_SHORT; lia| unfold S_SHORT; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }
replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
rewrite le16_cons.
remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; Z.div_mod_to_equations; lia).
pose proof (u8ro_read usegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
zstep. clear R1. cbv beta.
pose proof (u8ro_read usegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
zstep. clear R0. cbv beta.
zstep. zstep. zstep.
replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
remember (Z.land cw 32767) as L eqn:EL.
zstep. zstep. if_cases K1; zify_cond K1.
{
replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
cbn [io_diag io_S].
eapply (diagC_exit DCfgOverrun s_over S_OVER); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
| unfold S_OVER; lia| unfold S_OVER; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }
replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
zstep. zstep.
destruct (skipn4 (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) (Z.to_nat (2 + L)) ltac:(cbn [length] in *; lia)) as (q0 & q1 & q2 & q3 & rest' & EQ4).
pose proof (byte_range q0) as Rq0. pose proof (byte_range q1) as Rq1. pose proof (byte_range q2) as Rq2. pose proof (byte_range q3) as Rq3.
assert (QB : bytes_at usegs mm (A + 2 + L) (q0 :: q1 :: q2 :: q3 :: rest')).
{ rewrite <- EQ4. rewrite <- (firstn_skipn (Z.to_nat (2 + L)) (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) in BLKB.
apply bytes_at_app in BLKB. destruct BLKB as [_ X]. rewrite length_firstn in X.
replace (A + Z.of_nat (Nat.min (Z.to_nat (2 + L)) (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)))) with (A + 2 + L) in X by (cbn [length] in *; lia). exact X. }
rewrite skipn_map, EQ4, le32_cons.
remember (bv_unsigned q0 + bv_unsigned q1 * 256 + bv_unsigned q2 * 65536 + bv_unsigned q3 * 16777216) as BM eqn:EBM.
assert (SH1 : 0 <= Z.shiftl (bv_unsigned q1) 8 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (SH2 : 0 <= Z.shiftl (bv_unsigned q2) 16 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (SH3 : 0 <= Z.shiftl (bv_unsigned q3) 24 < 2^64) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
pose proof (u8ro_read usegs mm _ _ 1 q1 (wa (A + 2 + L + 1)) QB eq_refl ltac:(lia) eq_refl) as R1.
zstep. clear R1. cbv beta.
pose proof (u8ro_read usegs mm _ _ 0 q0 (wa (A + 2 + L)) QB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as R0.
zstep. clear R0. cbv beta.
pose proof (u8ro_read usegs mm _ _ 2 q2 (wa (A + 2 + L + 2)) QB eq_refl ltac:(lia) eq_refl) as R2.
zstep. clear R2. cbv beta.
pose proof (u8ro_read usegs mm _ _ 3 q3 (wa (A + 2 + L + 3)) QB eq_refl ltac:(lia) eq_refl) as R3.
zstep. clear R3. cbv beta.
zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
zstep. apply evt_done.
lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
eapply implM_bind. { apply ptarget_alloc_init_spec. }
cbv beta. intros [] s' ms' [-> ->].
replace (ret_pc (Z_to_bv 64 0x131e8)) with (Z_to_bv 64 0x131e8) by (symmetry; rpc).
replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
unfold RUN0. do 22 eexists. split; [reflexivity|].
split.
{ unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
split; [rewrite EL, land15_mod; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
split; [destruct (0 <? L); lia|].
split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
split; [exact P0|]. split; [exact SO0|].
split; [rewrite HnD in BLK; exact BLK|]. split; [unfold MFRAME; exact FR|]. split; [exact BA|]. split; [exact ERR| exact FRM].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End C.
End CANSEC1.
