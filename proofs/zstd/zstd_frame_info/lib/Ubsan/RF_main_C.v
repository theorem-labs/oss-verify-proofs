(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem MonadX.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls F_memcpy StdioFiles Startup Exit F_printf_iface Stdio_iface Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_facts RDriver_kit RDriver_ctx RF_main_A RF_main_B1 RF_main_B2 RF_main_B3 RF_main_B4.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
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

(* [comment removed for export] *)
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
  intros l H. destruct l as [|d0 [|d1 [|d2 [|d3 [|d4 [|d5 r]]]]]]; cbn in H; try lia. do 7 eexists. reflexivity.
Qed.
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
(* [comment removed for export] *)
#[using="Type"] Lemma testbit15 : forall c0 c1, 0 <= c0 < 256 -> 0 <= c1 < 256 -> Z.testbit (c0 + c1 * 256) 15 = (128 <=? c1).
Proof.
  intros c0 c1 H0 H1. Local Ltac2 Set LiaHints.tbl := fun () => "0010=28720314397.5000001S".
rewrite Z.testbit_eqb by lia. change (2 ^ 15) with 32768.
  replace ((c0 + c1 * 256) / 32768) with (c1 / 128) by (Z.div_mod_to_equations; nia).
  destruct (Z.leb_spec 128 c1).
  - replace (c1 / 128) with 1 by (Z.div_mod_to_equations; nia). reflexivity.
  - replace (c1 / 128) with 0 by (Z.div_mod_to_equations; nia). reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma cfg15_Z : forall u0 u1, 0 <= u0 < 256 -> 0 <= u1 < 256 ->
  Z.lor (Z.shiftr (Z.land (Z.shiftl ((sx8 u1) mod 2^64) 57) 18446744073709551615) 49) u0 = Z.land (u0 + u1 * 256) 32767.
Proof.
  intros u0 u1 H0 H1.
  change 18446744073709551615 with (Z.ones 64). Local Ltac2 Set LiaHints.tbl := fun () => "00A0=10008670412.611030411325.511052527910.611607912823.627857570251.632245714760.634771708033.635497649709.549305071429.651914555565.656121982141.563251886031.663374408857.67277063250.6 7701663367.6 8794636485.6 8931307546.6 00000600700;00<00@00C00D00E00K00L00M00S00T00U00V00Z00`S2H11HSS2H1SS2H1S1HSSS2H01ESSS2H11HSSSS2H0S2H11H".
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
      replace (u1 mod 128) with (u1 - 128) by (OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      change (2^57) with (2^8 * 2^49). rewrite Z.mul_assoc. rewrite Z.div_mul by lia. reflexivity. }
  rewrite E. rewrite lor_mul_add by lia. OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

(* [comment removed for export] *)
#[using="Type"] Lemma bm_Z : forall q0 q1 q2 q3, 0 <= q0 < 256 -> 0 <= q1 < 256 -> 0 <= q2 < 256 -> 0 <= q3 < 256 ->
  (Z.lor (Z.lor (Z.shiftl q1 8) q0) (Z.lor (Z.shiftl q2 16) (Z.land (bv_swrap 32 (Z.shiftl q3 24)) 18446744073709551615))) mod 2^32
  = q0 + q1 * 256 + q2 * 65536 + q3 * 16777216.
Proof.
  intros q0 q1 q2 q3 H0 H1 H2 H3.
  Local Ltac2 Set LiaHints.tbl := fun () => "00B0>29569839735.1035497649451.9 35851374962.104035948344.10 41243753043.1041889457323.1141891548331.9 4499441315.10 53343388596.9 56232789947.115874297110.11 62474669635.1163368316331.9 63370423723.1163831652966.1065500323883.1165502414891.9 9028293111.11 00000100200800>00?00@00A00G00T00[00\00`00a00b00h00i00j00nSSS2H31HS2H31HSSSS2H31HS2H02H12H22H3S2H02H1SS2H2SSS2H31HSSS2H0".
rewrite !Z.shiftl_mul_pow2 by lia.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  assert (C3 : exists c3, (c3 = q3 \/ c3 = q3 + 2^40 - 2^8) /\ bv_swrap 32 (q3 * 2 ^ 24) mod 2 ^ 64 = c3 * 2^24).
  { unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N N.div].
    change (2^32) with 4294967296 in *. change (Z.pow_pos 2 32) with 4294967296. change (4294967296 / 2) with 2147483648.
    destruct (Z.lt_ge_cases q3 128).
    - exists q3. split; [lia|]. rewrite (Z.mod_small (q3 * 2^24 + 2147483648)) by lia. rewrite Z.add_simpl_r. apply Z.mod_small. lia.
    - exists (q3 + 2^40 - 2^8). split; [lia|].
      replace ((q3 * 2 ^ 24 + 2147483648) mod 4294967296) with (q3 * 2 ^ 24 + 2147483648 - 4294967296) by (OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
      OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia. }
  destruct C3 as (c3 & Hc3 & ->).
  rewrite (Z.lor_comm (q2 * 2^16) (c3 * 2^24)). rewrite (lor_mul_add (q2 * 2^16) c3 24) by lia.
  rewrite (lor_mul_add q0 q1 8) by lia.
  replace (q2 * 2 ^ 16 + c3 * 2 ^ 24) with ((q2 + c3 * 2^8) * 2^16) by lia.
  rewrite (Z.lor_comm (q0 + q1 * 2^8)). rewrite (lor_mul_add (q0 + q1 * 2^8) (q2 + c3 * 2^8) 16) by lia.
  destruct Hc3 as [-> | ->]; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia.
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
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).
  Notation BASE' := (BASE sp0 argv envp uid hw draw TID).
  Notation FRAME' mm := (MFRAME sp0 argv mm J8 S7 S6 S5 S4).
  Notation RDONE' := (RDONE sp0 argv envp uid hw draw TID J8 S4 S5 S6 S7 S8 S9 S10 S11).
  Ltac hyps := first [exact VSP | exact VARGV | exact VENVP | exact EARGV | exact HT | exact MALLOC | exact FREE | exact FPR | exact FWX | exact SWF | exact FWR | exact TOW].

  (* [comment removed for export] *)
  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  Definition RQEXIT (code : Z) (s : PState) : machine_state -> Prop := pat_exit code s.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)
  Definition HDR (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) : Prop :=
    6 + L <= Z.of_nat (length DATA) /\ Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT /\ rblock_range A cap
    /\ 0 <= cw < 65536 /\ L = Z.land cw 32767 /\ 0 <= L < 32768 /\ L <= cw /\ cw = le16 (map bv_unsigned DATA)
    /\ cfg = (if 0 <? L then znth (map bv_unsigned DATA) 2 else 0) /\ 0 <= cfg < 256
    /\ -128 <= sc < 128 /\ (Z.testbit cw 15 = (sc <? 0)).

  (* [comment removed for export] *)
  Definition RUN0 (bufp : bptr) (A cap : Z) (DATA : list byte) (cw L cfg sc : Z) (s : PState) (ms : machine_state) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 x23 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (junk : list byte) (errv : word),
      ms = GST 0x1294c x1 t0 t1 t2 (Z_to_bv 64 (A + 2)) (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 L) (Z_to_bv 64 (A + 6 + L)) (Z_to_bv 64 (Z.of_nat (length DATA) - 6 - L)) (Z_to_bv 64 sc) (Z_to_bv 64 UREAD_STAGE) x23 t3 t4 t5 t6 F fc mm
      /\ HDR A cap DATA cw L cfg sc
      /\ RHEAP s [(bufp, A, cap)] mm /\ ps_so s = stdout_init
      /\ rw_cells usegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ FRAME' mm /\ BASE' mm /\ rw_cells usegs mm RERRNO [C4 errv] /\ frm0 fc.

  (* [comment removed for export] *)
  #[using="VSP HT FREE FWR TOW"] Lemma diagC_exit : forall (d : diag_msg) (msg : list Z) (PA : Z) (s : PState) (bufp : bptr) (A cap : Z)
      x1 t0 t1 t2 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : mem) (errv : word),
    s_diag (St:=PState) d = stderr_fwrite msg -> ro_bytes_b usegs PA (zbytes msg) = true -> zlength msg = 31 -> Forall (fun c => 0 <= c < 256) msg ->
    0x10000 <= PA -> PA + 31 <= 0x1c000 ->
    RHEAP s [(bufp, A, cap)] mm -> ps_so s = stdout_init -> FRAME' mm -> BASE' mm -> rw_cells usegs mm RERRNO [C4 errv] ->
    implM usegs (s_diag d ;;; raw_free bufp ;;; mret 2) s RQEXIT
      (GST 0x129dc x1 t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 A) (Z_to_bv 64 PA) (Z_to_bv 64 31) (Z_to_bv 64 1) (Z_to_bv 64 0x1dcf8) x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 F fc mm).
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
    { Local Ltac2 Set LiaHints.tbl := fun () => "00N0?11126984331.11111561318432.87 14357939516.87 15014092287.87 15717123633.11117383911676.11519954088631.13624361825921.87 28467145521.10932059271057.87 47854222187.87 4925046952.114 49366584741.11549371035685.1115437840273.114 56323174152.87 57628696595.11257628696595.11360778449190.87 61249635161.13663468596703.87 65753666776.11466023801653.10966026048179.13666026193812.87 66028024501.1116669525048.114 6669525048.115 67174027184.11167560135324.87 00000100200A00P00Q00R00S00W00X00Y00h00l01001401?01C01G01R01a01b01g01k01o02302702;02?02C02D02MSSS2ML3HIA2SF3BR1S2ML3HIA2SF3BR1SSSS2SFSSS2ML3HIA2SF3BR1S2SFS2SFS2SFS2SF3BR12HaS2SFS2HaS2SF3BR12HaS2ML3HIA2SF3BR1SS3LOAS2SFS2SFS2SFS2SFS2SFS2HaS2HaSS3LOA3HIA".
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
    replace (ret_pc (Z_to_bv 64 0x129e0)) with (Z_to_bv 64 0x129e0) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x4f000 /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
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
    (* [comment removed for export] *)
    unfold implM. iprefix. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind.
    { unfold rfree_stmt in FREE.
      eapply FREE with (lo := usp0 - 8388608) (B := usp0) (p := bufp) (A := A) (n := cap); try reflexivity; unfold RATP;
        rewrite ?(unsigned_lit 188464) by lia; rewrite ?(unsigned_lit (usp0 + -128)) by lia;
        first [ exact P1 | left; reflexivity | exact AUX1 | exact ST1 | exact MI1 | exact ERR | unfold RFREE_STACK; lia | lia ]. }
    cbv beta. intros [] s2 ms2 PO.
    destruct PO as (w0 & w1 & w2 & rb0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FAE3 & SOE3 & HEAP3).
    rewrite ?(unsigned_lit (usp0 + -128)) in ST3 by lia. rewrite ?(unsigned_lit (usp0 + -128)) in HPR3 by lia.
    replace (ret_pc (Z_to_bv 64 0x129e8)) with (Z_to_bv 64 0x129e8) by (symmetry; rpc).
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
  (* [comment removed for export] *)
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
    unfold implM. iprefix. zstep. zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00f0?10051342206.13010505953404.11411039251382.12114939502106.14015045294142.11115047375367.13017853067776.13020611481228.10121016489017.11421671956579.13022083353442.13022209101967.10123029066960.14428915217081.14128915217082.12129504615138.13129786644187.13030599421263.13031277540587.10131277540712.11432171981767.13034272850783.12336294664574.13136359080976.13138183258295.13039061230790.13141417907787.13041555686566.10141889083948.12942069433181.11442548581089.13142639358466.10147293857066.10147342265457.11047646126024.11452618908075.12054702042636.11455887575753.13156912929706.13057018341390.13058783042702.11459915138172.10159915138559.11463149464342.13063370214929.12765140884126.13065499920045.12865515440134.13066735321570.1246753474747.130 6755555970.111 8927294749.127 8927457312.129 8927457313.128 00000800=00B00C00H00M00V00^00c00o01G01L01h01m02202;02@02Q02V02[02e02j03103:03?03F03K03S03X04304>04M04R05005B05C05K05V05[05`05h06>06W06\06a07007507:07L07Q07V07f08608FS3HnD2RLS3HnDS3HnDFS3HnDS3HnDS3HnD3Rd2S3HnD2K0S3HnDS2SF3HnD3BR1S2SF3HnD3BR13Rd03Rd13EcwS3HnDS2SF3HnD4CAPR4LENR3BR12RL2K1S3HnDS3HnDS3HnD3Rd1S3HnDS2SF3HnD4LENR3BR1S3HnDS3HnDS3HnD4CAPRS3HnDS3HnD1HS3HnD3Rd1S3HnDS3HnD1HS3HnDS3HnD2K0S3HnDS2SF3HnD3BR13Rd03Rd13Ecw2RLS3HnD3Rd11HS2SF3HnD3BR12K0S3HnDS3HnD4CAPR3BR13BR23Rd03Rd13EcwS2SF3HnD3BR12RL2K1FS3HnD2K1S3HnD3Rd11HS3HnDS3HnDS3HnD2K1S2SF3HnD4CAPR4LENR3BR1S2SF3HnD4CAPR4LENR3BR12K0S3HnDS3HnDS2SF3HnD3BR12K1S3HnDS3HnDS2SF3HnD3BR12RL2K1S3HnDS3HnDS2SF3HnD3BR13Rq1S2SF3HnD3BR13Rq3S2SF3HnD3BR13Rq2".
if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io_S].
      eapply (diagC_exit DShortHdr s_short S_SHORT); [reflexivity| apply s_short_ro| reflexivity| unfold s_short; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_SHORT; lia| unfold S_SHORT; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }
    (* [comment removed for export] *)
    replace (Z.of_nat nD <? 6) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    destruct (list6 DATA ltac:(lia)) as (d0 & d1 & d2 & d3 & d4 & d5 & rest & ED). subst DATA. subst content.
    pose proof (byte_range d0) as Rd0. pose proof (byte_range d1) as Rd1. pose proof (byte_range d2) as Rd2.
    rewrite le16_cons.
    remember (bv_unsigned d0 + bv_unsigned d1 * 256) as cw eqn:Ecw.
    assert (RL : 0 <= Z.land cw 32767 <= cw) by (rewrite land15_mod; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia).
    pose proof (u8ro_read usegs mm _ _ 1 d1 (wa (A + 1)) BLKB eq_refl ltac:(lia) eq_refl) as R1.
    zstep. clear R1. cbv beta.
    pose proof (u8ro_read usegs mm _ _ 0 d0 (wa (A + 0)) BLKB eq_refl ltac:(lia) eq_refl) as R0.
    zstep. clear R0. cbv beta.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    replace (bv_unsigned (sxb d1)) with ((sx8 (bv_unsigned d1)) mod 2^64) by (unfold sxb; rewrite Z_to_bv_unsigned, signed_byte; reflexivity).
    rewrite (cfg15_Z _ _ Rd0 Rd1). rewrite <- Ecw.
    remember (Z.land cw 32767) as L eqn:EL.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      replace (Z.of_nat nD <? 6 + L) with true by (symmetry; apply Z.ltb_lt; lia). cbv iota.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
      cbn [io_diag io_S].
      eapply (diagC_exit DCfgOverrun s_over S_OVER); [reflexivity| apply s_over_ro| reflexivity| unfold s_over; apply Forall_app; split; [apply str_range| constructor; [lia| constructor]]
        | unfold S_OVER; lia| unfold S_OVER; lia| exact P0| exact SO0| exact FR0| exact BA| exact ERR0]. }
    replace (Z.of_nat nD <? 6 + L) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    zstep. zstep.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm s RQEXIT msx) end.
    eapply implM_bind. { apply ptarget_alloc_init_spec. }
    cbv beta. intros [] s' ms' [-> ->].
    replace (ret_pc (Z_to_bv 64 0x1294c)) with (Z_to_bv 64 0x1294c) by (symmetry; rpc).
    replace (Z_to_bv 64 (A + 2 + L + 4)) with (Z_to_bv 64 (A + 6 + L)) by (f_equal; lia).
    replace (Z_to_bv 64 (Z.of_nat nD + - L + -6)) with (Z_to_bv 64 (Z.of_nat (length (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest)) - 6 - L)) by (f_equal; lia).
    replace (sxb d1) with (Z_to_bv 64 (sx8 (bv_unsigned d1))) by (unfold sxb; rewrite signed_byte; reflexivity).
    eapply (K (d0 :: d1 :: d2 :: d3 :: d4 :: d5 :: rest) A cap cw L _ (sx8 (bv_unsigned d1))); [reflexivity|].
    unfold RUN0. do 22 eexists. split; [reflexivity|].
    split.
    { unfold HDR. cbn [length] in *. rewrite le16_cons, znth2_cons. unfold MAX_INPUT.
      split; [lia|]. split; [lia|]. split; [lia|]. split; [exact BR|]. split; [lia|]. split; [exact EL|].
      split; [rewrite EL, land15_mod; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia|]. split; [lia|]. split; [exact Ecw|]. split; [reflexivity|].
      split; [destruct (0 <? L); lia|].
      split; [unfold sx8; destruct (Z.ltb_spec (bv_unsigned d1) 128); lia|].
      rewrite Ecw, (testbit15 _ _ Rd0 Rd1). unfold sx8.
      destruct (Z.ltb_spec (bv_unsigned d1) 128); [rewrite (proj2 (Z.leb_gt _ _)) by lia; symmetry; apply Z.ltb_ge; lia | rewrite (proj2 (Z.leb_le _ _)) by lia; symmetry; apply Z.ltb_lt; lia]. }
    split; [exact P0|]. split; [exact SO0|].
    split; [rewrite HnD in BLK; exact BLK|]. split; [unfold MFRAME; exact FR|]. split; [exact BA|]. split; [exact ERR| exact FRM].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End C.
End CANSEC1.
