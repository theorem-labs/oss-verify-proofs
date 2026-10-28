(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape ZBridge HeapIface Asn1Aux Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StoreOk MemcpyLib ShapeLaws.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_file.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow NodesA SymDriveA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_code_67000_68000 A_code_68000_69000 A_code_96000_97000 A_code_e8000_e9000 A_code_ec000_ecd48             A_exit_lib A_unreg_globals A_tailkit_defs A_rip A_icpt_read A_main_tails.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_main_inv A_main_fin.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_main_loop.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
#[local] Existing Instance Lib.PropExec.fx0.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
#[local] Unset Lia Cache.

(* [comment removed for export] *)
Definition FDS2 : list (word * FdEntry) :=
  [(Z_to_bv 64 0, FdChannel (Z_to_bv 64 0)); (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1)); (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2))].
Lemma FDS_remove3 : forall path off, fd_remove (FDS path off) (Z_to_bv 64 3) = FDS2.
Proof. intros. reflexivity. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L53649721933.6000009S2bs1k2Hk". (* [comment removed for export] *)
Lemma nth_byte_readA : forall m (a : Z) (bs : list byte) (k : nat),
  bytes_at asegs m a bs -> (k < length bs)%nat ->
  ov_read_bytes asegs m (wa (a + Z.of_nat k)) 1 = Some [nth k bs (Z_to_bv 8 0)].
Proof.
  intros m a bs k BY Hk. rewrite (bytes_at_ov_read asegs m a bs k 1 BY) by lia.
  f_equal. rewrite <- (firstn_skipn_step bs k 0 (nth k bs (Z_to_bv 8 0))); [reflexivity|].
  apply nth_error_nth'. exact Hk.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L11029985341.6 L35497813549.6 L50038617690.7 L52611014062.28L5365412057.28 L56122408125.6 L63374408857.7 00000=00J00W00g01901F01SS2b02b12B02B1S2b02b12B02B1S2b02b12B02B1S2b02b12B02R02B1S2b02b12B02B11r2H0S2b02b12B02B1S2b02b12B02B1". (* [comment removed for export] *)
Lemma hdr_cfglenA : forall b0 b1 : byte,
  Z.lor (Z.shiftr (Z.land (Z.shiftl (bv_unsigned (sxb b1)) 57) 18446744073709551615) 49) (bv_unsigned b0)
  = bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128).
Proof.
  intros b0 b1.
  pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
  rewrite sxb_unsigned. set (B1 := bv_unsigned b1) in *. set (B0 := bv_unsigned b0) in *.
  change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (E : ((if B1 <? 128 then B1 else B1 + 2 ^ 64 - 256) * 2 ^ 57) mod 2 ^ 64 / 2 ^ 49 = (B1 mod 128) * 256).
  { destruct (Z.ltb_spec0 B1 128); Z.div_mod_to_equations; nia. }
  rewrite E. replace (B1 mod 128 * 256) with (Z.shiftl (B1 mod 128) 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm. rewrite lor_shiftl8_add by (Z.div_mod_to_equations; lia). reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L35498075693.2000001S". (* [comment removed for export] *)
Lemma hdr_cfglenA' : forall b0 b1 : byte,
  Z.lor (Z.shiftr ((Z.shiftl (bv_unsigned (sxb b1)) 57) mod 18446744073709551616) 49) (bv_unsigned b0)
  = bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128).
Proof.
  intros. rewrite <- hdr_cfglenA. change 18446744073709551616 with (2^64). change 18446744073709551615 with (Z.ones 64).
  rewrite Z.land_ones by lia. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition status (rv : Z) (b1 : byte) : Z := if (128 <=? bv_unsigned b1) then 0 else rv.
Definition CALLS (fdata : list byte) (cl : Z) : nat :=
  if cl =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)).
Definition SUCC (fs0 : Fs) (fdata : list byte) (cl : Z) : TSet := t_emit (W 1 (zero_lines (CALLS fdata cl))) (t_exit (exit_code 0) fs0).
Definition TAIL (fs0 : Fs) (fdata : list byte) (cl plen : Z) : TSet :=
  if plen =? 0 then SUCC fs0 fdata cl
  else t_alt2 (t_emit (W 1 []) (t_exit (exit_code (status 2 (nth 1 fdata (Z_to_bv 8 0)))) fs0)) (SUCC fs0 fdata cl).
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59913653220.1800000OS2B02B11H1q1r2H12H22q02r02H62H7". (* [comment removed for export] *)
Lemma cfg_mod : forall B0 B1 : Z, 0 <= B0 < 256 -> 0 <= B1 < 256 -> (B0 + 256 * B1) mod 32768 = B0 + 256 * (B1 mod 128).
Proof. intros. Z.div_mod_to_equations. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section Hdr.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
  Variable HID : artD asegs R HIA.
  Let AL := arl_AL R.
  Let L := arl_L R.
  #[local] Existing Instance L.   (* [comment removed for export] *)
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis GSB : al_gsb AL = 0x1099f8.
  Hypothesis HMALLOC : arl_malloc R = 0x69480.
  Hypothesis HFREE : arl_free R = 0x6947c.
  Hypothesis HMEMCPY : arl_memcpy_i R = 0x67db8.
  Hypothesis HTP : arl_tp R = 0x63ca90.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.

  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (path : list byte) (pathp : word) (fs0 : Fs) (fdata : list byte).
  Hypothesis Hfs : fs_lookup fs0 path = Some fdata.
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  Variables (TOP STKHI V0 : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis HV0 : V0 + 2^29 <= AVOL_SPLIT.      (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L989271055.2000006S2V01H". (* [comment removed for export] *)
  Let HV0M : V0 + 2^29 <= AVOL_MAX.                (* [comment removed for export] *)
  Proof. pose proof HV0 as H. unfold AVOL_SPLIT, AVOL_MAX in *. clear - H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Variable FR0 : Z.                               (* [comment removed for export] *)
  Hypothesis HFR0 : FR0 + 3 <= FR_MAX.            (* [comment removed for export] *)
  Variable pad : list byte.                       (* [comment removed for export] *)
  Let msp : Z := bv_unsigned sp0 - 128.   (* [comment removed for export] *)

  Ltac done_regs := apply evtA_done; unfold mkR; repeat (first [ reflexivity | lia | progress f_equal ]).
  Ltac solve_condb :=
    cbn [negb]; unfold bv_eqb, bv_ltu; rewrite ?bv_lts_zero_r; rewrite ?unsigned_lit by lia;
    repeat (first [ apply (proj2 (Bool.negb_true_iff _)) | apply (proj2 (Bool.negb_false_iff _)) ]);
    first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply Z.leb_le; lia | apply Z.leb_gt; lia ].
  Ltac ifc b :=
    lazymatch goal with
    | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_condb]
    end.

  (* [comment removed for export] *)
  Definition C1_post (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (m : mem) : machine_state -> Prop :=
    fun ms' => exists (j8 : list byte) m',
      ms' = MS (mkR (Z_to_bv 64 0x0f0010) (Z_to_bv 64 (msp + -16)) gp tp t0 t1 t2 s0 s1
                    (Z_to_bv 64 3) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               bvmap_empty (Z_to_bv 64 0x0eb5a8) (Z_to_bv 32 0) None m' (seg_rom asegs)
      /\ munch [(arl_stklo R, msp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' (arl_stklo R) (msp + -16)
      /\ rw_cells asegs m' (msp + -16) [CB 8 j8; C8 (Z_to_bv 64 0x0971dc)].

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12334604646.80L2287825204.81 L23026213784.81L23675258886.78L24616810379.80L36667852792.0 L46645985186.80L46700662962.82Q11799361125.83Q25524345151.80Q47708481035.80Q49698585326.82Q58443002963.81Q60823492826.80Q63460657675.8000000500:00?00L00Q00R00W00\01801?01L01_01l02602@S3sp0S3sp0S3sp0S1R3sp05STKLOS3sp0SS3sp0S3sp0S1R3sp05STKLO2HB5Ha_st5Hl_stS1R3sp0S1R3sp05STKLOS3sp04SPhi2HB5Ha_stS3sp04SPlo2HBS3sp04SPhiS3sp04SPlo". (* [comment removed for export] *)
  #[using="IMG SPlo SPhi STKLO"] Lemma C1_steps : forall (CS : Z -> Prop) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m,
    stk asegs m (arl_stklo R) msp -> mem_inv asegs m -> crange CS (arl_stklo R) (msp - arl_stklo R) ->
    evtA asegs AL CS (C1_post gp tp t0 t1 t2 s0 s1 s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m)
      (MS (mkR ra (Z_to_bv 64 msp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 3) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0971d4) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * ST MI SCS. unfold C1_post. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(arl_stklo R, bv_unsigned sp0 - 128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    carve_frame 16%nat ST. replace (bv_unsigned sp0 + -128 + -16) with (bv_unsigned sp0 + -144) in * by lia.
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep.                                   (* [comment removed for export] *)
    do 8 zstep.                                     (* [comment removed for export] *)
    do 8 zstep.                                     (* [comment removed for export] *)
    unfold C1_post; finish; eassumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L22608269962.75L23026213784.76L36667852792.0 L39334236075.75L52035364018.76L52071667727.75L53506590987.75L62987311026.76Q22484832684.75Q40545297994.75Q60827833697.75Q63456610224.7500000500:00;00@00E00F00K00P00U00Z00d00nS3sp0S3sp0SS3sp0S3sp0FS3sp0S3sp0S3sp0S3sp0S3sp04SPhiS3sp04SPlo". (* [comment removed for export] *)
  #[using="IMG SPlo SPhi"] Lemma C2_steps : forall (CS : Z -> Prop) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (j8 : list byte) m,
    rw_cells asegs m (msp + -16) [CB 8 j8; C8 (Z_to_bv 64 0x0971dc)] -> crange CS (msp - 16) 16 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) gp tp t0 t1 t2 s0 s1
                                (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           bvmap_empty (Z_to_bv 64 0x0971dc) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x0f0010) (Z_to_bv 64 (msp + -16)) gp tp t0 t1 t2 s0 s1
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0eb5ac) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * FR SCS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    replace (bv_unsigned sp0 - 128 + -16) with (bv_unsigned sp0 + -144) in * by lia.
    zstep.                                          (* [comment removed for export] *)
    do 5 zstep.                                     (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep.                            (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition FRAMEA := A_main_loop.FRAMEA sp0 pad.
  Let Ln : Z := Z.of_nat (length fdata).

  (* [comment removed for export] *)
  Record TINVA (buf cap : Z) (m : mem) (mo : Model) (h : HST asegs R HIA) : Prop := MKTINVA {
    ti_hm : HM asegs R HIA h [(buf, cap)] [] m;
    ti_hk : HK asegs R HIA h mo;
    ti_htop : htop asegs R HIA h = TOP;
    ti_hstkhi : hstkhi asegs R HIA h = STKHI;
    ti_vol : havol asegs R HIA h <= V0;
    ti_fr : hfr asegs R HIA h <= FR0;                 (* [comment removed for export] *)
    ti_tail : tail_memA (Z_to_bv 64 msp) m can tid wp0 rp0 wp1 rp1;
    ti_files : files_pristine m;
    ti_sshad : sshad asegs AL m (arl_stklo R) msp;
    ti_si : si_P SI m;
    ti_stk : stk asegs m (arl_stklo R) msp;
    ti_frame : rw_cells asegs m msp FRAMEA;
    ti_fs : m_fs mo = fs0;
    ti_fds : m_fds mo = FDS2;
    ti_bytes : bytes_at asegs m buf fdata;
    ti_wr : wr_at asegs m buf cap;
    ti_lcap : Ln < cap;
    ti_capok : cap_ok cap;
    ti_brange : 0 < buf /\ (buf + cap <= arl_stklo R \/ STKHI <= buf) /\ buf + cap <= alloc_ceiling;
    ti_fresh : forall c, c <> KBATCH -> hfresh _ _ _ HID h c;
    ti_fresh0 : (131072 <= cap /\ cap <= 2 * Ln) \/ forall c, hfresh _ _ _ HID h c
  }.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00H0@L11803550370.116L1206807738.98  L14744991142.109L15792433650.111L20542117738.114L22700267513.119L24374262304.116L27729527530.116L34882637204.117L40838710255.116L41681627164.116L47016053519.116L47335462129.116L5115413524.117 L5141069876.115 L51850867209.116L53579892516.116L55657602515.111L55713172657.109L61823592111.116L62022471159.98 L62372580040.116L64700386808.118L8620884186.116 00000B00c01501I01[02602M03K04804W04i05@05\06E06W06i07;07M07_08L08`09709Z0:1S3sp05fdata3msp2LnS1R3sp05fdata5STKHI6HSTKHI3msp2LnS3sp05fdata3msp2LnS1R3sp05fdata3msp2LnS3sp05fdata3msp2LnS3sp04SPlo5fdata3msp2Ln1a1HS3sp04SPlo5fdata3msp2LnS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp2Ln3buf3cap3HLc2BR2CBS1R3HIA3sp04SPlo5fdata3FR03msp2Ln3cap1h3FRB1HS3sp05fdata5STKHI6HSTKHI3msp2LnS3sp05fdata3msp2LnS3sp04SPhi5fdata3msp2LnS3sp04SPlo4SPhi5fdata3msp2LnS1R3sp04SPlo5fdata3TOP6HTOPlo3msp2Ln1a2HaS3sp05fdata3msp2LnS3sp05fdata3msp2LnS3sp05fdata3msp2LnS3sp05fdata3msp2LnS3sp05fdata3msp2LnS1R3HIA3sp04SPlo5fdata2V03msp2Ln3cap1h3VOL2CBS1R3sp05fdata3msp2LnS3sp04SPlo5fdata3msp2LnS1R3HIA3sp05fdata3msp2Ln3buf1h1x2HxS3sp04SPlo5fdata3msp2Ln". (* [comment removed for export] *)
  #[using="IMG ASB SIFP SPlo SPhi STKLO HTOPlo HSTKHI"] Lemma close_glue : forall (buf cap : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (m : mem) (mo : Model) (h : HST asegs R HIA) (T : TSet),
    LINVA R HIA HID sp0 path fs0 fdata can tid wp0 rp0 wp1 rp1 TOP STKHI V0 FR0 pad SI buf Ln cap m mo h -> Ln < cap ->
    (forall (a2' a3' a4' a5' a6' : word) m1 mo1,
        TINVA buf cap m1 mo1 h ->
        srealizesJ asegs (mkCfg (MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                                          (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) a2' a3' a4' a5' a6' (Z_to_bv 64 57)
                                          pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7
                                          (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                                     bvmap_empty (Z_to_bv 64 0x0971dc) (Z_to_bv 32 0) None m1 (seg_rom asegs)) mo1) T) ->
    srealizesJ asegs (mkCfg (MS (LREGSA sp0 pathp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf Ln cap)
                                 bvmap_empty (Z_to_bv 64 0x0971d4) (Z_to_bv 32 0) None m (seg_rom asegs)) mo) T.
  Proof.
    intros * LI HLc HC.
    pose proof LI as LI'. destruct LI' as [HH HKmo HT HS VOL FRB TM FI SSH SIm ST FR RSW FS FDSq BY REST WR LEN COK BR FRSH FRSH0].
    pose proof (cap_ok_bounds sp0 cap COK) as CB.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
    pose proof (hd_blk_band _ _ _ HID h _ _ m buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
    assert (SCS : crange (hcs asegs R HIA h) (arl_stklo R) (msp - arl_stklo R)).
    { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia]. }
    unfold LREGSA.
    (* [comment removed for export] *)
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | apply (C1_steps (hcs asegs R HIA h)); [exact ST | exact (tm_mi _ _ _ _ _ _ _ _ TM) | exact SCS] |].
    cbn beta. intros ms1 mo1 P1 HK1 MM1. ddestruct P1 as (j8 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    (* [comment removed for export] *)
    change (MS ?Rx bvmap_empty ?pc (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pc Mx rom).
    eapply (rz_closeA asegs (HK asegs R HIA h) (hk_halted _ _ HIA h)
              _ (Z_to_bv 64 0x0eb5a8) m1 mo1 W_e81f8 (Z_to_bv 64 3) (FdFile path (Z_to_bv 64 Ln)));
      [ exact F_e81f8 | exact E_e81f8 | exact HK1 | reflexivity | reflexivity | rewrite unsigned_lit by lia; lia
      | rewrite (A_main_fin.mo_mat_fds _ _ MM1), FDSq; apply FDS_lookup3 | ].
    lazymatch goal with |- srealizesJ _ (mkCfg (mkst (regupd ?RR 10 ?v) _ _ _) _) _ =>
      change (regupd RR 10 v) with
        (mkR (Z_to_bv 64 0x0f0010) (Z_to_bv 64 (msp + -16)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2 (Z_to_bv 64 2) (Z_to_bv 64 buf)
             v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 57)
             pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6) end.
    replace (v_addi (Z_to_bv 64 0x0eb5a8) 4) with (Z_to_bv 64 0x0eb5ac) by (apply bv_eq; reflexivity).
    rewrite (A_main_fin.mo_mat_fds _ _ MM1), FDSq, FDS_remove3.
    set (mo2 := with_fds FDS2 mo1).
    assert (HK2 : HK asegs R HIA h mo2) by (subst mo2; apply (hk_vmonly _ _ HIA h mo1); [exact HK1 | reflexivity | reflexivity | reflexivity | reflexivity]).
    (* [comment removed for export] *)
    change (mkst ?Rx ?pc ?Mx ?rom) with (MS Rx bvmap_empty pc (Z_to_bv 32 0) None Mx rom).
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HK2 | eapply (C2_steps (hcs asegs R HIA h)); [exact FR1 | eapply crange_sub; [exact SCS | rewrite STKLO; cbv delta [msp]; lia | lia]] |].
    cbn beta. intros ms3 mo3 -> HK3 MM3.
    apply HC.
    (* [comment removed for export] *)
    pose proof (stk_release asegs m1 (arl_stklo R) (msp + -16) _ ST1 FR1 ltac:(rewrite STKLO; cbv delta [msp]; lia)) as ST1'.
    cbn [cells_size csize Nat.add] in ST1'. replace (msp + -16 + Z.of_nat 16) with msp in ST1' by lia.
    assert (HH1 : HM asegs R HIA h [(buf, cap)] [] m1).
    { eapply (hm_munch _ _ HIA); [exact HH | exact MU1 | exact WM1 |].
      constructor; [| constructor]. cbn [fst snd]; intros a Ha. left. left. rewrite HT. cbv delta [msp] in Ha. lia. }
    split.
    - exact HH1.
    - exact HK3.
    - exact HT.
    - exact HS.
    - lia.
    - pose proof (ndbl_nonneg cap). lia.
    - eapply (tail_munch R HIA (hd_rtc _ _ _ HID) (hd_lowsh _ _ _ HID) (HM_ZIMG R HIA ASB) can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m m1 h [(buf, cap)] [] 0x65f000 0x65f000);
        rewrite ?unsigned_lit by lia;
        [exact TM | eapply munch_weaken; [| exact MU1]; solve_sub_fp | exact WM1 | lia | lia | rewrite STKLO; lia | cbv delta [msp]; lia | exact HH1 | exact MI1
        | eapply (proj2 (stk_split asegs m1 (arl_stklo R) (msp - 4096) msp ST1' ltac:(rewrite STKLO; cbv delta [msp]; lia)))].
    - eapply files_munch; [exact FI | exact MU1 | cbn [disjoint_from fst snd]; rewrite STKLO; cbv delta [msp]; lia].
    - eapply (sshad_keep_munch R HIA h _ _ m m1 buf buf); [exact HH | exact SSH | eapply munch_weaken; [| exact MU1]; solve_sub_fp | exact WM1 | intros x Hx; lia | rewrite HS; cbv delta [msp]; lia].
    - eapply si_munch; [exact SIm | exact MU1 |]. intros a NO. pose proof (SIFP a NO). cbn. rewrite STKLO. cbv delta [msp]. lia.
    - exact ST1'.
    - eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 |].
      cbn [cells_size csize A_main_loop.FRAMEA FRAMEA Nat.add disjoint_from fst snd]. rewrite STKLO. cbv delta [msp]. lia.
    - rewrite (mo_mat_fs _ _ MM3). subst mo2. change (m_fs (with_fds FDS2 mo1)) with (m_fs mo1). rewrite (mo_mat_fs _ _ MM1). exact FS.
    - rewrite (A_main_fin.mo_mat_fds _ _ MM3). subst mo2. reflexivity.
    - rewrite firstn_all2 in BY by lia. eapply bytes_at_transport; [exact BY | exact MU1 |]. cbn [disjoint_from fst snd]. rewrite STKLO. lia.
    - eapply wr_at_transport; [exact WR | exact WM1].
    - exact HLc.
    - exact COK.
    - exact BR.
    - exact FRSH.
    - exact FRSH0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L17860947755.61L22894955531.61L42263943501.6100000>00O00`S3sp05fdata2LnS3sp05fdata2Ln2HLS3sp05fdata2Ln2HL". (* [comment removed for export] *)
  #[using="IMG"] Lemma Hshort_steps : forall (CS : Z -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 x7 t3 t4 t5 t6 : word) (buf cap : Z) m,
    0 <= Ln < 6 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                                (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 5) (Z_to_bv 64 (-4095)) a2 a3 a4 a5 a6 (Z_to_bv 64 57)
                                pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7
                                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                           bvmap_empty (Z_to_bv 64 0x097298) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) a2 a3 a4 a5 a6 (Z_to_bv 64 57)
               pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0971dc) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * HL. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. ifc true. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0@L11028154364.75 L11447729958.104L12500131315.86 L17859014128.75 L18333377407.76 L19392081570.0  L22888828624.75 L33774851631.76 L39075111646.75 L49097507355.76 L52629933536.75 L5832329437.75  L59579215600.75 L64452784412.75 Q1841293521.75  Q20657901611.75 Q3728816425.75  Q41463098448.75 Q45244024394.75 Q48756875136.75 Q56897941899.75 Q57031419594.75 00000800900Y00j00k00l01W01X02002E02F02^02f03>03]03n04B04a05505F05a06<S3sp02b1FS5fdata2Ln3cap2b02HL1r3HOV2R02H0S3sp05fdata2Ln2b1FSS3sp04SPlo5fdata2Ln3cap2cl2b12HL3HOV2R13CLrFS3sp05fdata2Ln3cap2b12HLS3sp05fdata2Ln3buf2b1FS3sp05fdata2Ln2cl2b13HOVS3sp02b1S3sp05fdata2Ln2cl2b13CLrS5fdata2Ln3buf3cap2b12HL3HBC2R1S5fdata2Ln3buf2b1S5fdata2Ln3buf2b12HBS5fdata2Ln3buf3cap2b12HL3HBC2R1S5fdata2Ln3buf2b12HBS5fdata2Ln3buf2b1S5fdata2Ln3buf3cap2b12HL2R1S5fdata2Ln3buf3cap2b12HL2R1". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma Hover_steps : forall (CS : Z -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 x7 t3 t4 t5 t6 : word) (buf cap cl : Z) (b0 b1 : byte) m,
    6 <= Ln < cap -> cap <= 67108864 -> 0 < buf -> buf + cap < 2^47 ->
    ov_read_bytes asegs m (wa (buf + 0)) 1 = Some [b0] -> ov_read_bytes asegs m (wa (buf + 1)) 1 = Some [b1] ->
    crange CS buf cap -> cl = bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128) -> Ln < cl + 6 ->
    evtA asegs AL CS
      (fun ms' => exists a1', ms' = MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                                (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 (cl + 6)) a1' a2 a3 a4 a5 a6 (Z_to_bv 64 57)
                                (Z_to_bv 64 cl) (Z_to_bv 64 Ln) (Z_to_bv 64 3) (sxb b1) (Z_to_bv 64 RS) x7
                                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                           bvmap_empty (Z_to_bv 64 0x0972b4) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) a2 a3 a4 a5 a6 (Z_to_bv 64 57)
               pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0971dc) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * HL HC HB HBC RB0 RB1 CR Hcl HOV. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
    assert (CLr : 0 <= cl < 32768) by (subst cl; Z.div_mod_to_equations; lia).
    zstep. zstep. ifc false.
    zstep. zstep. zstep. zstep. zstep.
    first [rewrite hdr_cfglenA | rewrite hdr_cfglenA']; rewrite <- Hcl.
    zstep. zstep. ifc true.
    apply evtA_done. eexists _. unfold mkR. repeat (first [ reflexivity | lia | progress f_equal ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0120@L11028154364.83 L11447729958.112L12500131315.94 L13743529788.84 L13800039743.84 L14946363984.83 L15526920384.83 L15770865220.84 L16322629745.84 L16671906698.84 L17859014128.83 L18333377407.84 L18801868959.84 L19392081570.0  L21270650084.84 L22888828624.83 L26382242799.84 L28484349516.84 L30899565104.84 L32700812039.83 L33774851631.84 L34190485658.84 L37188192052.84 L39075111646.83 L40461941882.84 L41481127888.83 L43938115776.83 L44116245306.84 L47612646832.84 L48948562436.84 L49097507355.84 L52116904527.84 L52629933536.83 L53371922660.84 L54178039594.84 L59579215600.83 L63009767252.84 L64452784412.83 L65447867572.84 L6764619514.84  L7622844564.84  L9073172292.84  Q1841293521.83  Q20657901611.83 Q24135523578.83 Q26590172742.83 Q2789723050.83  Q3728816425.83  Q40417455158.83 Q41463098448.83 Q44393233288.83 Q45244024394.83 Q45510822896.83 Q48756875136.83 Q49640041892.83 Q51818728080.83 Q54139823462.83 Q55194950814.83 Q56897941899.83 Q57031419594.83 Q59340428960.83 Q6226029834.83  Q63537603100.83 Q67476437692.83 Q68713813506.83 Q8664299980.83  00000800900U00V00W00X00Y00Z00[00\00m00n00o01001101T01U01V01g02?02@02A02B02Z03203A03B03Z03[04304H04I04J04K04L04T04U04m04n05F05G05H06206C06e07=07_08308K09509M09a0:G0:X0;>0;d0<<0<^0=90=T0>:0>\0?:0?X0@60@TS3sp02b1FS5fdata2Ln2b02b11r2R01q1H2H0FFFFFFFS3sp05fdata2Ln2b1FFSFS3sp04SPlo5fdata2Ln3cap2b12HL2HC2R1FFS3sp05fdata2Ln2b1S3sp05fdata2Ln2cl2b13HOKFFFS3sp05fdata2Ln3cap2b12HLS3sp05fdata2Ln3buf2cl2b1S3sp02cl2b13CLrFS3sp05fdata2Ln3buf2cl2b1FS3sp05fdata2Ln3buf2cl2b1S3sp05fdata2Ln3buf2b1FFFFS3sp02b1FS3sp05fdata2Ln2cl2b13CLrFS3sp05fdata2Ln3buf2cl2b1FFS5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R13CLrS5fdata2Ln3buf2b1S5fdata2Ln3buf3cap2cl2b12HL3HOK2R1S5fdata2Ln3buf2cl2b13CLrS5fdata2Ln3buf3cap2cl2b12HL3HOK2R1S5fdata2Ln3buf2b12HBS5fdata2Ln3buf2cl2b13CLrS5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R13CLrS5fdata2Ln3buf2cl2b13CLrS5fdata2Ln3buf2b12HBS5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R1S5fdata2Ln3buf2b1S5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R1S5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R1S5fdata2Ln3buf2cl2b13CLrS5fdata2Ln3buf3cap2cl2b12HL3HOK2R1S5fdata2Ln3buf3cap2b12HL2R1S5fdata2Ln3buf3cap2b12HL2R1S5fdata2Ln3buf3cap2cl2b12HL3HBC3HOK2R1S5fdata2Ln3buf3cap2cl2b12HL3HOK2R1S5fdata2Ln3buf2cl2b12HB2R13CLrS5fdata2Ln3buf2cl2b12HB2R13CLrS5fdata2Ln3buf2cl2b12HB2R13CLrS5fdata2Ln3buf2cl2b12HB2R13CLr". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma Hok_steps : forall (CS : Z -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 x7 t3 t4 t5 t6 : word) (buf cap cl : Z) (b0 b1 p0 p1 p2 p3 : byte) m,
    6 <= Ln < cap -> cap <= 67108864 -> 0 < buf -> buf + cap < 2^47 ->
    ov_read_bytes asegs m (wa (buf + 0)) 1 = Some [b0] -> ov_read_bytes asegs m (wa (buf + 1)) 1 = Some [b1] ->
    crange CS buf cap -> cl = bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128) -> cl + 6 <= Ln ->
    ov_read_bytes asegs m (wa (buf + (cl + 2))) 1 = Some [p0] -> ov_read_bytes asegs m (wa (buf + (cl + 3))) 1 = Some [p1] ->
    ov_read_bytes asegs m (wa (buf + (cl + 4))) 1 = Some [p2] -> ov_read_bytes asegs m (wa (buf + (cl + 5))) 1 = Some [p3] ->
    evtA asegs AL CS
      (fun ms' => exists a0' a1' a2' a3', ms' = MS (mkR (Z_to_bv 64 0x097254) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                                (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2 + cl + 4)) (Z_to_bv 64 (Ln - cl - 6))
                                a0' a1' a2' a3'
                                (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2 + cl + 4)) (Z_to_bv 64 (Ln - cl - 6)) (sxb b1) (Z_to_bv 64 RS) x7
                                (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                           bvmap_empty (Z_to_bv 64 0x0973b0) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (mkR (Z_to_bv 64 0x0971dc) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
               (Z_to_bv 64 2) (Z_to_bv 64 buf) (Z_to_bv 64 0) (Z_to_bv 64 (-4095)) a2 a3 a4 a5 a6 (Z_to_bv 64 57)
               pathp (Z_to_bv 64 Ln) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS) x7
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
          bvmap_empty (Z_to_bv 64 0x0971dc) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * HL HC HB HBC RB0 RB1 CR Hcl HOK RP0 RP1 RP2 RP3. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 8 b0) as R0. pose proof (bv_unsigned_in_range 8 b1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
    assert (CLr : 0 <= cl < 32768) by (subst cl; Z.div_mod_to_equations; lia).
    zstep. zstep. ifc false.
    zstep. zstep. zstep. zstep. zstep.
    first [rewrite hdr_cfglenA | rewrite hdr_cfglenA']; rewrite <- Hcl.
    zstep. zstep. ifc false.
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    do 9 zstep.
    zstep. zstep.                                   (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                     (* [comment removed for export] *)
    zstep.                                          (* [comment removed for export] *)
    apply evtA_done. eexists _, _, _, _. unfold mkR. repeat (first [ reflexivity | lia | progress f_equal ]).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition target_stmtA : Prop :=
    forall (buf cap cl plen : Z) (t0 t1 t2 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (m : mem) (mo : Model) (h : HST asegs R HIA),
      TINVA buf cap m mo h -> 0 <= cl < 32768 -> 0 <= plen -> cl + 6 + plen = Ln ->
      srealizesJ asegs
        (mkCfg (MS (mkR (Z_to_bv 64 0x097254) (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
                        (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 buf) (Z_to_bv 64 (buf + 2)) (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2 + cl + 4)) (Z_to_bv 64 plen)
                        a4 a5 a6 a7
                        (Z_to_bv 64 cl) (Z_to_bv 64 (buf + 2 + cl + 4)) (Z_to_bv 64 plen) (sxb (nth 1 fdata (Z_to_bv 8 0))) (Z_to_bv 64 RS) x7
                        (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6)
                   bvmap_empty (Z_to_bv 64 0x0973b0) (Z_to_bv 32 0) None m (seg_rom asegs)) mo)
        (TAIL fs0 fdata cl plen).

  Hypothesis TARGET : target_stmtA.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00]0@L12500131315.127L15851360259.109L16855619843.130L16882893957.118L20851998927.115L22169021323.117L2414574394.110 L2414574394.121 L26160698123.130L27645142961.110L30484933857.115L32170212448.117L32171964359.121L3426655953.110 L34977474657.128L38749782723.121L39077278989.117L39087292074.121L39414254045.110L39414254045.121L39675959649.110L39675959649.121L39675959649.128L4006124574.133 L42250547024.121L42485194539.121L44261801751.131L45233603498.117L45244303373.121L48266554850.128L49266532233.128L512889190.133  L52018755744.121L52018755744.128L52157358816.121L52776274919.120L54715282434.128L57747639707.121L57761875516.117L61617734816.117L61981755008.121L62341220886.119L63960610831.107L6943675859.105 L6967381616.121 00000o01F02L03D03d04\05H06P07D07[08;08a09G09_0:>0;20;_0<L0=70>40>L0?>0@30@k0AN0BA0CU0D<0Dc0EW0F:0GP0H40HX0I;0J30JX0KU0LR0ME0Mh0N`0O<0ON0P1S3sp04SPlo5fdata5STKHI6HSTKHI3msp2Ln3cap2CB2b02b14RB0r1q1r1H2H0S3sp05fdata3msp2Ln4LONGS3sp04SPlo5fdata5STKHI6HSTKHI3msp2Ln3cap2CB2b02b14RB1r2cl3CLr2E23CFG1ES3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp05fdata3msp2Ln2b02b14RB0r2clS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CLr3CFG5OKLENS1R3HIA3sp04SPlo5fdata3FR04HFR03msp2Ln1h3FRBS1R3HIA3sp04SPlo5fdata3FR04HFR03msp2Ln1h3FRB4LONG2b02b14RB1r2cl3CFG4OVERS3sp04SPlo5fdata3msp2Ln2b02b14RB0r4RB1r2cl3CFG2EC2PZS3sp05fdata3msp2Ln4LONGS3sp05fdata3msp2Ln2b02b14RB1r2clS3sp05fdata3msp2Ln3cap2CB2b02b12cl3CFGS3sp05fdata3msp2Ln3cap2CB2b02b12cl3CFGS3sp05fdata3msp2Ln5SHORTS3sp05fdata3msp2Ln2b02b12cl3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CFG5OKLENS3sp05fdata3msp2Ln3cap4LCAP4LONG2b02b12cl3CFGS3sp05fdata3msp2Ln3cap4LCAP4LONG2b02b12cl3CFGS1R3HIA3sp04SPlo5fdata2V04HV0M3msp2Ln1h3VOLS1R3HIA3sp04SPlo5fdata2V04HV0M3msp2Ln1h3VOL2b02b14RB1r2cl3CFGS3sp05fdata3msp2Ln5SHORTS3sp04SPlo5fdata3msp2Ln2b02b14RB1r2cl3CLr3CFG4OVERS3sp04SPlo5fdata3msp2Ln3cap4LCAP2CB2b02b14RB1r2cl3CFGS3sp04SPlo5fdata3msp2Ln2b02b14RB0r4RB1r2cl3CFG2EC1n2E31lS3sp05fdata3msp2Ln2b02b12cl3CLr3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CFG4OVERS3sp04SPlo3fs05fdata5STKHI6HSTKHI3msp2Ln3cap2CB2b02b14RB1r2cl3CLr3CFG5OKLEN2EC2PZ2E3S3sp05fdata3msp2Ln3buf3BLO2b02b12cl3CFGS3sp05fdata3msp2Ln3buf3BLO2b02b12cl3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CFG5OKLENS3sp05fdata3msp2Ln2b02b12cl3CLr3CFGS3sp04SPlo5fdata5STKHI6HSTKHI3msp2Ln3cap2CB2b02b14RB0r4RB1r2cl3CFG5OKLEN2EC2PZ1n2E32n0S3sp05fdata3msp2Ln4LONG2b02b12cl3CFGS3sp05fdata3msp2Ln4LONG2b02b12cl3CFGS3sp05fdata3msp2Ln2b02b12cl3CLr3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp05fdata3msp2Ln2b02b12cl3CFG5OKLENS1R3sp04SPlo5fdata3msp2Ln3buf3cap3BCE5HCEIL2b02b14RB1r2cl3CFGS1R3sp04SPlo5fdata3msp2Ln3buf3cap3BCE5HCEIL2b02b14RB1r2cl3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CFG4OVERS3sp05fdata3msp2Ln2b02b12cl3CLr3CFGS3sp04SPlo5fdata3msp2Ln4LONG2b02b14RB1r2cl3CLr3CFG5OKLENS3sp05fdata3msp2Ln3LnR5SHORTS3sp05fdata3msp2LnS3sp05fdata3msp2Ln2b02b12cl3CLr3CFG". (* [comment removed for export] *)
  #[using="AL L IMG ASB HFREE HTP HIMGCS SIFP SPlo SPhi SPal STKLO HTOPlo HSTKHI HV0 HV0M HFR0 msp Ln TARGET"] Theorem after_loopA : after_loop_stmtA R HIA HID sp0 path pathp fs0 fdata can tid wp0 rp0 wp1 rp1 TOP STKHI V0 FR0 pad SI.
  Proof.
    intros buf cap ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 m mo h LI HLc.
    eapply close_glue; [exact LI | exact HLc |].
    intros a2' a3' a4' a5' a6' m1 mo1 TI.
    pose proof TI as TI'. destruct TI' as [HH HKmo HT HS VOL FRB TM FI SSH SIm ST FR FS FDSq BY WR LCAP COK BR FRSH FRSH0].
    pose proof (cap_ok_bounds sp0 cap COK) as CB.
    pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
    pose proof (hd_blk_band _ _ _ HID h _ _ m1 buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
    pose proof (hd_ceil _ _ _ HID) as HCEIL.
    pose proof (hcs_block _ _ HIA h _ _ m1 buf cap HH ltac:(left; reflexivity)) as CRB.
    assert (FD2 : fd_lookup (m_fds mo1) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite FDSq; reflexivity).
    assert (LnR : 0 <= Ln) by (cbv delta [Ln]; lia).
    destruct (Z.lt_ge_cases Ln 6) as [SHORT|LONG].
    { (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKmo | apply (Hshort_steps (hcs asegs R HIA h)); lia |].
      cbn beta. intros ms2 mo2 -> HK2 MM2.
      replace (BODYA fs0 fdata) with (t_die msg_short fs0).
      2:{ unfold BODYA, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; cbv delta [Ln] in *; lia).
          replace (length fdata <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; cbv delta [Ln] in *; lia). reflexivity. }
      eapply (err_tailA R HIA HID IMG ASB HFREE HTP HIMGCS sp0 SPlo SPhi SPal STKLO fs0 tid wp0 rp0 TOP STKHI HTOPlo HSTKHI pad can wp1 rp1 0x097298 msg_short buf cap);
        [ left; split; reflexivity | exact HH | exact HK2 | exact HT | exact HS | unfold AVOL_CALL in *; lia | unfold fr_charge; lia
        | rewrite (mo_mat_fs _ _ MM2); exact FS | rewrite (A_main_fin.mo_mat_fds _ _ MM2); exact FD2 | exact TM | exact FR | exact ST ]. }
    (* [comment removed for export] *)
    set (b0 := nth 0 fdata (Z_to_bv 8 0)). set (b1 := nth 1 fdata (Z_to_bv 8 0)).
    pose proof (nth_byte_readA m1 buf fdata 0 BY ltac:(cbv delta [Ln] in *; lia)) as RB0. change (Z.of_nat 0) with 0 in RB0. fold b0 in RB0.
    pose proof (nth_byte_readA m1 buf fdata 1 BY ltac:(cbv delta [Ln] in *; lia)) as RB1. change (Z.of_nat 1) with 1 in RB1. fold b1 in RB1.
    pose proof (bv_unsigned_in_range 8 b0) as RB0r. pose proof (bv_unsigned_in_range 8 b1) as RB1r. unfold bv_modulus in RB0r, RB1r. cbn in RB0r, RB1r.
    set (cl := bv_unsigned b0 + 256 * (bv_unsigned b1 mod 128)).
    assert (CLr : 0 <= cl < 32768) by (subst cl; Z.div_mod_to_equations; lia).
    assert (CFG : Z.to_nat ((bv_unsigned (nth 0 fdata (Z_to_bv 8 0)) + 256 * bv_unsigned (nth 1 fdata (Z_to_bv 8 0))) mod 32768) = Z.to_nat cl).
    { fold b0 b1. rewrite cfg_mod by lia. reflexivity. }
    destruct (Z.lt_ge_cases Ln (cl + 6)) as [OVER|OKLEN].
    { (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKmo | eapply (Hover_steps (hcs asegs R HIA h)); first [exact RB0 | exact RB1 | exact CRB | reflexivity | lia] |].
      cbn beta. intros ms2 mo2 (a1'' & ->) HK2 MM2.
      replace (BODYA fs0 fdata) with (t_die msg_overrun fs0).
      2:{ unfold BODYA, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; cbv delta [Ln] in *; lia).
          replace (length fdata <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; cbv delta [Ln] in *; lia). cbv zeta. rewrite CFG.
          replace (length fdata <? 6 + Z.to_nat cl)%nat with true by (symmetry; apply Nat.ltb_lt; cbv delta [Ln] in *; lia). reflexivity. }
      eapply (err_tailA R HIA HID IMG ASB HFREE HTP HIMGCS sp0 SPlo SPhi SPal STKLO fs0 tid wp0 rp0 TOP STKHI HTOPlo HSTKHI pad can wp1 rp1 0x0972b4 msg_overrun buf cap);
        [ right; split; reflexivity | exact HH | exact HK2 | exact HT | exact HS | unfold AVOL_CALL in *; lia | unfold fr_charge; lia
        | rewrite (mo_mat_fs _ _ MM2); exact FS | rewrite (A_main_fin.mo_mat_fds _ _ MM2); exact FD2 | exact TM | exact FR | exact ST ]. }
    (* [comment removed for export] *)
    pose proof (nth_byte_readA m1 buf fdata (Z.to_nat (cl + 2)) BY ltac:(cbv delta [Ln] in *; lia)) as RP0.
    pose proof (nth_byte_readA m1 buf fdata (Z.to_nat (cl + 3)) BY ltac:(cbv delta [Ln] in *; lia)) as RP1.
    pose proof (nth_byte_readA m1 buf fdata (Z.to_nat (cl + 4)) BY ltac:(cbv delta [Ln] in *; lia)) as RP2.
    pose proof (nth_byte_readA m1 buf fdata (Z.to_nat (cl + 5)) BY ltac:(cbv delta [Ln] in *; lia)) as RP3.
    rewrite Z2Nat.id in RP0, RP1, RP2, RP3 by lia.
    eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
      [exact HKmo | eapply (Hok_steps (hcs asegs R HIA h)); first [exact RB0 | exact RB1 | exact RP0 | exact RP1 | exact RP2 | exact RP3 | exact CRB | reflexivity | lia] |].
    cbn beta. (intros ms2 mo2 dd_H; ddestruct dd_H as (a0'' & a1'' & a2'' & a3'' & ->); intros HK2 MM2).
    eapply srzJ_conseq.
    - fold b1. eapply (TARGET buf cap cl (Ln - cl - 6) _ _ _ _ _ _ _ _ _ _ _ _ m1 mo2 h); [| lia | lia | lia].
      destruct TI; split; try assumption.
      all: rewrite ?(A_main_fin.mo_mat_fds _ _ MM2), ?(mo_mat_fs _ _ MM2); assumption.
    - (* [comment removed for export] *)
      unfold TAIL, SUCC, CALLS, BODYA, t_body.
      replace (MAX_INPUT <=? Z.of_nat (length fdata)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; cbv delta [Ln] in *; lia).
      replace (length fdata <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; cbv delta [Ln] in *; lia). cbv zeta. rewrite CFG.
      replace (length fdata <? 6 + Z.to_nat cl)%nat with false by (symmetry; apply Nat.ltb_ge; cbv delta [Ln] in *; lia).
      fold b0 b1.
      assert (EC : (if cl =? 0 then 1%nat else S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)))
                   = match Z.to_nat cl with 0%nat => 1%nat | S _ => S (Z.to_nat (bv_unsigned (nth 2 fdata (Z_to_bv 8 0)) mod 4)) end).
      { destruct (Z.eqb_spec cl 0) as [E|E]; [rewrite E; reflexivity|]. destruct (Z.to_nat cl) eqn:E2; [lia | reflexivity]. }
      rewrite EC.
      destruct (Z.eqb_spec (Ln - cl - 6) 0) as [PZ|PZ].
      + replace (length fdata - 6 - Z.to_nat cl)%nat with 0%nat by (cbv delta [Ln] in *; lia). apply t_eq_refl.
      + destruct (length fdata - 6 - Z.to_nat cl)%nat eqn:E3; [cbv delta [Ln] in *; lia|].
        apply t_alt2_congr_l.
        unfold status. replace (128 <=? bv_unsigned b1) with (32768 <=? bv_unsigned b0 + 256 * bv_unsigned b1).
        2:{ destruct (Z.leb_spec0 128 (bv_unsigned b1)); [apply (proj2 (Z.leb_le _ _)); lia | apply (proj2 (Z.leb_gt _ _)); lia]. }
        apply (t_emit_W_nil 1). apply t_exit_has_nil.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Hdr.
