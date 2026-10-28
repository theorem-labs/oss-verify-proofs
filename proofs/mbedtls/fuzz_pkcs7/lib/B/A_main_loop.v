(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape ZBridge HeapIface Asn1Aux Arr.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import StoreOk MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec SInv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_main_file.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy SRz AEvtS AEvtA AShadow AUnw NodesA SymDriveA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt ARtDrv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals ARestrict A_exit_lib A_unreg_globals A_tailkit_defs A_oomtail A_refused A_rip A_icpt_read A_main_tails.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_main_inv.
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

Section Loop.
  Variable R : art_layout.
  Variable HIA : artA asegs R.
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
  (* [comment removed for export] *)
  Variable HID : artD asegs R HIA.
  Let HRTC : forall m, arl_rtc R m -> asan_rtc m := hd_rtc _ _ _ HID.
  Let NEEDS : 0 <= arl_need_malloc R <= 4096 /\ 0 <= arl_need_free R <= 4096 /\ 0 <= arl_need_amem R <= 4096 := hd_needs _ _ _ HID.
  Let DRVS : forall a, drv_static a -> cstatic R a := hd_static _ _ _ HID.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variable sp0 : word.
  Hypothesis SPlo : 0x7fff80000000 <= bv_unsigned sp0.       (* [comment removed for export] *)
  Hypothesis SPhi : bv_unsigned sp0 <= 0x800000000000.       (* [comment removed for export] *)
  Hypothesis SPal : bv_unsigned sp0 mod 16 = 0.
  Hypothesis STKLO : arl_stklo R = bv_unsigned sp0 - 8388608.
  Variables (path : list byte) (pathp : word) (fs0 : Fs) (fdata : list byte).
  Hypothesis Hfs : fs_lookup fs0 path = Some fdata.
  Variables (can : word) (tid : Z) (wp0 rp0 wp1 rp1 : word).
  (* [comment removed for export] *)
  Variables (TOP STKHI V0 FR0 : Z).
  Hypothesis HTOPlo : bv_unsigned sp0 - 48 <= TOP.
  Hypothesis HSTKHI : bv_unsigned sp0 <= STKHI.
  Hypothesis HV0 : V0 + 2^29 <= AVOL_SPLIT.      (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010<L989271055.2000006S2V01H". (* [comment removed for export] *)
  Let HV0M : V0 + 2^29 <= AVOL_MAX.                (* [comment removed for export] *)
  Proof. pose proof HV0 as H. unfold AVOL_SPLIT, AVOL_MAX in *. clear - H. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Hypothesis HFR0 : FR0 <= FR_MAX.                 (* [comment removed for export] *)
  Variable pad : list byte.                        (* [comment removed for export] *)
  Let HBLK_BAND : forall h LB LF m A n, HM asegs R HIA h LB LF m -> In (A, n) LB ->
      0x65f000 <= A /\ A + n <= alloc_ceiling /\ (A + n <= 0x7fff7000 \/ 0x10007fff8000 <= A) := hd_blk_band _ _ _ HID.
  Let HM_LOWSH : forall h LB LF m, HM asegs R HIA h LB LF m -> mapped m 0x7fffa000 0x800d3000 := hd_lowsh _ _ _ HID.
  Let HCEIL : alloc_ceiling + 8 <= 0x7fffffffffff := hd_ceil _ _ _ HID.
  Hypothesis HIMGCS : forall h, A_unreg_globals.img_cs AL (hcs asegs R HIA h).
  (* [comment removed for export] *)
  Variable SI : sinv (arl_L R).
  Hypothesis SIFP : forall a, ~ outside (si_fp SI) a -> 0x63c0a0 <= a < 0x63c180.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L41853474148.50000009S3sp01n1H". (* [comment removed for export] *)
  #[using="sp0"] Lemma DNULL_big : forall h n, 131072 <= n -> AMAX_SEC <= n \/ hfresh _ _ _ HID h (pclass _ _ _ HID n).
  Proof. intros h n H. left. unfold AMAX_SEC. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Let msp : Z := bv_unsigned sp0 - 128.

  (* [comment removed for export] *)
  #[using="AL ASB"] Lemma HM_ZIMG : forall h LB LF m, HM asegs R HIA h LB LF m -> forall a : Z, ZIMG_LO <= a < ZIMG_HI -> m (Z_to_bv 64 a) = Some (Z_to_bv 8 0).
  Proof. intros h LB LF m HH. apply (img_shadow_low_zero AL m ASB). exact (hm_img_shadow _ _ HIA h LB LF m HH). Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma img_globs_off_rs : forallb (fun r => (snd (glob_piv r) <=? 0xc580a) || (0xc780a <=? fst (glob_piv r))) img_globs = true.
  Proof. vm_compute. reflexivity. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L59139675125.50L59315036641.5700000C00dS3sp04SPlo3msp1g2HgS3sp04SPlo3msp1g2Hg2hi2I21B2lo2I1". (* [comment removed for export] *)
  #[using="sp0 SPlo msp"] Lemma img_shval_rs : forall g, 0xc580a <= g < 0xc780a -> img_shval g = 0.
  Proof.
    intros g Hg. unfold img_shval.
    replace (in_iv g tab_piv) with false.
    2:{ symmetry. unfold in_iv, tab_piv, ATAB, ATAB_N. apply Bool.andb_false_iff. right. apply Z.ltb_ge. cbn. lia. }
    destruct (find (fun r => in_iv g (glob_piv r)) img_globs) as [r|] eqn:E; [|reflexivity].
    exfalso. apply find_some in E. destruct E as [IN IV].
    pose proof (proj1 (forallb_forall _ _) img_globs_off_rs r IN) as B. cbn beta in B.
    destruct (glob_piv r) as [lo hi]. cbn [fst snd] in B. unfold in_iv in IV. apply andb_prop in IV. destruct IV as [I1 I2].
    apply Bool.orb_prop in B. apply Z.leb_le in I1. apply Z.ltb_lt in I2. destruct B as [B|B]; apply Z.leb_le in B; lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L1628308131.61 L30235101378.59L41325459395.61L42633944771.61L47586859912.59L48405753527.59L50701533091.61L53449466050.59L61028955103.62L63368326909.6100000@00K00[01301<01J01b01m02602?S3sp03msp1n1a2HaS3sp03msp1nS3sp03msp1n1a2HaS3sp04SPlo3msp1n2Hn1a2HaS3sp03mspS3sp03msp1n2HnS3sp04SPlo3msp1n2Hn1a2HaS3sp03msp1nS3sp03mspS3sp03msp". (* [comment removed for export] *)
  #[using="IMG sp0 SPlo msp"] Lemma aobj_read_stage : forall h LB LF m n, HM asegs R HIA h LB LF m -> 0 <= n <= RSN ->
    aobj asegs AL (hcs asegs R HIA h) m RS n.
  Proof.
    intros h LB LF m n HH Hn. pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
    split.
    - apply (hcs_img _ _ HIA h); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; unfold RS, RSN in *; lia.
    - intros a Ha. exists (Z_to_bv 8 0). split; [| left; reflexivity].
      pose proof (img_shadow_ok_zero asegs AL m (a / 8) (hm_img_shadow _ _ HIA h LB LF m HH)
                    ltac:(unfold IMG_GLO, IMG_GHI, RS, RSN in *; split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia])
                    ltac:(unfold img_shadow0; rewrite img_shval_rs; [reflexivity|]; unfold RS, RSN in *;
                          split; [apply Z.div_le_lower_bound; lia | apply Z.div_lt_upper_bound; lia])) as BY.
      replace (shadow_of AL (8 * (a / 8))) with (shadow_of AL a) in BY; [exact BY|].
      unfold shadow_of. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition FRAMEA : list cell :=
    [CB 8 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (bv_unsigned sp0 + 32));
     C8 (Z_to_bv 64 0x0970e0); C8 (Z_to_bv 64 2); C8 (Z_to_bv 64 (bv_unsigned sp0 + 8)); C8 (Z_to_bv 64 0x0e0aa8)].

  (* [comment removed for export] *)
  Definition LREGSA (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (buf len cap : Z) : bvmap 5 word :=
    mkR ra (Z_to_bv 64 msp) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x63ca90) t0 t1 t2
        (Z_to_bv 64 2) (Z_to_bv 64 buf) a0 a1 a2 a3 a4 a5 a6 a7
        pathp (Z_to_bv 64 len) (Z_to_bv 64 3) (Z_to_bv 64 cap) (Z_to_bv 64 RS)
        x7 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) t3 t4 t5 t6.

  (* [comment removed for export] *)
  Definition ndbl (cap : Z) : Z :=
    match cap with
    | 65536 => 10 | 131072 => 9 | 262144 => 8 | 524288 => 7 | 1048576 => 6 | 2097152 => 5
    | 4194304 => 4 | 8388608 => 3 | 16777216 => 2 | 33554432 => 1 | _ => 0
    end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L37562282205.5100000>S3sp03msp1e2He". (* [comment removed for export] *)
  #[using="sp0 msp"] Lemma ndbl_double : forall cap, cap_ok cap -> cap < 67108864 -> ndbl (2 * cap) = ndbl cap - 1 /\ 1 <= ndbl cap.
  Proof.
    (intros cap dd_H; ddestruct dd_H as (e & He & ->); intros Hlt).
    assert (E : e = 16 \/ e = 17 \/ e = 18 \/ e = 19 \/ e = 20 \/ e = 21 \/ e = 22 \/ e = 23 \/ e = 24 \/ e = 25 \/ e = 26) by lia.
    destruct E as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
      first [ exfalso; vm_compute in Hlt; discriminate | split; [vm_compute; reflexivity | vm_compute; congruence] ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  #[using="Type"] Lemma ndbl_nonneg : forall cap, 0 <= ndbl cap.
  Proof. intros cap. unfold ndbl. repeat match goal with |- context [match ?x with _ => _ end] => destruct x end; cbv; congruence. Qed.

  Record LINVA (buf len cap : Z) (m : mem) (mo : Model) (h : HST asegs R HIA) : Prop := MKLINVA {
    la_hm : HM asegs R HIA h [(buf, cap)] [] m;
    la_hk : HK asegs R HIA h mo;
    la_htop : htop asegs R HIA h = TOP;
    la_hstkhi : hstkhi asegs R HIA h = STKHI;
    la_vol : havol asegs R HIA h + 6 * (67108864 - cap) <= V0;   (* [comment removed for export] *)
    la_fr : hfr asegs R HIA h + 6 * ndbl cap <= FR0;              (* [comment removed for export] *)
    la_tail : tail_memA (Z_to_bv 64 msp) m can tid wp0 rp0 wp1 rp1;
    la_files : files_pristine m;                                  (* [comment removed for export] *)
    la_sshad : sshad asegs AL m (arl_stklo R) msp;                 (* [comment removed for export] *)
    la_si : si_P SI m;                                              (* [comment removed for export] *)
    la_stk : stk asegs m (arl_stklo R) msp;
    la_frame : rw_cells asegs m msp FRAMEA;
    la_rs : wr_at asegs m RS RSN;                                   (* [comment removed for export] *)
    la_fs : m_fs mo = fs0;
    la_fds : m_fds mo = FDS path (Z_to_bv 64 len);
    la_bytes : bytes_at asegs m buf (firstn (Z.to_nat len) fdata);
    la_rest : exists rest, bytes_at asegs m (buf + len) rest /\ Z.of_nat (length rest) = cap - len;   (* [comment removed for export] *)
    la_wr : wr_at asegs m buf cap;
    la_len : 0 <= len <= Z.of_nat (length fdata);
    la_capok : cap_ok cap;
    la_brange : 0 < buf /\ (buf + cap <= arl_stklo R \/ STKHI <= buf) /\ buf + cap <= alloc_ceiling;
    (* [comment removed for export] *)
    la_fresh : forall c, c <> KBATCH -> hfresh _ _ _ HID h c;
    la_fresh0 : (131072 <= cap /\ cap <= 2 * len) \/ forall c, hfresh _ _ _ HID h c   (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Ltac solve_condb :=
    cbn [negb]; unfold bv_eqb, bv_ltu; rewrite ?bv_lts_zero_r; rewrite ?Z.shiftr_div_pow2 by lia; change (2^26)%Z with 67108864%Z; rewrite ?unsigned_lit by lia;
    repeat (first [ apply (proj2 (Bool.negb_true_iff _)) | apply (proj2 (Bool.negb_false_iff _)) ]);
    first [ reflexivity | apply Z.eqb_eq; lia | apply Z.eqb_neq; lia | apply Z.ltb_lt; lia | apply Z.ltb_ge; lia
          | apply Z.leb_le; lia | apply Z.leb_gt; lia ].
  Ltac done_regs := apply evtA_done; unfold mkR; rewrite ?Z.shiftl_mul_pow2 by lia; change (2^1)%Z with 2%Z; repeat (first [ reflexivity | lia | progress f_equal ]).
  Ltac ifc b :=
    lazymatch goal with
    | |- ?EV (MS ?R ?F (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; solve_condb]
    end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15618424127.75L34319674987.74L36407763275.75L65116865035.74L9771207474.75 00000D00\01401L01`S3sp04SPlo3len3cap1KS3sp04SPlo3len3cap2Hl2HcS3sp04SPlo3len3cap2Hl2HcS3sp04SPlo3len3cap2Hl2HcS3sp04SPlo3len3cap1K". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma E1_steps : forall (CS : Z -> Prop) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (buf len cap : Z) m,
    0 <= len < cap -> cap <= 67108864 -> 0 < buf -> buf + cap <= 2^47 ->
    let w := Z.min (cap - len) 65536 in
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x0971c8) t0 t1 t2 (Z_to_bv 64 3) (Z_to_bv 64 RS) (Z_to_bv 64 w) a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf len cap)
                           bvmap_empty (Z_to_bv 64 0x5a414) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x0971ac) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hl Hc Hb Hbc. cbv zeta. unfold LREGSA, RS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. zstep.
    if_cases K; zify_cond K.
    - zstep. zstep. zstep. zstep. apply evtA_done. replace (Z.min (cap - len) 65536) with (cap + - len) by lia. reflexivity.
    - zstep. zstep. zstep. zstep. zstep. apply evtA_done. replace (Z.min (cap - len) 65536) with 65536 by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG"] Lemma E2a_steps : forall (CS : Z -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (buf len cap : Z) m,
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x0971c8) t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) t3 t4 t5 t6 buf len cap)
                           bvmap_empty (Z_to_bv 64 0x0971d4) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x0971c8) t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x0971c8) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros *. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L41369099190.75L53506590987.75L58234631467.75L58817443483.7500000<00A00M00YS3sp02nb3HnbS3sp0S3sp02nb3HnbS3sp02nb3Hnb". (* [comment removed for export] *)
  #[using="IMG"] Lemma E2m_steps : forall (CS : Z -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (buf len cap nb : Z) m,
    0 <= len -> 0 < nb < 2^40 -> len + nb <= cap -> cap <= 67108864 -> 0 < buf -> buf + cap <= 2^47 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 (Z_to_bv 64 (buf + len)) (Z_to_bv 64 RS) (Z_to_bv 64 nb) a3 a4 a5 a6 a7 (Z_to_bv 64 nb) t3 t4 t5 t6 buf len cap)
                           bvmap_empty (Z_to_bv 64 0x67db8) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x0971c8) t0 t1 t2 (Z_to_bv 64 nb) a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x0971c8) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hl Hnb Hlc Hc Hb Hbc. unfold LREGSA, RS. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. ifc false. zstep. zstep. ifc true. zstep. zstep. zstep. zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00;0?L10690687171.73L12642205388.73L22642726558.73L23195586408.73L27469949392.73L34319674987.73L48879598672.73L52601847421.73L57689708871.73L6105557256.73 L64797413510.7300000<00=00>00?00@00c00d00e01H01I01bS3sp03len2nbFFFFS3sp04SPlo3len3cap2nb2Hl3Hnb3Hlc2HcFFS3sp04SPlo3len3cap2nb2Hl3Hnb3Hlc2HcFS3sp04SPlo3len3cap2nb3Hlc". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma E2b_steps : forall (CS : Z -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf len cap nb : Z) m,
    0 <= len -> 0 < nb < 2^40 -> len + nb < cap -> cap <= 67108864 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf (len + nb) cap)
                           bvmap_empty (Z_to_bv 64 0x0971ac) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nb) t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x097160) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hl Hnb Hlc Hc. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. zstep. ifc false. zstep. zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L30976304750.71L38905550934.7100000D00XS3sp04SPlo3len2nb2HcS3sp04SPlo3len2nb2Hc". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma E2c_steps : forall (CS : Z -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf len cap nb : Z) m,
    0 <= len -> 0 < nb < 2^40 -> len + nb = cap -> cap = 67108864 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf cap cap)
                           bvmap_empty (Z_to_bv 64 0x097328) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nb) t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x097160) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hl Hnb Hlc Hc. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    subst cap.
    zstep. try replace (nb + len) with 67108864 by lia. try replace (len + nb) with 67108864 by lia. zstep. zstep. try (ifc true). zstep. zstep. try (ifc true). done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00C0?L1224063972.73 L20864980733.73L22642726558.73L23195586408.73L27469949392.73L29492658376.73L34319674987.73L34509431238.73L36133902151.73L39642679310.73L44121618120.73L48879598672.73L50431086452.73L53506590987.73L55907629259.73L59238019949.73L64261373644.73L65043911255.73L6751737895.73 00000100200300400500600B00[00l01E01V01W01X01]01f01o02002502:FFFFFFS3sp03cap2HcS3sp04SPlo3len3cap2nb3HlcS3sp04SPlo3cap2HcS3sp04SPlo3len3cap2nb3HlcS3sp04SPlo3cap2HcFFS3sp0S3sp03capS3sp03capFS3sp0S3sp0". (* [comment removed for export] *)
  #[using="IMG SPlo"] Lemma E2d_steps : forall (CS : Z -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf len cap nb : Z) m,
    0 <= len -> 0 < nb < 2^40 -> len + nb = cap -> 65536 <= cap < 67108864 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x097188) t0 t1 t2 (Z_to_bv 64 (2 * cap)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf cap (2 * cap))
                           bvmap_empty (Z_to_bv 64 0x69480) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x097160) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 nb) t3 t4 t5 t6 buf len cap)
          bvmap_empty (Z_to_bv 64 0x097160) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * Hl Hnb Hlc Hc. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. try replace (nb + len) with cap by lia. try replace (len + nb) with cap by lia. zstep. zstep. ifc true. zstep. zstep. ifc false. zstep. zstep. zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG"] Lemma E3a_steps : forall (CS : Z -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf cap : Z) m,
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x097188) t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf cap (2 * cap))
                           bvmap_empty (Z_to_bv 64 0x097348) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x097188) t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf cap (2 * cap))
          bvmap_empty (Z_to_bv 64 0x097188) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros *. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. done_regs.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15923652533.69L28818265767.69L34319674987.69L53506590987.69L68652831286.6900000<00F00R00W00aS3sp03cap2HcS3sp01A2HAS3sp03cap2HcS3sp0S3sp01A2HA". (* [comment removed for export] *)
  #[using="IMG"] Lemma E3b_steps : forall (CS : Z -> Prop) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf cap A : Z) m,
    0 < A < 2^47 -> 65536 <= cap < 67108864 ->
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x0971a4) t0 t1 t2 (Z_to_bv 64 A) (Z_to_bv 64 buf) (Z_to_bv 64 cap) a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 A cap (2 * cap))
                           bvmap_empty (Z_to_bv 64 0x67db8) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x097188) t0 t1 t2 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 buf cap (2 * cap))
          bvmap_empty (Z_to_bv 64 0x097188) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros * HA Hc. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. ifc false. zstep. zstep. ifc false. zstep. zstep. zstep. zstep. done_regs.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG"] Lemma E4_steps : forall (CS : Z -> Prop) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (buf cap A : Z) m,
    evtA asegs AL CS
      (fun ms' => ms' = MS (LREGSA (Z_to_bv 64 0x0971ac) t0 t1 t2 (Z_to_bv 64 buf) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 A cap (2 * cap))
                           bvmap_empty (Z_to_bv 64 0x6947c) (Z_to_bv 32 0) None m (seg_rom asegs))
      (MS (LREGSA (Z_to_bv 64 0x0971a4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 buf) t3 t4 t5 t6 A cap (2 * cap))
          bvmap_empty (Z_to_bv 64 0x0971a4) (Z_to_bv 32 0) None m (seg_rom asegs)).
  Proof.
    intros *. unfold LREGSA. subst msp. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
    zstep. zstep. done_regs.
  Qed.

  Definition OOMA : TSet := t_die msg_oom fs0.
  Definition BODYA : TSet := t_body fdata fs0.

  (* [comment removed for export] *)
  Definition after_loop_stmtA : Prop :=
    forall (buf cap : Z) (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (m : mem) (mo : Model) (h : HST asegs R HIA),
      LINVA buf (Z.of_nat (length fdata)) cap m mo h -> Z.of_nat (length fdata) < cap ->
      srealizesJ asegs (mkCfg (MS (LREGSA ra t0 t1 t2 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf (Z.of_nat (length fdata)) cap)
                                   bvmap_empty (Z_to_bv 64 0x0971d4) (Z_to_bv 32 0) None m (seg_rom asegs)) mo) BODYA.

  Section WithAfter.
    Hypothesis AFTER : after_loop_stmtA.

    Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22615015996.62L39686836314.60L59850863857.60L7037789351.62 00000Q00m01E01TS3sp04SPlo3msp1A1n1B1k2HA2HB1i2HiS3sp04SPlo3msp1A1n1B1k2H22HBS3sp04SPlo3msp1A1B2H12HAS3sp03msp1A1B1i". (* [comment removed for export] *)
    #[using="sp0 SPlo msp"] Lemma wr_at_sub : forall m A n B k, wr_at asegs m A n -> A <= B -> B + k <= A + n -> 0 <= k -> wr_at asegs m B k.
    Proof. (intros m A n B k dd_H; ddestruct dd_H as (H1 & H2 & H3); intros HA HB Hk). split; [lia|]. split; [lia|]. intros i Hi. replace (B + i) with (A + (B - A + i)) by lia. apply H3. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L37708112921.55L38189601434.55L46956218626.5500000;00G00XS3sp03msp1AS3sp03msp2xsS3sp03msp1A2xs2ys". (* [comment removed for export] *)
    #[using="sp0 SPlo msp"] Lemma u8arr_prefix : forall m A xs ys, u8arr asegs m A (xs ++ ys) -> u8arr asegs m A xs.
    Proof.
      intros m A xs ys [HB HW]. split.
      - exact (proj1 (proj1 (bytes_at_app asegs m A xs ys) HB)).
      - eapply wr_at_sub; [exact HW | lia | rewrite length_app, Nat2Z.inj_add; lia | lia].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L9386758311.5400000MS3sp04SPlo3msp4junk1n1k2LL2Hk". (* [comment removed for export] *)
    #[using="sp0 SPlo msp"] Lemma firstn_junk : forall (junk : list byte) (n k : nat), length junk = n -> (k <= n)%nat ->
      junk = firstn k junk ++ skipn k junk /\ length (firstn k junk) = k.
    Proof. intros junk n k LL Hk. split; [symmetry; apply firstn_skipn | rewrite firstn_length; lia]. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    #[using="Type"] Lemma bytes_at_prefix : forall m A xs (k : nat), bytes_at asegs m A xs -> bytes_at asegs m A (firstn k xs).
    Proof. intros m A xs k H. rewrite <- (firstn_skipn k xs) in H. exact (proj1 (proj1 (bytes_at_app asegs m A _ _) H)). Qed.
    #[using="Type"] Lemma bytes_at_suffix : forall m A xs (k : nat), bytes_at asegs m A xs -> bytes_at asegs m (A + Z.of_nat (length (firstn k xs))) (skipn k xs).
    Proof. intros m A xs k H. rewrite <- (firstn_skipn k xs) in H. exact (proj2 (proj1 (bytes_at_app asegs m A _ _) H)). Qed.

    #[using="R HIA HID NEEDS"] Lemma mo_frame_fds : forall mo mo', mo_frame mo mo' -> m_fds mo' = m_fds mo.
    Proof. unfold mo_frame, m_fds; intros mo mo' H; intuition congruence. Qed.
    #[using="R HIA HID NEEDS"] Lemma mo_frame_fs : forall mo mo', mo_frame mo mo' -> m_fs mo' = m_fs mo.
    Proof. unfold mo_frame, m_fs; intros mo mo' H; intuition congruence. Qed.
    #[using="R HIA HID NEEDS"] Lemma mo_mat_fds : forall mo mo', mo_mat mo mo' -> m_fds mo' = m_fds mo.
    Proof. unfold mo_mat, m_fds; intros mo mo' H; intuition congruence. Qed.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L62069740404.5300000>S3sp03msp1a2Ha". (* [comment removed for export] *)
    #[using="HIA HID DRVS sp0 msp"] Lemma client_range_rs : forall LB SP, client_range L LB SP RS RSN.
    Proof. intros LB SP a Ha. right. left. apply DRVS. unfold drv_static, RS, RSN in *. lia. Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00E0@L20902015966.101L24374262305.101L25735394805.101L25735394805.104L26912666961.105L30815508625.101L34850882987.103L36680291293.103L39433950396.101L40838710254.101L41681627165.101L41969432315.101L47016053518.101L47335462128.101L47591052552.101L5115413524.102 L56915284113.101L57622410744.104L62069740404.102L62778761367.101L64228181469.10100000A00U00n02D02c03403N03h04<04X04g05;05O05h06706]06n07K07i09609LS3sp05fdata3msp1wS3sp04SPlo5fdata3mspS3sp04SPlo5fdata3msp1w2HwS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3buf3len3cap1w5rest'2RL3LEN3BR22Hw2CB3BLO3BHIS3sp05fdata3msp3buf3len2m21i2HiS3sp05fdata3msp1wS3sp05fdata3msp3buf3len2Q0S3sp05fdata3msp3buf3len2Q1S3sp05fdata3msp1w2HwS3sp05fdata5STKHI6HSTKHI3mspS3sp05fdata3mspS3sp05fdata3msp1w2HwS3sp04SPhi5fdata3mspS3sp04SPlo4SPhi5fdata3mspS3sp05fdata3mspS1R3sp04SPlo5fdata3TOP6HTOPlo3msp1a2HaS3sp05fdata3msp1wS3sp04SPlo5fdata3msp1w2Hw1a1HS3sp04SPlo5fdata3msp1w2Hw1a2HaS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3buf3len3cap1w3BR22Hw3Hlc2CB3BLO3BHIS3sp04SPlo5fdata3msp1w". (* [comment removed for export] *)
    #[using="IMG ASB HRTC DRVS SPlo SPhi STKLO HTOPlo HSTKHI HBLK_BAND HM_LOWSH SIFP"] Lemma linva_rs : forall buf len cap m mo h m2 mo2 (w : Z),
      LINVA buf len cap m mo h -> 0 <= w <= RSN -> len <= cap ->
      munch [(RS, RS + w); (arl_stklo R, msp)] m m2 -> wmono asegs m m2 -> mem_inv asegs m2 ->
      stk asegs m2 (arl_stklo R) msp ->
      HK asegs R HIA h mo2 -> m_fds mo2 = FDS path (Z_to_bv 64 len) -> m_fs mo2 = fs0 ->
      LINVA buf len cap m2 mo2 h.
    Proof.
      intros * LI Hw Hlc MU WM MI2 ST2 HK2 FDS2 FS2. pose proof (cap_ok_bounds sp0 cap (la_capok _ _ _ _ _ _ LI)) as CB.
      ddestruct LI as [HH HK HT HS VOL FR TM FI SSH SIm ST FRM RSW FS FDS BY REST WR LEN COK [BR1 [BR2 BR3]] FRSH FRSH0].
      pose proof (HBLK_BAND h _ _ m buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
      assert (HH2 : HM asegs R HIA h [(buf, cap)] [] m2).
      { eapply (hm_munch _ _ HIA); [exact HH | exact MU | exact WM |].
        constructor; [| constructor; [| constructor]]; cbn [fst snd]; intros a Ha.
        - left. right. left. apply DRVS. unfold drv_static, RS, RSN in *. lia.
        - left. left. rewrite HT. cbv delta [msp] in Ha. lia. }
      split; try assumption.
      - eapply (tail_munch_rs R HIA HRTC HM_LOWSH HM_ZIMG can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m m2 h); rewrite ?unsigned_lit by lia;
          [exact TM | exact MU | exact WM | lia | rewrite STKLO; lia | cbv delta [msp]; lia | exact HH2 | exact MI2
          | eapply (proj2 (stk_split asegs m2 (arl_stklo R) (msp - 4096) msp ST2 ltac:(rewrite STKLO; cbv delta [msp]; lia)))].
      - eapply files_munch; [exact FI | exact MU | cbn [disjoint_from fst snd]; rewrite STKLO; unfold RS; cbv delta [msp]; lia].
      - eapply (sshad_keep_munch R HIA h); [exact HH | exact SSH | exact MU | exact WM | | rewrite HS; cbv delta [msp]; lia].
        replace (RS + w - RS) with w by lia. apply (hcs_img _ _ HIA h); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; unfold RS, RSN in *; lia.
      - eapply si_munch; [exact SIm | exact MU |]. intros a NO. pose proof (SIFP a NO). cbn. rewrite STKLO. unfold RS, RSN in *. cbv delta [msp]. lia.
      - eapply rw_cells_transport; [exact FRM | exact MU | exact WM |].
        cbn [cells_size csize FRAMEA Nat.add disjoint_from fst snd]. rewrite STKLO. unfold RS, RSN in *. cbv delta [msp]. lia.
      - eapply wr_at_transport; [exact RSW | exact WM].
      - eapply bytes_at_transport; [exact BY | exact MU |]. cbn [disjoint_from fst snd]. rewrite firstn_length, STKLO. unfold RS, RSN in *. cbv delta [msp]. lia.
      - ddestruct REST as (rest & RB & RL). exists rest. split; [| exact RL].
        destruct rest as [|r0 rest']; [ddestruct RB as (Q0 & Q1 & _); split; [lia|]; split; [lia|]; intros i Hi; cbn in Hi; lia|].
        eapply bytes_at_transport; [exact RB | exact MU |]. cbn [disjoint_from fst snd length]. cbn [length] in RL. rewrite STKLO. unfold RS, RSN in *. cbv delta [msp]. lia.
      - eapply wr_at_transport; [exact WR | exact WM].
      - repeat split; assumption.
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L10168902283.104L12774310386.109L18019440245.109L22251287078.101L22949631189.104L24374408707.104L25069502223.104L25069811245.110L32028595177.104L38926757261.111L40838827980.104L41681511487.104L44185746638.104L47016199980.104L47335577810.104L47972275468.101L51317268088.101L52743385949.104L56197385505.104L57622410744.107L58625790621.104L59790376165.104L63331652519.104L65179352172.107L65269853966.104L66287702001.10600000R01;01d02B02g03F04P05f06d07R08908S09=09\0:@0:j0;W0<80=:0=o0?=0?k0@\0AV0B?0C1S3sp05fdata3msp3buf3len3cap2bs3LENS3sp05fdata3msp3buf3len3cap2nb2bs4rest2Q1S3sp05fdata3msp3buf3len3cap2nb2bs4rest2Q0S3sp05fdata3msp3len3cap2bs3LENS3sp05fdata3msp3buf3len3cap2nb2bs3HlcS3sp04SPlo5fdata3msp3len3cap2bsS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3buf3len3cap2nb2bs3LEN3BR22CB3NB2S1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3buf3len3cap2nb2bs4rest2RL3LEN3BR23Hnb2CB3NB2S3sp04SPlo5fdata5STKHI6HSTKHI3msp3len3cap2nb2bs3LEN3Hnb2CB3NB2S3sp05fdata3msp3buf3len3cap2m62nb2bs4rest1i2HiS3sp05fdata5STKHI6HSTKHI3msp3len3cap2bsS3sp05fdata3msp3len3cap2bsS3sp04SPlo5fdata3msp3buf3len3cap2bs3LEN2CBS3sp04SPhi5fdata3msp3len3cap2bsS3sp04SPlo4SPhi5fdata3msp3len3cap2bsS3sp04SPlo5fdata3msp3len3cap2nb2bs3Hnb3HlcS3sp04SPlo5fdata3msp3len3cap2nb2bs3Hnb3Hlc2CBS3sp05fdata3msp3buf3len3cap2nb2bsS3sp04SPlo5fdata5STKHI6HSTKHI3msp3buf3len3cap2nb2bs3LEN2CB3BHI3NB2S3sp04SPlo5fdata3msp3buf3len3cap2nb2bs3LEN2CB3BLO1a1HS1R3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp3buf3len3cap2nb2bs3LEN3BR23Hnb2CB3NB2S3sp04SPlo5fdata3msp3buf3len3cap2bs3LEN2CB3BLOS3sp04SPlo5fdata3msp3buf3len3cap2nb2bs3LEN2CB3BLOS3sp04SPlo5fdata3msp3buf3len3cap2nb2bs4rest2RL3Hnb3Hlc3NB1S3sp04SPlo5fdata3msp3len3cap2nb2bs2Hc3HnbS3sp04SPlo5fdata3msp3len3cap2nb2bs4rest2RL3Hnb3NB1". (* [comment removed for export] *)
    #[using="ASB HRTC SPlo SPhi STKLO HSTKHI HBLK_BAND HM_LOWSH SIFP"] Lemma linva_cp : forall buf len cap m mo h m6 mo6 (nb : Z) bs,
      LINVA buf len cap m mo h -> 0 < nb -> len + nb <= cap -> Z.of_nat (length bs) = nb ->
      bs = file_read fdata (Z_to_bv 64 len) (Z_to_bv 64 (Z.min (cap - len) 65536)) ->
      munch [(buf + len, buf + len + nb); (arl_stklo R, msp)] m m6 -> wmono asegs m m6 -> mem_inv asegs m6 ->
      u8arr asegs m6 (buf + len) bs -> stk asegs m6 (arl_stklo R) msp -> HM asegs R HIA h [(buf, cap)] [] m6 ->
      HK asegs R HIA h mo6 -> m_fds mo6 = FDS path (Z_to_bv 64 (len + nb)) -> m_fs mo6 = fs0 ->
      LINVA buf (len + nb) cap m6 mo6 h.
    Proof.
      intros * LI Hnb Hlc LENB Hbs MU WM MI6 U6 ST6 HH6 HK6 FDS6 FS6. pose proof (cap_ok_bounds sp0 cap (la_capok _ _ _ _ _ _ LI)) as CB.
      ddestruct LI as [HH HK HT HS VOL FR TM FI SSH SIm ST FRM RSW FS FDS BY REST WR LEN COK [BR1 [BR2 BR3]] FRSH FRSH0].
      pose proof (HBLK_BAND h _ _ m buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
      ddestruct (read_bs fdata len (Z.min (cap - len) 65536) ltac:(lia) ltac:(lia) ltac:(lia)) as (NB1 & NB2 & APP). rewrite <- Hbs in NB1, NB2, APP.
      rewrite LENB in NB1, NB2, APP.
      split; try assumption.
      - eapply (tail_munch R HIA HRTC HM_LOWSH HM_ZIMG can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m m6 h); rewrite ?unsigned_lit by lia;
          [exact TM | exact MU | exact WM | lia | lia | rewrite STKLO; lia | cbv delta [msp]; lia | exact HH6 | exact MI6
          | eapply (proj2 (stk_split asegs m6 (arl_stklo R) (msp - 4096) msp ST6 ltac:(rewrite STKLO; cbv delta [msp]; lia)))].
      - eapply files_munch; [exact FI | exact MU | cbn [disjoint_from fst snd]; rewrite STKLO; cbv delta [msp]; lia].
      - eapply (sshad_keep_munch R HIA h); [exact HH | exact SSH | exact MU | exact WM | | rewrite HS; cbv delta [msp]; lia].
        replace (buf + len + nb - (buf + len)) with nb by lia. eapply crange_sub; [eapply (hcs_block _ _ HIA h); [exact HH | left; reflexivity] | lia | lia].
      - eapply si_munch; [exact SIm | exact MU |]. intros a NO. pose proof (SIFP a NO). cbn. rewrite STKLO. cbv delta [msp]. lia.
      - eapply rw_cells_transport; [exact FRM | exact MU | exact WM |].
        cbn [cells_size csize FRAMEA Nat.add disjoint_from fst snd]. rewrite STKLO. cbv delta [msp]. lia.
      - eapply wr_at_transport; [exact RSW | exact WM].
      - rewrite <- APP. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
        + eapply bytes_at_transport; [exact BY | exact MU |]. cbn [disjoint_from fst snd]. rewrite firstn_length, STKLO. cbv delta [msp]. lia.
        + rewrite firstn_length. replace (buf + Z.of_nat (Nat.min (Z.to_nat len) (length fdata))) with (buf + len) by lia. exact (proj1 U6).
      - ddestruct REST as (rest & RB & RL). exists (skipn (Z.to_nat nb) rest). split.
        + pose proof (bytes_at_suffix m (buf + len) rest (Z.to_nat nb) RB) as RB2. rewrite firstn_length in RB2.
          replace (buf + len + Z.of_nat (Nat.min (Z.to_nat nb) (length rest))) with (buf + (len + nb)) in RB2 by lia.
          destruct (skipn (Z.to_nat nb) rest) as [|r0 rest'] eqn:ES; [ddestruct RB2 as (Q0 & Q1 & _); split; [lia|]; split; [lia|]; intros i Hi; cbn in Hi; lia|].
          eapply bytes_at_transport; [exact RB2 | exact MU |]. rewrite <- ES, skipn_length. cbn [disjoint_from fst snd]. rewrite STKLO. cbv delta [msp]. lia.
        + rewrite skipn_length. lia.
      - eapply wr_at_transport; [exact WR | exact WM].
      - lia.
      - repeat split; assumption.
      - destruct FRSH0 as [Hc | Hc]; [left; lia | right; exact Hc].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L10389221236.94L263310189.94  L3924681351.94 L48849682215.94L54071766562.94L9357346183.94 L9899459048.94 00000100`01V02D02E03>03`FS1R1L3sp05fdata5STKHI3msp3cap2Ab5junk22B12B22B3S1R3HIA3sp04SPlo5fdata2V03msp3cap1h2h55junk23VOL2HV2CBS1R3HIA3HID3sp04SPlo5fdata3msp3cap2h55junk22CBFS1R3HIA3sp04SPlo5fdata3FR03msp3cap1h2h55junk23FRB3HFR3ND1S3sp04SPlo5fdata3msp3cap5junk23LJ2". (* [comment removed for export] *)
    #[using="SPlo"] Lemma linva_grow : forall buf cap m mo h Ab m5 mo5 h5 (junk2 : list byte),
      LINVA buf cap cap m mo h ->
      HM asegs R HIA h5 [(Ab, 2 * cap)] [] m5 -> HK asegs R HIA h5 mo5 ->
      htop asegs R HIA h5 = TOP -> hstkhi asegs R HIA h5 = STKHI -> havol asegs R HIA h5 <= havol asegs R HIA h + (4 * cap + 2 * AVOL_CALL) ->
      hfr asegs R HIA h5 <= hfr asegs R HIA h + 6 ->
      tail_memA (Z_to_bv 64 msp) m5 can tid wp0 rp0 wp1 rp1 -> files_pristine m5 -> sshad asegs AL m5 (arl_stklo R) msp -> si_P SI m5 ->
      stk asegs m5 (arl_stklo R) msp -> rw_cells asegs m5 msp FRAMEA -> wr_at asegs m5 RS RSN ->
      m_fs mo5 = fs0 -> m_fds mo5 = FDS path (Z_to_bv 64 cap) ->
      u8arr asegs m5 Ab (firstn (Z.to_nat cap) fdata) -> bytes_at asegs m5 (Ab + cap) junk2 -> Z.of_nat (length junk2) = cap -> wr_at asegs m5 Ab (2 * cap) ->
      0 < Ab -> (Ab + 2 * cap <= arl_stklo R \/ STKHI <= Ab) -> Ab + 2 * cap <= alloc_ceiling ->
      cap < 67108864 -> (forall c, c <> KBATCH -> hfresh _ _ _ HID h5 c) ->
      LINVA Ab cap (2 * cap) m5 mo5 h5.
    Proof.
      intros * LI HH HK HT HS HV HFR TM FI SSH SIm ST FR RSW FS FDS U J2 LJ2 WR B1 B2 B3 CL FRSH5.
      ddestruct LI as [_ _ _ _ VOL FRB _ _ _ _ _ _ _ _ _ _ _ _ LEN COK [BR1 [BR2 BR3]] _ _].
      pose proof (cap_ok_bounds sp0 cap COK) as CB. destruct (cap_ok_double sp0 cap COK CL) as [COK2 _].
      destruct (ndbl_double cap COK CL) as [ND1 ND2].
      split; try assumption.
      all: first [ unfold AVOL_CALL in *; lia | rewrite ND1; lia | destruct U as [BY _]; exact BY | exists junk2; split; [exact J2 | lia]
                 | repeat split; assumption | left; lia | match goal with |- ?g => idtac "LGROW:" g end ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

    Local Ltac2 Set LiaOrc.tbl := fun () => "03;0@L10168970540.163L10389987505.187L10389987518.190L10390089269.160L10398360587.187L10401973495.191L1111036325.331 L1111445926.245 L1111445927.191 L1121857453.329 L1121939374.298 L1123916968.211 L1194192770.271 L1206759174.163 L12594695402.249L14153657326.271L14282799924.187L15032584066.298L15034610820.211L1627436045.188 L1631712665.187 L16348335696.119L1638134183.192 L16758087890.337L16794316867.298L16796484421.211L16886708740.337L17364638086.211L17668345428.298L18219351865.337L18760631522.160L18761043938.192L18767252040.188L18769432284.187L191252428.245  L191252429.191  L19572498720.269L19718664194.337L19754213317.338L20047037745.163L20618328753.329L21729862831.187L21796429754.123L22064734011.211L22251224223.144L22949436274.163L23123635138.271L23125562690.333L23643297250.330L2401875518.211 L24374589863.330L24632377621.151L24680531698.271L26224911744.160L26225290880.192L26231532330.188L26233679806.187L26421815233.144L27463347768.337L27467501468.163L27882476794.123L28350103543.191L28701539402.249L2890500031.190 L29615006336.264L29657308358.332L30600543762.163L30600543763.187L30784642501.150L31655956075.272L31706901524.195L32163904766.187L32167768897.337L32168048614.188L32170145728.190L32171914944.160L32172341323.195L32174482187.116L32232403912.337L32245248719.270L32673964386.97 L33473412303.337L35414432009.337L36272883378.271L36578158303.272L36598446949.245L36600448366.329L37028613982.298L37030703581.271L37043302745.163L38174912396.163L3826540931.249 L38337387555.298L38339407653.211L38339502752.271L38352069156.163L39640727572.337L40384344379.119L40849309295.333L41213733890.163L41678321892.119L41681693595.330L41691018750.150L4406486552.163 L45244221706.160L45246307521.116L45643475915.298L45763396361.335L46539328782.271L46919600001.119L46943576666.119L47016511624.330L471865254.148  L47335380849.119L47335380852.187L47335380853.163L47335380857.295L47335380858.245L47335380859.191L47335496304.144L47335790454.330L47335790457.331L47337482610.298L47337564529.329L47339591665.271L47339690612.211L47357068372.155L47357068376.191L47739775485.163L48754630848.269L49715014645.337L50353592617.333L50355498025.337L50355529641.271L50425356868.188L50458688081.245L50666698105.148L50837205574.329L51317199041.144L51696214403.191L51747314873.295L5178804694.191 L51816673296.329L52519014883.211L52526758686.119L53135847897.245L53353811608.211L53416999178.331L54397937506.123L54712466775.187L55254858986.249L55273913070.273L55490117797.192L55490365084.260L55562932745.119L55719169545.260L56236897374.155L5647144728.339 L56628655252.119L567788350.123  L56969085050.116L57173583497.119L57622410744.337L57747590300.160L57749379415.116L57956144997.163L58880148041.165L59718465949.271L60742066176.119L6079076338.119 L61806958927.165L62009659087.271L62009819978.211L62011748428.298L62011928655.333L62022225483.163L62022225487.119L62811512283.329L63125899062.335L63127990838.337L63177494500.269L63192105220.330L63443649189.211L6384891850.187 L65056340073.119L65509844272.144L65934330362.123L67528959190.331L67529106645.245L67543833310.329L67571906942.273L67744223410.114L7275040446.163 L7338727524.187 L7881489628.191 L8102887051.333 L8258107261.164 L8456250932.211 L8458523954.298 L9668404022.248 L9668832182.242 L9949655282.191 L9949655283.245 00000g01_02V03N04E05406G07@08909L0:_0;X0<e0=c0>Y0A30Ab0B`0CO0DI0EF0Eo0Fi0Gj0Hm0Ia0K10LC0Mn0Nl0O_0PR0QE0R80Rl0S`0U40VZ0W\0XK0YI0YJ0Z=0[40[\0\X0]Y0^Z0`h0b50c80dF0eU0fe0gk0hl0jD0jk0l;0m30mY0nH0o>10J11T12[13O14C15116C17c18U19a1:a1;Z1<L1=E1=l1?61AX1C=1D?1EI1Fc1H91IE1Jg1L<1MQ1NP1OH1P<1QE1R?1SH1TB1UR1V91WD1XC1Xj1Yh1ZU1[M1\D1]01^[1_Y1`Z1a>1b61c91ch1dV1eO1fH1gW1hP1iI1j71kF1lU1md1o320B21;22222m23e24g26K27I28G29E2:C2;A2<?2=@2=o2>^2?\2@K2AX2BG2Bn2C]2DY2FB2Fh2Fi2G_2I>2J:2K=2Kd2M22Mi2O32O\2PB2Pn2QR2Rd2Sh2Ta2Uh2Vj2X42X[2YL2Z\2[\2\M2]M2^M2_>2_d2bB2db2gJ2hK2iM2jL2kC2kg2lK2m12mo2n^2o\30d31O32N32O33i34g35k36Z37X38J39939m3:aS3sp05fdata3msp4fuel3buf3len3cap5Hfuel3LEN1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest7NOTFULLS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest7NOTFULLS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPal5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS1R3sp05fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3sp05fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest1a1n2HnS1R3HIA1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2BR2CB3BHI1w2bs2nb3NB13NB04rest5FULL'5CAPLT2Ab4junk4ABLK3AB13FA43AHI2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest5FULL'S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14rest4FULLS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1wS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest5FULL'S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest5FULL'2Ab4junk3AB12LJ3LJ1S1R3HIA3sp04SPlo5fdata2V04HV0M3msp4fuel3len3cap1h5Hfuel1w2bs2nb4rest4CAP24VOL63HV0S1R3HIA3sp04SPlo5fdata3FR04HFR03msp4fuel3len3cap1h5Hfuel2CB1w2bs2nb4rest3ND23FR62h42Ab4junk4HFR43AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel3LEN1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel3LEN1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel3LEN1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel3LEN1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel2CB1w2bs2nb4rest5FULL'2Ab4junk3AB12LJ3LJ1S1R3HIA3sp04SPlo5fdata3msp4fuel3len3cap1h5Hfuel3LEN2CB1w2bs2nb4rest2h42Ab4junk3HV43AB12LJ3LJ13h114HV11S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk3AB22LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1FS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w1x1y2Hx2HyS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel3LEN1wS3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3HIA3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2CB3BHI1w2bs2nb3NB13NB04rest5FULL'5CAPLT2Ab4junk3AB13AB23FA43AHI2LJ3LJ1S1R3HIA3sp04SPlo5fdata3FR04HFR03msp4fuel3len3cap1h5Hfuel1w2bs2nb4rest3ND23FR6S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel3LEN2CB1w2Hw2bs2nb3NB23NB0S1R3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2AK3AB12LJ3LJ1S3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel2CB1w2bs2nb3NB13NB23NB04restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel3LEN1w2Hw2bs2nb4rest5FULL'4CAP2S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2Hw2bs2nb3NB14rest5FULL'S3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel2CB1w2bs2nb3NB13NB23NB04rest7NOTFULLS3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest5FULL'2Ab4junk3AB12LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3len3cap5Hfuel1w1xS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest1a1n2HnS3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel2CB1w2bs2nb3NB13NB04restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb4rest2Ab4junk3AB12LJS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk3ALO2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel3Hlc1w2bs2nbS1L3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB13ACE2LJ3LJ11HS3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb3NB13NB23NB04rest5FULL'5CAPLTS3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest4CAP22Ab4junk3AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb3NB13NB04rest5CAPLTS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest4CAP2S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest4CAP2S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1wS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S1R3HIA1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2BR2CB3BHI1w2bs2nb3NB13NB23NB04rest5FULL'5CAPLT2Ab4junk4ABLK3AB13AB23FA43AHI2LJ3LJ1S3sp03fs05fdata3msp3buf3len3cap2ra2t02t12t22a02a12a22a32a42a52a62a72x72t32t42t52t61m2mo5Hfuel7la_len0S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2AK3AB12LJ3LJ1S1L3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel2CB3BCE1w2bs2nb4rest2Ab4junk3AB12LJ3LJ11HS1R3HIA3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap1h5Hfuel2HS1w2bs2nb4restS1R3HIA3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap1h5Hfuel2HS2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S1R3sp04SPlo5STKLO5fdata3msp4fuel3len3cap5Hfuel2CB2NF1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S1R3sp04SPlo5STKLO5fdata3msp4fuel3len3cap5Hfuel2CB2NA1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S1R3sp04SPlo5STKLO5fdata3msp4fuel3len3cap5Hfuel2NA1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest1a2HaS3sp05fdata3TOP6HTOPlo3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3TOP6HTOPlo3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3TOP6HTOPlo3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3TOP6HTOPlo3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest5FULL'2Ab4junk3AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS3sp05fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel1w2Hw2bs2nb4rest3RL2S3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2Hw2bs2nbS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3buf3len3cap5Hfuel3BLO1w2bs2nb4restS3sp05fdata3msp4fuel3buf3len3cap5Hfuel3BLO1wS1R3HIA3sp04SPlo5fdata2V04HV0M3msp4fuel3len3cap1h5Hfuel2CB1w2bs2nb4rest4CAP24VOL62h42Ab4junk3HV43AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1wS1R3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1wS3sp04SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nbS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1wS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1wS3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo4SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2Hw2bs2nb4LENFS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest6CAPMAXS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB14restS3sp05fdata3msp4fuel3buf3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3HIA3sp04SPlo5fdata3msp4fuel3len3cap1h5Hfuel2CB1w2bs2nb4rest2h42Ab4junk4HFR43AB12LJ3LJ13h115HFR11S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest6CAPMAXS1R3sp05fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nb4restS1R3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nbS3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2HwS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2Hw2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest4CAP2S1R3HIA3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap1h5Hfuel2HS2CB1w2bs2nb4rest2h42Ab4junk3HS43AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w1xFS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest1a1n2HnS3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap5Hfuel3BR22CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest4CAP2S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest4CAP22Ab3AB1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS1L3sp04SPlo5fdata5HCEIL3msp4fuel3len3cap5Hfuel3LEN2CB1w2bs2nb4rest2Ab3AB13ACES3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2Hw2bs2nb4LENFS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1wS3sp05fdata3msp4fuel3len3cap5Hfuel1w1xS3sp05fdata3msp4fuel3len3cap5Hfuel3Hlc3LEN1wS3sp05fdata3msp4fuel3len3cap5Hfuel1wS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB13ALO2LJ3LJ11a1HS1L3sp04SPlo5fdata5HCEIL3msp4fuel3buf3len3cap5Hfuel3BCE1w2bs2nb4restS1L3sp04SPlo5fdata5HCEIL3msp4fuel3buf3len3cap5Hfuel3BCE1wS3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel3LEN2CB3BLO1w2bs2nb3NB14restS1R3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel3BR21w2bs2nb3NB14restS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk3AB12LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2HwS1R3sp04SPlo5STKLO5fdata3msp4fuel3len3cap5Hfuel1wS3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap5Hfuel3LEN3BR22CB1w2bs2nb4restS1R3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS1R3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS1R3sp05fdata3msp4fuel3len3cap5Hfuel1wS1R3HIA1L3sp04SPlo5STKLO5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2BR2CB3BHI1w2bs2nb3NB13NB04rest5FULL'5CAPLT2Ab4junk4ABLK3AB13AB23FA43AHI2LJ3LJ1S1R3HIA1L3sp04SPlo4SPal5STKLO5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2BR2CB1w2bs2nb3NB13NB04rest5FULL'5CAPLT2Ab4junk4AL164ABLK3AB13AB23FA42LJ3LJ1S1R3HIA1L3sp04SPlo4SPal5STKLO5fdata5STKHI6HSTKHI3msp4fuel3buf3len3cap1h5Hfuel2HS3LEN2BR2CB3BHI1w2bs2nb3NB13NB04rest5FULL'5CAPLT2Ab4junk4AL164ABLK3AB13AB23FA43AHI2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel2CB1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk3ALO2LJ3LJ1S1R3sp04SPlo5STKLO5fdata3msp4fuel3len3cap5Hfuel2NM1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb3NB13NB04restS3sp05fdata3msp4fuel3len3cap5Hfuel1wS3sp05fdata3msp4fuel3len3cap5Hfuel1wS3sp05fdata3msp4fuel3len3cap5Hfuel1w1xS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1R3sp05fdata3msp4fuel3buf3len3cap5Hfuel3BR21w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel3HlcS3sp04SPlo5fdata3msp4fuel3len3cap5Hfuel1w2Hw2bs2nb3NB14rest3RL2FS3sp04SPlo5fdata5STKHI6HSTKHI3msp4fuel3len3cap5Hfuel1w2bs2nb3NB13NB23NB04rest5FULL'6CAPMAXS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S1L3sp04SPlo5fdata3msp4fuel3buf3len3cap5Hfuel3BCE1w2bs2nb3NB14rest1HS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2Ab4junk2LJ3LJ1S3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest2AbS3sp05fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4restS3sp04SPhi5fdata3msp4fuel3len3cap5Hfuel1w2bs2nb4rest". (* [comment removed for export] *)
    #[using="IMG ASB HMALLOC HFREE HMEMCPY HTP HRTC NEEDS DRVS SPlo SPhi SPal STKLO Hfs HTOPlo HSTKHI HV0 HV0M HFR0 HBLK_BAND HM_LOWSH HCEIL HIMGCS SIFP AFTER"] Lemma read_loopA : forall (fuel : nat) (buf len cap : Z)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 : word) (m : mem) (mo : Model) (h : HST asegs R HIA),
      Z.of_nat (length fdata) - len < Z.of_nat fuel -> len < cap ->
      LINVA buf len cap m mo h ->
      srealizesJ asegs (mkCfg (MS (LREGSA ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 buf len cap)
                                   bvmap_empty (Z_to_bv 64 0x0971ac) (Z_to_bv 32 0) None m (seg_rom asegs)) mo) (LSHAPE fs0 fdata cap).
    Proof.
      induction fuel as [|fuel IH]; intros buf len cap ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x7 t3 t4 t5 t6 m mo h Hfuel Hlc LI.
      { destruct LI. lia. }
      pose proof LI as LI'. destruct LI' as [HH HKmo HT HS VOL FRB TM FI SSH SIm ST FR RSW FS FDSq BY REST WR LEN COK BR FRSH FRSH0].
      pose proof (cap_ok_bounds sp0 cap COK) as CB. dpose NEEDS as (NM & NF & NA).
      pose proof (art_alwf _ _ HIA) as ALWF. pose proof (hcs_ok _ _ HIA h) as CSOK.
      pose proof (HBLK_BAND h _ _ m buf cap HH ltac:(left; reflexivity)) as (BLO & BCE & BHI).
      pose proof IMG as IMG'. unfold asan_img_ok in IMG'. cbv delta [AL] in IMG'. ddestruct IMG' as (HGOT & HILO & HIHI & HGSB2).
      pose proof (hcs_img _ _ HIA h) as HCSI.
      set (w := Z.min (cap - len) 65536).
      assert (Hw : 1 <= w <= 65536 /\ len + w <= cap) by (subst w; lia).
      (* [comment removed for export] *)
      eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
        [exact HKmo | apply (E1_steps (hcs asegs R HIA h)); lia |].
      cbn beta. intros ms1 mo1 -> HK1 MM1. unfold LREGSA.
      (* [comment removed for export] *)
      eapply (read_icpt_fileA AL IMG ALWF (hcs asegs R HIA h) CSOK ASB (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                m mo1 3 RS w (arl_stklo R) path (Z_to_bv 64 len) fdata);
        [ exact HK1
        | rewrite (mo_mat_fds _ _ MM1), FDSq; apply FDS_lookup3
        | rewrite (mo_mat_fs _ _ MM1), FS; exact Hfs
        | apply rtc_rd_consts; apply HRTC; eapply (hm_rtc _ _ HIA); exact HH
        | eapply wr_at_sub; [exact RSW | lia | unfold RSN; lia | lia]
        | apply (aobj_read_stage h _ _ m w HH); unfold RSN; lia
        | lia
        | unfold A_rip.app_range, RS; left; lia
        | (* [comment removed for export] *) intros x y Hx Hy; apply (HCSI (RS - 64) (RSN + 128)); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; unfold RS, RSN in *; lia
        | intros c Hc; destruct (hm_shadow_rd _ _ HIA h _ _ m c HH Hc) as (b & B & _); exists b; exact B
        | rewrite unsigned_lit by lia; exact ST
        | rewrite STKLO; lia
        | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; lia]
        | rewrite unsigned_lit by lia; left; rewrite STKLO; unfold RS; lia
        | exact (tm_mi _ _ _ _ _ _ _ _ TM)
        | lia
        | right; unfold RS; lia
        | reflexivity | reflexivity | subst w; reflexivity
        | ].
      cbv zeta. intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 MU WM MI2 ST2 BY2 LENB HK2 FDS2 FS2.
      rewrite unsigned_lit in MU, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x0971c8)) with (Z_to_bv 64 0x0971c8) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      ddestruct (read_bs fdata len w ltac:(lia) ltac:(lia) ltac:(lia)) as (NB1 & NB2 & APP).
      set (bs := file_read fdata (Z_to_bv 64 len) (Z_to_bv 64 w)) in *.
      set (nb := Z.of_nat (length bs)) in *.
      change (len_word bs) with (Z_to_bv 64 nb).
      assert (FDS2' : m_fds mo2 = FDS path (Z_to_bv 64 (len + nb))).
      { rewrite FDS2, (mo_mat_fds _ _ MM1), FDSq, FDS_insert. subst nb. change (len_word bs) with (Z_to_bv 64 (Z.of_nat (length bs))). rewrite zbv_add. reflexivity. }
      assert (LI2 : LINVA buf len cap m2 mo h).
      { eapply (linva_rs buf len cap m mo h m2 mo w); try eassumption; unfold RSN; lia. }
      clear MU WM ST2.
      assert (WCS : crange (hcs asegs R HIA h) (msp - 4096) 4096).
      { eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; lia | rewrite HS; lia]. }
      assert (FD2' : fd_lookup (m_fds mo2) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite FDS2'; apply FDS_lookup2).
      destruct (Z.eq_dec nb 0) as [NB0|NB0].
      - (* [comment removed for export] *)
        assert (LENF : len = Z.of_nat (length fdata)) by lia.
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
          [exact HK2 | rewrite NB0; apply (E2a_steps (hcs asegs R HIA h)) |].
        cbn beta. intros ms3 mo3 -> HK3 MM3.
        rewrite (LSHAPE_body sp0) by lia. unfold BODY, LREGSA. rewrite LENF.
        apply (AFTER buf cap) with (h := h); [| lia].
        rewrite NB0, Z.add_0_r in FDS2'. rewrite LENF in LI2. destruct LI2; split; try assumption.
        all: rewrite ?(mo_mat_fds _ _ MM3), ?(mo_mat_fs _ _ MM3), ?FDS2', ?FS2, ?(mo_mat_fs _ _ MM1), <- ?LENF; first [assumption | reflexivity | rewrite LENF; reflexivity].
      - (* [comment removed for export] *)
        pose proof LI2 as LI2'. destruct LI2' as [HH2 _ _ _ _ _ TM2 _ _ _ ST2 _ RSW2 _ _ BYP2 REST2 WR2 _ _ _ _ _].
        ddestruct REST2 as (rest & RB2 & RL2).
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
          [exact HK2 | apply (E2m_steps (hcs asegs R HIA h)); lia |].
        cbn beta. intros ms5 mo5 -> HK5 MM5. unfold LREGSA. rewrite <- HMEMCPY.
        eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h)); [exact HK5 | |].
        { eapply (artA_amemcpy _ _ HIA (arl_memcpy_i R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                   bvmap_empty (Z_to_bv 32 0) m2 h [(buf, cap)] [] (buf + len) RS nb (arl_stklo R) (firstn (Z.to_nat nb) rest) bs);
            rewrite ?unsigned_lit by lia;
            [ right; left; reflexivity | exact HH2
            | split; [apply bytes_at_prefix; exact RB2 | eapply wr_at_sub; [exact WR2 | lia | rewrite firstn_length; lia | lia]]
            | exact BY2
            | rewrite firstn_length; lia | lia
            | eapply aobj_sub; [eapply (hm_aobj_block _ _ HIA h); [exact HH2 | left; reflexivity] | lia | lia]
            | apply (aobj_read_stage h _ _ m2 nb HH2); unfold RSN; lia
            | right; right; unfold RS; lia
            | exact ST2 | lia | cbv delta [msp]; lia
            | eapply crange_sub; [apply (hcs_stack _ _ HIA h) | lia | rewrite HS; cbv delta [msp]; lia]
            | exact MI2
            | ddestruct BR as (BR1 & [BR2|BR2] & BR3); [left; lia | right; cbv delta [msp]; lia]
            | left; unfold RS; rewrite STKLO; lia
            | right; pose proof HCEIL; lia
            | right; unfold RS; lia
            | lia
            | eapply client_wrange_block; [apply in_app_iff; left; left; reflexivity | lia | lia]
            | rewrite HT; cbv delta [msp]; lia
            | reflexivity | reflexivity | reflexivity ]. }
        cbn beta. intros ms6 mo6 P6 HK6 MM6. ddestruct P6 as (u0 & u1 & u2 & r6 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m6 & -> & MU6 & WM6 & MI6 & -> & U6 & ST6 & HH6).
        rewrite ?unsigned_lit in MU6, ST6 by lia.
        replace (ret_pc (Z_to_bv 64 0x097160)) with (Z_to_bv 64 0x097160) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        assert (LI6 : LINVA buf (len + nb) cap m6 mo6 h).
        { eapply (linva_cp buf len cap m2 mo h m6 mo6 nb bs LI2); try eassumption; try lia.
          - subst bs w. reflexivity.
          - rewrite (mo_mat_fds _ _ MM6), (mo_mat_fds _ _ MM5). exact FDS2'.
          - rewrite (mo_mat_fs _ _ MM6), (mo_mat_fs _ _ MM5), FS2, (mo_mat_fs _ _ MM1). exact FS. }
        clear MU6 WM6 U6.
        assert (FD6 : fd_lookup (m_fds mo6) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2))) by (rewrite (la_fds _ _ _ _ _ _ LI6); apply FDS_lookup2).
        destruct (Z_lt_le_dec (len + nb) cap) as [NOTFULL|FULL].
        + (* [comment removed for export] *)
          eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
            [exact HK6 | apply (E2b_steps (hcs asegs R HIA h)); lia |].
          cbn beta. intros ms7 mo7 -> HK7 MM7.
          apply (IH buf (len + nb) cap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 mo7 h); [lia | lia |].
          destruct LI6; split; try assumption.
          all: rewrite ?(mo_mat_fds _ _ MM7), ?(mo_mat_fs _ _ MM7); assumption.
        + assert (FULL' : len + nb = cap) by lia. clear FULL.
          destruct (Z.eq_dec cap 67108864) as [CAPMAX|CAPLT].
          * (* [comment removed for export] *)
            eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
              [exact HK6 | apply (E2c_steps (hcs asegs R HIA h)); lia |].
            cbn beta. intros ms7 mo7 -> HK7 MM7.
            rewrite (LSHAPE_body sp0) by lia.
            replace (BODY fs0 fdata) with (t_die msg_refused (m_fs mo7)).
            2:{ unfold BODY, t_body. replace (MAX_INPUT <=? Z.of_nat (length fdata)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
                rewrite (mo_mat_fs _ _ MM7), (la_fs _ _ _ _ _ _ LI6). reflexivity. }
            unfold LREGSA. change (MS ?Rx bvmap_empty ?pcx (Z_to_bv 32 0) None ?Mx ?rom) with (mkst Rx pcx Mx rom).
            eapply (refused_tailA AL (hcs asegs R HIA h) (HK asegs R HIA h) IMG ALWF CSOK ASB (HIMGCS h)
                      (hk_halted _ _ HIA h) (hk_mat _ _ HIA h) (hk_vmonly _ _ HIA h) (Z_to_bv 64 msp) mo7);
              rewrite ?unsigned_lit by lia;
              [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia | exact HK7
              | rewrite (mo_mat_fds _ _ MM7); exact FD6
              | exact WCS
              | apply HCSI; rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
              | reflexivity | reflexivity | reflexivity
              | exact (la_tail _ _ _ _ _ _ LI6) ].
          * (* [comment removed for export] *)
            pose proof (cap_ok_double sp0 cap COK ltac:(lia)) as [COK2 CAP2]. pose proof (ndbl_double cap COK ltac:(lia)) as [ND1 ND2].
            eapply (rz_evtA_K asegs AL (hcs asegs R HIA h) (HK asegs R HIA h) (hk_halted _ _ HIA h) (hk_mat _ _ HIA h));
              [exact HK6 | apply (E2d_steps (hcs asegs R HIA h)); lia |].
            cbn beta. intros ms7 mo7 -> HK7 MM7. unfold LREGSA. rewrite <- HMALLOC.
            eapply srzJ_conseq; [| apply (LSHAPE_grow sp0 fs0 fdata cap); lia].
            pose proof LI6 as LI7. destruct LI7 as [HH6' _ _ _ VOL6 FR6 TM6 FI6 SSH6 SI6 ST6' FR6' RSW6 FS6 FDS6 BY6 REST6 WR6 _ _ _ FRSH6 _].
            eapply (heapA_malloc_split _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                      bvmap_empty (Z_to_bv 32 0) m6 mo7 h [(buf, cap)] [] (2 * cap) (arl_stklo R) 0);
              rewrite ?unsigned_lit by lia;
              [ exact HH6' | exact HK7 | exact ST6' | lia | lia | rewrite HT; cbv delta [msp]; lia | cbv delta [msp]; lia
              | exact (tm_mi _ _ _ _ _ _ _ _ TM6) | rewrite HTP; reflexivity | reflexivity | unfold AMAX; lia | apply DNULL_big; lia
              | unfold AVOL_CALL in *; lia
              | unfold AVOL_CALL in *; lia   (* [comment removed for export] *)
              | apply uwc_data; [lia | rewrite STKLO; lia]
              | unfold fr_charge; lia
              | intros _; eapply Z.le_lt_trans; [apply cnt24_le_length| cbn [length]; unfold C24MAX; lia]   (* [comment removed for export] *)
              | apply OOM_nil | apply LSHAPE_nil | | ].
            -- (* [comment removed for export] *)
               intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 h4 MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HFRESH4 HH4.
               replace (ret_pc (Z_to_bv 64 0x097188)) with (Z_to_bv 64 0x097188) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
               eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
                 [exact HK4 | apply (E3a_steps (hcs asegs R HIA h4) _ _ _ _ _ _ _ _ _ _ _ _ _ _ buf cap m4) |].
               cbn beta. intros ms8 mo8 -> HK8 MM8. unfold LREGSA, OOM.
               replace fs0 with (m_fs mo8) by (rewrite (mo_mat_fs _ _ MM8), (mo_frame_fs _ _ MF4), (mo_mat_fs _ _ MM7); exact FS6).
               eapply (oom_glueA AL (hcs asegs R HIA h4) (HK asegs R HIA h4) IMG ALWF (hcs_ok _ _ HIA h4) ASB (HIMGCS h4)
                         (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4) (hk_vmonly _ _ HIA h4) (Z_to_bv 64 msp));
                 rewrite ?unsigned_lit by lia;
                 [ cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia
                 | eapply crange_mono; [exact HCS4|]; eapply crange_sub; [apply (hcs_stack _ _ HIA h) | rewrite STKLO; cbv delta [msp]; lia | rewrite HS; cbv delta [msp]; lia]
                 | intros a n Ha Hn; apply (hcs_img _ _ HIA h4); rewrite ?HILO, ?HIHI, ?HGOT, ?HGSB2; lia
                 | right; reflexivity
                 | eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m6 m4 h4); rewrite ?unsigned_lit by lia; [exact TM6 | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]
                 | exact HK8
                 | rewrite (mo_mat_fds _ _ MM8), (mo_frame_fds _ _ MF4), (mo_mat_fds _ _ MM7); exact FD6 ].
            -- (* [comment removed for export] *)
               intros t0'' t1'' t2'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 h4 Ab junk MI4 ST4 MF4 WM4 HP4 HT4 HS4 HF4 HK4 HCS4 HV4 HFR4 HFRESH4 AL16 FRESH ABLK HH4 RW4.
               replace (ret_pc (Z_to_bv 64 0x097188)) with (Z_to_bv 64 0x097188) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
               destruct (hm_apart _ _ HIA h4 _ _ m4 HH4) as [HBLKS _]. pose proof (Forall_inv HBLKS) as AB. cbn [fst snd app] in AB. ddestruct AB as (AB1 & AB2 & AB3 & AB4).
               pose proof FRESH as FRESH'. ddestruct FRESH' as (FA1 & FA2 & FA3 & FA4). specialize (FA4 buf cap ltac:(cbn; left; reflexivity)).
               pose proof (HBLK_BAND h4 _ _ m4 Ab (2 * cap) HH4 ltac:(left; reflexivity)) as (ALO & ACE & AHI).
               (* [comment removed for export] *)
               eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
                 [exact HK4 | apply (E3b_steps (hcs asegs R HIA h4) _ _ _ _ _ _ _ _ _ _ _ _ _ _ buf cap Ab m4); lia |].
               cbn beta. intros ms8 mo8 -> HK8 MM8. unfold LREGSA. rewrite <- HMEMCPY.
               (* [comment removed for export] *)
               pose proof RW4 as RW4'. destruct RW4' as [[WF4 _] _]. cbn in WF4. destruct WF4 as [LJ _].
               destruct (firstn_junk junk (Z.to_nat (2 * cap)) (Z.to_nat cap) LJ ltac:(lia)) as [JSPLIT LJ1].
               pose proof (u8arr_of_rw_cells asegs m4 Ab _ junk RW4) as U4full. pose proof U4full as U4. rewrite JSPLIT in U4. apply u8arr_prefix in U4.
               pose proof (bytes_at_suffix m4 Ab junk (Z.to_nat cap) (proj1 U4full)) as J2. rewrite LJ1 in J2. rewrite Z2Nat.id in J2 by lia.
               assert (BY4 : bytes_at asegs m4 buf (firstn (Z.to_nat (len + nb)) fdata)).
               { eapply (presA_bytes_at asegs R); [exact HP4 | exact BY6 | | cbn; exact I].
                 eapply client_range_block; [apply in_app_iff; left; left; reflexivity | lia | rewrite firstn_length; lia]. }
               assert (LENF1 : Z.of_nat (length (firstn (Z.to_nat (len + nb)) fdata)) = cap) by (rewrite firstn_length; lia).
               eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4)); [exact HK8 | |].
               { eapply (artA_amemcpy _ _ HIA (arl_memcpy_i R) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          bvmap_empty (Z_to_bv 32 0) m4 h4 ((Ab, 2 * cap) :: [(buf, cap)]) [] Ab buf cap (arl_stklo R));
                   rewrite ?unsigned_lit by lia;
                   [ right; left; reflexivity | exact HH4 | exact U4 | exact BY4 | rewrite LJ1; lia | exact LENF1
                   | eapply aobj_sub; [eapply (hm_aobj_block _ _ HIA h4); [exact HH4 | left; reflexivity] | lia | lia]
                   | eapply (hm_aobj_block _ _ HIA h4); [exact HH4 | right; left; reflexivity]
                   | right; lia
                   | exact ST4 | lia | cbv delta [msp]; lia
                   | eapply crange_sub; [apply (hcs_stack _ _ HIA h4) | lia | rewrite HS4, HS; cbv delta [msp]; lia]
                   | exact MI4
                   | rewrite HS in ABLK; destruct ABLK as [AK|AK]; [left; lia | right; cbv delta [msp]; lia]
                   | ddestruct BR as (BR1 & [BR2|BR2] & BR3); [left; lia | right; cbv delta [msp]; lia]
                   | right; pose proof HCEIL; lia
                   | right; pose proof HCEIL; lia
                   | lia
                   | eapply client_wrange_block; [apply in_app_iff; left; left; reflexivity | lia | lia]
                   | rewrite HT4, HT; cbv delta [msp]; lia
                   | reflexivity | reflexivity | reflexivity ]. }
               cbn beta. intros ms9 mo9 P9 HK9 MM9. ddestruct P9 as (q0 & q1 & q2 & r9 & q4 & q5 & q6 & q7 & q8 & q9 & q10 & q11 & q12 & q13 & q14 & m9 & -> & MU9 & WM9 & MI9 & -> & U9 & ST9 & HH9).
               rewrite ?unsigned_lit in MU9, ST9 by lia.
               replace (ret_pc (Z_to_bv 64 0x0971a4)) with (Z_to_bv 64 0x0971a4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
               (* [comment removed for export] *)
               eapply (rz_evtA_K asegs AL (hcs asegs R HIA h4) (HK asegs R HIA h4) (hk_halted _ _ HIA h4) (hk_mat _ _ HIA h4));
                 [exact HK9 | apply (E4_steps (hcs asegs R HIA h4)) |].
               cbn beta. intros ms10 mo10 -> HK10 MM10. unfold LREGSA. rewrite <- HFREE.
               (* [comment removed for export] *)
               eapply srzJ_of_aevtS; [ | apply LSHAPE_nil | ].
               { eapply (heapA_freeD _ _ _ HID _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                          bvmap_empty (Z_to_bv 32 0) m9 mo10 h4 ((Ab, 2 * cap) :: [(buf, cap)]) [] buf cap (arl_stklo R) 0);
                   rewrite ?unsigned_lit by lia;
                   [ exact HH9 | exact HK10 | right; left; reflexivity | exact ST9 | lia | cbv delta [msp]; lia
                   | rewrite HT4, HT; cbv delta [msp]; lia | cbv delta [msp]; lia | exact MI9 | rewrite HTP; reflexivity | reflexivity
                   | unfold AVOL_CALL in *; lia
                   | apply uwc_data; [lia | rewrite STKLO; lia]
                   | unfold fr_charge in *; lia ]. }
               (intros c11 dd_H; ddestruct dd_H as (ms11 & mo11 & -> & P11)).
               ddestruct P11 as (v0 & v1 & v2 & r11 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m11 & -> & MI11 & ST11 & MF11 & HP11 & h11 & HT11 & HS11 & HF11 & HK11 & HCS11 & HV11 & HFR11 & HFRESH11 & HH11).
               replace (ret_pc (Z_to_bv 64 0x0971ac)) with (Z_to_bv 64 0x0971ac) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
               replace (lb_remove buf ((Ab, 2 * cap) :: [(buf, cap)])) with [(Ab, 2 * cap)] in HP11, HH11.
               2:{ cbn [lb_remove fst]. replace (Ab =? buf) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Z.eqb_refl. reflexivity. }
               rewrite ?unsigned_lit in ST11, HP11 by lia.
               (* [comment removed for export] *)
               apply (IH Ab cap (2 * cap) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m11 mo11 h11); [lia | lia |].
               assert (TM4 : tail_memA (Z_to_bv 64 msp) m4 can tid wp0 rp0 wp1 rp1).
               { eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m6 m4 h4); rewrite ?unsigned_lit by lia;
                   [exact TM6 | rewrite <- HS; exact HP4 | exact HH4 | exact MI4 | exact ST4 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]. }
               assert (TM9 : tail_memA (Z_to_bv 64 msp) m9 can tid wp0 rp0 wp1 rp1).
               { eapply (tail_munch R HIA HRTC HM_LOWSH HM_ZIMG can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m4 m9 h4); rewrite ?unsigned_lit by lia;
                   [exact TM4 | exact MU9 | exact WM9 | lia | lia | rewrite STKLO; lia | cbv delta [msp]; lia | exact HH9 | exact MI9
                   | eapply (proj2 (stk_split asegs m9 (arl_stklo R) (msp - 4096) msp ST9 ltac:(rewrite STKLO; cbv delta [msp]; lia)))]. }
               assert (TM11 : tail_memA (Z_to_bv 64 msp) m11 can tid wp0 rp0 wp1 rp1).
               { eapply (tail_presA R HIA ASB HRTC HM_LOWSH HM_ZIMG DRVS can tid wp0 rp0 wp1 rp1 (Z_to_bv 64 msp) m9 m11 h11); rewrite ?unsigned_lit by lia;
                   [exact TM9 | rewrite <- HS, <- HS4; exact HP11 | exact HH11 | exact MI11 | exact ST11 | rewrite STKLO; cbv delta [msp]; lia | cbv delta [msp]; lia | cbv delta [msp]; lia]. }
               assert (FI11 : files_pristine m11).
               { eapply (files_presA R DRVS); [| exact HP11].
                 eapply files_munch; [| exact MU9 | cbn [disjoint_from fst snd]; rewrite STKLO; cbv delta [msp]; lia].
                 eapply (files_presA R DRVS); [exact FI6 | exact HP4]. }
               assert (SSH11 : sshad asegs AL m11 (arl_stklo R) msp).
               { eapply (presA_sshad asegs R); [exact HP11 | | lia | rewrite HS4, HS; cbv delta [msp]; lia].
                 eapply (sshad_keep_munch R HIA h4); [exact HH4 | | exact MU9 | exact WM9 | | rewrite HS4, HS; cbv delta [msp]; lia].
                 - eapply (presA_sshad asegs R); [exact HP4 | exact SSH6 | lia | rewrite HS; cbv delta [msp]; lia].
                 - replace (Ab + cap - Ab) with cap by lia. eapply crange_sub; [eapply (hcs_block _ _ HIA h4); [exact HH4 | left; reflexivity] | lia | lia]. }
               assert (SI11 : si_P SI m11).
               { eapply si_heap_presx; [| eapply presA_presx; exact HP11 | intros; exact I].
                 eapply si_munch; [| exact MU9 | intros a NO; pose proof (SIFP a NO); cbn; rewrite STKLO; cbv delta [msp]; lia].
                 eapply si_heap_presx; [exact SI6 | eapply presA_presx; exact HP4 | intros; exact I]. }
               assert (FRM11 : rw_cells asegs m11 msp FRAMEA).
               { eapply (presA_rw_cells asegs R); [exact HP11 | | apply client_range_stack; lia | cbn; exact I].
                 eapply rw_cells_transport; [| exact MU9 | exact WM9 | cbn [cells_size csize FRAMEA Nat.add disjoint_from fst snd]; cbv delta [msp]; lia].
                 eapply (presA_rw_cells asegs R); [exact HP4 | exact FR6' | apply client_range_stack; lia | cbn; exact I]. }
               assert (RSW11 : wr_at asegs m11 RS RSN).
               { eapply heap_presx_wr_at; [eapply presA_presx; exact HP11 | | apply client_range_rs | cbn; exact I].
                 eapply wr_at_transport; [| exact WM9].
                 eapply heap_presx_wr_at; [eapply presA_presx; exact HP4 | exact RSW6 | apply client_range_rs | cbn; exact I]. }
               replace (len + nb) with cap in LI6 by lia.
               eapply (linva_grow buf cap m6 mo6 h Ab m11 mo11 h11 (skipn (Z.to_nat cap) junk) LI6 HH11 HK11); rewrite ?unsigned_lit by lia.
               ** rewrite HT11, HT4. exact HT.
               ** rewrite HS11, HS4. exact HS.
               ** unfold AVOL_CALL in *. lia.
               ** unfold fr_charge in *. lia.
               ** exact TM11.
               ** exact FI11.
               ** exact SSH11.
               ** exact SI11.
               ** exact ST11.
               ** exact FRM11.
               ** exact RSW11.
               ** rewrite (mo_frame_fs _ _ MF11), (mo_mat_fs _ _ MM10), (mo_mat_fs _ _ MM9), (mo_mat_fs _ _ MM8), (mo_frame_fs _ _ MF4), (mo_mat_fs _ _ MM7). exact FS6.
               ** rewrite (mo_frame_fds _ _ MF11), (mo_mat_fds _ _ MM10), (mo_mat_fds _ _ MM9), (mo_mat_fds _ _ MM8), (mo_frame_fds _ _ MF4), (mo_mat_fds _ _ MM7). rewrite <- FULL'. exact FDS6.
               ** (* [comment removed for export] *)
                  replace (Z.to_nat cap) with (Z.to_nat (len + nb)) by lia.
                  eapply (presA_u8arr asegs R); [exact HP11 | exact U9 | | cbn; exact I].
                  eapply client_range_block; [apply in_app_iff; left; left; reflexivity | lia | rewrite firstn_length; lia].
               ** (* [comment removed for export] *)
                  eapply (presA_bytes_at asegs R); [exact HP11 | | | cbn; exact I].
                  { eapply bytes_at_transport; [exact J2 | exact MU9 |]. rewrite skipn_length. cbn [disjoint_from fst snd]. rewrite STKLO. lia. }
                  rewrite skipn_length. eapply client_range_block; [apply in_app_iff; left; left; reflexivity | lia | lia].
               ** rewrite skipn_length. lia.
               ** (* [comment removed for export] *)
                  eapply heap_presx_wr_at; [eapply presA_presx; exact HP11 | | | cbn; exact I].
                  { eapply wr_at_transport; [| exact WM9]. pose proof (proj2 RW4) as W4. cbn [cells_size csize] in W4. rewrite Nat.add_0_r, Z2Nat.id in W4 by lia. exact W4. }
                  eapply client_range_block; [apply in_app_iff; left; left; reflexivity | lia | lia].
               ** lia.
               ** rewrite HS in ABLK. exact ABLK.
               ** exact AB3.
               ** lia.
               ** intros c Hc. apply (HFRESH11 c Hc). apply (HFRESH4 c ltac:(left; unfold AMAX_SEC; lia)). exact (FRSH6 c Hc).
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithAfter.
End Loop.
