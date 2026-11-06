(* fuzz_recv on image A (fuzz_link.asan 0x823cc, listing offset AF_fuzz_recv = 0x200): the failure arm of its walk
   from the call of ___errno_location at +0x220 (lib/A/Prog/fuzz_recv_defs.v RV_AT_ERRNO), from the epilogue's piece
   RV_RET and the failure arm's Post RV_FPOST.
   - the call: LinkWalkErrno.v aj_gx_errno_at (a0 := tp - 164, which is errno; every other register and every byte
     kept);
   - the fresh symbolic state ss_er at +0x224 (fuzz_recv_kit.v rv_st_ok): a0 is atom 10, errno's 4 bytes are the
     region rv_err_rs;
   - the run +0x224 .. +0x238 (LinkWalkErrno.v paj_run_to_xe, stopped at +0x23c): the instrumented check of the
     4-byte store to a0 (its obligation from the call's addressable range of errno), `sw s0, 0(a0)` (errno :=
     end_errno), s2 := -1;
   - at +0x23c: rv_inv by fuzz_recv_kit.v rv_inv_step (the run writes errno's 4 bytes only), then RV_RET with the
     Post from RV_FPOST.
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtErrnoLoc.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkErrno fuzz_recv_c fuzz_recv_defs fuzz_recv_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Ltac rve_zrng := try change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); try change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32);
  try change (Z.of_N 8) with 8; try change (Z.of_N 4) with 4; lia.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ERRF : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
Hypothesis ERRNO : aerrno_location_realizes SEGS B (pa_sigma LS____errno_location).
Variable c : rvc.
Hypothesis HC : rv_call SK B c.
#[local] Notation W := (c_W c).
#[local] Notation memc := (c_memc c).

Lemma rve_region : forall E ss ms i r,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r -> region_ok SEGS E (ms_mem ms) r.
Proof. intros E ss ms i r HS Hi. exact (st_ok_region_nth (segs := SEGS) E (abs_ss VAL ss) ms i r HS Hi). Qed.

(* THE FAILURE ARM from the call of ___errno_location *)
Lemma rv_err_ok : RV_RET SK B c -> RV_FPOST SK B c -> RV_AT_ERRNO SK B c.
Proof.
  intros RVRET RVFPOST regs mem md HI Hnc HRA H8 H19 Hnx Hmi Hbuf.
  pose proof HC as ((_ & HGX & _ & _ & _ & _ & Htp & _) & _ & WF & _ & _ & Herr & Hewr & Hesh & _).
  pose proof WF as (_ & _ & _ & _ & _ & _ & _ & _ & Wee & _).
  pose proof (pal_env B TL) as ENV.
  destruct (rv_sp_bounds SK B c HC) as (Hceil & Hlo & Hhi & H47 & H16 & HXO).
  destruct (rv_pre_facts SK B TL c HC) as (Hb0 & Hlen & Hamr & Hbg & Hbf & Hef & Heg & He0 & He1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HI as (HJ & Hfd & Hfs & Hsp & Hgp & Htp0 & H26 & H27 & _ & _ & PR).
  assert (Usp : spZ regs = rv_sp c - 96).
  { unfold spZ. rewrite Hsp. unfold w64. apply unsigned_lit_small.
    unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia. }
  unfold rv_goal.
  (* the call of ___errno_location at +0x220 *)
  eapply SRr_bind.
  { apply (aj_gx_errno_at SK SEGS B LAWS pa_segs_low (pa_sigma LS____errno_location) ERRNO (c_G c) (c_XO c)
      (c_OUT c) W regs mem (c_STK c) (c_sp0 c) (c_FP c) (c_ly c) (c_S c) (c_W0 c) (c_mem0 c) (c_md0 c) (c_own c)
      (c_lyc c) (c_Sc c) md (c_k c) (Z_to_bv 64 (BASE + RV_ER)) HGX HJ).
    - rewrite Usp. unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in *. lia.
    - rewrite Usp. lia.
    - exact HRA.
    - apply ret_ok_codeptr_v; unfold RV_ER, AF_fuzz_recv; first [lia | reflexivity]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hsm & H10 & Hrk & Hm).
  assert (Emem : mem2 = mem) by (apply functional_extensionality; exact Hm). subst mem2. clear Hm.
  assert (K : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> 1 <= z < 32 -> z <> 10 -> getr regs2 rr = getr regs rr)
    by (intros rr z -> Hz Hz10; exact (Hrk z Hz Hz10)).
  assert (R2 : getr regs2 2 = getr regs 2) by (apply (K _ 2); [apply bv_eq; reflexivity | lia | lia]).
  assert (R3 : getr regs2 3 = getr regs 3) by (apply (K _ 3); [apply bv_eq; reflexivity | lia | lia]).
  assert (R4 : getr regs2 4 = getr regs 4) by (apply (K _ 4); [apply bv_eq; reflexivity | lia | lia]).
  assert (R8 : getr regs2 8 = getr regs 8) by (apply (K _ 8); [apply bv_eq; reflexivity | lia | lia]).
  assert (R19 : getr regs2 19 = getr regs 19) by (apply (K _ 19); [apply bv_eq; reflexivity | lia | lia]).
  assert (R26 : getr regs2 26 = getr regs 26) by (apply (K _ 26); [apply bv_eq; reflexivity | lia | lia]).
  assert (R27 : getr regs2 27 = getr regs 27) by (apply (K _ 27); [apply bv_eq; reflexivity | lia | lia]).
  clear K Hrk.
  assert (Hfd2 : m_fds md2 = m_fds md)
    by (rewrite (same_but_materialized_wvb _ _ Hsm); exact (proj1 (wvb_fds_fs _ _ _))).
  assert (Hfs2 : m_fs md2 = m_fs md)
    by (rewrite (same_but_materialized_wvb _ _ Hsm); exact (proj2 (wvb_fds_fs _ _ _))).
  assert (HI2 : rv_inv SK B c regs2 mem md2).
  { apply (rv_inv_step SK B TL c HC regs mem md regs2 mem md2 (fun _ => False) HI HJ2 Hfd2 Hfs2).
    - intros a _ _. reflexivity.
    - intros a [].
    - intros a Ha. exact Ha.
    - exact R2.
    - exact R3.
    - exact R4.
    - exact R26.
    - exact R27. }
  (* a0 = tp - 164 = errno *)
  assert (Utp : bv_unsigned (getr regs 4) = as_tp B).
  { rewrite Htp0, Htp. unfold w64. apply unsigned_lit_small. unfold kLowMemEnd in *. lia. }
  assert (R10 : getr regs2 10 = Z_to_bv 64 (as_errno B)) by (rewrite H10, Utp, Herr; reflexivity).
  assert (U10r : bv_unsigned (ew (rv_E c regs2) 10) = as_errno B).
  { rewrite (rv_E_reg c regs2 10 10%bv) by (lia || reflexivity). rewrite R10.
    apply unsigned_lit_small. unfold kLowMemEnd in *. lia. }
  (* THE FRESH STATE ss_er at +0x224 *)
  assert (HS : st_ok_pi SEGS VAL (rv_E c regs2) (rv_ss RV_ER rv_err_rs [(10%nat, mkAF 0 (SHADOW_OFF - 4) 0)])
                 (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + RV_ER)) mem (seg_rom SEGS)))).
  { assert (Ub : base_val (rv_E c regs2) (Some 10%nat) = as_errno B) by (cbn [base_val]; exact U10r).
    assert (Ub2 : base_val (rv_E c regs2) (Some 2%nat) = rv_sp c - 96).
    { cbn [base_val]. rewrite (rv_E_reg c regs2 2 2%bv) by (lia || reflexivity). rewrite R2. exact Usp. }
    apply (rv_st_ok SK B c HC regs2 mem md2 RV_ER rv_err_rs _ HI2 (eq_trans R19 H19)).
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, rv_err_rs.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Ub.
      split; [lia|]. split; [unfold kLowMemEnd in *; lia|]. split; [|constructor].
      intros o Ho. apply (writable_kept (segs := SEGS) (w_H W) memc mem); [exact (PR _) | apply Hewr; lia].
    - apply all_disjoint_of_extents. unfold rv_fr, rv_err_rs, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Ub, Ub2. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
      split; [|exact I].
      pose proof Hef as Hef'. unfold apart_frame in Hef'. change (spZ (c_regs0 c)) with (rv_sp c) in Hef'.
      unfold FUZZ_RECV_AK, FUZZ_RECV_AFRAME, ESTACK in Hef'. lia.
    - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
    - cbn [atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10r.
      rewrite Z.pow_0_r, Z.mod_1_r. unfold SHADOW_OFF, kLowMemEnd in *. lia. }
  remember (rv_E c regs2) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; apply rv_E_env).
  assert (E2 : ew E 2 = getr regs2 2) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  assert (E3 : ew E 3 = getr regs2 3) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  assert (E4 : ew E 4 = getr regs2 4) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  assert (E8 : ew E 8 = Z_to_bv 64 (nk_end_errno (c_bs c)))
    by (rewrite HEdef, (rv_E_reg c regs2 8 8%bv) by (lia || reflexivity); rewrite R8, H8; reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 (as_errno B))
    by (rewrite HEdef, (rv_E_reg c regs2 10 10%bv) by (lia || reflexivity); exact R10).
  assert (E19 : ew E 19 = getr regs2 19) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  assert (E19' : ew E 19 = Z_to_bv 64 SHADOW_OFF) by (rewrite E19, R19, H19; reflexivity).
  assert (E26 : ew E 26 = getr regs2 26) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  assert (E27 : ew E 27 = getr regs2 27) by (rewrite HEdef; apply (rv_E_reg c); [lia | reflexivity]).
  clear HEdef. rename U10r into U10.
  assert (SHOK : sh_ok SEGS rv_Bx [] E (mrestrict (w_H W) mem)) by constructor.
  pose proof (paj_run_to_xe SK B LAWS ENV ERRF (c_G c) HGX (c_XO c) (c_OUT c)) as RUNTO.
  (* +0x224 .. +0x238: the instrumented check, errno := s0, s2 := -1; stop at +0x23c *)
  paj_run_to_tok RUNTO HS HJ2 SHOK rv_span RV_RT.
  - (* the check's obligation: errno's 4 bytes are addressable *)
    unfold rv_Bx. rewrite (U_atom E 19 SHADOW_OFF E19') by (unfold SHADOW_OFF; lia).
    rewrite (U_atom E 10 (as_errno B) E10) by (unfold kLowMemEnd in *; lia).
    try cbn [ms_mem mkst]. rewrite <- (aview_rd_of SEGS).
    apply (rv_ra_kept SK B TL c HC regs2 mem md2 (as_errno B) 4 HI2);
      [lia | unfold kLowMemEnd, kHighMemEnd in *; lia | exact Hesh].
  - (* the run writes errno's 4 bytes *)
    lazymatch goal with |- awr_ok_xe _ _ ?rs _ _ _ _ _ _ _ _ _ _ =>
      let rs' := eval vm_compute in rs in change rs with rs' end.
    apply awr_ok_xe_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia|].
    apply awr_ok_xe_cons; [|apply awr_ok_xe_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U10 in Ha.
    right. unfold aerrno. lia.
  - (* +0x23c *)
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into msF end.
    (* every byte but errno's as before the run *)
    assert (UNk : forall a, 0 <= a < 2 ^ 64 -> ~ (as_errno B <= a < as_errno B + 4) ->
              aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) mem a).
    { apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => as_errno B <= a < as_errno B + 4) HFr).
      intros bb wlo whi aa Hin Hrr. vm_compute in Hin.
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr; [lia|].
      rewrite U10 in Hrr. lia. }
    (* errno's word: the stored s0 = end_errno *)
    pose proof (rve_region _ _ _ 1 _ HS eq_refl) as HRe.
    assert (Verr : val_mem SEGS (rdW W (ms_mem msF)) (as_errno B + 0) 4 (nk_end_errno (c_bs c))).
    { eapply (field_of_region (segs := SEGS) _ _ _ _ _ _ _ _ _ _ 4%N);
        [ exact HRe | exact U10 | repeat (first [left; reflexivity | right])
        | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E8;
          rewrite unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity
        | rve_zrng | rve_zrng ]. }
    rewrite Z.add_0_r in Verr.
    (* next and misuse, outside errno *)
    assert (VnxF : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + NK_NEXT) 4 (nk_next (c_bs c))).
    { apply (val_mem_kept (w_H W) mem); [|exact Hnx].
      intros k Hk. cbn in Hk. unfold apart_gnl in Heg. apply UNk; unfold LA_G_NL, NK_NEXT, NK_SIZE in *; lia. }
    assert (VmiF : val_mem SEGS (rdW W (ms_mem msF)) (LA_G_NL + NK_MISUSE) 4 (rv_msu c)).
    { apply (val_mem_kept (w_H W) mem); [|exact Hmi].
      intros k Hk. cbn in Hk. unfold apart_gnl in Heg. apply UNk; unfold LA_G_NL, NK_MISUSE, NK_SIZE in *; lia. }
    (* every buffer byte defined: unchanged, or an errno byte *)
    assert (HbufF : forall i, 0 <= i < rv_len c -> aview SEGS (w_H W) (ms_mem msF) (rv_buf c + i) <> None).
    { intros i Hi. unfold amem_range in Hamr.
      assert (Hbr : 0 <= rv_buf c + i < 2 ^ 64) by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
      destruct (Z_lt_le_dec (rv_buf c + i) (as_errno B)) as [Hl|Hl].
      - rewrite UNk; [exact (Hbuf i Hi) | exact Hbr | lia].
      - destruct (Z_lt_le_dec (rv_buf c + i) (as_errno B + 4)) as [Hl2|Hl2].
        + pose proof (Verr (Z.to_nat (rv_buf c + i - as_errno B)) ltac:(lia)) as Hb.
          replace (as_errno B + Z.of_nat (Z.to_nat (rv_buf c + i - as_errno B))) with (rv_buf c + i) in Hb by lia.
          unfold aview. rewrite Hb. cbn [option_map]. discriminate.
        + rewrite UNk; [exact (Hbuf i Hi) | exact Hbr | lia]. }
    (* the registers the run left *)
    prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
    prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
    prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
    pmkst HS.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdF) _ => set (MDF := mdF) end.
    assert (Hfd3 : m_fds MDF = m_fds md2) by (unfold MDF; exact (proj1 (wvb_fds_fs _ _ _))).
    assert (Hfs3 : m_fs MDF = m_fs md2) by (unfold MDF; exact (proj2 (wvb_fds_fs _ _ _))).
    assert (HIF : rv_inv SK B c (ms_regs msF) (ms_mem msF) MDF).
    { apply (rv_inv_step SK B TL c HC regs2 mem md2 (ms_regs msF) (ms_mem msF) MDF
               (fun a => as_errno B <= a < as_errno B + 4) HI2 HJ2 Hfd3 Hfs3 UNk).
      - intros a Ha. right. unfold rv_ewr. right. right. right. exact Ha.
      - intros a Ha. exact (apresent_grows _ _ _ _ HG Ha).
      - exact (eq_trans Q2 E2).
      - exact (eq_trans Q3 E3).
      - exact (eq_trans Q4 E4).
      - exact (eq_trans Q26 E26).
      - exact (eq_trans Q27 E27). }
    assert (HR19 : getr (ms_regs msF) 19 = w64 SHADOW_OFF) by exact (eq_trans Q19 E19').
    assert (HPost : forall regs2', getr regs2' 10 = getr (ms_regs msF) 18 ->
              fuzz_recv_apost SEGS B (c_regs0 c) (rdW W memc) regs2' (rdW W (ms_mem msF))).
    { intros r2 Hr2. apply (RVFPOST (ms_regs msF) (ms_mem msF) MDF r2 HIF Hnc VnxF VmiF Verr HbufF).
      rewrite Hr2, Q18. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
    pose proof (RVRET (ms_regs msF) (ms_mem msF) MDF HIF HR19 HPost) as FIN.
    unfold rv_goal in FIN. exact FIN.
Qed.
End w.

