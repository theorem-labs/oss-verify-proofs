(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 307 of its 339 lines of code are new or changed and 37 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntClsCuts YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame CtrlParsed.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require GateModel slot_classify.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma cl8_nth_error_ext : forall (A : Type) (l1 l2 : list A),
  (forall n, nth_error l1 n = nth_error l2 n) -> l1 = l2.
Proof.
  induction l1 as [|a1 l1 IH]; intros l2 H.
  - destruct l2 as [|a2 l2]; [reflexivity|]. specialize (H 0%nat). discriminate.
  - destruct l2 as [|a2 l2]. { specialize (H 0%nat). discriminate. }
    specialize (H 0%nat) as H0. cbn in H0. injection H0 as ->. f_equal. apply IH. intros n. exact (H (S n)).
Qed.

Lemma cl8_fld_nth_error : forall (G : list byte) a q, (q < 6)%nat ->
  nth_error (fld G a 6) q = nth_error G (a + q).
Proof.
  intros G a q Hq. unfold fld. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec q 6) as [_|H6]; [apply nth_error_skipn | lia].
Qed.

Lemma cl8_aview_of_garr8 : forall (H0 : word -> bool) (m : word -> option byte) p (L : list byte) k,
  garr8 SEGS (mrestrict H0 m) p (map (fun b : byte => bv_unsigned b) L) -> (k < length L)%nat ->
  aview SEGS H0 m (p + Z.of_nat k) = Some (bv_unsigned (nth k L (Z_to_bv 8 0))).
Proof.
  intros H0 m p L k HG Hk. unfold aview.
  rewrite (garr8_mbyte SEGS (mrestrict H0 m) p (map (fun b : byte => bv_unsigned b) L) k HG
    ltac:(rewrite length_map; exact Hk)).
  cbn [option_map]. f_equal.
  assert (Hmn : nth k (map (fun b : byte => bv_unsigned b) L) 0 = bv_unsigned (nth k L (Z_to_bv 8 0)))
    by exact (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0) k).
  rewrite Hmn, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma cl8_aview_eq_nth : forall (H0 : word -> bool) (m : word -> option byte) p (L : list byte) q (G : list byte) k i,
  garr8 SEGS (mrestrict H0 m) p (map (fun b : byte => bv_unsigned b) L) ->
  garr8 SEGS (mrestrict H0 m) q (map (fun b : byte => bv_unsigned b) G) ->
  (k < length L)%nat -> (i < length G)%nat ->
  (aview SEGS H0 m (p + Z.of_nat k) = aview SEGS H0 m (q + Z.of_nat i) <-> nth_error L k = nth_error G i).
Proof.
  intros H0 m p L q G k i HL HG Hk Hi.
  rewrite (cl8_aview_of_garr8 H0 m p L k HL Hk), (cl8_aview_of_garr8 H0 m q G i HG Hi).
  rewrite (nth_error_nth' L (Z_to_bv 8 0) Hk), (nth_error_nth' G (Z_to_bv 8 0) Hi).
  split; intros E; injection E as E; [f_equal; apply bv_eq; exact E | rewrite E; reflexivity].
Qed.

Lemma cl8_gate_ne : forall (H0 : word -> bool) (m : word -> option byte) p (G : list byte) k j,
  garr8 SEGS (mrestrict H0 m) p (map (fun b : byte => bv_unsigned b) G) ->
  gate_ok G -> 0 <= k < j -> j < gn G ->
  (forall i, 0 <= i < 6 -> aview SEGS H0 m (p + 32 * k + i) = aview SEGS H0 m (p + 32 * j + i)) ->
  False.
Proof.
  intros H0 m p G k j HG GOK Hkj Hj Hall.
  destruct GOK as (LG & HN & HD).
  pose proof (HD (Z.to_nat k) (Z.to_nat j) ltac:(lia) ltac:(lia)) as Hne.
  unfold bytes_eqb in Hne.
  destruct (list_eq_dec Z.eq_dec _ _) as [Heq|Hd]; [discriminate Hne | clear Hne].
  apply Hd. f_equal. apply cl8_nth_error_ext. intros q.
  destruct (Nat.ltb_spec q 6) as [Hq|Hq].
  - unfold gmac. rewrite (cl8_fld_nth_error G (32 * Z.to_nat k) q Hq), (cl8_fld_nth_error G (32 * Z.to_nat j) q Hq).
    apply (proj1 (cl8_aview_eq_nth H0 m p G p G (32 * Z.to_nat k + q) (32 * Z.to_nat j + q) HG HG ltac:(lia) ltac:(lia))).
    specialize (Hall (Z.of_nat q) ltac:(lia)).
    replace (p + Z.of_nat (32 * Z.to_nat k + q)) with (p + 32 * k + Z.of_nat q) by lia.
    replace (p + Z.of_nat (32 * Z.to_nat j + q)) with (p + 32 * j + Z.of_nat q) by lia.
    exact Hall.
  - unfold gmac.
    assert (E1 : nth_error (fld G (32 * Z.to_nat k) 6) q = None)
      by (apply nth_error_None; unfold fld; rewrite length_firstn, length_skipn; lia).
    assert (E2 : nth_error (fld G (32 * Z.to_nat j) 6) q = None)
      by (apply nth_error_None; unfold fld; rewrite length_firstn, length_skipn; lia).
    rewrite E1, E2. reflexivity.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let DSEAT := d_seat B MT XM_LIB RLO RHI tfib_K.
Let DFACTS := d_facts_ok B MT XM_LIB RLO RHI tfib_K.
Let DBRT := d_body_rt B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).

Theorem cl_L8 : cl_L8_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros cx h i n now op nb fr len nn k j W c HLJ.
  unfold cl_LJ, d_at in HLJ.
  destruct HLJ as (fq & ly3 & S3 & regs & mem3 & md3 & kj & acc & -> & Hfq0 & Hbase & HJ0 & Hfrs & Hk & Hnev & Hmo & Hacc & HP).
  destruct HP as (HLmem & Hjregs).
  destruct HLmem as (Sg & G & push & Hcl_base & Hcl_sg & Hcl_gate & Hgn & Hcl_spl).
  destruct Hcl_base as (Hi' & Hn' & Hnow' & Hop4 & Hop256 & HrL & Hsp0 & Hfrm & Hv248 & Hv408 & Hv392 & Hlennb & Hnbmax & Hnbcn & Hbody).
  destruct Hjregs as (Hkj0 & Hjn & Hr23 & Hr24 & Hr21 & Hr26 & Hr19 & Hr22 & Hr27).
  pose proof Hcl_gate as (LG & HGgate3 & GOK).
  pose proof GOK as (_ & HgnB & _).
  assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 kj)
    by (split; [exact Hbase | split; [exact HJ0 | exact Hfrs]]).
  destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 kj HctxD)
    as (Hmod16 & Hlo & Hhi47 & HFB1 & HFB2 & HFBia & HFBoff & HFBmod & HFBpres & HSHpres & HJpres & HARm & Hfinm & Efa & Efl).
  pose proof asan_consts as (AClo & ACsh & ACshb & AChm & AClm).
  destruct (d_A_range cx ltac:(unfold MFRAME, LLVMF_STK in *; lia)) as (HAr1 & HAr2m).
  assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold MFRAME, LLVMF_STK in *; lia).
  assert (G_ac : alloc_ceiling + 32768 <= d_S cx) by (unfold LLVMF_STK in Hlo; lia).
  assert (G_A1 : d_S cx - 607 <= d_A cx) by (unfold MFRAME in HAr1; lia).
  assert (G_A2 : d_A cx <= d_S cx - 576) by (unfold MFRAME in HAr1; lia).
  pose proof Hfrm as Hfrm_keep.
  pose proof Hsp0 as Hsp0_keep.
  pose proof HrL as (Hsprl & Hgprl & Htprl & H8rl & H9rl & H18rl & H20rl & H25rl).
  pose proof Hbody as (T0 & G0 & Lk0 & H0' & Hframe & Hshadow & Hobjs & Hblocks & Hinput & Himg & Hoffb & Hgeob & _ & Hstkb & Hawrb).
  pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
  assert (HEI : img_env VAL A_LIM (d_env cx E (cl_vals regs []))).
  { destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (cl_vals regs [])) (rd W mem3)) by constructor.
  pose proof (DSEAT LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 kj E 0xda0 cl_sr (cl_vals regs []) [] [] [] (d_facts [] [])
    HctxD HdE Hregs Hflag (cl_regs_ok B cx E regs [] HdE HrL HAr2)
    (DFACTS LAWS cx ly3 S3 W mem3 md3 kj E (cl_vals regs []) [] [] HctxD HdE I I)
    (Forall_nil _) (Forall_nil _) (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
  unfold ss_d in HS.
  cl_ro_base HS 516%nat. cl_ro_base HS 529%nat. cl_ro_base HS 60%nat.
  pose (RUN := paj_run (fx := fq) B LAWS).
  unfold cfg_at. change (w64 (BASE + 0xda0)) with (Z_to_bv 64 (BASE + 0xda0)).
  paj_run_tok RUN HS HJ0 SHOK cl_span.
  { cbn [ss_mem]. repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  assert (Hpt := cl_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity)).
  clear HF HFr HG.
  assert (Emem : ms_mem ms = mem3) by (apply functional_extensionality; exact Hpt).
  rewrite Emem in HJ0.
  assert (RGp : forall r : Z, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] ->
      getr (ms_regs ms) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms (Z_to_bv 5 r) HS),
      (cl_regs_ok B cx E regs [] HdE HrL HAr2 (Z_to_bv 5 r)).
    cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]). destruct Hr. }
  assert (Q10 : getr (ms_regs ms) 10 = w64 (d_obj cx OG + 32 * k)).
  { transitivity (getr regs 19).
    - rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 10%bv HS), (cl_regs_ok B cx E regs [] HdE HrL HAr2 19%bv).
      f_equal; vm_compute; reflexivity.
    - exact Hr19. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (d_obj cx OG + 32 * j)).
  { transitivity (getr regs 22).
    - rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 11%bv HS), (cl_regs_ok B cx E regs [] HdE HrL HAr2 22%bv).
      f_equal; vm_compute; reflexivity.
    - exact Hr22. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 6).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 12%bv HS).
    match goal with |- context [sr_get ?s ?r] => let v := eval vm_compute in (sr_get s r) in change (sr_get s r) with v end.
    vm_compute. reflexivity. }
  assert (Q1 : getr (ms_regs ms) 1 = w64 (BASE + 0xdb0)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W) _ _ ms 1%bv HS).
    match goal with |- context [sr_get ?s ?r] => let v := eval vm_compute in (sr_get s r) in change (sr_get s r) with v end.
    exact (codeptr_val (d_env cx E (cl_vals regs [])) 0xdb0 HEI). }
  assert (Hsp2 : getr (ms_regs ms) 2 = getr regs 2) by exact (RGp 2 ltac:(cbv [In]; tauto)).
  pmkst HS.
  rewrite Emem.
  eapply SRr_bind.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq)
      W (ms_regs ms) mem3 LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ kj
      (d_obj cx OG + 32 * k) (d_obj cx OG + 32 * j) 6 (d_A cx - d_S cx)
      (Z_to_bv 64 (BASE + 0xdb0)) HJ0 Q10 Q11 Q12).
    - lia.
    - unfold d_obj, dobj_off. lia.
    - unfold d_obj, dobj_off. lia.
    - unfold d_obj, dobj_off. lia.
    - unfold d_obj, dobj_off. lia.
    - unfold spZ. rewrite Hsp2. unfold spZ in Hsprl. lia.
    - pose proof (Z.div_mod (d_A cx) 32 ltac:(lia)) as DAm. pose proof (Z.div_mod (d_S cx) 16 ltac:(lia)) as DSm. lia.
    - unfold MFRAME in *. lia.
    - unfold ESTACK, LLVMF_STK, MFRAME in *. lia.
    - etransitivity; [exact (RGp 3 ltac:(cbv [In]; tauto))|exact Hgprl].
    - etransitivity; [exact (RGp 4 ltac:(cbv [In]; tauto))|exact Htprl].
    - exact Q1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + apply (aview_some_of_apresent SEGS (w_H W) mem3 a). apply HFBpres. unfold d_obj, dobj_off in Ha. lia.
      + unfold spZ. rewrite Hsp2. unfold spZ in Hsprl. unfold ESTACK, d_obj, dobj_off in *. lia.
    - intros a Ha. split.
      + apply (aview_some_of_apresent SEGS (w_H W) mem3 a). apply HFBpres. unfold d_obj, dobj_off in Ha. lia.
      + unfold spZ. rewrite Hsp2. unfold spZ in Hsprl. unfold ESTACK, d_obj, dobj_off in *. lia.
    - intros a Ha. unfold ESTACK, d_obj, dobj_off in *. lia.
    - intros a Ha. unfold ESTACK, d_obj, dobj_off in *. lia.
    - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBia | exact HFB2 | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia].
    - apply (amem_range_sub_app (d_FB cx) 4096); [exact HFBia | exact HFB2 | unfold d_obj, dobj_off; lia | unfold d_obj, dobj_off; lia | lia].
    - eapply range_addressable_sub;
        [ exact (cl_obj_ra cx W mem3 OG Hshadow ltac:(pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia) ltac:(lia) ltac:(vm_compute; reflexivity))
        | unfold d_obj, dobj_off; cbn [dobj_size]; lia | unfold d_obj, dobj_off; cbn [dobj_size]; lia ].
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx) (d_obj cx OG + 32 * k) 6 HARm Hfinm);
        [ rewrite Efa; unfold d_obj, dobj_off; lia | rewrite Efa, fs6; unfold d_obj, dobj_off; lia | lia ].
    - eapply range_addressable_sub;
        [ exact (cl_obj_ra cx W mem3 OG Hshadow ltac:(pose proof (Z.div_mod (d_FB cx) 32 ltac:(lia)); lia) ltac:(lia) ltac:(vm_compute; reflexivity))
        | unfold d_obj, dobj_off; cbn [dobj_size]; lia | unfold d_obj, dobj_off; cbn [dobj_size]; lia ].
    - intros _. apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W mem3 md3 DFRAME_CLASS (c_fpos cx) (d_obj cx OG + 32 * j) 6 HARm Hfinm);
        [ rewrite Efa; unfold d_obj, dobj_off; lia | rewrite Efa, fs6; unfold d_obj, dobj_off; lia | lia ]. }
  cbv beta.
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HPr & Hres & Hcmp & Hfr & Hpres2).
  assert (Keq : forall a, 0 <= a < 2 ^ 64 -> (a < d_A cx - 2 * ESTACK \/ d_A cx <= a) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
  { intros a Ha Hr. apply Hfr; [lia | intro Hbad; unfold ESTACK in *; lia]. }
  assert (Hac_lt : alloc_ceiling < d_A cx - 2 * ESTACK) by (unfold ESTACK, LLVMF_STK, MFRAME in *; lia).
  assert (RR : forall r : Z, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27] ->
      getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr.
    assert (Hcs : acallee_saved r).
    { cbv [In] in Hr. unfold acallee_saved. repeat (destruct Hr as [Hr|Hr]; [subst r; lia|]). destruct Hr. }
    rewrite (HPr r Hcs). apply RGp. exact Hr. }
  assert (Hrl2 : d_rL B cx regs2).
  { unfold d_rL. split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
    - unfold spZ. assert (R2 : getr regs2 2 = getr regs 2) by exact (RR 2 ltac:(cbv [In]; tauto)).
      rewrite R2. unfold spZ in Hsprl. exact Hsprl.
    - assert (R3 : getr regs2 3 = getr regs 3) by exact (RR 3 ltac:(cbv [In]; tauto)). rewrite R3. exact Hgprl.
    - assert (R4 : getr regs2 4 = getr regs 4) by exact (RR 4 ltac:(cbv [In]; tauto)). rewrite R4. exact Htprl.
    - assert (R8 : getr regs2 8 = getr regs 8) by exact (RR 8 ltac:(cbv [In]; tauto)). rewrite R8. exact H8rl.
    - assert (R9 : getr regs2 9 = getr regs 9) by exact (RR 9 ltac:(cbv [In]; tauto)). rewrite R9. exact H9rl.
    - assert (R18 : getr regs2 18 = getr regs 18) by exact (RR 18 ltac:(cbv [In]; tauto)). rewrite R18. exact H18rl.
    - assert (R20 : getr regs2 20 = getr regs 20) by exact (RR 20 ltac:(cbv [In]; tauto)). rewrite R20. exact H20rl.
    - assert (R25 : getr regs2 25 = getr regs 25) by exact (RR 25 ltac:(cbv [In]; tauto)). rewrite R25. exact H25rl. }
  assert (HC2 : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem2 md2 kj)
    by (split; [exact Hbase | split; [exact HJ2 | exact Hfrs]]).
  assert (Hshadow2 : d_shadow cx dsh_rec W mem2).
  { apply (cl_shadow_keep cx dsh_rec W W mem3 mem2 Hshadow). intros a Ha.
    pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSB.
    unfold kLowMemEnd, kHighShadowEnd in HSB. apply Keq; [unfold DFRAME_SH in *; lia | left; unfold DFRAME_SH in *; lia]. }
  assert (Hframe2 : d_frame cx h dsh_rec W mem2).
  { apply (cl_frame_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h dsh_rec W mem3 ly3 S3 W mem2 md2 kj HC2 Hframe).
    intros a Ha.
    pose proof (shadow_addr_bounds (d_FB cx) ltac:(unfold kHighMemEnd in *; lia)) as HSB.
    unfold kLowMemEnd, kHighShadowEnd in HSB.
    apply Keq.
    - destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]]; unfold MFRAME, LLVMF_STK in *; lia.
    - destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]];
        [ right | right | left | left | left ]; unfold MFRAME, LLVMF_STK in *; lia. }
  assert (Hbody2 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem2).
  { apply (DBRT cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 mem2
      (d_A cx - 2 * ESTACK) (d_A cx) (fun a => d_A cx - 2 * ESTACK <= a < d_A cx) Hbody).
    - unfold ESTACK, LLVMF_STK, MFRAME in *. lia.
    - lia.
    - intros a Ha. left. exact Ha.
    - intros a Ha Hna. apply Hfr; [exact Ha | intro Hbad; apply Hna; unfold ESTACK in *; lia].
    - intros a _ Hp. apply Hpres2. exact Hp.
    - exact Hframe2.
    - exact Hshadow2.
    - lia. }
  apply SRr_ret. unfold cl_BR, d_at.
  exists fq, ly3, S3, regs2, mem2, md2, kj, acc.
  split; [reflexivity|]. split; [exact Hfq0|].
  split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs|].
  split; [exact Hk|]. split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
  split; [| split].
  - exists Sg, G, push.
    split; [| split; [| split; [| split]]].
    + refine (conj Hi' (conj Hn' (conj Hnow' (conj Hop4 (conj Hop256 (conj Hrl2
        (conj _ (conj _ (conj _ (conj _ (conj _ (conj Hlennb (conj Hnbmax (conj Hnbcn Hbody2)))))))))))))).
      * destruct Hsp0_keep as (Ha232 & Ha344). split.
        -- eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Ha232].
           intros xq Hxq. apply Keq; [lia | right; lia].
        -- eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Ha344].
           intros xq Hxq. apply Keq; [lia | right; lia].
      * destruct Hfrm_keep as (Hlen0 & Hfr0 & Hnbc0 & Hfrg). split; [exact Hlen0|]. split; [exact Hfr0|]. split; [exact Hnbc0|].
        destruct (Z.eq_dec fr 0) as [E0|Hne].
        -- subst fr. rewrite (Hfr0 eq_refl). intros q Hq. rewrite length_map, length_firstn in Hq. lia.
        -- assert (Hin : In (fr, len) (ablocks B ly3 S3)).
           { pose proof Hblocks as (HPerm & _). eapply Permutation_in; [apply Permutation_sym; exact HPerm|].
             unfold dxb. replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hne). left; reflexivity. }
           destruct (al_blocks SEGS B LAWS ly3 S3 W mem3 md3 fr len HARm Hin) as (_ & Hfr4096 & Hfrceil & _).
           pose proof (req_size_pos len ltac:(lia)) as (_ & Hreqlen).
           eapply (YC88.garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hfrg].
           intros a Ha. rewrite length_map in Ha.
           assert (Hle : Z.of_nat (length (firstn (Z.to_nat len) (rest_of (c_pl cx) nb))) <= len)
             by (rewrite length_firstn; lia).
           apply Keq; lia.
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hv248].
        intros xq Hxq. apply Keq; [lia | right; lia].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hv408].
        intros xq Hxq. apply Keq; [lia | right; lia].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hv392].
        intros xq Hxq. apply Keq; [lia | right; lia].
    + destruct Hcl_sg as (HSglen & HSgg & HSgf). split; [exact HSglen|]. split; [| exact HSgf].
      eapply (YC88.garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2); [| exact HSgg].
      intros a Ha. rewrite length_map in Ha. apply Keq; [unfold d_obj, dobj_off in *; lia | left; unfold d_obj, dobj_off in *; lia].
    + split; [exact LG|]. split; [| exact GOK].
      eapply (YC88.garr8_aview_kept SEGS (w_H W) (w_H W) mem3 mem2 (d_obj cx OG) (map (fun b : byte => bv_unsigned b) G)); [| exact HGgate3].
      intros a Ha. rewrite length_map, LG in Ha. apply Keq; [unfold d_obj, dobj_off in *; lia | left; unfold d_obj, dobj_off in *; lia].
    + exact Hgn.
    + destruct Hcl_spl as (Hp224 & Hpush01 & Hp280 & Hp336 & Hp368).
      split; [| split; [exact Hpush01 | split; [| split]]].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hp224].
        intros xq Hxq. apply Keq; [lia | right; lia].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hp280].
        intros xq Hxq. apply Keq; [lia | right; lia].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hp336].
        intros xq Hxq. apply Keq; [lia | right; lia].
      * eapply (YC88.val_mem_aview_kept_x SEGS (w_H W) (w_H W) mem3 mem2); [| exact Hp368].
        intros xq Hxq. apply Keq; [lia | right; lia].
  - unfold cl_jregs.
    split; [lia|]. split; [lia|].
    split; [exact (cl_cs (ms_regs ms) regs2 23 (w64 (k + 1)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 23 ltac:(cbv [In]; tauto)) Hr23))|].
    split; [exact (cl_cs (ms_regs ms) regs2 24 (w64 nn) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 24 ltac:(cbv [In]; tauto)) Hr24))|].
    split; [exact (cl_cs (ms_regs ms) regs2 21 (w64 (d_obj cx OG + 32 + 32 * k)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 21 ltac:(cbv [In]; tauto)) Hr21))|].
    split; [exact (cl_cs (ms_regs ms) regs2 26 (w64 (nn - 1 - k)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 26 ltac:(cbv [In]; tauto)) Hr26))|].
    split; [exact (cl_cs (ms_regs ms) regs2 19 (w64 (d_obj cx OG + 32 * k)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 19 ltac:(cbv [In]; tauto)) Hr19))|].
    split; [exact (cl_cs (ms_regs ms) regs2 22 (w64 (d_obj cx OG + 32 * j)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 22 ltac:(cbv [In]; tauto)) Hr22))|].
    exact (cl_cs (ms_regs ms) regs2 27 (w64 (nn - j)) HPr ltac:(unfold acallee_saved; lia) (eq_trans (RGp 27 ltac:(cbv [In]; tauto)) Hr27)).
  - intro Hz.
    assert (Hv0 : v = w64 0) by (rewrite <- Hres; exact Hz).
    pose proof (proj1 Hcmp Hv0) as Hforall.
    apply (cl8_gate_ne (w_H W) mem3 (d_obj cx OG) G k j HGgate3 GOK ltac:(lia) ltac:(lia)).
    intros ii Hii. specialize (Hforall ii Hii). exact Hforall.
Qed.

End h.
End f.
End d.
