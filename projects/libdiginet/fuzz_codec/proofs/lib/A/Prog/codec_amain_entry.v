(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACez.v:26-243 (the harness entry
   segment, tfib_lib_A_seg) at c8557374ad2e for fuzz_knock's ASan image (fuzz_knock.asan, sha256
   61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118), and the S0/S1 boundary state from the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACf7.v:27-28 (ss_A2). rule 24: no function proved (a port of the released
   cgif_file_fuzzer harness walk structure). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain0.v, with its module paths changed; 308 of its 337 lines of code are new or changed and 277 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/diginet_counter_text_A_s0.v, with its module names changed; 360 of its 414 lines of code are new or changed and 283 lines of the source are left out. *)
(* Segment ENTRY of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan 0x8084c-0x80ab8), part b and the
   segment lemma seg_entry_holds.
   From the request's return (codec_amain_entry_a.v ae_r1, 0x808c0) to the loop head 0x80abc:
   - the state at 0x808c0: atoms 33 = the flag address FL, 34 = shadow_addr F; s4 pinned to the shadow offset (atom
     32); the frame (atom 10 = a0 = F, flag address at F + 504), its 64 shadow bytes (zero after the request) and the
     spill window 16(s1) .. 167(s1); the alias of (F >> 3) + s4 to atom 34 and of n >> 26 to 0 (n < 2 ^ 26);
   - 0x808c0 .. 0x80a3c: one run: `bnez s6` at 0x808d0 is taken (F >= 4096; the machine-stack fallback 0x808d4 ..
     0x808ec is not reached), 144(s1) = F, the frame's description words, the 56 shadow stores (shm 0xf8), `beqz a1`
     at 0x80a18 is taken (n >> 26 = 0), the spills 72 / 32 / 64(s1), s3 = F + 64, s6 = F + 176, s11 = F + 432;
   - 0x80a3c: check_personality through its contract cdc_check_pers_specX (CPgWalkCall.cpw_call), its cimg_rd from
     the start-up facts (CPgSat.sat_img_rd, CPgWalkRo's row freedom, the read-only image kept along the journal), the
     state re-seated at 0x80a40 with the three regions kept (region_kept_tcj_frame / _stack);
   - 0x80a40 .. 0x80ab8: one run: s10 = 0, in.p / in.n at 152 / 160(s1), s9 = F + 64, s3 = F + 432, the spills
     16 .. 120(s1), s11 = 10;
   - at 0x80abc: mcommon read off the final state's regions and registers (the saves kept by the runs and the call,
     the input bytes by the journal), the cut inv_head g pos sp1 0 with the cursor at c = 0. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YO09 YE00 YE01 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgMainC CPgChkC CodecRo CodecGlobs.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalk CPgWalkKept CPgWalkFrame CPgWalkImg CPgWalkRo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkCall CPgSat.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_inv codec_amain_lem codec_amain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_entry_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* n >> 26 of an input length below 2 ^ 26 *)
Lemma ae_srl26 : forall E (m : nat) n, ew E m = Z_to_bv 64 n -> 0 <= n < 2 ^ 26 ->
  sv_denot E (SAlu ALU_SRL (SOff m 0) (SLit 26)) = sv_denot E (SLit 0).
Proof.
intros E m n Hn Hr. rewrite (denot_lit_U E (SAlu _ _ _)), (denot_lit_U E (SLit 0)). f_equal.
rewrite U_SAlu, !U_SLit, U_SOff, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
rewrite Z.add_0_r, (zcanon_id n) by (unfold M64; lia). change (Z.land (zcanon 26) 63) with 26.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia. reflexivity.
Qed.

(* the state at 0x808c0 *)
Definition ae_rs2 : smem :=
  [cw_frame_region 10 33 3; cw_fshadow_region 34 3; YP09.mkRegion (Some 9%nat) 16 168 16 168 []].
Definition ae_G2 : facts :=
  mkFacts [(10%nat, HPTR 6); (33%nat, HPTR 0); (34%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0);
           (24%nat, mkAF 0 (2 ^ 26 - 1) 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0);
     (SAlu ALU_SRL (SOff 24 0) (SLit 26), SLit 0)].

(* the write windows of the walk's states: the frame (atom 10), its shadow (atom 34), the spill window (atom 9) *)
Ltac ae_awr :=
  lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 3 _ 10%nat);
      [reflexivity | eassumption | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 3) with 512; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 3 _ 34%nat);
      [reflexivity | eassumption | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 3 / 8) with 64; lia |]
  | lazymatch goal with U9 : bv_unsigned (ew _ 9) = ?s1 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
      eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (s1 - s0));
      [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] end ].
Ltac ae_kwr :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hb end;
     repeat match goal with H : frame_addr _ _ _ = _ |- _ => rewrite H in Hb end;
     lia | ]);
  destruct Hr.

(* the 33 string rows: in a read-only segment, inside the image's read range, below the read window's end *)
Lemma ae_rows_ok : forallb (fun r => am_ro_b (fst r) (snd r) && (0 <? snd r) && (IMG_LO + 64 <=? fst r) &&
  (fst r + snd r + 64 <=? IMG_HI) && (fst r + snd r <=? CA_RHI)) CA_ROSTRS = true.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : ACeh.ro_tfa_below_ofl}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
(* the saves keep their values when their bytes do *)
Lemma ae_saves_kept : forall g (W W' : world tfibsegs) m m',
  (forall a, e_sp0 g - 104 <= a < e_sp0 g -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  ae_saves g W m -> ae_saves g W' m'.
Proof.
intros g W W' m m' HK (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13).
assert (KV : forall o v, 8 <= o <= 104 -> val_mem tfibsegs (mrestrict (w_H W) m) (e_sp0 g - o) 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') (e_sp0 g - o) 8 v).
{ intros o v Ho Hv. apply (cw_val_mem_kept (w_H W) (w_H W') m m'); [|exact Hv].
  intros x Hx. cbn [Z.of_nat Pos.of_succ_nat] in Hx. apply HK. lia. }
split; [exact (KV 8 _ ltac:(lia) S1)|]. split; [exact (KV 16 _ ltac:(lia) S2)|].
split; [exact (KV 24 _ ltac:(lia) S3)|]. split; [exact (KV 32 _ ltac:(lia) S4)|].
split; [exact (KV 40 _ ltac:(lia) S5)|]. split; [exact (KV 48 _ ltac:(lia) S6)|].
split; [exact (KV 56 _ ltac:(lia) S7)|]. split; [exact (KV 64 _ ltac:(lia) S8)|].
split; [exact (KV 72 _ ltac:(lia) S9)|]. split; [exact (KV 80 _ ltac:(lia) S10)|].
split; [exact (KV 88 _ ltac:(lia) S11)|]. split; [exact (KV 96 _ ltac:(lia) S12)|].
exact (KV 104 _ ltac:(lia) S13).
Qed.
Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis GM : globs_marked tfibsegs B CODEC_GLOBS.
Hypothesis IV : img_shadow_vis tfibsegs B.
Hypothesis RF : cpw_rows_free B CA_ROSTRS.
Hypothesis CPERS : cdc_check_pers_specX tfibsegs B MT CA_RLO CA_RHI CA_PERS CA_ROSTRS AM_check_pers.
Hypothesis ASM3 : astack_malloc_realizes tfibsegs B 3.
Hypothesis SMP : stack_malloc_progressP B.

(* check_personality's image ranges: the personalities and the 33 string rows *)
Lemma ae_cimg : forall (W : world tfibsegs) memc sp T,
  arodata_ok B (aview tfibsegs (w_H W) memc) -> CA_RHI <= sp - T ->
  cimg_rd tfibsegs B CA_RLO CA_RHI W memc sp T ((CA_PERS, 48) :: CA_ROSTRS).
Proof.
intros W memc sp T HR Hwin.
split; [intros a Ha; exact (HR a Ha)|].
apply Forall_cons.
- cbn [fst snd]. split.
  + intros i Hi. right. unfold CA_PERS, CA_RLO, CA_RHI. lia.
  + apply (sat_img_rd tfibsegs B CODEC_GLOBS sp T CA_PERS 48 GM cg_PERS IV);
    [ lia | unfold CA_PERS; lia | cbv [IMG_LO CA_PERS]; lia | cbv [IMG_HI IMG_TOP CA_PERS]; lia
    | unfold CA_PERS; lia | | | ].
    * intros x Hx. split; [|exact (tl_lib_consts B TL x ltac:(unfold lib_const_addr; unfold CA_PERS in Hx; lia))].
      unfold in_img. eexists. split; [right; right; left; reflexivity|].
      match goal with |- Z.le ?lo x /\ Z.lt x (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
        change lo with l; change sz with h end.
      unfold CA_PERS in Hx. lia.
    * left. unfold CA_PERS, kLowMemEnd. lia.
    * unfold CA_PERS, CA_RHI in *. lia.
- apply Forall_forall. intros [q sz] Hin.
  pose proof (proj1 (forallb_forall _ _) ae_rows_ok (q, sz) Hin) as Hb. cbv beta in Hb. cbn [fst snd] in Hb |- *.
  apply andb_prop in Hb as [Hb H5]. apply andb_prop in Hb as [Hb H4]. apply andb_prop in Hb as [Hb H3].
  apply andb_prop in Hb as [Hro H2].
  apply Z.ltb_lt in H2. apply Z.leb_le in H3. apply Z.leb_le in H4. apply Z.leb_le in H5.
  cbv [IMG_LO IMG_HI IMG_TOP CA_RHI] in H3, H4, H5, Hwin.
  assert (Hgl : In (q, sz) CODEC_GLOBS) by exact (proj1 (Forall_forall _ _) CA_ROSTRS_globs (q, sz) Hin).
  split.
  + intros i Hi. apply (am_in_ro q sz Hro). lia.
  + apply (sat_img_rd tfibsegs B CODEC_GLOBS sp T q sz GM Hgl IV);
    [ lia | lia | cbv [IMG_LO]; lia | cbv [IMG_HI IMG_TOP]; lia | lia | | | lia ].
    * intros x Hx. split.
      -- pose proof Hro as Hro'. unfold am_ro_b in Hro'. apply existsb_exists in Hro' as (s & Hs & Hc).
         apply andb_prop in Hc as (Hc & Hhi). apply andb_prop in Hc as (_ & Hlo).
         apply Z.leb_le in Hlo. apply Z.leb_le in Hhi.
         unfold in_img. exists s. split; [exact Hs | lia].
      -- destruct (cpw_rows_free_In B CA_ROSTRS q sz (x - q) RF Hin ltac:(lia)) as (Ho & He).
         replace (q + (x - q)) with x in Ho, He by lia. exact (conj Ho He).
    * left. unfold kLowMemEnd. lia.
Qed.

Lemma ae_p2 : forall g W2 c2, e_pre B MT K XM_LIB g -> ae_r1 B g W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => exists pos sp1, inv_head B MT K XM_LIB g pos sp1 0 W3 c3).
Proof.
intros g W2 c2 Hpre Hr1.
destruct Hr1 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ & Hfrs2 & HSf & Hbb2 & Hz & Hflag & R10 & R2 & R9 & R8
  & R3 & R4 & R20 & R24 & R25 & HSV).
unfold ae_sp1 in R2, R9.
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (HFN & _ & Ha0 & Ha1 & Hpn & Hnpl & HPL & Hfr0 & Hev & Hlive & _).
pose proof HFN as (HAR0 & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
change (spZ (e_regs g)) with (e_sp0 g) in Hal16, Hslo, Hshi.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : LLVMF_STK = 32768) by reflexivity.
assert (Hin : In (3, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 3 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 3 pos HAR2 Hin) as (HF64 & _ & _).
destruct (FFL _ _ _ _ _ 3 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 3) with 512 in HFceil, HFapp, Hz.
unfold FA in *.
set (F := frame_addr (e_ly g) 3 pos) in *.
set (FL := flag_addr (e_ly g) 3 pos) in *.
set (sp1 := 32 * ((e_sp0 g - 288) / 32)) in *.
destruct (sp1_facts (e_sp0 g - 288) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : e_sp0 g - 304 <= sp1 <= e_sp0 g - 288) by lia. clear Hsp1r.
assert (Hn26 : 0 <= e_n g < 2 ^ 26) by (destruct Hpn as [[-> _] | [Hn _]]; lia).
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8 : F / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
(* the start state *)
set (E := Ereg regs2 (cw_extra [FL; shadow_addr F])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (subst E; exact (cw_ew_x regs2 [FL; shadow_addr F] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (shadow_addr F)) by (subst E; exact (cw_ew_x regs2 [FL; shadow_addr F] 1)).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 (e_n g)) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = shadow_addr F)
  by (rewrite E34; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok tfibsegs E (mkSS 0x808c0 (sr_set sr_atoms 20%bv (SOff 32 0)) ae_rs2 None ae_G2)
  (restrict (w_H (e_W g)) (mkst regs2 (Z_to_bv 64 0x808c0) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [FL; shadow_addr F])) with E.
  - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite R20. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold ae_rs2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (cw_frame_region_ok B LAWS FFL _ 10 33 (e_ly g) S2 (e_W g) mem2 md2 3 pos HAR2 Hin E10 E33).
      change (fs_frame_bytes 3) with 512. fold F FL. replace (F + 512 - 8) with (F + 504) by lia. exact Hflag.
    + apply (cw_fshadow_region_ok B LAWS _ 34 (e_ly g) S2 (e_W g) mem2 md2 3 pos HAR2 Hin E34).
      change (fs_frame_bytes 3) with 512. exact Hz.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply HJpres. lia.
  - apply pairwise_disjoint_of_extents. unfold ae_rs2, cw_frame_region, cw_fshadow_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 3) with 512. change (512 / 8) with 64.
    rewrite U10, U34, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *. repeat split; lia.
  - split; [|split; [exact I|]].
    + destruct (cw_frame_afacts B LAWS E 10 33 34 (e_ly g) S2 (e_W g) mem2 md2 3 pos FFL HAR2 Hin E10 E33 E34)
        as (A10 & A33 & A34).
      unfold ae_G2. cbn [f_atoms atoms_ok]. split; [exact A10|]. split; [exact A33|]. split; [exact A34|].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, E32, E24, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
    + unfold ae_G2. cbn [f_alias alias_ok]. split; [|split; [|exact I]].
      * exact (shadow_decl_ok E 10%nat 32%nat 34%nat F SB E10 ltac:(lia) E32 E34).
      * exact (ae_srl26 E 24 (e_n g) E24 Hn26). }
clearbody E.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((F <= a < F + 512) \/ (shadow_addr F <= a < shadow_addr F + 64) \/ (sp1 + 16 <= a < sp1 + 168)) ->
  aview tfibsegs (w_H (e_W g)) mem2 a = aview tfibsegs (w_H (e_W g)) mem2 a) by (intros; reflexivity).
(* 0x808c0 .. jal 0x83364 at 0x80a3c: one plain run (no instrumented check on the way) *)
aj_run_to tfibtbl_lib_ok HS HJ 0x83364; [ae_awr|].
cw_keep ae_kwr.
(* the saves at the call *)
assert (HSV1 : ae_saves g (e_W g) (ms_mem ms)).
{ apply (ae_saves_kept g (e_W g) (e_W g) mem2 (ms_mem ms)); [|exact HSV].
  intros a Ha. apply KE; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
  unfold shadow_addr, SHADOW_OFF. lia. }
clear KE.
(* 0x83364: check_personality through its contract *)
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
assert (Esp : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
assert (HRO : arodata_ok B (aview tfibsegs (w_H (e_W g)) (ms_mem ms)))
  by exact (arodata_ok_at B MT K XM_LIB g _ _ _ _ _ _ _ Hpre HJ).
pose proof sat_T_main_check_pers as HT. unfold T_main_need in HT.
assert (HTp : 0 <= T_check_pers) by (unfold T_check_pers; pose proof sat_T_from_name_strcmp; unfold ESTACK in *; lia).
eapply (cpw_call (e_W g) E _ ms _ _ _ HS eq_refl).
{ eapply CPERS.
  - eapply (cpw_entry B).
    + exact HJ.
    + rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
    + unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    + rewrite Q3, (EE 3%nat 3%bv eq_refl). exact R3.
    + rewrite Q4, (EE 4%nat 4%bv eq_refl). exact R4.
    + rewrite Esp. exact Hsp1al16.
    + rewrite Esp. lia.
    + rewrite Esp. lia.
    + unfold EV_CDC, EV_LIB in *. lia.
    + apply Permutation_refl.
    + rewrite Hbb2. unfold LIVE_CDC, LIVE_LIB in *. lia.
  - apply ae_cimg; [exact HRO | rewrite Esp; unfold CA_RHI; lia]. }
cbv beta. intros W3 c3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hfrs3 & HPerm3 & HIO3 & HMLE3 & KT3 & _).
rewrite Q1. rewrite Esp in KT3.
(* the saves after the call *)
assert (HSV3 : ae_saves g W3 mem3).
{ apply (ae_saves_kept g (e_W g) W3 (ms_mem ms) mem3); [|exact HSV1].
  intros a Ha. pose proof KT3 as (K1 & _). apply K1; [lia | lia | intros Hx; exact Hx]. }
(* the frame after the call *)
pose proof HJ3 as (HAR3 & Hly3 & _).
assert (Hin3 : In (3, pos) (frames S3)) by (rewrite Hfrs3; exact Hin).
assert (EF3 : frame_addr ly3 3 pos = F) by (unfold F, frame_addr; destruct Hly3 as (_ & _ & _ & _ & _ & EFl & _); lia).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 3 pos HAR3 Hin3) as (_ & _ & Hpr3 & Hsh3).
rewrite EF3 in Hpr3, Hsh3. change (fs_frame_bytes 3) with 512 in Hpr3, Hsh3. change (512 / 8) with 64 in Hsh3.
(* the state re-seated at 0x80a40: the frame, its shadow and the spill window kept *)
lazymatch type of HS with st_ok _ _ ?ssv _ =>
  let Kv := eval vm_compute in (run_K 0 (SOff 32 0) [] ssv) in
  jafter_call_keep HS Kv regs3 (mrestrict (w_H W3) mem3) HP3 [0; 1; 2]%nat HS2 end.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_tcj_frame B E _ _ _ _ _ _ _ _ _ 10%nat _ _ _ _ _ F 3 pos KT3 U10 Hin).
    + left. change (fs_frame_bytes 3) with 512. fold F. lia.
    + intros a Ha Hx. exact Hx.
    + intros a Ha. exact (proj1 (Hpr3 a ltac:(lia))).
  - eapply (region_kept_tcj_frame B E _ _ _ _ _ _ _ _ _ 34%nat _ _ _ _ _ (shadow_addr F) 3 pos KT3 U34 Hin).
    + right. change (fs_frame_bytes 3 / 8) with 64. fold F. lia.
    + intros a Ha Hx. exact Hx.
    + intros a Ha. replace a with (shadow_addr F + (a - shadow_addr F)) by lia.
      exact (proj1 (Hsh3 (a - shadow_addr F) ltac:(lia))).
  - eapply (region_kept_tcj_stack B E _ _ _ _ _ _ _ _ _ 9%nat _ _ _ _ _ sp1 KT3 U9).
    + intros a Ha. split; [lia|]. split; [lia | intros Hx; exact Hx].
    + intros a Ha. split; lia. }
specialize (HS2 HQ). clear HQ. rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok _ ?En _ _ => remember En as E' eqn:HE' in HS end.
assert (EE' : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E' n = getr regs2 r)
  by (intros nn r Hnl Hnn; rewrite HE', ew_havoc_old by lia; apply EE; exact Hnn).
assert (E32' : ew E' 32 = Z_to_bv 64 SB) by (rewrite HE', ew_havoc_old by lia; exact E32).
assert (E33' : ew E' 33 = Z_to_bv 64 FL) by (rewrite HE', ew_havoc_old by lia; exact E33).
assert (E34' : ew E' 34 = Z_to_bv 64 (shadow_addr F)) by (rewrite HE', ew_havoc_old by lia; exact E34).
assert (E10' : ew E' 10 = Z_to_bv 64 F) by (rewrite HE', ew_havoc_old by lia; exact E10).
assert (E2' : ew E' 2 = Z_to_bv 64 sp1) by (rewrite HE', ew_havoc_old by lia; exact E2).
assert (E9' : ew E' 9 = Z_to_bv 64 sp1) by (rewrite HE', ew_havoc_old by lia; exact E9).
assert (E24' : ew E' 24 = Z_to_bv 64 (e_n g)) by (rewrite HE', ew_havoc_old by lia; exact E24).
assert (U10' : bv_unsigned (ew E' 10) = frame_addr ly3 3 pos) by (rewrite EF3, E10'; apply unsigned_lit_small; lia).
assert (U34' : bv_unsigned (ew E' 34) = shadow_addr (frame_addr ly3 3 pos))
  by (rewrite EF3, E34'; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (U9' : bv_unsigned (ew E' 9) = sp1) by (rewrite E9'; apply unsigned_lit_small; lia).
assert (U10F : bv_unsigned (ew E' 10) = F) by (rewrite E10'; apply unsigned_lit_small; lia).
assert (U34F : bv_unsigned (ew E' 34) = shadow_addr F)
  by (rewrite E34'; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
clear HE' EE E32 E33 E34 E10 E2 E9 E24 U10 U34 U9 U2 Q1 Q2 Q3 Q4.
clear KT3 HSV1 HRO HJ HP3 Esp. clear ms.
change (0 + EV_CDC) with 0 in HJ3.
assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((F <= a < F + 512) \/ (shadow_addr F <= a < shadow_addr F + 64) \/ (sp1 + 16 <= a < sp1 + 168)) ->
  aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W3) mem3 a) by (intros; reflexivity).
(* 0x80a40 .. 0x80ab8: one plain run to the loop head *)
aj_run_to tfibtbl_lib_ok HS HJ3 0x80abc; [ae_awr|].
cw_keep ae_kwr.
(* the final state at 0x80abc *)
assert (HSVf : ae_saves g W3 (ms_mem ms)).
{ apply (ae_saves_kept g W3 W3 mem3 (ms_mem ms)); [|exact HSV3].
  intros a Ha. apply KE; [lia|]. pose proof (Z.mul_div_le F 8 ltac:(lia)) as HF8b.
  unfold shadow_addr, SHADOW_OFF. lia. }
destruct (cw_frame_start MT MTL MTF B (e_ly g) (e_S g) S2 HSf) as (P1 & M1).
destruct (cw_frame_step MT MTL B (e_ly g) (e_S g) (e_ly g) S2 ly3 S3 P1 M1 HPerm3 HMLE3) as (P3 & M3).
rreg HS (2%bv : bv 5) G2. rreg HS (9%bv : bv 5) G9. rreg HS (8%bv : bv 5) G8. rreg HS (3%bv : bv 5) G3.
rreg HS (4%bv : bv 5) G4. rreg HS (20%bv : bv 5) G20. rreg HS (18%bv : bv 5) G18. rreg HS (21%bv : bv 5) G21.
rreg HS (22%bv : bv 5) G22. rreg HS (25%bv : bv 5) G25. rreg HS (19%bv : bv 5) G19. rreg HS (27%bv : bv 5) G27.
rreg HS (26%bv : bv 5) G26.
pose proof (st_ok_region_nth E' _ _ 0 _ HS eq_refl) as RG0.
pose proof (st_ok_region_nth E' _ _ 1 _ HS eq_refl) as RG1.
pose proof (st_ok_region_nth E' _ _ 2 _ HS eq_refl) as RG2.
cbn [ms_mem restrict] in RG0, RG1, RG2.
lazymatch type of RG0 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG0 end.
lazymatch type of RG2 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG2 end.
lazymatch type of RG1 with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RG1 end.
assert (Hp63 : 0 <= e_p g < 2 ^ 63).
{ destruct Hpn as [[_ ->] | [Hn Hb]]; [unfold A_EMPTY; lia|].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hb) as (_ & H4096 & Hbc & _).
  pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq). lia. }
  (* the spills, from the final spill window *)
  assert (SPL : forall od e v, In (YP09.mkChunk od (CVal 8 e)) (YP09.r_chunks
      ltac:(lazymatch type of RG2 with region_ok _ _ _ ?rg => exact rg end)) ->
    sv_denot E' e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
    val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (sp1 + od) 8 v).
  { intros od e v Hc He Hv.
    exact (field_of_region E' _ 9%nat sp1 _ _ _ _ _ od 8%N e v RG2 U9' Hc He ltac:(zside) ltac:(zside)). }
  assert (DF : forall o, 0 <= o <= 512 -> sv_denot E' (SOff 10 o) = Z_to_bv 64 (F + o))
    by (intros o Ho; cbn [sv_denot]; rewrite E10', unsigned_lit_small by lia; reflexivity).
rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl). cbn [ss_pc].
apply SRr_ret. exists pos, sp1.
unfold inv_head, mcut.
exists ly3, S3, (ms_regs ms), (ms_mem ms). eexists. exists 0.
split; [reflexivity|].
split; [exact HJ3|].
split; [rewrite Hfrs3; exact Hfrs2|].
split; [unfold EV_LIB; lia|].
split; [exact M3|].
split.
{ unfold mcommon, FA. fold F.
  split; [exact Hpre|].
  split; [reflexivity|].
  split; [rewrite G2, E2'; reflexivity|].
  split; [rewrite G9, E9'; reflexivity|].
  split; [rewrite G8, (EE' 8%nat 8%bv ltac:(lia) eq_refl); exact R8|].
  split; [rewrite G3, (EE' 3%nat 3%bv ltac:(lia) eq_refl); exact R3|].
  split; [rewrite G4, (EE' 4%nat 4%bv ltac:(lia) eq_refl); exact R4|].
  split; [rewrite G20, E32'; reflexivity|].
  split; [rewrite G18, E34'; reflexivity|].
  split; [rewrite G21; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
  split; [rewrite G22, E10', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G25, E10', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G19, E10', unsigned_lit_small by lia; reflexivity|].
  split; [rewrite G27; reflexivity|].
  split; [exact HF64|].
  split; [apply (SPL 16 (SOff 10 223)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 24 (SOff 10 34)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 32 (SOff 10 32)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 40 (SOff 10 320)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 48 (SLit 23728)); [ae_in | reflexivity | lia]|].
  split; [apply (SPL 56 (SOff 10 324)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 64 (SOff 10 0)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 72 (SOff 10 0)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 80 (SLit 5104)); [ae_in | reflexivity | lia]|].
  split; [apply (SPL 88 (SOff 10 216)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 96 (SOff 10 284)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 104 (SOff 10 344)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  split; [apply (SPL 112 (SLit 134976)); [ae_in | reflexivity | unfold CM_DESK; lia]|].
  split; [apply (SPL 120 (SOff 10 252)); [ae_in | rewrite DF by lia; f_equal; lia | lia]|].
  (* the saves *)
  destruct HSVf as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96 & S104).
  do 13 (split; [eassumption|]).
  (* the flag word *)
  split; [exact (ae_fld E' _ 10 _ _ _ _ _ _ 504 8%N 33%nat FL RG0 U10F ltac:(ae_in) E33' ltac:(zside) ltac:(zside))|].
  (* the frame's shadow bytes *)
  split.
  { intros i Hi. rewrite <- am_shm8_eq.
    apply (am_sh_read_all E' W3 (ms_mem ms) _ (shadow_addr F) am_shm8 RG1).
    - cbn [YP09.r_base base_val]. exact U34F.
    - vm_compute. reflexivity.
    - rewrite am_shm8_eq, am_shm_len. lia. }
  (* the input bytes, kept by the journal *)
  split.
  { pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
    intros j Hj. pose proof Hj as Hj'. rewrite length_map in Hj'.
    destruct (HPL j Hj) as (Hv & Hr). split; [|exact Hr].
    assert (Hn0 : 0 < e_n g) by lia.
    assert (Hin0 : In (e_p g, e_n g) (ablocks B (e_ly g) (e_S g)))
      by (destruct Hpn as [[Hz0 _] | [_ Hb]]; [lia | exact Hb]).
    assert (Hinb3 : In (e_p g, e_n g) (ablocks B ly3 S3))
      by (eapply Permutation_in; [apply Permutation_sym; exact P3 | exact Hin0]).
    pose proof (req_size_pos (e_n g) ltac:(lia)) as (_ & Hrq).
    apply (cw_val_mem_kept (w_H (e_W g)) (w_H W3) (e_mem g) (ms_mem ms)); [|exact Hv].
    intros x Hx. cbn [Z.of_nat] in Hx.
    replace x with (e_p g + (x - e_p g)) by lia.
    apply (F2 (e_p g) (e_n g) (x - e_p g) Hin0 Hinb3); [lia | apply inFP_nil]. }
  exact P3. }
(* the loop counter and the cursor *)
split; [split; [lia | exact G26]|].
exists 0. split; [lia|].
split.
- apply (SPL 152 (SOff 25 0)); [ae_in | | lia].
  cbn [sv_denot]. rewrite (EE' 25%nat 25%bv ltac:(lia) eq_refl), R25. unfold w64.
  rewrite unsigned_lit_small by lia. f_equal; lia.
- apply (SPL 160 (SOff 24 0)); [ae_in | | lia].
  cbn [sv_denot]. rewrite E24', unsigned_lit_small by lia. f_equal; lia.
Qed.
(* ENTRY 0x8084c-0x80ab8: the segment lemma of codec_amain_inv.v *)
Theorem seg_entry_holds : seg_entry B MT K XM_LIB.
Proof.
intros g W2 c2 (-> & ->) Hpre.
eapply SRr_bind; [exact (ae_p1 B MT K XM_LIB TL LAWS ML ASM3 SMP g Hpre)|].
intros W3 c3 _ H3. exact (ae_p2 g W3 c3 Hpre H3).
Qed.
End b.
End a.
