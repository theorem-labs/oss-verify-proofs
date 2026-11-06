(* Segment S0 of diginet_counter_text's walk in image A, part b: from the frame request's return (ct_s0_r1, 0x86198)
   to __asan_memset's return (ct_s0_r2, 0x86258).
   0x86198 .. 0x86254: s2 = s8 = F (bnez s2 at 0x861a8 is taken: F >= 4096, so the machine-stack fallback
   0x861ac .. 0x861c4 is not reached), 48(s1) := F, s5 = F + 64, the frame header F[0] = 0x41b58ab3, F[8] = 0x1b966,
   F[16] = 0x86120, s7 = SB + F / 8, the frame's 16 shadow bytes, a0 = F + 64, a1 = 0, a2 = 32, jal 0x51e34: one plain
   run from a state built at 0x86198 (atoms 33 = FL, 34 = SB + F / 8; the frame, its shadow and the spill slot), then
   __asan_memset (F + 64, 0, 32) through YC85.aj_intrin_atS. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgChkC CPgWalk CPgWalkKept CPgWalkIntr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgWalkFrame diginet_counter_text_A_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_text_A_s0_a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a byte read as 1 byte gives the reader's value *)
Lemma ct_aview_of_val1 : forall H (m : word -> option byte) a v,
  val_mem tfibsegs (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview tfibsegs H m a = Some v.
Proof.
intros H m a v Hv Hr. pose proof (Hv 0%nat ltac:(lia)) as Hb. cbn [Z.of_nat] in Hb. rewrite Z.add_0_r in Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (bv_modulus 8) with 256. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. repeat rewrite (Z.mod_small v 256 Hr). reflexivity.
Qed.
(* four zero bytes *)
Lemma ct_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview tfibsegs H m (a + i) = Some 0) -> val_mem tfibsegs (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj. destruct (aview_byte tfibsegs H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
(* the bytes of a garr8 list, as the reader sees them *)
Lemma ct_garr8_aview : forall H (m : word -> option byte) base l,
  garr8 tfibsegs (mrestrict H m) base l -> forall j, 0 <= j < Z.of_nat (length l) ->
  aview tfibsegs H m (base + j) = Some (nth (Z.to_nat j) l 0).
Proof.
intros H m base l G j Hj. destruct (G (Z.to_nat j) ltac:(lia)) as (V & R).
rewrite Z2Nat.id in V by lia. exact (ct_aview_of_val1 H m (base + j) _ V R).
Qed.
(* one byte of a region from a literal 1-byte chunk *)
Lemma ct_fld_lit1 : forall E m n bse cs lo hi wlo whi od z v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = bse ->
  In (YP09.mkChunk od (CVal 1 (SLit z))) cs -> z mod 2 ^ 64 mod 256 = v ->
  val_mem tfibsegs m (bse + od) 1 v.
Proof.
intros E m n bse cs lo hi wlo whi od z v Hr Hb Hc Hv.
pose proof (field_of_region_any E m n bse cs lo hi wlo whi od 1 (SLit z) Hr Hb Hc ltac:(lia)) as H.
cbn [sv_denot N.to_nat Pos.to_nat] in H. rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H.
change (bv_modulus 64) with (2 ^ 64) in H. change (2 ^ (8 * Z.of_N 1)) with 256 in H. rewrite Hv in H. exact H.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis AIS : aintrin_realizes tfibsegs B OSet 0x51e34.
Let errno_low := tl_env B TL.

(* the state at 0x86198: s9 = SB (atom 32), the frame at atom 10 (a0 = F) with the flag address (atom 33) at
   F + 120, the frame's shadow at atom 34, the spill slot 48(s1) *)
Definition ct_rs2 : smem :=
  [cw_frame_region 10 33 1; cw_fshadow_region 34 1; YP09.mkRegion (Some 9%nat) 48 56 48 56 []].
Definition ct_G2 : facts :=
  mkFacts [(10%nat, HPTR 6); (33%nat, HPTR 0); (34%nat, mkAF (SB + 512) (SB + 2 ^ 44) 3);
           (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0), SOff 34 0)].

Lemma ct_s0_p2 : forall g W2 c2, ct_pre B g -> ct_s0_r1 B g W2 c2 -> SRr tfibsegs W2 c2 (ct_s0_r2 B g).
Proof.
intros [STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs q sg dt tb sj dj] W2 c2 Hpre Hr1.
pose proof (ct_wr_where B _ Hpre) as HWR.
unfold ct_pre in Hpre.
unfold ct_s0_r1, ct_s0_r2, ct_s0_j, ct_saves, cg_sp, cg_sp1, cg_F, cg_FL, ct_wr in *.
cbn [cg_STK cg_sp0 cg_FP cg_ly cg_S cg_W0 cg_mem0 cg_md0 cg_own cg_lyc cg_Sc cg_W cg_memc cg_mdc cg_k cg_regs
  cg_q cg_sg cg_dt cg_tb cg_sj cg_dj] in Hpre, HWR, Hr1 |- *.
destruct Hpre as (HE & H10 & Hstr & H11 & Hsg & Hsj & Hsjl & H12 & Hdt & Hdj & Hd1 & Hd2 & Hd3 & Hfr8).
destruct Hr1 as (-> & S2 & regs2 & mem2 & md2 & pos & -> & (HJ2 & HK2 & KW2 & Eab & Hfrs2 & Hnin & HSf & Hio & Hflag &
  V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27) & Hz & R10 & R2 & R9 & R8 & R3 & R4 &
  R19 & R20 & R22 & R25).
pose proof (cw_entry_stack B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter_text HE
  ltac:(unfold T_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & Hpres).
pose proof HE as (HJc & Hra & Hra4 & Hgp & Htp & _ & Hwlo & Hwhi & Hev & Hlive).
pose proof HJc as (HARc & _).
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (TT : T_counter_text = 4288) by reflexivity. rewrite TT in *.
pose proof Hsg as (Hsg0 & Hsg63 & _). pose proof Hdt as (Hdt0 & Hdt63 & _).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & (Hsp0al & _) & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS _ _ _ _ _ 1 pos HAR2 Hin) as (HF4096 & HFceil & HFapp).
destruct (frame_al64 tfibsegs B _ _ _ _ _ 1 pos HAR2 Hin) as (HF64 & _ & _).
destruct (FFL _ _ _ _ _ 1 pos HAR2 Hin) as (_ & _ & _ & (HFL4096 & _ & HFLc)).
change (fs_frame_bytes 1) with 128 in HFceil, HFapp.
set (F := frame_addr lyc 1 pos) in *. set (FL := flag_addr lyc 1 pos) in *.
set (sp1 := 32 * ((spZ regs - 160) / 32)) in *.
destruct (sp1_facts (spZ regs - 160) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 176 <= sp1 <= spZ regs - 160) by lia. clear Hsp1r.
assert (HF0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (HF8 : F / 8 <= 2 ^ 44 - 2 ^ 20) by (apply Z.div_le_upper_bound; lia).
(* the start state *)
set (E := Ereg regs2 (cw_extra [FL; SB + F / 8])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 FL) by (subst E; exact (cw_ew_x regs2 [FL; SB + F / 8] 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (SB + F / 8)) by (subst E; exact (cw_ew_x regs2 [FL; SB + F / 8] 1)).
assert (E10 : ew E 10 = Z_to_bv 64 F) by (rewrite (EE 10%nat 10%bv eq_refl); exact R10).
assert (E2 : ew E 2 = Z_to_bv 64 sp1) by (rewrite (EE 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (U10 : bv_unsigned (ew E 10) = F) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = SB + F / 8) by (rewrite E34; apply unsigned_lit_small; unfold SB; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs2 (cw_extra [FL; SB + F / 8])) E) by (subst E; apply env_agree_refl).
assert (HS : st_ok tfibsegs E (mkSS 0x86198 (sr_set sr_atoms 25%bv (SOff 32 0)) ct_rs2 None ct_G2)
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x86198) mem2 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra [FL; SB + F / 8])) with E.
  - apply regs_ok_pin; [subst E; apply regs_ok_Ereg | intros Hx; discriminate Hx |].
    rewrite R25. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - vm_compute. reflexivity.
  - unfold ct_rs2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    + apply (cw_frame_region_ok B LAWS FFL _ 10 33 lyc S2 W mem2 md2 1 pos HAR2 Hin E10 E33).
      change (fs_frame_bytes 1) with 128. fold F FL. replace (F + 128 - 8) with (F + 120) by lia. exact Hflag.
    + apply (cw_fshadow_region_ok B LAWS _ 34 lyc S2 W mem2 md2 1 pos HAR2 Hin E34).
      change (fs_frame_bytes 1) with 128. exact Hz.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable tfibsegs). apply HJpres2. lia.
  - apply pairwise_disjoint_of_extents. unfold ct_rs2, cw_frame_region, cw_fshadow_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 1) with 128. change (128 / 8) with 16.
    rewrite U10, U34, U9. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold in_app, kLowShadowBeg, kHighMemBeg, SB in *. repeat split; lia.
  - split; [|split; [exact I|]].
    + destruct (cw_frame_afacts B LAWS E 10 33 34 lyc S2 W mem2 md2 1 pos FFL HAR2 Hin E10 E33 E34) as (A10 & A33 & A34).
      unfold ct_G2. cbn [f_atoms atoms_ok]. split; [exact A10|]. split; [exact A33|]. split; [exact A34|].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, E32, unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
      split; [split; [lia|]; split; [exact Hsp1al | lia]|]. split; [split; [lia|]; split; [exact Hsp1al | lia]|].
      split; [split; [unfold SB; lia|]; split; [reflexivity | lia]|]. exact I.
    + unfold ct_G2. cbn [f_alias alias_ok]. split; [|exact I].
      exact (shadow_decl_ok E 10%nat 32%nat 34%nat F SB E10 ltac:(lia) E32 E34). }
clearbody E.
assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) mem2)) by constructor.
(* 0x86198 .. jal 0x51e34 at 0x86254: one plain run, stopped at __asan_memset *)
aj_run_to tfibtbl_lib_ok HS HJ2 0x51e34.
{ lazymatch goal with |- awr_ok ?Ev ?rs ?stk ?s0 ?fp ?b0 ?bc ?lyv ?ownv =>
    let rs' := eval vm_compute in rs in change (awr_ok Ev rs' stk s0 fp b0 bc lyv ownv) end.
  repeat first
  [ apply awr_ok_nil
  | eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 1 pos 10%nat);
      [reflexivity | exact U10 | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 1) with 128; lia |]
  | eapply (cw_awr_ok_cons_fshadow _ _ _ _ _ _ _ _ _ _ 1 pos 34%nat);
      [reflexivity | rewrite U34; reflexivity | left; reflexivity | cbn; lia | cbn; change (fs_frame_bytes 1 / 8) with 16; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0)); [reflexivity | rewrite U9; lia | cbn; lia | cbn; lia |] ]. }
assert (HP2 : Permutation (ablocks B lyc S2) (ablocks B lyc Sc)) by (rewrite Eab; apply Permutation_refl).
(* what the run kept: only the frame, its shadow and the spill slot 48(s1) changed *)
set (Xb := fun a => (F <= a < F + 128) \/ (SB + F / 8 <= a < SB + F / 8 + 16) \/ (sp1 + 48 <= a < sp1 + 56)).
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?H ?m1) (mrestrict _ ?m2), HG : mem_grows _ _ |- _ =>
  assert (KX : forall a, 0 <= a < 2 ^ 64 -> ~ Xb a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
  [ intros a Ha Hx; apply (ct_kept_of_frame Ef rs H m1 m2 HFr a Ha); intros (r & Hr & Hb); apply Hx; unfold Xb;
    lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
    repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?U10, ?U34, ?U9 in Hb; lia | ]);
    destruct Hr
  | ];
  assert (KP : forall a, apresent H m1 a -> apresent H m2 a) by (intros a Hp; exact (apresent_grows _ _ _ a HG Hp));
  clear HFr HG
end.
clear_frames.
assert (HK3 : tcj_kept tfibsegs B 4288 lyc Sc W memc W (ms_mem ms) (spZ regs) (fun a => sg <= a < sg + 8 \/ dt <= a < dt + 1)).
{ apply (cw_kept_step B LAWS 4288 lyc Sc W memc mdc W mem2 (ms_mem ms) (spZ regs) _ Xb ltac:(lia) HARc HK2 KX); [|exact KP].
  intros a Ha. unfold Xb in Ha. destruct Ha as [Ha | [Ha | Ha]]; [right; right | right; right | left; lia].
  - apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W (ms_mem ms) _ k 1 pos a
      HJc HJ2 HP2). left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
  - apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W (ms_mem ms) _ k 1 pos a
      HJc HJ2 HP2). right; left. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
    fold F. unfold SB in Ha. lia. }
(* a byte of the write set is not fresh *)
assert (NF : forall a, (sg <= a < sg + 8 \/ dt <= a < dt + 1) -> cw_fresh B lyc Sc a -> False).
{ intros a Ha (_ & _ & Hb & Hf). destruct (HWR a Ha) as ([(b & m & Hinb & Hr) | (cid & p & Hinf & Hr)] & _).
  - apply (Hb b m (a - b) Hinb ltac:(lia)). lia.
  - apply (proj1 (Hf cid p Hinf)). exact Hr. }
(* the frame's shadow and the flag word at the call *)
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as RGF. pose proof (st_ok_region_nth E _ _ 1 _ HS eq_refl) as RGS.
cbn [ms_mem restrict] in RGF, RGS.
lazymatch type of RGF with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RGF end.
lazymatch type of RGS with region_ok _ _ _ ?rg => let rg' := eval vm_compute in rg in change rg with rg' in RGS end.
assert (GSH : garr8 tfibsegs (mrestrict (w_H W) (ms_mem ms)) (SB + F / 8) CT_FRAME_SHADOW).
{ intros j Hj. cbn [length CT_FRAME_SHADOW] in Hj.
  do 16 (destruct j as [|j]; [split; [eapply (ct_fld_lit1 E _ 34 _ _ _ _ _ _ _ _ _ RGS U34); [ct_in | reflexivity]
                                      | cbn [nth CT_FRAME_SHADOW]; lia] |]); lia. }
assert (VFL : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (F + 120) 8 FL).
{ eapply (ct_fld E _ 10 _ _ _ _ _ _ 120 8%N 33%nat FL RGF U10); [ct_in | exact E33 | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia]. }
clear RGF RGS.
(* the registers at the call *)
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2. rreg HS (3%bv : bv 5) Q3. rreg HS (4%bv : bv 5) Q4.
rreg HS (8%bv : bv 5) Q8. rreg HS (9%bv : bv 5) Q9. rreg HS (10%bv : bv 5) Q10. rreg HS (11%bv : bv 5) Q11.
rreg HS (12%bv : bv 5) Q12. rreg HS (18%bv : bv 5) Q18. rreg HS (19%bv : bv 5) Q19. rreg HS (20%bv : bv 5) Q20.
rreg HS (21%bv : bv 5) Q21. rreg HS (22%bv : bv 5) Q22. rreg HS (23%bv : bv 5) Q23. rreg HS (24%bv : bv 5) Q24.
rreg HS (25%bv : bv 5) Q25.
rewrite U10 in Q10, Q21.
(* the shadow of [F + 64, F + 96) and its hull *)
assert (HF64e : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)) as D; rewrite HF64, Z.add_0_r in D; exact D).
assert (HF8e : F / 8 = 8 * (F / 64)).
{ rewrite HF64e at 1. replace (64 * (F / 64)) with ((8 * (F / 64)) * 8) by lia. apply Z.div_mul. lia. }
assert (D64 : (F + 64) / 8 = F / 8 + 8) by (symmetry; apply (Z.div_unique _ 8 _ 0); lia).
assert (D95 : (F + 64 + 32 - 1) / 8 = F / 8 + 11) by (symmetry; apply (Z.div_unique _ 8 _ 7); lia).
assert (Hh1 : shadow_addr (F + 64) / 8 * 8 = SB + F / 8 + 8).
{ unfold shadow_addr. rewrite D64.
  assert (Hq : (SHADOW_OFF + (F / 8 + 8)) / 8 = 268431361 + F / 64)
    by (symmetry; apply (Z.div_unique _ 8 _ 0); unfold SHADOW_OFF; lia).
  rewrite Hq. unfold SB. lia. }
assert (Hh2 : shadow_addr (F + 64 + 32 - 1) / 8 * 8 = SB + F / 8 + 8).
{ unfold shadow_addr. rewrite D95.
  assert (Hq : (SHADOW_OFF + (F / 8 + 11)) / 8 = 268431361 + F / 64)
    by (symmetry; apply (Z.div_unique _ 8 _ 3); unfold SHADOW_OFF; lia).
  rewrite Hq. unfold SB. lia. }
(* 0x51e34: __asan_memset (F + 64, 0, 32), through CPgWalkIntr.cw_intrin_call (the walk keeps no region of its
   own across it: the next part builds its state afresh at 0x86258) *)
assert (Esp : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
apply (cw_intrin_call B LAWS OSet 0x51e34 AIS W E _ ms _ STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S2 k
  (F + 64) 0 32 549464 64%nat [] _ HS eq_refl eq_refl HJ2 Q10 Q11 Q12).
- lia.
- lia.
- lia.
- rewrite Esp. unfold ESTACK. lia.
- rewrite Esp. lia.
- rewrite Esp. exact Hsp1al16.
- exact Hsp0al.
- rewrite Q3, (EE 3%nat 3%bv eq_refl), R3. exact Hgp.
- rewrite Q4, (EE 4%nat 4%bv eq_refl), R4. exact Htp.
- vm_compute. reflexivity.
- lia.
- vm_compute. reflexivity.
- intros a Ha. split.
  + right; right; right. exists 1, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    change (fs_frame_bytes 1) with 128. fold F. lia.
  + rewrite Esp. unfold ESTACK. lia.
- unfold amem_range. unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. rewrite C3, C4, C5. unfold kHighMemBeg in C3. lia.
- apply zero_shadow_of_bytes;
    [rewrite HF64e; replace (64 * (F / 64) + 64) with ((8 * (F / 64) + 8) * 8) by lia; apply Z_mod_mult | reflexivity | lia |].
  intros i Hi. change (32 / 8) with 4 in Hi. rewrite D64.
  replace (SHADOW_OFF + (F / 8 + 8) + i) with (SB + F / 8 + (8 + i)) by (unfold SB, SHADOW_OFF; lia).
  rewrite (ct_garr8_aview _ _ _ _ GSH (8 + i) ltac:(cbn [length CT_FRAME_SHADOW]; lia)).
  assert (Hi' : (Z.to_nat (8 + i) = 8 \/ Z.to_nat (8 + i) = 9 \/ Z.to_nat (8 + i) = 10 \/ Z.to_nat (8 + i) = 11)%nat) by lia.
  destruct Hi' as [-> | [-> | [-> | ->]]]; reflexivity.
- intros _ s Hs. rewrite Hh1, Hh2 in Hs.
  replace s with (SB + F / 8 + (s - (SB + F / 8))) by lia.
  rewrite (ct_garr8_aview _ _ _ _ GSH (s - (SB + F / 8)) ltac:(cbn [length CT_FRAME_SHADOW]; lia)). discriminate.
- exact I.
- vm_compute. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
- submem_to.
- apply Forall_nil.
- intros regs3 mem3 md3 HJ3 HP3 Ra0 Heff Hfr Hpres3 Hsame _.
rewrite Esp in Hfr. unfold ESTACK in Hfr.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 64 <= a < F + 64 + 32) -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) (ms_mem ms) a) by exact Hfr.
assert (CS : forall r, acallee_saved r -> getr regs3 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP3.
apply SRr_ret. split; [reflexivity|].
exists S2, regs3, mem3, md3, pos.
split; [reflexivity|].
(* bytes kept by the run and the call *)
assert (KK : forall a, 0 <= a < 2 ^ 64 -> ~ Xb a -> ~ (F + 64 <= a < F + 64 + 32) -> ~ (sp1 - 4096 <= a < sp1) ->
  aview tfibsegs (w_H W) mem3 a = aview tfibsegs (w_H W) mem2 a).
{ intros a Ha H1 H2 H3. rewrite (KM a Ha H2 H3). exact (KX a Ha H1). }
assert (KVS : forall a vv, spZ regs - 104 <= a -> a + 8 <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 vv -> val_mem tfibsegs (mrestrict (w_H W) mem3) a 8 vv).
{ intros a vv H1 H2 Hv. apply (cw_val_mem_kept (w_H W) (w_H W) mem2 mem3 a 8 vv); [|exact Hv].
  intros x Hx. cbn in Hx. apply KK; [lia | unfold Xb, SB; lia | lia | lia]. }
split.
{ split; [exact HJ3|].
  split.
  { apply (cw_kept_step B LAWS 4288 lyc Sc W memc mdc W (ms_mem ms) mem3 (spZ regs) _
      (fun a => (F + 64 <= a < F + 64 + 32) \/ (sp1 - 4096 <= a < sp1)) ltac:(lia) HARc HK3); [| |exact Hpres3].
    - intros a Ha Hx. apply KM; [exact Ha | intros H; apply Hx; left; exact H | intros H; apply Hx; right; exact H].
    - intros a [Ha | Ha]; [right; right | left; lia].
      apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem3 _ k 1 pos a
        HJc HJ3 HP2). left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
  split.
  { intros a Ha. rewrite <- (KW2 a Ha).
    assert (Hab : 0 <= a < 2 ^ 64) by (destruct Ha; lia).
    pose proof (HWR a Ha) as (_ & Hw).
    apply KK; [exact Hab | | | lia].
    - intros [Hx | [Hx | Hx]]; [| |lia].
      + apply (NF a Ha). apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem3 _ k 1 pos a
          HJc HJ3 HP2). left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia.
      + apply (NF a Ha). apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem3 _ k 1 pos a
          HJc HJ3 HP2). right; left. unfold in_zr, shadow_addr, SHADOW_OFF. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16.
        fold F. unfold SB in Hx. lia.
    - intros Hx. apply (NF a Ha). apply (cw_fresh_frame_j B LAWS FFL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k lyc S2 W mem3 _ k 1 pos a
        HJc HJ3 HP2). left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 1) with 128. fold F. lia. }
  split; [exact Eab|]. split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact HSf|].
  split; [eapply same_io_trans; [exact Hio|]; eapply same_io_trans; [apply cw_same_io_wvb | apply same_io_materialized; exact Hsame]|].
  split.
  { apply rdword_of_val_mem; [|lia].
    apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem ms) mem3 (F + 120) 8 FL); [|exact VFL].
    intros x Hx. cbn in Hx. apply KM; lia. }
  split; [eapply KVS; [lia | lia | exact V1]|].
  split; [eapply KVS; [lia | lia | exact V8]|].
  split; [eapply KVS; [lia | lia | exact V9]|].
  split; [eapply KVS; [lia | lia | exact V18]|].
  split; [eapply KVS; [lia | lia | exact V19]|].
  split; [eapply KVS; [lia | lia | exact V20]|].
  split; [eapply KVS; [lia | lia | exact V21]|].
  split; [eapply KVS; [lia | lia | exact V22]|].
  split; [eapply KVS; [lia | lia | exact V23]|].
  split; [eapply KVS; [lia | lia | exact V24]|].
  split; [eapply KVS; [lia | lia | exact V25]|].
  split; [eapply KVS; [lia | lia | exact V26]|].
  eapply KVS; [lia | lia | exact V27]. }
split.
{ intros j Hj. destruct (GSH j Hj) as (Vj & Rj). split; [|exact Rj].
  apply (cw_val_mem_kept (w_H W) (w_H W) (ms_mem ms) mem3 _ 1 _); [|exact Vj].
  intros x Hx. cbn [length CT_FRAME_SHADOW] in Hj.
  assert (Hx' : SB + F / 8 <= x < SB + F / 8 + 16) by (cbn [Z.of_nat Pos.of_succ_nat] in Hx; fold F in Hx; lia). clear Hx.
  unfold SB in Hx'. apply KM; [lia | | lia].
  unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. lia. }
split.
{ intros i Hi. apply ct_val_mem_zero4. intros i' Hi'.
  pose proof (Heff (4 * i + i') ltac:(lia)) as He. fold F in He |- *.
  replace (F + 64 + 4 * i + i') with (F + 64 + (4 * i + i')) by lia.
  rewrite He. reflexivity. }
assert (P2 : getr regs3 2 = getr (ms_regs ms) 2) by exact (CS 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : getr regs3 3 = getr (ms_regs ms) 3) by exact (CS 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : getr regs3 4 = getr (ms_regs ms) 4) by exact (CS 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : getr regs3 8 = getr (ms_regs ms) 8) by exact (CS 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : getr regs3 9 = getr (ms_regs ms) 9) by exact (CS 9 ltac:(unfold acallee_saved; lia)).
assert (P18 : getr regs3 18 = getr (ms_regs ms) 18) by exact (CS 18 ltac:(unfold acallee_saved; lia)).
assert (P19 : getr regs3 19 = getr (ms_regs ms) 19) by exact (CS 19 ltac:(unfold acallee_saved; lia)).
assert (P20 : getr regs3 20 = getr (ms_regs ms) 20) by exact (CS 20 ltac:(unfold acallee_saved; lia)).
assert (P21 : getr regs3 21 = getr (ms_regs ms) 21) by exact (CS 21 ltac:(unfold acallee_saved; lia)).
assert (P22 : getr regs3 22 = getr (ms_regs ms) 22) by exact (CS 22 ltac:(unfold acallee_saved; lia)).
assert (P23 : getr regs3 23 = getr (ms_regs ms) 23) by exact (CS 23 ltac:(unfold acallee_saved; lia)).
assert (P24 : getr regs3 24 = getr (ms_regs ms) 24) by exact (CS 24 ltac:(unfold acallee_saved; lia)).
assert (P25 : getr regs3 25 = getr (ms_regs ms) 25) by exact (CS 25 ltac:(unfold acallee_saved; lia)).
split; [rewrite P2, Q2; exact E2|].
split; [rewrite P9, Q9; exact E9|].
split; [rewrite P8, Q8, (EE 8%nat 8%bv eq_refl); exact R8|].
split; [rewrite P3, Q3, (EE 3%nat 3%bv eq_refl); exact R3|].
split; [rewrite P4, Q4, (EE 4%nat 4%bv eq_refl); exact R4|].
split; [rewrite P18, Q18; exact E10|].
split; [rewrite P24, Q24; exact E10|].
split; [rewrite P19, Q19, (EE 19%nat 19%bv eq_refl); exact R19|].
split; [rewrite P20, Q20, (EE 20%nat 20%bv eq_refl); exact R20|].
split; [rewrite P22, Q22, (EE 22%nat 22%bv eq_refl); exact R22|].
split; [rewrite P21, Q21; reflexivity|].
split; [rewrite P23, Q23; exact E34|].
rewrite P25, Q25. exact E32.
Qed.
End s.
