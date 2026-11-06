(* fuzz_preset image A' (asan, #102 pin 1be0f53d96cb, unstripped twin bff8519bbe3e, facts 8f3e7e1a07f1): the walk of
   put_utf8 (A' 0x88164, slot 6881) and of ex_utf8 (A' 0x84764, slot 3169), ONE proof run from either entry slot of the
   whole-range listing A_prog_listing (lib/A/Listing_prog.v, PAImg_prog.v A_entry_put_utf8 / A_entry_ex_utf8), and the
   text tput_utf8_specX (the kit's cut 7cdbb61b5fa0, lib/A/PRH_FnReader.v:290-303) at PA := PI_prog_A: pb_put_utf8X_Ap.
   RELOCATED A -> A' (a Theorem Labs lane's order: B' first, then A'): the old-pin A walk a working branch
   dafa4151f91 lib/A/Prog/ExUtf8.v (image A f0d2e8d40c7e) moved to A'. bytecmp 1480ca2faea0: put_utf8 old A 0x87c28 vs
   A' 0x88164, 520 bytes each, EQUAL-mod-pcrel (11 pc-relative words, 0 real differences; a planted one-word change reads
   DIFFERENT); all 14 pc-relative targets name the same place (put_utf8+0x178 x3, __asan_report_store1 x10; the
   auipc+ld at +0x8 reads .got +0x60, __asan_shadow_memory_dynamic_address, on both). The only numbers that move are the
   entry offsets from BASE = pa_val A_TEXT (old A 0x8154c, A' 0x815e0): put_utf8 26332 -> 27524, ex_utf8 11940 -> 12676.
   The A bodies of put_utf8 and ex_utf8 are one body up to pc-relative targets (no UBSan checks on A).
   THE FILE IS lib/B/Prog/ExUtf8WB.v (the B' row, same branch) UNDER THE A NAME MAP: old A ExUtf8.v and old B ExUtf8B.v
   are the same text apart from the header, the A/B names and the offsets, so the B' re-binding (the memory-invariant
   runner paj_run_x_inv with P := u8_P SEGS mem, the text's fpostm / most own / room_live_cf / S' = S through the
   shared lib/A/Prog/ExUtf8W.v) carries over unchanged. Every run below is re-run by the engine against the A' listing
   (Listing_prog 7ed1529926bd, PAImg_prog 16c7bdadef3d; the cut's PAImg_prog 505a51ff7d08 differs only in its header
   comment and #[global] -> #[export] on PL_prog_A / PI_prog_A: no slot, offset or value moved). Form: YCbqG's
   afn_pre_x / apost_base_x over ARx; every conclusion is SRr (YA0n.v). Model: PjGrammar.utf8. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnReader CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import ExUtf8W.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lia's division equations (Rocq's ZifyNat sets this flag true): the byte bounds below (cp / 64, cp mod 64, ...) need
   them, and the Require closure now sets the flag false globally (CfParamsPreset.v -> YGcfAbudget.v -> YFfn.v ->
   YA09 / YA08 / YA0e); set it back for this file only *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* the walk is stated for an ARBITRARY image instance PA : PAImg A_prog_listing; keep PAImg_prog's global instance out
   of instance search so no implicit argument can resolve to it (only PL_prog_A, the listing's one PAListing, is used);
   the text's instance PA := PI_prog_A is passed explicitly in Section t *)
#[local] Remove Hints PI_prog_A : typeclass_instances.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg A_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the image binding of the shadow base (YC1fP.v PALibCore: A_OBJ 0 is its GOT word, A_OBJ 12 its cell) *)
Hypothesis TL : PALibCore (PI := PA) B.
(* image fact: the shadow-base GOT word and the shadow cell lie in the image *)
Hypothesis HOBJ : forall i a, (i = 0 \/ i = 12)%nat -> VAL (A_OBJ i) <= a < VAL (A_OBJ i) + 8 -> in_img SEGS a.
Let RET := paj_ret_at (PL := PL_prog_A) (PI := PA).
Let ENT := u8_entry (PA := PA) B ARx LAWS TL HOBJ.
#[local] Abbreviation POST := (u8_post (SK := SK) (PA := PA) B PST ARx).

Lemma u8_case1 : forall eo ly S Hp W regs mem md ch STK o cp b m,
  eo = 12676 \/ eo = 27524 ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 0 <= cp <= 127 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + 1 <= b + m ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + eo) regs mem md) (POST STK regs ly S Hp W mem md o [cp]).
Proof.
  intros eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 Hcp Hbb Hbo Hon HRA.
  destruct (ENT ly S Hp W regs mem md ch STK o cp eo 1 0 127 (@nil acond) b m HPRE HSTK H10 H11 ltac:(lia) ltac:(lia) ltac:(lia)
    Hbb Hbo Hon ltac:(lia) HRA I ltac:(vm_compute; reflexivity)) as [HS SHOK].
  pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK [(o, o + Z.of_nat (length [cp]))] ly S Hp W regs mem md ch HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hbb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  assert (HrL : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  remember (EU (PA := PA) regs) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EU; apply Eimg_env).
  assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (split; [intros n Hn; subst E; unfold EU; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE0 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE0 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (proj1 HAE0 10%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 cp) by (rewrite (proj1 HAE0 11%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Eu10 : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (HPM : u8_P SEGS mem mem) by (intros Hm; exact Hm).
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS _ (u8_plaw SEGS mem)).
  unfold cfg_at. change (w64 (BASE + eo)) with (Z_to_bv 64 (BASE + eo)).
  destruct Heo as [-> | ->].
  all: paj_run_tok_x_inv RUN HS HJ SHOK HPM U8_SPAN.
  all: try u8_awr.
  all: lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- SRr _ _ _ _ =>
      let R10 := fresh "R10" in let R1 := fresh "R1" in
      prreg HS0 (10%bv : bv 5) R10; prreg HS0 (1%bv : bv 5) R1;
      pose proof (u8_region_nth SEGS Ex _ _ 3 _ HS0 eq_refl) as HR3; cbn [ms_mem restrict] in HR3;
      eapply (RET W _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity));
      let mat' := fresh "mat" in intros mat';
      unfold u8_post, apost_base_x;
      exists ly, S, Hp, (ms_regs msx), (ms_mem msx); eexists; exists 0;
      split; [cbn [ms_regs ms_mem]; rewrite R1, E1, Hra; reflexivity|];
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ0 | exact LAWS | exact (@pa_segs_low _ _ PA)]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF] HS0);
              [env_agree_chain HAE0 | vm_compute; reflexivity]|];
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [rewrite R10; reflexivity|];
      split; [| split; [
        intros a Ha Hw Ho; apply (aview_eq_of SEGS); apply HFr0; rewrite unsigned_lit_small by lia;
        intros (r & Hin & Hr); cbn [ss_mem ss_u8 u8_regions stack_region got_regionP bcell_regionP In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold stack_region, got_regionP, bcell_regionP in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Eu10 in Hr; cbn [length Z.of_nat Pos.of_succ_nat] in Ho; lia
      | exact HPM]]
  end.
  all: lazymatch goal with
  | HR3 : region_ok SEGS ?Ex _ _ |- garr8 _ _ ?o _ =>
    assert (Eu10x : bv_unsigned (ew Ex 10) = o) by (cbn [ew ewset Nat.eqb]; exact Eu10);
    assert (E11x : ew Ex 11 = Z_to_bv 64 cp) by (cbn [ew ewset Nat.eqb]; exact E11);
    pose proof (u8_field_of_region Ex _ 10%nat o _ _ _ _ _ 0 1%N (SOff 11 0) HR3 Eu10x ltac:(cbn; left; reflexivity) ltac:(cbn; lia)) as V0;
    rewrite (U_atom Ex 11 cp E11x) in V0 by lia; rewrite Z.add_0_r in V0; change (N.to_nat 1) with 1%nat in V0;
    change (2 ^ (8 * Z.of_N 1)) with 256 in V0; rewrite Z.mod_small in V0 by lia;
    apply u8_garr8_cons; [exact V0 | lia | apply garr8_nil]
  end.
Qed.

Lemma u8_case2 : forall eo ly S Hp W regs mem md ch STK o cp b m,
  eo = 12676 \/ eo = 27524 ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 128 <= cp <= 2047 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + 2 <= b + m ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o 2 ->
  SRr SEGS W (cfg_at SEGS (BASE + eo) regs mem md) (POST STK regs ly S Hp W mem md o [192 + cp / 64; 128 + cp mod 64]).
Proof.
  intros eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 Hcp Hbb Hbo Hon HRA.
  destruct (ENT ly S Hp W regs mem md ch STK o cp eo 2 128 2047 (@nil acond) b m HPRE HSTK H10 H11 ltac:(lia) ltac:(lia) ltac:(lia)
    Hbb Hbo Hon ltac:(lia) HRA I ltac:(vm_compute; reflexivity)) as [HS SHOK].
  pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK [(o, o + Z.of_nat (length [192 + cp / 64; 128 + cp mod 64]))] ly S Hp W regs mem md ch HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hbb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  assert (HrL : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  remember (EU (PA := PA) regs) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EU; apply Eimg_env).
  assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (split; [intros n Hn; subst E; unfold EU; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE0 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE0 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (proj1 HAE0 10%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 cp) by (rewrite (proj1 HAE0 11%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Eu10 : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (HPM : u8_P SEGS mem mem) by (intros Hm; exact Hm).
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS _ (u8_plaw SEGS mem)).
  unfold cfg_at. change (w64 (BASE + eo)) with (Z_to_bv 64 (BASE + eo)).
  destruct Heo as [-> | ->].
  all: paj_run_tok_x_inv RUN HS HJ SHOK HPM U8_SPAN.
  all: try u8_awr.
  all: lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- SRr _ _ _ _ =>
      let R10 := fresh "R10" in let R1 := fresh "R1" in
      prreg HS0 (10%bv : bv 5) R10; prreg HS0 (1%bv : bv 5) R1;
      pose proof (u8_region_nth SEGS Ex _ _ 3 _ HS0 eq_refl) as HR3; cbn [ms_mem restrict] in HR3;
      eapply (RET W _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity));
      let mat' := fresh "mat" in intros mat';
      unfold u8_post, apost_base_x;
      exists ly, S, Hp, (ms_regs msx), (ms_mem msx); eexists; exists 0;
      split; [cbn [ms_regs ms_mem]; rewrite R1, E1, Hra; reflexivity|];
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ0 | exact LAWS | exact (@pa_segs_low _ _ PA)]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF] HS0);
              [env_agree_chain HAE0 | vm_compute; reflexivity]|];
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [rewrite R10; reflexivity|];
      split; [| split; [
        intros a Ha Hw Ho; apply (aview_eq_of SEGS); apply HFr0; rewrite unsigned_lit_small by lia;
        intros (r & Hin & Hr); cbn [ss_mem ss_u8 u8_regions stack_region got_regionP bcell_regionP In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold stack_region, got_regionP, bcell_regionP in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Eu10 in Hr; cbn [length Z.of_nat Pos.of_succ_nat] in Ho; lia
      | exact HPM]]
  end.
  all: lazymatch goal with
  | HR3 : region_ok SEGS ?Ex _ _ |- garr8 _ _ ?o _ =>
    assert (Eu10x : bv_unsigned (ew Ex 10) = o) by (cbn [ew ewset Nat.eqb]; exact Eu10);
    assert (E11x : ew Ex 11 = Z_to_bv 64 cp) by (cbn [ew ewset Nat.eqb]; exact E11);
    assert (Hv0 : U Ex (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 6)) (SLit (-64))) mod 256 = 192 + cp / 64) by (apply (u8_bA Ex cp 6 64 6); [exact E11x | lia | lia | lia | reflexivity | apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | change (2 ^ 6 * 2 ^ 6) with 4096; lia] | change (2 ^ 6) with 64; lia]);
    u8_byte HR3 Ex o 0 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 6)) (SLit (-64))) (192 + cp / 64) Hv0 V0;
    assert (Hv1 : U Ex (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64) by (apply (u8_bB Ex cp); [exact E11x | lia | lia]);
    u8_byte HR3 Ex o 1 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) (128 + cp mod 64) Hv1 V1;
    rewrite Z.add_0_r in V0;
    apply u8_garr8_cons; [exact V0 | lia |];
    apply u8_garr8_cons; [exact V1 | lia |];
    apply garr8_nil
  end.
Qed.

Lemma u8_case3 : forall eo ly S Hp W regs mem md ch STK o cp b m,
  eo = 12676 \/ eo = 27524 ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 2048 <= cp <= 65535 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + 3 <= b + m ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o 3 ->
  SRr SEGS W (cfg_at SEGS (BASE + eo) regs mem md) (POST STK regs ly S Hp W mem md o [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64]).
Proof.
  intros eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 Hcp Hbb Hbo Hon HRA.
  destruct (ENT ly S Hp W regs mem md ch STK o cp eo 3 2048 65535 [mkAC BC_EQ (SAluw ALU_SRL (SOff 11 0) (SLit 16)) (SLit 0)] b m HPRE HSTK H10 H11 ltac:(lia) ltac:(lia) ltac:(lia)
    Hbb Hbo Hon ltac:(lia) HRA (u8_c3 (PA := PA) regs cp H11 ltac:(lia)) ltac:(vm_compute; reflexivity)) as [HS SHOK].
  pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK [(o, o + Z.of_nat (length [224 + cp / 4096; 128 + (cp / 64) mod 64; 128 + cp mod 64]))] ly S Hp W regs mem md ch HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hbb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  assert (HrL : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  remember (EU (PA := PA) regs) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EU; apply Eimg_env).
  assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (split; [intros n Hn; subst E; unfold EU; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE0 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE0 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (proj1 HAE0 10%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 cp) by (rewrite (proj1 HAE0 11%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Eu10 : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (HPM : u8_P SEGS mem mem) by (intros Hm; exact Hm).
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS _ (u8_plaw SEGS mem)).
  unfold cfg_at. change (w64 (BASE + eo)) with (Z_to_bv 64 (BASE + eo)).
  destruct Heo as [-> | ->].
  all: paj_run_tok_x_inv RUN HS HJ SHOK HPM U8_SPAN.
  all: try u8_awr.
  all: lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- SRr _ _ _ _ =>
      let R10 := fresh "R10" in let R1 := fresh "R1" in
      prreg HS0 (10%bv : bv 5) R10; prreg HS0 (1%bv : bv 5) R1;
      pose proof (u8_region_nth SEGS Ex _ _ 3 _ HS0 eq_refl) as HR3; cbn [ms_mem restrict] in HR3;
      eapply (RET W _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity));
      let mat' := fresh "mat" in intros mat';
      unfold u8_post, apost_base_x;
      exists ly, S, Hp, (ms_regs msx), (ms_mem msx); eexists; exists 0;
      split; [cbn [ms_regs ms_mem]; rewrite R1, E1, Hra; reflexivity|];
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ0 | exact LAWS | exact (@pa_segs_low _ _ PA)]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF] HS0);
              [env_agree_chain HAE0 | vm_compute; reflexivity]|];
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [rewrite R10; reflexivity|];
      split; [| split; [
        intros a Ha Hw Ho; apply (aview_eq_of SEGS); apply HFr0; rewrite unsigned_lit_small by lia;
        intros (r & Hin & Hr); cbn [ss_mem ss_u8 u8_regions stack_region got_regionP bcell_regionP In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold stack_region, got_regionP, bcell_regionP in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Eu10 in Hr; cbn [length Z.of_nat Pos.of_succ_nat] in Ho; lia
      | exact HPM]]
  end.
  all: lazymatch goal with
  | HR3 : region_ok SEGS ?Ex _ _ |- garr8 _ _ ?o _ =>
    assert (Eu10x : bv_unsigned (ew Ex 10) = o) by (cbn [ew ewset Nat.eqb]; exact Eu10);
    assert (E11x : ew Ex 11 = Z_to_bv 64 cp) by (cbn [ew ewset Nat.eqb]; exact E11);
    assert (Hv0 : U Ex (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 12)) (SLit (-32))) mod 256 = 224 + cp / 4096) by (apply (u8_bA Ex cp 12 32 5); [exact E11x | lia | lia | lia | reflexivity | apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | change (2 ^ 12 * 2 ^ 5) with 131072; lia] | change (2 ^ 12) with 4096; lia]);
    u8_byte HR3 Ex o 0 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 12)) (SLit (-32))) (224 + cp / 4096) Hv0 V0;
    assert (Hv1 : U Ex (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) mod 256 = 128 + (cp / 64) mod 64) by (apply (u8_bC Ex cp 52); [exact E11x | lia | lia | change (2 ^ (58 - 52)) with 64; lia]);
    u8_byte HR3 Ex o 1 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) (128 + (cp / 64) mod 64) Hv1 V1;
    assert (Hv2 : U Ex (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64) by (apply (u8_bB Ex cp); [exact E11x | lia | lia]);
    u8_byte HR3 Ex o 2 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) (128 + cp mod 64) Hv2 V2;
    rewrite Z.add_0_r in V0;
    apply u8_garr8_cons; [exact V0 | lia |];
    apply u8_garr8_cons; [exact V1 | lia |];
    replace (o + 1 + 1) with (o + 2) by lia;
    apply u8_garr8_cons; [exact V2 | lia |];
    apply garr8_nil
  end.
Qed.

Lemma u8_case4 : forall eo ly S Hp W regs mem md ch STK o cp b m,
  eo = 12676 \/ eo = 27524 ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 65536 <= cp < 2 ^ 21 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + 4 <= b + m ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o 4 ->
  SRr SEGS W (cfg_at SEGS (BASE + eo) regs mem md) (POST STK regs ly S Hp W mem md o [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64]).
Proof.
  intros eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 Hcp Hbb Hbo Hon HRA.
  destruct (ENT ly S Hp W regs mem md ch STK o cp eo 4 65536 2097151 [mkAC BC_NE (SAluw ALU_SRL (SOff 11 0) (SLit 16)) (SLit 0)] b m HPRE HSTK H10 H11 ltac:(lia) ltac:(lia) ltac:(lia)
    Hbb Hbo Hon ltac:(lia) HRA (u8_c4 (PA := PA) regs cp H11 ltac:(lia)) ltac:(vm_compute; reflexivity)) as [HS SHOK].
  pose proof (ajournal_x_init (SK := SK) SEGS B PST ARx STK [(o, o + Z.of_nat (length [240 + cp / 262144; 128 + (cp / 4096) mod 64; 128 + (cp / 64) mod 64; 128 + cp mod 64]))] ly S Hp W regs mem md ch HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md b m HAR Hbb) as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
  assert (HrL : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  remember (EU (PA := PA) regs) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EU; apply Eimg_env).
  assert (HAE0 : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
    by (split; [intros n Hn; subst E; unfold EU; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E1 : ew E 1 = getr regs 1) by (rewrite (proj1 HAE0 1%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite (proj1 HAE0 2%nat ltac:(lia)); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (proj1 HAE0 10%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 cp) by (rewrite (proj1 HAE0 11%nat ltac:(lia)); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (Eu10 : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (HPM : u8_P SEGS mem mem) by (intros Hm; exact Hm).
  pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS _ (u8_plaw SEGS mem)).
  unfold cfg_at. change (w64 (BASE + eo)) with (Z_to_bv 64 (BASE + eo)).
  destruct Heo as [-> | ->].
  all: paj_run_tok_x_inv RUN HS HJ SHOK HPM U8_SPAN.
  all: try u8_awr.
  all: lazymatch goal with
  | HS0 : st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx), HJ0 : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HFr0 : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- SRr _ _ _ _ =>
      let R10 := fresh "R10" in let R1 := fresh "R1" in
      prreg HS0 (10%bv : bv 5) R10; prreg HS0 (1%bv : bv 5) R1;
      pose proof (u8_region_nth SEGS Ex _ _ 3 _ HS0 eq_refl) as HR3; cbn [ms_mem restrict] in HR3;
      eapply (RET W _ _ _ _ _ HS0 eq_refl ltac:(vm_compute; reflexivity));
      let mat' := fresh "mat" in intros mat';
      unfold u8_post, apost_base_x;
      exists ly, S, Hp, (ms_regs msx), (ms_mem msx); eexists; exists 0;
      split; [cbn [ms_regs ms_mem]; rewrite R1, E1, Hra; reflexivity|];
      split; [eapply (ajournal_x_materialize (SK := SK)); solve [exact HJ0 | exact LAWS | exact (@pa_segs_low _ _ PA)]|];
      split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [Z_to_bv 64 SHADOW_OFF] HS0);
              [env_agree_chain HAE0 | vm_compute; reflexivity]|];
      split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
      split; [rewrite R10; reflexivity|];
      split; [| split; [
        intros a Ha Hw Ho; apply (aview_eq_of SEGS); apply HFr0; rewrite unsigned_lit_small by lia;
        intros (r & Hin & Hr); cbn [ss_mem ss_u8 u8_regions stack_region got_regionP bcell_regionP In] in Hin;
        destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; unfold stack_region, got_regionP, bcell_regionP in Hr;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?Usp, ?Eu10 in Hr; cbn [length Z.of_nat Pos.of_succ_nat] in Ho; lia
      | exact HPM]]
  end.
  all: lazymatch goal with
  | HR3 : region_ok SEGS ?Ex _ _ |- garr8 _ _ ?o _ =>
    assert (Eu10x : bv_unsigned (ew Ex 10) = o) by (cbn [ew ewset Nat.eqb]; exact Eu10);
    assert (E11x : ew Ex 11 = Z_to_bv 64 cp) by (cbn [ew ewset Nat.eqb]; exact E11);
    assert (Hv0 : U Ex (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 18)) (SLit (-16))) mod 256 = 240 + cp / 262144) by (apply (u8_bA Ex cp 18 16 4); [exact E11x | lia | lia | lia | reflexivity | apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | change (2 ^ 18 * 2 ^ 4) with 4194304; lia] | change (2 ^ 18) with 262144; lia]);
    u8_byte HR3 Ex o 0 (SAlu ALU_OR (SAlu ALU_SRL (SOff 11 0) (SLit 18)) (SLit (-16))) (240 + cp / 262144) Hv0 V0;
    assert (Hv1 : U Ex (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 46)) (SLit 58)) (SLit (-128))) mod 256 = 128 + (cp / 4096) mod 64) by (apply (u8_bC Ex cp 46); [exact E11x | lia | lia | change (2 ^ (58 - 46)) with 4096; lia]);
    u8_byte HR3 Ex o 1 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 46)) (SLit 58)) (SLit (-128))) (128 + (cp / 4096) mod 64) Hv1 V1;
    assert (Hv2 : U Ex (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) mod 256 = 128 + (cp / 64) mod 64) by (apply (u8_bC Ex cp 52); [exact E11x | lia | lia | change (2 ^ (58 - 52)) with 64; lia]);
    u8_byte HR3 Ex o 2 (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 11 0) (SLit 52)) (SLit 58)) (SLit (-128))) (128 + (cp / 64) mod 64) Hv2 V2;
    assert (Hv3 : U Ex (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) mod 256 = 128 + cp mod 64) by (apply (u8_bB Ex cp); [exact E11x | lia | lia]);
    u8_byte HR3 Ex o 3 (SAlu ALU_ADD (SAlu ALU_AND (SOff 11 0) (SLit 63)) (SLit (-128))) (128 + cp mod 64) Hv3 V3;
    rewrite Z.add_0_r in V0;
    apply u8_garr8_cons; [exact V0 | lia |];
    apply u8_garr8_cons; [exact V1 | lia |];
    replace (o + 1 + 1) with (o + 2) by lia;
    apply u8_garr8_cons; [exact V2 | lia |];
    replace (o + 2 + 1) with (o + 3) by lia;
    apply u8_garr8_cons; [exact V3 | lia |];
    apply garr8_nil
  end.
Qed.

(* THE WALK, one proof for both entries: ex_utf8 (offset 12676) and put_utf8 (offset 27524) *)
Lemma u8_walk : forall eo ly S Hp W regs mem md ch STK o cp b m,
  eo = 12676 \/ eo = 27524 ->
  afn_pre_x SEGS B ARx STK ly S Hp W regs mem md ch -> 16 <= STK ->
  getr regs 10 = w64 o -> getr regs 11 = w64 cp -> 0 <= cp < 2 ^ 21 ->
  In (b, m) (ablocks B ly S) -> b <= o -> o + Z.of_nat (length (PjGrammar.utf8 cp)) <= b + m ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF o (Z.of_nat (length (PjGrammar.utf8 cp))) ->
  SRr SEGS W (cfg_at SEGS (BASE + eo) regs mem md) (POST STK regs ly S Hp W mem md o (PjGrammar.utf8 cp)).
Proof.
  intros eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 Hcp Hbb Hbo Hon HRA.
  destruct (Z_lt_le_dec cp 128) as [C1|C1].
  { rewrite u8_arm1 in * by lia.
    exact (u8_case1 eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 ltac:(lia) Hbb Hbo Hon HRA). }
  destruct (Z_lt_le_dec cp 2048) as [C2|C2].
  { rewrite u8_arm2 in * by lia.
    exact (u8_case2 eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 ltac:(lia) Hbb Hbo Hon HRA). }
  destruct (Z_lt_le_dec cp 65536) as [C3|C3].
  { rewrite u8_arm3 in * by lia.
    exact (u8_case3 eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 ltac:(lia) Hbb Hbo Hon HRA). }
  rewrite u8_arm4 in * by lia.
  exact (u8_case4 eo ly S Hp W regs mem md ch STK o cp b m Heo HPRE HSTK H10 H11 ltac:(lia) Hbb Hbo Hon HRA).
Qed.

End a.

(* ---- the TEXT (cut 7cdbb61b5fa0 lib/A/PRH_FnReader.v:290-303 tput_utf8_specX) at image A': PA := PI_prog_A (the
   whole-program listing's instance), PI := prh_img_A (PRH_Img.v), cp := CfParams_preset (the instance the B' twin and
   a Theorem Labs lane's parse_string use). Discharged here from the image files: HOBJ (the shadow-base GOT word and cell are image
   bytes: find_segment over PI_prog_A's segments), HPST (S1ImgA.v pst_in_img_A), the head width (CfParamsPreset.v
   preset_head_wide), the entry (PAImg_prog.v A_entry_put_utf8: slot 6881, offset 27524) and the frame (PRH_Img.v).
   KEPT as named Section hypotheses: LAWS (the allocator relation's laws) and TL (the shadow-base binding of B);
   neither has an A' discharge in this tree. ---- *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {RL : PrhRoomLive}.
#[local] Abbreviation PA := PI_prog_A.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Abbreviation VAL := (@pa_val _ A_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
(* the allocator relation's laws (YCbqG.v AR_laws_x; at preset's ARcfx: YGcallcf.AR_laws_x_xs of YG0lawscf.AR_laws_ok_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the image binding of the shadow base of B (YC1fP.v PALibCore: A_OBJ 0 is its GOT word, A_OBJ 12 its cell) *)
Hypothesis TL : PALibCore (PI := PA) B.

(* the shadow-base GOT word and the shadow cell are image bytes (find_segment over PI_prog_A's segments) *)
Lemma pbu_obj_img : forall i a, (i = 0 \/ i = 12)%nat -> VAL (A_OBJ i) <= a < VAL (A_OBJ i) + 8 -> in_img SEGS a.
Proof.
  intros i a Hi Ha.
  assert (Hs : match find_segment SEGS (VAL (A_OBJ i)) 8 with Some _ => true | None => false end = true)
    by (destruct Hi as [-> | ->]; vm_compute; reflexivity).
  destruct (find_segment SEGS (VAL (A_OBJ i)) 8) as [sg|] eqn:F; [|discriminate Hs].
  destruct (find_segment_hit _ _ _ _ F) as (Hin & H1 & H2). exists sg. split; [exact Hin | lia].
Qed.
(* alloc.c's statics are image bytes (S1ImgA.v, by computation over image A's segments) *)
Lemma pbu_pst_img : forall a, Exists (in_zr a) (@prh_pst prh_img_A) -> in_img SEGS a.
Proof. exact pst_in_img_A. Qed.
(* the entry: put_utf8's slot of the listing (PAImg_prog.v A_entry_put_utf8) at offset 27524 from BASE *)
Lemma pbu_entry : @pa_sigma _ A_prog_listing PA AS_put_utf8 = BASE + 27524.
Proof. etransitivity; [exact (proj1 A_entry_put_utf8) | vm_compute; reflexivity]. Qed.
(* the frame: put_utf8's own frame (PRH_Img.v pi_frame F_put_utf8) *)
Lemma pbu_frame : 16 <= @STK_put_utf8 prh_img_A.
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Theorem pb_put_utf8X_Ap : tput_utf8_specX (cp := CP) (PI := prh_img_A) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
  unfold tput_utf8_specX. intros ly S Hp W regs mem md ch o cp0 Lam peak cnt fail ran most own [HPRE HRO] H10 H11 Hcp HIN HWD HLG.
  destruct HIN as (a & k & Hak & Hao & Hok).
  pose proof preset_head_wide as HW8.
  pose proof (prh_ledger_blocks (cp := CP) (PI := prh_img_A) (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own HLG) as HF.
  pose proof (proj1 (Forall_forall _ _) HF (a, k) Hak) as (K0 & K1 & K2 & K3 & K4). cbn [fst snd] in K0, K1, K2, K3, K4.
  pose proof HWD as (Hd0 & Hdceil & Hdam & Hdwr & HRA & Hhull).
  rewrite pbu_entry.
  eapply SRr_mono.
  { exact (u8_walk (SK := SK) (PA := PA) B (@prh_pst prh_img_A) ARx LAWS TL pbu_obj_img 27524 ly S Hp W regs mem md ch
      (@STK_put_utf8 prh_img_A) o cp0 (a - @cf_head CP) (k + @cf_head CP) (or_intror eq_refl) HPRE pbu_frame H10 H11
      ltac:(lia) K1 ltac:(lia) ltac:(lia) HRA). }
  intros W' c' _ Hpost.
  exact (u8_to_fpost (cp := CP) (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK LAWS pbu_pst_img preset_head_wide
    (@STK_put_utf8 prh_img_A) regs ly S Hp W mem md ch o cp0 (a - @cf_head CP) (k + @cf_head CP) Lam peak cnt fail ran
    most own W' c' HPRE pbu_frame HLG K1 ltac:(lia) ltac:(lia) ltac:(intros _; lia) Hpost).
Qed.
End t.

(* the statement as the consumer cites it (implicit arguments shown), and its closure *)
Set Printing Implicit.
About pb_put_utf8X_Ap.
Check pb_put_utf8X_Ap.
Unset Printing Implicit.
Print Assumptions pb_put_utf8X_Ap.
