(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ENTRY segment of pj_set's image-A' walk (fuzz_preset asan, A 0x8685c; the cuts of
   lib/A/Prog/pj_setA_defs.v): from the contract's premises (pjsA_pre) at the entry to the cut pjsA_C1 at the
   `jal pj_get` (+0x38), then the C1 segment (pjsA_seg_c1, a premise) to the walk's post pjsA_FIN.
   proves no function (kind: segment lemma).
   The body walked (whole-program listing lib/A/Listing_prog.v, PA := PI_prog_A, engine YC80x / YC1fPx over YCbqG's
   ajournal_x at the caller-window widened window (STK_pj_set dd + d) (sp0 + d), YCbqGcallW.v ajournal_x_init_W):
     +0x00 .. +0x18  frame 48; ra, s0, s1, s2, s3, s4 saved at sp+40, +32, +24, +16, +8, +0;
     +0x1c .. +0x20  s0 := val, s2 := key;
     +0x24 .. +0x2c  the shadow base: the listing's own PHi / PLdHi slots read the .got word (A_OBJ 0) and the cell
                     it names (A_OBJ 12, __asan_shadow_memory_dynamic_address), whose values AR_laws_x's const-cell
                     law gives (alx_const) at the PALib binding of B (cgif's convention, the stand-in PAL below);
     +0x30 .. +0x34  s1 := obj, a1 := key; the run stops at PJSA_C1.
   The frame is the ONLY memory the segment writes, and it lies above the allocator ceiling, so every premise of
   the contract text about the object, the value, the key and the ledger rides to the cut by one keep (pjsn_keep_low).
   The memnorm keep from the entry memory (pjsA_inv's last conjunct) is the runner's memory invariant (YC1fPx.v
   paj_run_to_x_inv at YSRrMemnorm.v srr_inv_laws_imp of srr_inv_laws_memnorm_k). The segment is before any free, so
   it runs plainly under YGcfRhLift.ra_rh_of_SRr and hands C1's SRr' statement its goal by SRr_ret.
   Numerals: 48 / 56 / 40 / 32 / 24 / 16 / 8 (LENGTH: frame, struct, slot offsets); 2 ^ 46 / 2 ^ 47 (LENGTH: the
   stack band); atom indices 2 / 32 (DERIVED: the engine's numbering). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA pj_setA_defs pj_setA_glue pj_setA_steps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_A.

(* the symbolic state at pj_set's entry: its own 48-byte frame below the entry sp (atom 2), the .got slot of the
   shadow-offset cell and the cell (the PALib convention), the shadow offset as atom 32 *)
Definition PJSNA_Bx : sv := SOff 32 0.
Definition PJSNA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pjsnA_regions : smem := [ stack_region 48; got_regionP; bcell_regionP 32 ].
Definition pjsnA_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] A_alias_hints.
Definition ss_pjsnA : sstate := mkSS PJSA_PC sr_atoms pjsnA_regions None pjsnA_facts.

Ltac pjsnA_lits :=
  repeat match goal with
  | |- context [@pa_val ?r A_prog_listing PI_prog_A ?j] =>
    let v := eval vm_compute in (@pa_val r A_prog_listing PI_prog_A j) in
    change (@pa_val r A_prog_listing PI_prog_A j) with v
  | |- context [A_prog_val ?j] =>
    let v := eval vm_compute in (A_prog_val j) in change (A_prog_val j) with v end.

Section ent. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_A.
#[local] Notation PL := PL_prog_A.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* STAND-IN for the unit's image binding of B (the TfibSyms analogue; at the A' instance lib/A/PALibA.v palib_A) *)
Hypothesis PAL : PALib (L := A_prog_listing) (PI := PA) B.

Definition PJSNA_E (regs : bvmap 5 word) : env :=
  Eimg (L := A_prog_listing) (PI := PA) (Ereg regs [Z_to_bv 64 SHADOW_OFF]).

(* every region of this state writes only pj_set's own frame *)
Lemma pjsnA_awr_ok : forall E STK sp0 d FP bl0 blc ly own,
  bv_unsigned (ew E 2) = sp0 -> 48 <= STK -> 0 <= d ->
  awr_ok E pjsnA_regions (STK + d) (sp0 + d) FP bl0 blc ly own.
Proof.
intros E STK sp0 d FP bl0 blc ly own Hsp HS Hd a (r & Hin & Hr).
unfold pjsnA_regions, stack_region, got_regionP, bcell_regionP in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia|lia].
rewrite Hsp in Hr. left. lia.
Qed.

(* what such a run keeps: every byte outside [sp0 - 48, sp0) *)
Lemma pjsnA_frame_keep : forall (Wx : world SEGS) E (m m' : word -> option byte) sp0,
  bv_unsigned (ew E 2) = sp0 ->
  frame_of E pjsnA_regions (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 48 <= a < sp0) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E m m' sp0 Hsp HF a Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). unfold pjsnA_regions, stack_region, got_regionP, bcell_regionP in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia|lia].
rewrite Hsp in Hr. lia.
Qed.

(* a chunk of the state and the value it states *)
Definition pjsnA_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pjsnA_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pjsnA_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pjsnA_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pjsnA_val : forall E ss ms j off (w : N) e v b a, st_ok_pi SEGS VAL E ss ms ->
  pjsnA_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pjsnA_cv_ok E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.


(* ---- the keep: the data of the contract's premises lives below the allocator ceiling, so it rides the prologue ---- *)
Lemma pjsnA_agree : forall (W : world SEGS) m m' (X : Z -> Prop),
  (forall x, X x -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
  mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  pj_agreeR SEGS (mrestrict (w_H W) m) (mrestrict (w_H W) m') X.
Proof.
intros W m m' X HK MG x Hx.
split; [exact (mbyte_of_aview SEGS (w_H W) (w_H W) m m' x (HK x Hx))|].
intros Hw. exact (writable_at_grows SEGS _ _ x MG Hw).
Qed.

(* every block of a ledger list, and every struct the texts place, lies below the ceiling *)
Lemma pjsnA_blk_low : forall ly S Hp W mem md Lam peak cnt fail ran most own a k,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (a, k) Lam -> forall x, a <= x < a + k -> 0 <= x < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k HAR HLED Hin x Hx.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk0 & Hab & _ & _ & _).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hcl & _).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold req_size in Hcl. destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

Theorem pjsA_seg_ent_holds : forall CTX0 dd,
  pjsA_texts B ARx CTX0 dd -> pjsA_seg_c1 B ARx CTX0 dd -> pjsA_seg_entry B ARx CTX0 dd.
Proof.
intros CTX0 dd TXT HC1 en HPRE. pose proof HPRE as HPRE0.
destruct en as [ly S Hp W regs mem md ch d o k w mbs tv D Dw num str kids keys n cap kname Lam peak cnt fail ran most own
  rpx rpos rpi rpH0 rphist].
unfold pjsA_pre in HPRE.
cbn [jsA_ly jsA_S jsA_Hp jsA_W jsA_regs jsA_mem jsA_md jsA_ch jsA_d jsA_o jsA_k jsA_w jsA_ms jsA_tv jsA_D jsA_Dw jsA_num jsA_str
  jsA_kids jsA_keys jsA_n jsA_cap jsA_kname jsA_Lam jsA_peak jsA_cnt jsA_fail jsA_ran jsA_most jsA_own jsA_x jsA_os jsA_i jsA_H0 jsA_hist]
  in HPRE |- *.
set (en := MkPjsEntA ly S Hp W regs mem md ch d o k w mbs tv D Dw num str kids keys n cap kname Lam peak cnt fail ran most own
  rpx rpos rpi rpH0 rphist).
destruct HPRE as (HFPRE & HUNIV & HROOM & HPOS & HLOS & HCONS & H10 & H11 & H12 & HFWIN & HNODE & HHDR & HCAP & HSLOTO &
  HNODEW & HSLOTW & HWC & HDW & HWF & HAP & HDEPO & HDEPV & HCSTR & HKEPT & HKF & HLED & HCNT & HKLEN & HGROW & HLIVE &
  HTBLK & HFORD & HHEAD & HRUN).
pose proof HFPRE as (HAFN & HROD & HSTKHI).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HFWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_segs_low _ A_prog_listing PA) as Hsegs.
set (sp0 := spZ regs) in *.
assert (HSTK48 : 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity). lia. }
(* the value lies below the ceiling (the kit says so); the object may be in the caller's window, so only its memory
   range is known *)
assert (HSTKE : ESTACK + 48 <= STK_pj_set dd).
{ unfold STK_pj_set, zmaxl. cbn [fold_right].
  replace (pi_frame F_pj_set) with 48 by (vm_compute; reflexivity).
  assert (HE : STK_RT_ECALL = ESTACK) by reflexivity. lia. }
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HO4096 : 4096 <= o) by (destruct HSLOTO as (H4096 & _); exact H4096).
assert (HOTOP : o + 56 <= kHighMemEnd)
  by (destruct HSLOTO as (_ & _ & _ & Hamr & _); destruct Hamr as [Hx | (Hx1 & Hx2)]; lia).
assert (HW4096 : 4096 <= w) by (destruct HSLOTW as (H4096 & _); exact H4096).
assert (HWTOPK : w + 56 <= kHighMemEnd)
  by (destruct HSLOTW as (_ & _ & _ & Hamr & _); destruct Hamr as [Hx | (Hx1 & Hx2)]; lia).
assert (HLOWW : w + 56 <= YM05.alloc_ceiling).
{ destruct HSLOTW as (_ & Hat & _).
  destruct Hat as [(a & kk & Hin & Ha & Hk) | [(b & m & Hin & _ & Hb & Hm) | [(cid & pos & Hin & Hf & Hfm) | (Hw1 & Hw2)]]].
  - pose proof (pjsnA_blk_low ly S Hp W mem md Lam peak cnt fail ran most own a kk HAR HLED Hin (w + 55) ltac:(lia)). lia.
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & Hc & _).
    assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia). lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _). lia.
  - exfalso. fold sp0 in Hw1. lia. }
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx (STK_pj_set dd) d (pjsA_FP en) ly S Hp W regs mem md ch
  HAFN HFWIN) as HJ.
remember (PJSNA_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold PJSNA_E; apply Eimg_env).
assert (EL : forall j, (j < A_TEXT)%nat -> ew E j = ew (Ereg regs [Z_to_bv 64 SHADOW_OFF]) j)
  by (intros j Hj; subst E; unfold PJSNA_E; apply Eimg_low; exact Hj).
assert (Er : forall j (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r -> ew E j = getr regs r).
{ intros j r Hj Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ j r Hr). }
assert (E2 : ew E 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (Uimg : forall j, (A_TEXT <= j < A_LIM)%nat -> bv_unsigned (ew E j) = VAL j).
{ intros j Hj. subst E. unfold PJSNA_E. rewrite Eimg_img by exact Hj. apply unsigned_lit_small. apply pa_val_range. }
assert (BV : forall j, (A_TEXT <= j < A_LIM)%nat -> base_val E (Some j) = VAL j)
  by (intros j Hj; cbn [base_val]; apply Uimg; exact Hj).
assert (Dv : forall (j : nat) v, ew E j = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff j 0) = Z_to_bv 64 v).
{ intros j v Hj Hv. cbn [sv_denot]. rewrite Hj, Z.add_0_r, unsigned_lit_small by exact Hv. reflexivity. }
assert (Di : forall j, (A_TEXT <= j < A_LIM)%nat -> sv_denot E (SOff j 0) = Z_to_bv 64 (VAL j)).
{ intros j Hj. cbn [sv_denot]. rewrite Uimg by exact Hj. rewrite Z.add_0_r. reflexivity. }
destruct (alx_const SEGS B ARx LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite (pal_got_shadow B PAL), (pal_cell B PAL) in Kgot. rewrite (pal_cell B PAL) in Kcell.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SHADOW_OFF]) E)
  by (subst E; split; [intros j Hj; unfold PJSNA_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_pjsnA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PJSA_PC)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pjsnA. apply pa_entry_st_ok_full.
  - subst E. unfold PJSNA_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pjsnA_regions, stack_region, got_regionP, bcell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks];
    rewrite ?BV by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros q Hq. apply (apresent_writable SEGS). apply Hpres. lia.
    + pose proof (@pa_val_range _ A_prog_listing PA (A_OBJ 0)). pose proof (@pa_val_range _ A_prog_listing PA (A_OBJ 12)).
      split; [lia|]. split; [pjsnA_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [apply Di; unfold A_OBJ, A_TEXT, A_LIM; lia | lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    + pose proof (@pa_val_range _ A_prog_listing PA (A_OBJ 12)).
      split; [lia|]. split; [pjsnA_lits; lia|]. split; [intros q Hq; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ _ 0 8 (SOff 32 0) SHADOW_OFF);
      [apply Dv; [exact E32 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia | lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
  - apply pairwise_disjoint_of_extents.
    unfold pjsnA_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp.
    rewrite !Uimg by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. pjsnA_lits.
    repeat split; lia.
  - split; [|split; [exact I | apply A_alias_hints_ok; exact HEI]].
    unfold pjsnA_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia. }
assert (SHOK : sh_ok SEGS PJSNA_Bx [] E (mrestrict (w_H W) mem)) by constructor.
clear HE EL.
unfold cfg_at. change (w64 (SIGMA AS_pj_set)) with (Z_to_bv 64 (BASE + PJSA_PC)).
apply YGcfRhLift.ra_rh_of_SRr.
(* the memnorm keep from the entry memory, the runner's memory invariant (YSRrMemnorm.v's instance) *)
pose (PMN := fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m).
pose proof (YSRrMemnorm.srr_inv_laws_imp SEGS _ mem (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)) as PLAW.
fold PMN in PLAW.
assert (HPM : PMN (ms_mem (mkst regs (Z_to_bv 64 (BASE + PJSA_PC)) mem (seg_rom SEGS)))) by (intros h; exact h).
pose (RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL PA B PST ARx hl LAWS PMN PLAW).
(* ---- +0x00 .. +0x34: the frame, the shadow base, the argument moves; stop at the `jal pj_get` ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PJSNA_Bspan PJSA_C1;
  [apply (pjsnA_awr_ok E (STK_pj_set dd) sp0 d); [exact Usp | exact HSTK48 | exact Hd0] |].
clear HF.
pose proof (pjsnA_frame_keep W E mem _ sp0 Usp HFr) as KF. clear HFr.
pmkst HS.
prreg HS (2%bv : bv 5) R2. prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9.
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (18%bv : bv 5) R18.
prreg HS (20%bv : bv 5) R20.
set (m1 := ms_mem ms) in *.
assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m1)) by exact HG.
pose proof (ajx_pres HJ) as HpresJ.
assert (KLOW : forall x, 0 <= x < 2 ^ 64 -> x < YM05.alloc_ceiling ->
  aview SEGS (w_H W) m1 x = aview SEGS (w_H W) mem x).
{ intros x Hx Hc. apply KF; [lia|]. lia. }
assert (KSH : forall p nn, 0 <= p -> p + nn <= kHighMemEnd ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p nn ->
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF p nn).
{ intros p nn Hp0 Hpn HR. eapply range_addressable_agree; [|exact HR]. intros x Hx.
  pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
  apply KLOW; lia. }
assert (KHU : forall p nn, 0 <= p -> 0 < nn -> p + nn <= kHighMemEnd ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p nn -> shadow_hull_vis (aview SEGS (w_H W) m1) p nn).
{ intros p nn Hp0 Hn Hpn HH s Hs.
  assert (Hsb : kLowMemEnd <= s < kHighShadowEnd).
  { unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
    pose proof (Z.div_pos p 8 ltac:(lia) ltac:(lia)).
    assert ((p + nn - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_mod (SHADOW_OFF + p / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + p / 8) 8 ltac:(lia)).
    pose proof (Z.div_mod (SHADOW_OFF + (p + nn - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (SHADOW_OFF + (p + nn - 1) / 8) 8 ltac:(lia)).
    unfold SHADOW_OFF in *. lia. }
  rewrite KLOW by lia. exact (HH s Hs). }
(* the slot facts ride (every byte and its shadow is below the ceiling) *)
assert (KSLOT : forall p, 0 <= p -> p + 56 <= kHighMemEnd ->
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs mem p ->
  prhPj_slot (PA := PA) B (STK_pj_set dd) d ly S Lam W regs m1 p).
{ intros p Hp0 Hlow (H4096 & Hat & Hrw & Hamr & Hown & Hra' & Hhull).
  split; [exact H4096|]. split; [exact Hat|].
  split; [split; [exact (proj1 Hrw)|];
          intros x Hx; exact (writable_at_grows SEGS _ _ x MG (proj2 Hrw x Hx))|].
  split; [exact Hamr|]. split; [exact Hown|].
  split; [apply KSH; [lia | lia | exact Hra'] | apply KHU; [lia | lia | lia | exact Hhull]]. }
(* the tree facts ride *)
assert (KNODE : forall p (t : PjTree.jv) Dl,
  (forall x, pj_footR p Dl x -> aview SEGS (w_H W) m1 x = aview SEGS (w_H W) mem x) ->
  pj_nodeR SEGS (mrestrict (w_H W) mem) (prh_lin Lam) p t Dl ->
  pj_nodeR SEGS (mrestrict (w_H W) m1) (prh_lin Lam) p t Dl).
{ intros p t Dl HX HN. apply (pj_nodeR_frame SEGS t _ _ _ p Dl HN).
  apply (pjsnA_agree W mem m1); [exact HX | exact MG]. }
assert (HFOOTO : forall x, pj_footR o D x -> aview SEGS (w_H W) m1 x = aview SEGS (w_H W) mem x).
{ intros x [Hx | (b & Hin & Hb)].
  - destruct HSLOTO as (_ & _ & _ & _ & Hown & _). destruct (Hown x ltac:(lia)) as (_ & Hns).
    apply KF; [lia|]. lia.
  - destruct b as (a' & k'). unfold pj_holdsR in Hb. cbn [fst snd] in Hb.
    assert (Hlam : In (a', k') Lam)
      by exact (PjsBlkA.pjsbA_node SEGS (PjTree.JObj mbs) (mrestrict (w_H W) mem) (prh_lin Lam) o D HNODE a' k' Hin).
    pose proof (pjsnA_blk_low ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HLED Hlam x Hb).
    apply KF; lia. }
assert (HFOOTW : forall x, pj_footR w Dw x -> aview SEGS (w_H W) m1 x = aview SEGS (w_H W) mem x).
{ intros x [Hx | (b & Hin & Hb)].
  - destruct HSLOTW as (H4096w & _ & _ & _ & _ & _ & _). apply KF; lia.
  - destruct b as (a' & k'). unfold pj_holdsR in Hb. cbn [fst snd] in Hb.
    assert (Hlam : In (a', k') Lam)
      by exact (PjsBlkA.pjsbA_node SEGS tv (mrestrict (w_H W) mem) (prh_lin Lam) w Dw HNODEW a' k' Hin).
    pose proof (pjsnA_blk_low ly S Hp W mem md Lam peak cnt fail ran most own a' k' HAR HLED Hlam x Hb).
    apply KF; lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?md1) _ =>
  assert (HC1P : pjsA_C1 B ARx dd en (ms_regs ms) m1 md1 0); [| apply SRr_ret; exact (HC1 en _ _ _ 0 HPRE0 HC1P)] end.
assert (Ur : forall j (r : bv 5), (j < 32)%nat -> Z.of_nat j = bv_unsigned r ->
  U E (SOff j 0) = bv_unsigned (getr regs r)).
{ intros j r Hj Hr. rewrite U_SOff, (Er j r Hj Hr), Z.add_0_r. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 (getr regs r)) as Rr. unfold bv_modulus in Rr. unfold M64. exact Rr. }
assert (E11 : ew E 11 = Z_to_bv 64 k) by (rewrite (Er 11%nat 11%bv) by (first [lia | reflexivity]); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 w) by (rewrite (Er 12%nat 12%bv) by (first [lia | reflexivity]); exact H12).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (Er 10%nat 10%bv) by (first [lia | reflexivity]); exact H10).
(* the six saved registers, read from the run's own chunks *)
assert (VRA : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48 + 40) 8 (raZ regs)).
{ refine (pjsnA_val E _ _ 2 (-8) 8 (SOff 1 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 1%nat 1%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Rr. unfold bv_modulus in Rr. unfold raZ. cbn in Rr |- *. lia. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48 + 32) 8 (s0Z regs)).
{ refine (pjsnA_val E _ _ 2 (-16) 8 (SOff 8 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 8%nat 8%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Rr. unfold bv_modulus in Rr. unfold s0Z. cbn in Rr |- *. lia. }
assert (VS1 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48 + 24) 8 (bv_unsigned (getr regs 9))).
{ refine (pjsnA_val E _ _ 2 (-24) 8 (SOff 9 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 9%nat 9%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (VS2 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48 + 16) 8 (bv_unsigned (getr regs 18))).
{ refine (pjsnA_val E _ _ 2 (-32) 8 (SOff 18 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 18%nat 18%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (VS3 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48 + 8) 8 (bv_unsigned (getr regs 19))).
{ refine (pjsnA_val E _ _ 2 (-40) 8 (SOff 19 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 19%nat 19%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (VS4 : val_mem SEGS (mrestrict (w_H W) m1) (sp0 - 48) 8 (bv_unsigned (getr regs 20))).
{ refine (pjsnA_val E _ _ 2 (-48) 8 (SOff 20 0) _ sp0 _ HS _ Usp _ _ _ _).
  - vm_compute. reflexivity.
  - lia.
  - exact (Ur 20%nat 20%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Rr. unfold bv_modulus in Rr. cbn in Rr |- *. lia. }
assert (HKPT : forall r, In r PJSA_KEPT -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr.
  exact (regs_kept_of_st_ok_pi (PI := PA) E _ _ regs [Z_to_bv 64 SHADOW_OFF] PJSA_KEPT HS HAE
    ltac:(vm_compute; reflexivity) r Hr). }
subst en. unfold pjsA_C1, pjsA_inv, pjsA_data, jsA_sp1, jsA_sp0, pjsA_FP, PJSA_FR.
cbn [jsA_ly jsA_S jsA_Hp jsA_W jsA_regs jsA_mem jsA_md jsA_ch jsA_d jsA_o jsA_k jsA_w jsA_ms jsA_tv jsA_D jsA_Dw jsA_num jsA_str
  jsA_kids jsA_keys jsA_n jsA_cap jsA_kname jsA_Lam jsA_peak jsA_cnt jsA_fail jsA_ran jsA_most jsA_own jsA_klen].
fold sp0.
split.
{ (* the invariant at C1 *)
  split; [exact HJ|].
  split; [intros a Ha Hfp; apply KF; [lia | lia]|].
  split; [unfold spZ at 1; rewrite R2, Usp, unsigned_lit_small by lia; unfold PJSA_FR; lia|].
  split; [exact VRA|]. split; [exact VS0|]. split; [exact VS1|]. split; [exact VS2|]. split; [exact VS3|].
  split; [replace (sp0 - 48 + 0) with (sp0 - 48) by lia; exact VS4|].
  split; [rewrite R8, E12; reflexivity|].
  split; [rewrite R18, E11; reflexivity|].
  split; [rewrite R20, E32; reflexivity|].
  split; [exact HKPT|].
  split; [intros a Ha; apply HpresJ; lia|].
  split; [|exact HPM].
  intros a Hro Hos Her.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(sg & Hin & _ & Hr) | Hr];
    [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
  pose proof (Hsegs a Hi) as Hlo.
  rewrite KLOW by lia. exact (HROD a Hro Hos Her). }
split.
{ (* the data at C1 *)
  split; [exact HROOM|].
  split; [exact (KSLOT o ltac:(lia) ltac:(lia) HSLOTO)|].
  split; [exact (KSLOT w ltac:(lia) ltac:(lia) HSLOTW)|].
  split.
  { (* the key's C string *)
    pose proof (fun a => cstr_ok_tail_lt (PA := PA) W mem k kname a HCSTR) as HTAIL.
    destruct HCSTR as ((Hg & Hnz) & H4096 & Hceilk & H32b & Hamr8 & Hra' & Hhull & Hv).
    split; [split; [|exact Hnz]|].
    - intros j Hj. destruct (Hg j Hj) as [Hval Hrng]. split; [|exact Hrng].
      intros kk Hkk. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) mem m1 _
        (KLOW (k + Z.of_nat j + Z.of_nat kk) ltac:(rewrite length_app in Hj; cbn [length] in Hj; lia)
              ltac:(rewrite length_app in Hj; cbn [length] in Hj; lia))).
      exact (Hval kk Hkk).
    - split; [exact H4096|]. split; [exact Hceilk|]. split; [exact H32b|]. split; [exact Hamr8|].
      split; [apply KSH; [lia | lia | exact Hra']|].
      split; [apply KHU; [lia | lia | lia | exact Hhull]|].
      intros a Ha. pose proof (HTAIL a Ha) as Hab. rewrite KLOW by lia. exact (Hv a Ha). }
  split; [exact HKEPT|].
  (* the ledger: the statics and every head word are kept *)
  apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W m1 Lam peak cnt fail ran most own HLED).
  - intros a Ha. pose proof (pst_in_img_A a Ha) as Hi. pose proof (Hsegs a Hi) as Hlo. apply KLOW; lia.
  - intros a kk i Hin Hi.
    destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a kk most own HLED Hin)
      as (Hk0 & Hab & _ & _ & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (Hal & H4096 & Hcl & _).
    pose proof (@cf_head_nonneg cp) as Hh0.
    assert (Hreq : a - cf_head + 1 <= YM05.alloc_ceiling)
      by (unfold req_size in Hcl; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    apply KF; lia.
  - intros a kk _ H. exact H.
  - apply Permutation_refl. }
split; [rewrite R10, E10; reflexivity|].
split; [rewrite R11, E11; reflexivity|].
split; [rewrite R9, E10; reflexivity|].
split; [exact (KNODE o (PjTree.JObj mbs) D HFOOTO HNODE)|].
split.
{ apply (pj_hdrR_frame SEGS (mrestrict (w_H W) mem)); [exact HHDR|].
  apply (pjsnA_agree W mem m1); [intros x Hx; apply HFOOTO; left; exact Hx | exact MG]. }
split; [exact (KNODE w tv Dw HFOOTW HNODEW)|].
(* the object's footprint and val's read as at the entry *)
split; [exact (pjsnA_agree W mem m1 (pj_footR o D) HFOOTO MG)|].
exact (pjsnA_agree W mem m1 (pj_footR w Dw) HFOOTW MG).
Qed.
End ent.
