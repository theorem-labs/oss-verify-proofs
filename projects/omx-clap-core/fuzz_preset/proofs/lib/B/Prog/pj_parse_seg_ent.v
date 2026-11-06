(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: pj_parse of fuzz_preset's asan-ubsan image (B 0x862ec; preset_file.c :296-309), the ENTRY
   segment of the walk cut in lib/B/Prog/pj_parse_defs.v: from the kit's premises (pjp_pre, the record of the kit's
   tpj_parse_specX premises) at the entry to the cut pjp_C1 at the `jal parse_value` (+0x4c), then the C1 segment
   (pjp_seg_C1, a premise of the theorem) to the kit's post pjp_FIN.
   proves no function (kind: segment lemma): pjp_seg_entry_holds is pjp_seg_entry from pjp_texts and pjp_seg_C1.
   The body walked (whole-program listing lib/B/Listing_prog.v, PA := PI_prog_B, engine YC80x / YC1fPx over YCbqG's
   ajournal_x at the caller-window widened window (STK_pj_parse + d) (sp0 + d), YCbqGcallW.v ajournal_x_init_W):
     +0x00 .. +0x10  frame 48, ra / s0 / t0 saved at sp+40 / sp+32 / sp+8, a1 := t0 + len; the engine stops at the
                     UBSan PTR-OVF `bltu a1, a0` (+0x14), whose taken arm src_rd refutes (t0 + len < 2 ^ 64);
     +0x18 .. +0x3c  s0 := out; the engine itself decides the UBSan NULL `beqz` (+0x28: t0 >= 4096 by the atom fact,
                     t0 + len >= t0 by the branch's condition); end at sp+16, depth 0 at sp+24, the memset arguments;
     +0x40           memset (out, 0, 56) by YGcallMxmn.v aj_intrin_at_xm_fr (out: a live non-harness allocator block
                     or a fake frame of S, prhReader_at with the kit's apartness from the harness blocks), from pjp_texts'
                     __asan_memset text (aintrin_realizes_xm: with the memnorm keep);
     +0x44 .. +0x48  a0 := sp + 8, a1 := out; the run stops at PJP_C1.
   The frame region is written only over [sp0 - 40, sp0): pj_parse never writes its slot at sp1 = sp0 - 48, so the
   entry word there (whose parse_string free trace is in CW by pjp_pre's prh_cw_pj, the kit's PRH_Base.v :1521-1527) is
   pjp_C1's. The cursor's shadow at C1 is the real stack's (YCbqG.v alx_zshadow_byte at the journal's allocator
   state).
   The memory overlay's normal form (the kit's entry premise YAkMemnorm.memnorm) rides along both engine stretches by the
   runners' memnorm twins (YC1fPx.v paj_run_x_inv / paj_run_to_x_inv at P := YAkMemnorm.memnorm SEGS, laws
   YSRrMemnorm.srr_inv_laws_memnorm_k) and across the memset by its keep, to pjp_C1's pjp_inv.
   THE RE-HIDING MOVE: the C1 segment concludes SRr' SEGS RZ_cf (parse_value's text does), so this plain SRr run is
   lifted once at the entry (YGcfRhLift.ra_rh_of_SRr) and hands its continuation to pjp_seg_C1 at the cut. The text's
   hull budget (pjp_pre's last conjunct) is not read before the cut.
   Numerals: 48 / 40 / 32 / 24 / 16 / 8 / 56 (LENGTH: frame, slots, struct sizes, granule); -8 .. -40 (LENGTH: frame
   slot offsets from the entry sp); 4096 / 4144 (LENGTH: page, ESTACK + frame); 2 ^ 44 / 2 ^ 46 / 2 ^ 47 (LENGTH: shadow
   span, stack band); 33 (DERIVED: the first atom after the registers and the shadow-base atom). No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_Charge PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnPj PRH_FnParse.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB pj_parse_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance prh_img_B.

(* the symbolic state at pj_parse's entry: its own frame of PJP_FR = 48 bytes below the entry sp (atom 2), read over
   [sp0 - 48, sp0) and written only over [sp0 - 40, sp0) (the slot at sp0 - 48 is never written); the text pointer
   t0 (atom 10) and its length (atom 11) in the ranges the text's premises give *)
Definition PJE_Bx : sv := SOff 32 0.
Definition PJE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition pje_frame : YP09.region := YP09.mkRegion (Some 2%nat) (- PJP_FR) 0 (- PJP_FR + 8) 0 [].
Definition pje_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47) 0); (11%nat, mkAF 0 (2 ^ 47) 0)] [] [].
Definition ss_pje : sstate := mkSS PJP_PC sr_atoms [pje_frame] None pje_facts.

(* the shadow hull of an application range below kHighMemEnd lies in the shadow region [kLowMemEnd, kHighShadowEnd)
   (FuzzStrdupB.v sd_hull_low's arithmetic, at the region's own ends) *)
Lemma pje_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= kHighMemEnd ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowMemEnd <= s < kHighShadowEnd.
Proof.
intros x n s H0 Hn Hx Hs. unfold shadow_addr, kLowMemEnd, kHighShadowEnd, kHighMemEnd, SHADOW_OFF in *.
pose proof (Z.div_pos x 8 H0 ltac:(lia)) as P1.
assert (P3 : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
pose proof (Z.div_mod (SHADOW_OFF + x / 8) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (SHADOW_OFF + x / 8) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia)) as M2.
unfold SHADOW_OFF in *.
lia.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Notation PA := PI_prog_B.
#[local] Notation PL := PL_prog_B.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_B)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable HL : Z.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
Definition PJE_E (regs : bvmap 5 word) : env := @Eimg _ B_prog_listing PA (Ereg regs []).

(* every region of a stretch's start state is pj_parse's frame window: base atom 2 (the entry sp), written over
   [sp0 - 40, sp0) *)
Definition pje_rs (rs : smem) : Prop :=
  forall r, In r rs -> r_base r = Some 2%nat /\ r_wlo r = - PJP_FR + 8 /\ r_whi r = 0.
Ltac pje_rs_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr; repeat (destruct Hr as [<- | Hr]; [repeat split; reflexivity |]); destruct Hr.
(* the write permission of such a stretch: it writes only its own frame, inside the widened window *)
Lemma pje_awr_ok : forall E rs STK sp0 d FP bl0 blc ly own,
  pje_rs rs -> bv_unsigned (ew E 2) = sp0 -> PJP_FR <= STK -> 0 <= d ->
  awr_ok E rs (STK + d) (sp0 + d) FP bl0 blc ly own.
Proof.
intros E rs STK sp0 d FP bl0 blc ly own Hrs Hsp HS Hd a (r & Hin & Hr). destruct (Hrs r Hin) as (Hb & Hl & Hh).
rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. unfold PJP_FR in *. left. lia.
Qed.
(* what such a stretch keeps: every byte outside [sp0 - 40, sp0) (YC1fP's frame_of over the stretch's regions) *)
Lemma pje_frame_keep : forall (Wx : world SEGS) E rs (m m' : word -> option byte) sp0,
  pje_rs rs -> bv_unsigned (ew E 2) = sp0 ->
  frame_of E rs (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - PJP_FR + 8 <= a < sp0) -> aview SEGS (w_H Wx) m' a = aview SEGS (w_H Wx) m a.
Proof.
intros Wx E rs m m' sp0 Hrs Hsp HF a Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia.
intros (r & Hin & Hr). destruct (Hrs r Hin) as (Hb & Hl & Hh).
rewrite Hb, Hl, Hh in Hr. cbn [base_val] in Hr. rewrite Hsp in Hr. lia.
Qed.
(* FuzzMalloc.v (lib/A/Prog) fm_U_add, as PvB_A.v pva_U_add *)
Lemma pje_U_add : forall E a b, U E (SAlu ALU_ADD a b) = (U E a + U E b) mod 2 ^ 64.
Proof. intros E a b. rewrite U_SAlu. cbn [zalu_raw]. unfold zcanon, M64. reflexivity. Qed.

(* a chunk of a symbolic state and the bytes it states (PvB_A.v pva_cv / pva_cv_ok / pva_val, at st_ok_pi) *)
Definition pje_cv (rs : smem) (j : nat) (off w : Z) : option YP09.chunk :=
  match find_region rs (Some j) off w with Some r => find_chunk (YP09.r_chunks r) off w | None => None end.
Lemma pje_cv_ok : forall E ss ms j off w c, st_ok SEGS E ss ms -> pje_cv (ss_mem ss) j off w = Some c ->
  YP09.chunk_ok SEGS E (ms_mem ms) (bv_unsigned (ew E j)) c.
Proof.
intros E ss ms j off w c HS H. unfold pje_cv in H.
destruct (find_region (ss_mem ss) (Some j) off w) as [r|] eqn:Hr; [|discriminate H].
destruct (find_region_sound _ _ _ _ _ Hr) as (Hin & Hb & _).
destruct (find_chunk_sound _ _ _ _ H) as (Hcin & _).
destruct (st_ok_mem_ok SEGS E ss ms HS) as (_ & Hrs & _).
destruct (proj1 (Forall_forall _ _) Hrs r Hin) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hcin) as Hck. rewrite Hb in Hck. exact Hck.
Qed.
Lemma pje_val : forall E ss ms j off (w : N) e v b a, st_ok_pi SEGS VAL E ss ms ->
  pje_cv (ss_mem ss) j off (Z.of_N w) = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E j) = b -> a = b + off -> U E e = v -> Z.of_N w <= 8 -> 0 <= v < 2 ^ (8 * Z.of_N w) ->
  val_mem SEGS (ms_mem ms) a (N.to_nat w) v.
Proof.
intros E ss ms j off w e v b a HS H Hb Ha HU Hw Hv. subst a.
pose proof (pje_cv_ok E (abs_ss VAL ss) ms j off (Z.of_N w) _ HS H) as Hck. rewrite Hb in Hck.
apply (val_of_chunk_ok SEGS E _ _ off w e v Hck); [|exact Hv | exact Hw].
rewrite <- HU. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* bytes and words ride through a change that keeps their views (PvB_A.v pva_val_keep / pva_garr8_keep) *)
Lemma pje_val_keep : forall (W W' : world SEGS) m m' a (n : nat) v, val_mem SEGS (mrestrict (w_H W) m) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hv Hk k Hkn. rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)).
- exact (Hv k Hkn).
- apply Hk. lia.
Qed.
Lemma pje_garr8_keep : forall (W W' : world SEGS) m m' a l, garr8 SEGS (mrestrict (w_H W) m) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (mrestrict (w_H W') m') a l.
Proof.
intros W W' m m' a l Hg Hk j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (pje_val_keep W W' m m' _ 1 _ Hv). intros x Hx. apply Hk. cbn [Z.of_nat] in Hx. lia.
Qed.
(* a byte the view shows, as a one-byte value, and a byte array from the bytes the view shows *)
Lemma pje_val1_of_aview : forall H m a v, aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv k Hk. assert (Ek : k = 0%nat) by lia. subst k.
replace (a + Z.of_nat 0) with a by lia.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|]; cbn [option_map] in Hv; [|discriminate Hv].
injection Hv as <-. pose proof (bv_unsigned_in_range 8 b) as Rb. unfold bv_modulus in Rb.
rewrite YI04.le_byte_small by (cbn in Rb |- *; lia). cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned.
reflexivity.
Qed.
Lemma pje_garr8_of_aview : forall H m p l, Forall (fun x => 0 <= x < 256) l ->
  (forall j, (j < length l)%nat -> aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 SEGS (mrestrict H m) p l.
Proof.
intros H m p l Hl Hv j Hj. split.
- apply pje_val1_of_aview. exact (Hv j Hj).
- apply (proj1 (Forall_forall _ _) Hl). apply nth_In. exact Hj.
Qed.
(* a zero word read at a narrower width *)
Lemma pje_val_zero : forall m a (n n' : nat), (n' <= n)%nat -> val_mem SEGS m a n 0 -> val_mem SEGS m a n' 0.
Proof.
intros m a n n' Hn H k Hk. rewrite (H k ltac:(lia)). f_equal.
all: try (lazymatch goal with |- ?f _ _ _ = ?g _ _ _ => unfold f, g end;
  rewrite !Zmod_0_l, !Z.shiftr_0_l, !Zmod_0_l; reflexivity).
Qed.
(* a word read through a view that agrees on its eight bytes *)
Lemma pje_rdword_eq : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* the memory only grows when every present byte stays present *)
Lemma pje_grows_of_apresent : forall (H : word -> bool) m m',
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' Hp x Hx. unfold mrestrict in *. destruct (H x) eqn:Ehx; [exact Hx|].
destruct (m x) as [b|] eqn:Em; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (unfold apresent; rewrite Z_to_bv_bv_unsigned; split; [exact Ehx | exists b; exact Em]).
destruct (Hp _ Ha) as [_ [b' Hb']]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.

Theorem pjp_seg_entry_holds : forall CTX0 CW,
  pjp_texts (SK := SK) B ARx CTX0 CW -> pjp_seg_C1 (SK := SK) B ARx CTX0 CW -> pjp_seg_entry (SK := SK) B ARx CTX0 CW.
Proof.
intros CTX0 CW HTX HC1 en HPRE. pose proof HPRE as HPRE0.
destruct HTX as (_ & _ & _ & AMSET).
destruct en as [ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran most own].
unfold pjp_pre in HPRE.
cbn [je_ly je_S je_Hp je_W je_regs je_mem je_md je_ch je_d je_t0 je_len je_out je_tl je_Lam je_peak je_cnt je_fail
  je_ran je_most je_own] in HPRE |- *.
set (en := MkPjpEnt ly S Hp W regs mem md ch d t0 len out tl Lam peak cnt fail ran most own).
destruct HPRE as (HFPRE & HUNIV & HCWpj & HWROOM & HROOM & HFRM & H10 & H11 & H12 & Hlen & HSRC & HHOME &
  HMAXRUN & HWIN & HSLOT & HOUTC & HLAMD & HTXT & HLED & HCNT & HRQ & HLIVE & HFRB & HMN0 & HPKS & HPK24 & HTCEIL &
  HRQM & _).
(* The kit's cursor set at the entry, by name: the parse_string arm (the slot word) is what the C1 cut carries *)
unfold prh_cw_pj in HCWpj. destruct HCWpj as (_ & HCWslot).
pose proof HFPRE as (HAFN & HROD & HSTK64 & HRA64 & HFZ64).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof HSLOT as (Hout4096 & Hat & Hrw & Hamr & Hown & Hora & Hohull).
pose proof HSRC as (Hbytes & Ht4096 & Htceil & Htamr & Htra & Hthull).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFR48 : pi_frame F_pj_parse = 48) by (vm_compute; reflexivity).
assert (HSTK : 4144 <= STK_pj_parse) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
set (sp0 := spZ regs) in *.
assert (Hlen0 : 0 <= len) by lia.
(* out's place (prhReader_at): not a harness block (the kit's apartness premise), not the caller window (out is below
   alloc_ceiling), so a live allocator block that is not a harness block, or a fake frame of S *)
assert (Hplace : (exists b m, In (b, m) (ablocks B ly S) /\ ~ In (b + cf_head, m - cf_head) Lam /\ b <= out /\
    out + 56 <= b + m) \/
  (exists cid pos, In (cid, pos) (frames S) /\ frame_addr ly cid pos <= out /\
    out + 56 <= frame_addr ly cid pos + fs_frame_bytes cid)).
{ destruct Hat as [(a & k & Hin & Ha & Hk) | [Hb | [Hf | (Hw1 & Hw2)]]].
  - exfalso. destruct (HLAMD a k Hin); lia.
  - left; exact Hb.
  - right; exact Hf.
  - exfalso. fold sp0 in Hw1. lia. }
assert (Hout56 : out + 56 <= YM05.alloc_ceiling /\ (forall a, out <= a < out + 56 -> ~ in_img SEGS a)).
{ destruct Hplace as [(b & m & Hin & _ & Hb & Hm) | (cid & pos & Hin & Hf & Hfm)].
  - destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & Hc & _).
    assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
    rewrite Hrq in Hc. split; [lia|]. intros a Ha.
    apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md b m a HAR Hin). rewrite Hrq. lia.
  - destruct (frames_bounds_x SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Hc & _).
    split; [lia|]. intros a Ha. apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos a HAR Hin). lia. }
destruct Hout56 as (Hout56 & Hout_img).
pose proof (ajournal_x_init_W (SK := SK) SEGS B PST ARx STK_pj_parse d [(out, out + 56)] ly S Hp W regs mem md ch
  HAFN HWIN) as HJ.
remember (PJE_E regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold PJE_E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; subst E; unfold PJE_E; apply Eimg_low; exact Hn).
assert (Er : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn Hr. rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr). }
assert (E2 : ew E 2 = getr regs 2) by (apply Er; [lia | reflexivity]).
assert (E10 : ew E 10 = Z_to_bv 64 t0) by (rewrite (Er 10%nat 10%bv) by (first [lia | reflexivity]); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 len) by (rewrite (Er 11%nat 11%bv) by (first [lia | reflexivity]); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 out) by (rewrite (Er 12%nat 12%bv) by (first [lia | reflexivity]); exact H12).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E ss_pje
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + PJP_PC)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pje. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, pje_frame, PJP_FR.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  - cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  - split; [|split; [exact I | exact I]].
    cbn [pje_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E10, E11, !unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; first [exact Hal16 | lia]. }
assert (SHOK : sh_ok SEGS PJE_Bx [] E (mrestrict (w_H W) mem)) by constructor.
clear HE EL.
(* the run to the cut is plain SRr: lifted once into SRr' SEGS RZ_cf, the relation of the C1 segment *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS YGcfRehidePost.RZ_cf).
unfold cfg_at. change (w64 (SIGMA AS_pj_parse)) with (Z_to_bv 64 (BASE + PJP_PC)).
pose (RUN := @paj_run_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTO := @paj_run_to_x_inv fx rc SK B_prog_listing PL PA B PST ARx HL LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
(* the memory overlay's normal form at the entry machine state (the kit's premise), the runners' invariant *)
pose proof HMN0 as HPM.
pose (BR := @paj_branch fx rc B_prog_listing PA).
assert (HFRle : PJP_FR <= STK_pj_parse) by (unfold PJP_FR; lia).
(* ---- +0x00 .. +0x10: the frame, ra / s0 / t0 saved, a1 := t0 + len; stop at the PTR-OVF check ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PJE_Bspan; [apply (pje_awr_ok E _ STK_pj_parse sp0 d); [pje_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
clear HF. rename HG into G1.
pose proof (fun Hrs => pje_frame_keep W E _ mem _ sp0 Hrs Usp HFr) as K1. specialize (K1 ltac:(pje_rs_tac)). clear HFr.
psrr_branch_tok RUN BR HS SHOK PJE_Bspan.
{ (* +0x14 `bltu a1, a0` taken: t0 + len would wrap below t0; src_rd bounds it *)
  exfalso. rewrite branch_ltu_U, pje_U_add, (U_atom E 10 t0 E10), (U_atom E 11 len E11) in Hc by lia.
  apply Z.ltb_lt in Hc. rewrite Z.mod_small in Hc by lia. lia. }
(* ---- +0x18 .. +0x3c: s0 := out, the nullness xor (the engine decides the NULL check: t0 >= 4096), end at sp+16,
   depth 0 at sp+24, the memset arguments; stop at `jal __asan_memset` ---- *)
paj_run_tok_x_inv RUN HS HJ SHOK HPM PJE_Bspan; [apply (pje_awr_ok E _ STK_pj_parse sp0 d); [pje_rs_tac | exact Usp | exact HFRle | exact Hd0] |].
clear HF. rename HG into G2.
pose proof (fun Hrs => pje_frame_keep W E _ _ _ sp0 Hrs Usp HFr) as K2. specialize (K2 ltac:(pje_rs_tac)). clear HFr.
pmkst HS.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
assert (Hsp1 : spZ (ms_regs ms0) = sp0 + d + (- PJP_FR - d)).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by lia. unfold PJP_FR. lia. }
(* ---- +0x40: memset (out, 0, 56) into out's block or caller fake frame (YGcallMxmn.v aj_intrin_at_xm_fr) ---- *)
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  eapply (YGcallMxmn.aj_intrin_at_xm_fr (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ _ PA) OSet (SIGMA AS___asan_memset)
    AMSET W rT mT (STK_pj_parse + d) (sp0 + d) [(out, out + 56)] ly S Hp W mem md [] ly S Hp _ 0 out 0 56 (- PJP_FR - d) _ HJ)
  end.
  - rewrite Q10, E12. reflexivity.
  - rewrite Q11. reflexivity.
  - rewrite Q12. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Hsp1.
  - unfold PJP_FR. lia.
  - unfold PJP_FR. lia.
  - rewrite Hes. unfold PJP_FR. lia.
  - rewrite Q3, (Er 3%nat 3%bv) by (first [lia | reflexivity]). exact Hgp.
  - rewrite Q4, (Er 4%nat 4%bv) by (first [lia | reflexivity]). exact Htp.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
  - intros a Ha. split.
    + destruct Hplace as [(b & m & Hin & _ & Hb & Hm) | (cid & pos & Hin & Hf & Hfm)].
      * left. right. left. split; [exists (out, out + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists b, m. split; [exact Hin|]. unfold req_size; destruct (Z.eqb_spec m 0); lia.
      * right. split; [exists (out, out + 56); split; [left; reflexivity | cbn [fst snd]; lia]|].
        exists cid, pos. split; [exact Hin|]. unfold in_zr, frame_rng; cbn [fst snd]. lia.
    + rewrite Hes. unfold PJP_FR. lia.
  - exact Hamr.
  - eapply range_addressable_agree; [|exact Hora]. intros x Hx.
    pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr.
    rewrite K2, K1 by (unfold PJP_FR; lia). reflexivity.
  - intros _ s Hs. pose proof (pje_hull_bounds out 56 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as Hsb.
    rewrite K2, K1 by (unfold PJP_FR; lia). exact (Hohull s Hs).
  - exact I. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Ha04 & Heff & Hfr4 & Hpres4 & HMK4).
(* the memory overlay after the memset: its keep *)
assert (HPM4 : YAkMemnorm.memnorm SEGS mem4) by (apply HMK4; exact HPM). clear HPM HMK4.
cbv beta iota in Heff.
pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4J & _).
jafter_call_keep_pi HS 33%nat regs4 (mrestrict (w_H W) mem4) HP4 [0]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
{ constructor; [|apply Forall_nil]. split.
  - intros a Ha. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha. rewrite Usp in Ha.
    apply (mbyte_of_aview SEGS). apply Hfr4; [lia | lia | rewrite Hes; unfold PJP_FR; lia].
  - intros a Ha _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    apply (apresent_writable SEGS). apply Hpres4J. unfold PJP_FR in *; lia. }
specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
remember (havoc E 33 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HSX.
assert (HIM4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD4 : forall n, (n < 33)%nat -> ew E4 n = ew E n) by (intros n Hn; rewrite HE4; apply ew_havoc_old; exact Hn).
assert (HAE4 : env_agree 32 (Ereg regs []) E4) by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE4.
assert (Usp4 : bv_unsigned (ew E4 2) = sp0) by (rewrite OLD4 by (cbv; lia); exact Usp).
assert (SHOK4 : sh_ok SEGS PJE_Bx [] E4 (mrestrict (w_H W) mem4)) by constructor.
clear HS HJ SHOK. rename HSX into HS. rename HJ4 into HJ. rename SHOK4 into SHOK.
rename HPM4 into HPM.
(* ---- +0x44 .. +0x48: a0 := sp + 8, a1 := out; stop at the `jal parse_value` (PJP_C1) ---- *)
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM PJE_Bspan PJP_C1;
  [apply (pje_awr_ok E4 _ STK_pj_parse sp0 d); [pje_rs_tac | exact Usp4 | exact HFRle | exact Hd0] |].
clear HF. rename HG into G5.
pose proof (fun Hrs => pje_frame_keep W E4 _ _ _ sp0 Hrs Usp4 HFr) as K5. specialize (K5 ltac:(pje_rs_tac)). clear HFr.
pmkst HS.
prreg HS (8%bv : bv 5) R8. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (2%bv : bv 5) R2.
pose proof HJ as (HARJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (E4_10 : ew E4 10 = Z_to_bv 64 t0) by (rewrite OLD4 by (cbv; lia); exact E10).
assert (E4_11 : ew E4 11 = Z_to_bv 64 len) by (rewrite OLD4 by (cbv; lia); exact E11).
assert (E4_12 : ew E4 12 = Z_to_bv 64 out) by (rewrite OLD4 by (cbv; lia); exact E12).
assert (U4r : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> U E4 (SOff n 0) = bv_unsigned (getr regs r)).
{ intros n r Hn Hr. rewrite U_SOff, OLD4, (Er n r Hn Hr), Z.add_0_r by lia. apply zcanon_id.
  pose proof (bv_unsigned_in_range 64 (getr regs r)) as Rr. unfold bv_modulus in Rr. unfold M64. exact Rr. }
(* ---- the memory at C1 against the entry's ---- *)
set (m5 := ms_mem ms1) in *.
assert (MG : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) m5)).
{ pose proof (pje_grows_of_apresent (w_H W) _ _ Hpres4) as G4. intros x Hx. apply G5, G4, G2, G1, Hx. }
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (out <= a < out + 56) -> ~ (sp0 - PJP_FR - ESTACK <= a < sp0) ->
  aview SEGS (w_H W) m5 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1 H2. rewrite K5, Hfr4, K2, K1 by (rewrite ?Hes in *; unfold PJP_FR in *; lia). reflexivity. }
assert (KSLOT : forall i, 0 <= i < 8 -> aview SEGS (w_H W) m5 (sp0 - PJP_FR + i) = aview SEGS (w_H W) mem (sp0 - PJP_FR + i)).
{ intros i Hi. rewrite K5, Hfr4, K2, K1 by (rewrite ?Hes in *; unfold PJP_FR in *; lia). reflexivity. }
assert (KZERO : forall i, 0 <= i < 56 -> aview SEGS (w_H W) m5 (out + i) = Some 0).
{ intros i Hi. rewrite K5, Heff by (unfold PJP_FR in *; lia). reflexivity. }
assert (KSH : forall s, kLowMemEnd <= s < kHighShadowEnd -> aview SEGS (w_H W) m5 s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply KALL; [lia | | rewrite Hes; unfold PJP_FR; lia]. intros Ho. unfold amem_range in Hamr. lia. }
assert (KRA : forall p n, 0 <= p -> p + n <= kHighMemEnd ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF p n -> range_addressable (aview SEGS (w_H W) m5) SHADOW_OFF p n).
{ intros p n Hp0 Hpn H. eapply range_addressable_agree; [|exact H]. intros x Hx.
  pose proof (shadow_addr_bounds x ltac:(lia)) as Hsx. unfold shadow_addr in Hsx. unfold shadow_of_addr. apply KSH. exact Hsx. }
assert (KHU : forall p n, 0 <= p -> 0 < n -> p + n <= kHighMemEnd ->
  shadow_hull_vis (aview SEGS (w_H W) mem) p n -> shadow_hull_vis (aview SEGS (w_H W) m5) p n).
{ intros p n Hp0 Hn Hpn H s Hs. rewrite KSH by exact (pje_hull_bounds p n s Hp0 Hn Hpn Hs). exact (H s Hs). }
assert (KTXT : forall x, t0 <= x < t0 + Z.of_nat (length tl) -> aview SEGS (w_H W) m5 x = aview SEGS (w_H W) mem x).
{ intros x Hx. apply KALL; [lia | lia | rewrite Hes; unfold PJP_FR; lia]. }
(* ---- the frame words the run wrote (the engine's chunks of the frame region) ---- *)
assert (VRA : val_mem SEGS (mrestrict (w_H W) m5) (sp0 - PJP_FR + 40) 8 (raZ regs)).
{ refine (pje_val E4 _ _ 2 (-8) 8 (SOff 1 0) _ sp0 _ HS _ Usp4 _ _ _ _).
  - vm_compute. reflexivity.
  - unfold PJP_FR. lia.
  - exact (U4r 1%nat 1%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Rr. unfold bv_modulus in Rr. unfold raZ. cbn in Rr |- *. lia. }
assert (VS0 : val_mem SEGS (mrestrict (w_H W) m5) (sp0 - PJP_FR + 32) 8 (s0Z regs)).
{ refine (pje_val E4 _ _ 2 (-16) 8 (SOff 8 0) _ sp0 _ HS _ Usp4 _ _ _ _).
  - vm_compute. reflexivity.
  - unfold PJP_FR. lia.
  - exact (U4r 8%nat 8%bv ltac:(lia) eq_refl).
  - lia.
  - pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Rr. unfold bv_modulus in Rr. unfold s0Z. cbn in Rr |- *. lia. }
assert (VP : val_mem SEGS (mrestrict (w_H W) m5) (sp0 - PJP_FR + 8) 8 t0).
{ refine (pje_val E4 _ _ 2 (-40) 8 (SOff 10 0) _ sp0 _ HS _ Usp4 _ _ _ _).
  - vm_compute. reflexivity.
  - unfold PJP_FR. lia.
  - apply (U_atom E4 10 t0 E4_10). lia.
  - lia.
  - cbn. lia. }
assert (VEND : val_mem SEGS (mrestrict (w_H W) m5) (sp0 - PJP_FR + 8 + 8) 8 (t0 + len)).
{ refine (pje_val E4 _ _ 2 (-32) 8 (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) _ sp0 _ HS _ Usp4 _ _ _ _).
  - vm_compute. reflexivity.
  - unfold PJP_FR. lia.
  - rewrite pje_U_add, (U_atom E4 10 t0 E4_10), (U_atom E4 11 len E4_11) by lia. apply Z.mod_small. lia.
  - lia.
  - cbn. lia. }
assert (VDEP : val_mem SEGS (mrestrict (w_H W) m5) (sp0 - PJP_FR + 8 + 16) 4 0).
{ apply (pje_val_zero _ _ 8 4 ltac:(lia)).
  refine (pje_val E4 _ _ 2 (-24) 8 (SLit 0) _ sp0 _ HS _ Usp4 _ _ _ _).
  - vm_compute. reflexivity.
  - unfold PJP_FR. lia.
  - rewrite U_SLit. reflexivity.
  - lia.
  - cbn. lia. }
assert (HKEPT : forall r, In r PJP_KEPT -> getr (ms_regs ms1) r = getr regs r).
{ intros r Hr. unfold PJP_KEPT in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ ?r = _ =>
        let Rr := fresh "Rr" in prreg HS r Rr; rewrite Rr, OLD4 by (cbv; lia);
        rewrite (Er _ r) by (first [lia | reflexivity]); reflexivity end |]).
  destruct Hr. }
apply SRr_ret. cbv beta.
lazymatch goal with |- SRr' _ _ _ (mkCfg _ ?md5) _ =>
  assert (HC1P : pjp_C1 (SK := SK) B ARx CW en (ms_regs ms1) m5 md5 0); [| exact (HC1 en _ _ _ 0 HPRE0 HC1P)] end.
subst en. unfold pjp_C1, pjp_inv, pjp_cursor, pjp_out_ok, pjp_text_ok, pj_in_okR, je_sp1, je_sp0.
cbn [je_ly je_S je_Hp je_W je_regs je_mem je_md je_ch je_d je_t0 je_len je_out je_tl je_Lam je_peak je_cnt je_fail
  je_ran je_most je_own]. fold sp0.
split.
{ (* pjp_inv at C1 *)
  split; [exact HFRM|]. split; [intros r Hr; reflexivity|]. split; [exact HJ|].
  split; [intros a Ha; apply KALL; [lia | lia | rewrite Hes; unfold PJP_FR in *; lia]|].
  split; [unfold spZ at 1; rewrite R2, Usp4, unsigned_lit_small by lia; unfold PJP_FR; lia|].
  split; [exact VRA|]. split; [exact VS0|].
  split; [rewrite R8, E4_12; reflexivity|].
  split; [exact HKEPT|].
  split; [intros a Ha; apply HpresJ; unfold PJP_FR in *; lia|].
  split.
  - (* the cursor's shadow: real stack below sp0 (YCbqG's stack-shadow law alx_zshadow_byte at the C1 state) *)
    intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W m5 _ x HARJ). unfold PJP_FR in *. lia.
  - split; [|exact HPM]. intros a Hro Hno Herr.
    assert (Hi : in_img SEGS a).
    { destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)]. }
    pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
    rewrite KALL; [exact (HROD a Hro Hno Herr) | lia | intros Ho; exact (Hout_img a Ho Hi) | rewrite Hes; unfold PJP_FR; lia]. }
split.
{ (* the never-written slot at sp1 still holds the entry word, whose parse_string free trace is in CW (pjp_pre's
     prh_cw_pj, second arm) *)
  intros r Hr w0 Hw. apply (HCWslot r Hr). rewrite HFR48. rewrite <- Hw. symmetry. apply pje_rdword_eq.
  intros i Hi. exact (KSLOT i Hi). }
split; [rewrite R10, Usp4; unfold w64, PJP_FR; f_equal; lia|].
split; [rewrite R11, E4_12; reflexivity|].
split.
{ (* the cursor struct at sp1 + 8 *)
  split; [exact VP|]. split; [exact VEND|]. split; [exact VDEP|].
  split; [intros x Hx; apply (apresent_writable SEGS); apply HpresJ; unfold PJP_FR in *; lia|].
  split; [unfold PJP_FR; lia|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hlen|].
  split; [exact (pje_garr8_keep W W mem m5 t0 tl Hbytes KTXT)|].
  split; [right; unfold PJP_FR in *; lia | lia]. }
split.
{ (* the zeroed node *)
  unfold pj_zeroR. apply pje_garr8_of_aview.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. apply KZERO. lia. }
split.
{ (* out's facts at C1 *)
  split; [exact Hout4096|]. split; [exact HOUTC|]. split; [exact Hplace|]. split; [exact HLAMD|].
  split; [split; [exact (proj1 Hrw) | intros x Hx; exact (writable_at_grows SEGS _ _ x MG (proj2 Hrw x Hx))]|].
  split; [exact Hamr|]. split; [intros a Ha; exact (proj1 (Hown a Ha))|].
  split; [apply KRA; [lia | lia | exact Hora] | apply KHU; [lia | lia | lia | exact Hohull]]. }
split.
{ (* the text, at home *)
  split; [|exact HHOME].
  split; [exact (pje_garr8_keep W W mem m5 t0 tl Hbytes KTXT)|].
  split; [exact Ht4096|]. split; [exact Htceil|]. split; [exact Htamr|].
  split; [apply KRA; [lia | lia | exact Htra]|].
  intros Hn. apply KHU; [lia | exact Hn | lia | exact (Hthull Hn)]. }
(* the ledger: the statics and every head word are kept *)
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W m5 Lam peak cnt fail ran most own HLED).
- intros a Ha. pose proof (pst_in_img_B a Ha) as Hi. pose proof (@pa_segs_low _ _ PA a Hi) as Hlo.
  apply KALL; [lia | intros Ho; exact (Hout_img a Ho Hi) | rewrite Hes; unfold PJP_FR; lia].
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLED Hin) as (Hk0 & Hab & _ & _ & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (Hal & H4096 & Hcl & _).
  pose proof (@cf_head_nonneg cp) as Hh0. pose proof (@cf_head_al cp) as Hh8.
  assert (Hreq : a - cf_head + 1 <= YM05.alloc_ceiling) by (unfold req_size in Hcl; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply KALL; [lia | | rewrite Hes; unfold PJP_FR; lia].
  (* the head word lies in its own allocator block, apart from out's block or fake frame *)
  intros Ho. destruct Hplace as [(b & m & Hbin & Hnl & Hb & Hm) | (cid & pos & Hfin & Hf & Hfm)].
  + assert (Hne : (b, m) <> (a - cf_head, k + cf_head)).
    { intros Eq. injection Eq as Eb Em. apply Hnl. rewrite Eb, Em.
      replace (a - cf_head + cf_head) with a by lia. replace (k + cf_head - cf_head) with k by lia. exact Hin. }
    pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W mem md b m _ _ HAR Hbin Hab Hne) as Hd.
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hbin) as (Hbal & _).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
    destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec (k + cf_head) 0); lia.
  + pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md _ _ cid pos HAR Hab Hfin) as Hd.
    destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hfin) as (Hfal & _).
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd.
    destruct (Z.eqb_spec (k + cf_head) 0); lia.
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.
End e.
