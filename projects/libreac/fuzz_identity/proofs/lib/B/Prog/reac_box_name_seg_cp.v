(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:104-108;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 358-361,
   386-392, 532-535, for libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_stem.v, with its module paths and module names changed; 983 of its 1024 lines of code are new or changed and 232 lines of the source are left out. *)
(* reac_box_name (fuzz_identity.asan-ubsan, AF_reac_box_name = 0x2600): the three copy loops of its program walk
   (the walk, its cut-point states lib/B/Prog/reac_box_name_inv.v and the top chain
   lib/B/Prog/reac_box_name.v:161). Each loop copies a NUL-terminated string into a buffer struct, per character:
     rbn_cp_stem  C2 -> C3  0x83088 .. 0x830cc  stem -> nb (cursor s5, look-ahead s10, -1 in s8);
     rbn_cp_w4    C4 -> C5  0x83128 .. 0x8316c  w4   -> nb (cursor s4, look-ahead s5,  -1 in s8);
     rbn_cp_dp    C8 -> C9  0x83298 .. 0x832dc  nm   -> db (cursor s8, look-ahead s4,  -1 in s5).
   The loop body is the same 17 slots in the three instances: c := zext.b a0; sb_ch(b, c); the UBSan trap on the
   cursor (beq P,K to 0x835a8); the ASan check of the look-ahead's shadow byte (the token engine turns it into the
   obligation range_addressable Q 1, so errpath_load1 is never reached); P += 1; a0 := lbu 0(P); Q += 1; exit at
   the NUL, else back to the head. Each lemma is an induction on k (the characters left), in the form of cgif
   lib/A/AC8b.v tcbb_loopX, and its iteration is one proof script, cp_iter: the run from the head to the call (it
   stores nothing), the call (cp_call: HSC, tsb_ch_spec at BASE + AF_sb_ch by PSIG), a fresh symbolic state at the
   return slot with the next byte as an extra atom, the trap refuted, the run to the exit or back to the head.
   What the call keeps of the cut state comes from its tcj_kept (cp_keeps, cp_carry, cp_stem_tr); the struct's
   new state is sbm_ch of the old one (reac_box_name_sbm.v sbm_ch_post, sbm_str_snoc). *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI08 YI09 YI0s YI0t YI0m YI0n YP0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBProgSig IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm reac_box_name_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c sb_dec_c box_name_lemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : identb_prog_sig_ok.
Hypothesis HSC : tsb_ch_spec B.
Hypothesis HSB : tsb_dec_spec B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* ---- Memory facts carried by a step that kept the bytes of their footprint ---- *)
Lemma cp_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) q l,
  (forall a, q <= a < q + Z.of_nat (length l) -> aview SEGS H m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) q l -> garr8 SEGS (mrestrict H m') q l.
Proof.
intros H m m' q l K Gq. apply (garr8_frame SEGS _ _ q l Gq). intros a Ha. apply (mbyte_of_aview SEGS). exact (K a Ha).
Qed.
Lemma cp_val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v K Hv. eapply val_mem_kept; [|exact Hv]. intros k Hk. apply K. lia.
Qed.
Lemma cp_ra_kept : forall (H : word -> bool) (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview SEGS H m' (shadow_of_addr SHADOW_OFF x) = aview SEGS H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview SEGS H m) SHADOW_OFF a n -> range_addressable (aview SEGS H m') SHADOW_OFF a n.
Proof.
intros H m m' a n K R x Hx. destruct (R x Hx) as (s & Hs & Hok). exists s. split; [rewrite (K x Hx); exact Hs | exact Hok].
Qed.
Lemma cp_rdword_kept : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, a <= x < a + 8 -> aview SEGS H m' x = aview SEGS H m x) ->
  rdword (aview SEGS H m') a = rdword (aview SEGS H m) a.
Proof. intros H m m' a K. apply rdword_ext. intros k Hk. apply K. lia. Qed.
(* ---- What a step keeps, in IdentBCJ.v's tcj_kept form ---- *)
(* A run that changed no byte (frame_of with no writable window) kept everything. *)
Lemma cp_tcj_eq : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp,
  (forall w, mrestrict (w_H W) m' w = mrestrict (w_H W) m w) ->
  (forall a, sp - STK <= a < sp -> apresent (w_H W) m' a) ->
  tcj_kept B STK lyc Sc W m W m' sp (fun _ => False).
Proof.
intros STK lyc Sc W m m' sp Heq Hw.
assert (KA : forall a, aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) by (intros a; apply aview_eq_of; apply Heq).
split; [intros; apply KA|]. split; [intros; apply KA|]. split; [intros; apply KA|]. split; [intros; apply KA|].
split; [|exact Hw].
intros a _ _ (Hh & b & Hb). split; [exact Hh|]. exists b.
pose proof (Heq (Z_to_bv 64 a)) as E. unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb.
Qed.
Lemma cp_tcj_trans : forall STK lyc Sc (W : world SEGS) (m1 m2 m3 : word -> option byte) sp (E1 E2 : Z -> Prop),
  tcj_kept B STK lyc Sc W m1 W m2 sp E1 -> tcj_kept B STK lyc Sc W m2 W m3 sp E2 ->
  tcj_kept B STK lyc Sc W m1 W m3 sp (fun a => E1 a \/ E2 a).
Proof.
intros STK lyc Sc W m1 m2 m3 sp E1 E2 (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6).
split; [intros a Ha Hs He; rewrite (B1 a Ha Hs (fun x => He (or_intror x))); exact (A1 a Ha Hs (fun x => He (or_introl x)))|].
split; [intros b m i Hin Hi He; rewrite (B2 b m i Hin Hi (fun x => He (or_intror x))); exact (A2 b m i Hin Hi (fun x => He (or_introl x)))|].
split; [intros a Hi Hns Her; rewrite (B3 a Hi Hns Her); exact (A3 a Hi Hns Her)|].
split; [intros cid pos a Hin Hr He; rewrite (B4 cid pos a Hin Hr (fun x => He (or_intror x))); exact (A4 cid pos a Hin Hr (fun x => He (or_introl x)))|].
split; [intros a Ha Hs Hp; exact (B5 a Ha Hs (A5 a Ha Hs Hp))|]. exact B6.
Qed.
Lemma cp_tcj_mono : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp (E E' : Z -> Prop),
  tcj_kept B STK lyc Sc W m W m' sp E -> (forall a, E a -> E' a) -> tcj_kept B STK lyc Sc W m W m' sp E'.
Proof.
intros STK lyc Sc W m m' sp E E' (A1 & A2 & A3 & A4 & A5 & A6) HE.
split; [intros a Ha Hs He; exact (A1 a Ha Hs (fun x => He (HE _ x)))|].
split; [intros b mm i Hin Hi He; exact (A2 b mm i Hin Hi (fun x => He (HE _ x)))|].
split; [exact A3|].
split; [intros cid pos a Hin Hr He; exact (A4 cid pos a Hin Hr (fun x => He (HE _ x)))|].
split; [exact A5 | exact A6].
Qed.
(* The write set of one sb_ch call on the struct at b with the buffer [q, q + cap). *)
Definition cp_wr (b q cap : Z) (a : Z) : Prop := (b + 16 <= a < b + 28) \/ (q <= a < q + cap).
(* ---- Where things lie in a cut state ---- *)
Lemma cp_lay : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  AR SEGS B lyc Sc (x_W c) memc mdc /\
  x_s1 c mod 32 = 0 /\ x_sp0 c - 351 <= x_s1 c <= x_sp0 c - 320 /\ x_sp0 c mod 16 = 0 /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + (336 + 2 * ESTACK) <= x_sp0 c /\ x_sp0 c <= ly_stk_hi lyc /\
  ly_stk_hi lyc <= 2 ^ 47 /\
  In (3, x_fpos c) (frames Sc) /\ frame_addr lyc 3 (x_fpos c) = x_F c /\
  4096 <= x_F c /\ x_F c + 512 <= alloc_ceiling /\ x_F c mod 32 = 0 /\ in_app (x_F c) 512 /\
  x_FS c = SHADOW_OFF + x_F c / 8 /\ x_F c = 8 * (x_F c / 8) /\
  (forall a, x_sp0 c - (336 + 2 * ESTACK) <= a < x_sp0 c -> apresent (w_H (x_W c)) memc a) /\
  (forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos) /\
  (forall cid pos, In (cid, pos) (frames (x_S c)) -> In (cid, pos) (frames Sc)).
Proof.
intros c lyc Sc memc mdc regs (Hpre & HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EF : forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos).
{ intros cid pos. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & E6 & _). rewrite E6. reflexivity. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (Hin : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (Hal & Happ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (Hf0 & Hfc & _).
change (fs_frame_bytes 3) with 512 in *.
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; apply EF).
rewrite HF in Hal, Happ, Hf0, Hfc.
unfold x_s1.
pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as D2.
pose proof (Z.div_mod (x_F c) 32 ltac:(lia)) as D3. pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D4.
pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as D5.
split; [exact HAR|].
split; [rewrite Z.mul_comm; apply Z_mod_mult|].
split; [lia|]. split; [exact Hal16|].
split; [rewrite Eslo; lia|]. split; [rewrite Eslo; lia|]. split; [rewrite Eshi; lia|]. split; [rewrite Eshi; lia|].
split; [exact Hin|]. split; [exact HF|].
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [exact Happ|].
split; [reflexivity|]. split; [lia|].
split; [exact Hpres|]. split; [exact EF|].
intros cid pos H. rewrite Hfrs. right. exact H.
Qed.
(* ---- The keep facts of tcj_kept, per footprint ---- *)
Lemma cp_kw : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp (E : Z -> Prop) a,
  tcj_kept B STK lyc Sc W m W m' sp E -> alloc_ceiling <= a < 2 ^ 64 -> sp <= a -> ~ E a ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros STK lyc Sc W m m' sp E a (A1 & _) Ha Hs He. apply A1; [exact Ha | lia | exact He]. Qed.
Lemma cp_kf : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp (E : Z -> Prop) cid pos a,
  tcj_kept B STK lyc Sc W m W m' sp E -> In (cid, pos) (frames Sc) ->
  (frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid \/
   shadow_addr (frame_addr lyc cid pos) <= a < shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8) ->
  ~ E a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros STK lyc Sc W m m' sp E cid pos a (_ & _ & _ & A4 & _) Hin Hr He. apply (A4 cid pos a Hin); [|exact He].
unfold frame_rng, in_zr. cbn [fst snd]. exact Hr.
Qed.
Lemma cp_ki : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp (E : Z -> Prop) a,
  tcj_kept B STK lyc Sc W m W m' sp E ->
  in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof. intros STK lyc Sc W m m' sp E a (_ & _ & A3 & _) H1 H2 H3. exact (A3 a H1 H2 H3). Qed.
Lemma cp_kb : forall STK lyc Sc (W : world SEGS) (m m' : word -> option byte) sp (E : Z -> Prop) bb n i,
  tcj_kept B STK lyc Sc W m W m' sp E -> In (bb, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ E (bb + i) ->
  aview SEGS (w_H W) m' (bb + i) = aview SEGS (w_H W) m (bb + i).
Proof. intros STK lyc Sc W m m' sp E bb n i (_ & A2 & _) H1 H2 H3. exact (A2 bb n i H1 H2 H3). Qed.
(* ---- The cut states' parts, carried to a memory that kept their footprint ---- *)
Ltac cp_rg HR R n := refine (eq_trans (HR n ltac:(cbn [In]; tauto)) R).
Lemma cp_core_tr : forall c lyc Sc m mdc regs m' md' (regs' : bvmap 5 word),
  rbn_core B G c lyc Sc m mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 23%bv] -> getr regs' r = getr regs r) ->
  (forall a, x_sp0 c - 104 <= a < x_sp0 c \/ x_F c + 504 <= a < x_F c + 512 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_core B G c lyc Sc m' md' regs'.
Proof.
intros c lyc Sc m mdc regs m' md' regs' (Hpre & _ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsv & Hfl) HJ HR K.
split; [exact Hpre|]. split; [exact HJ|]. split; [exact Hperm|].
split; [cp_rg HR R2 (2%bv : bv 5)|]. split; [cp_rg HR R3 (3%bv : bv 5)|]. split; [cp_rg HR R4 (4%bv : bv 5)|]. split; [cp_rg HR R8 (8%bv : bv 5)|].
split; [cp_rg HR R9 (9%bv : bv 5)|]. split; [cp_rg HR R18 (18%bv : bv 5)|]. split; [cp_rg HR R19 (19%bv : bv 5)|]. split; [cp_rg HR R23 (23%bv : bv 5)|].
split.
- unfold rbn_saved in *. rewrite Forall_forall in *. intros p Hp. specialize (Hsv p Hp).
  assert (Hoff : 8 <= fst p <= 104)
    by (unfold rbn_saved_regs in Hp; cbn [In] in Hp; repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia|]); destruct Hp).
  unfold x_mem_at in *. eapply cp_val_mem_kept; [|exact Hsv]. intros x Hx. apply K. left. lia.
- rewrite (cp_rdword_kept _ m m'); [exact Hfl|]. intros x Hx. apply K. right. lia.
Qed.
Lemma cp_live_tr : forall c lyc Sc m mdc regs m' md' (regs' : bvmap 5 word),
  rbn_live B G c lyc Sc m mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 23%bv] -> getr regs' r = getr regs r) ->
  (forall a, x_sp0 c - 104 <= a < x_sp0 c \/ x_F c + 504 <= a < x_F c + 512 \/ x_s1 c <= a < x_s1 c + 88 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  (forall a, inFP (x_FP c) a -> (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_live B G c lyc Sc m' md' regs'.
Proof.
intros c lyc Sc m mdc regs m' md' regs' (Hcore & Hok & Hbk & Hsl & R22) HJ HR K KB.
split.
{ apply (cp_core_tr c lyc Sc m mdc regs); [exact Hcore | exact HJ | |].
  - intros r Hr. apply HR. cbn [In] in Hr |- *. tauto.
  - intros a Ha. apply K. lia. }
split; [exact Hok|].
split.
{ intros a Ha Hb. rewrite (KB a Ha Hb). exact (Hbk a Ha Hb). }
split; [|cp_rg HR R22 (22%bv : bv 5)].
unfold rbn_slots, x_mem_at in *. cbv zeta in *.
destruct Hsl as (V0 & V8 & V16 & V24 & V32 & V40 & V48 & V56 & V80).
repeat split; (eapply cp_val_mem_kept; [|eassumption]); intros x Hx; apply K; right; right; lia.
Qed.
Lemma cp_sb_tr : forall c m m' b q cap cs ov,
  rbn_sb c m b q cap cs ov ->
  (forall a, b <= a < b + 28 \/ q <= a < q + Z.of_nat (length cs) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_sb c m' b q cap cs ov.
Proof.
intros c m m' b q cap cs ov (Vp & Vc & Vn & Vo & Ho & Hl & Hr & Gq) K. unfold x_mem_at in *.
split; [eapply cp_val_mem_kept; [|exact Vp]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply cp_val_mem_kept; [|exact Vc]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply cp_val_mem_kept; [|exact Vn]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [eapply cp_val_mem_kept; [|exact Vo]; intros x Hx; apply K; left; cbn in Hx; lia|].
split; [exact Ho|]. split; [exact Hl|]. split; [exact Hr|].
eapply cp_garr8_kept; [|exact Gq]. intros a Ha. apply K. right. exact Ha.
Qed.
Lemma cp_w4done_tr : forall c m m' (regs regs' : bvmap 5 word),
  rbn_w4done c m regs -> getr regs' 27 = getr regs 27 ->
  (forall a, x_s1 c + 184 <= a < x_s1 c + 212 \/ x_W4 c <= a < x_W4 c + 5 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_w4done c m' regs'.
Proof.
intros c m m' regs regs' (Hsb & Gw & R27) E27 K.
pose proof Hsb as (_ & _ & _ & _ & _ & Hl & _).
split; [apply (cp_sb_tr c m); [exact Hsb|]; intros a Ha; apply K; unfold x_wb in Ha; lia|].
split; [|rewrite E27; exact R27].
unfold x_mem_at in *. eapply cp_garr8_kept; [|exact Gw]. intros a Ha. apply K. right.
rewrite length_app in Ha. cbn [length] in Ha. lia.
Qed.
Lemma cp_nmdone_tr : forall c m m' (regs regs' : bvmap 5 word),
  rbn_nmdone c m regs -> getr regs' 25 = getr regs 25 ->
  (forall a, x_s1 c + 152 <= a < x_s1 c + 180 \/ x_NM c <= a < x_NM c + 24 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_nmdone c m' regs'.
Proof.
intros c m m' regs regs' (Hsb & Gw & R25) E25 K.
pose proof Hsb as (_ & _ & _ & _ & _ & Hl & _).
split; [apply (cp_sb_tr c m); [exact Hsb|]; intros a Ha; apply K; unfold x_nb in Ha; lia|].
split; [|rewrite E25; exact R25].
unfold x_mem_at in *. eapply cp_garr8_kept; [|exact Gw]. intros a Ha. apply K. right.
rewrite length_app in Ha. cbn [length] in Ha. lia.
Qed.
Lemma cp_tkdone_tr : forall c m m' (regs regs' : bvmap 5 word),
  rbn_tkdone c m regs -> getr regs' 26 = getr regs 26 ->
  (forall a, x_s1 c + 120 <= a < x_s1 c + 148 \/ x_TK c <= a < x_TK c + 24 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_tkdone c m' regs'.
Proof.
intros c m m' regs regs' (Hsb & Gw & R26) E26 K.
pose proof Hsb as (_ & _ & _ & _ & _ & Hl & _).
split; [apply (cp_sb_tr c m); [exact Hsb|]; intros a Ha; apply K; unfold x_tb in Ha; lia|].
split; [|rewrite E26; exact R26].
unfold x_mem_at in *. eapply cp_garr8_kept; [|exact Gw]. intros a Ha. apply K. right.
rewrite length_app in Ha. cbn [length] in Ha. lia.
Qed.
Lemma cp_scope_tr : forall c m m' w nm tk dp,
  rbn_scope c m w nm tk dp ->
  (forall a, x_FS c + 4 <= a < x_FS c + 30 -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_scope c m' w nm tk dp.
Proof.
intros c m m' w nm tk dp (S4 & S8 & S16 & S24) K. unfold rbn_scope. cbv zeta.
split; [rewrite K by lia; exact S4|].
split; [intros j Hj; rewrite K by lia; exact (S8 j Hj)|].
split; [intros j Hj; rewrite K by lia; exact (S16 j Hj)|].
intros j Hj; rewrite K by lia; exact (S24 j Hj).
Qed.
(* The stem across a step whose write set E lies in the machine stack or the frame F: a string of a frame of the
   caller (another frame of frames Sc than F), or an image string the journal keeps. *)
Lemma cp_stem_tr : forall c lyc Sc m mdc regs m' md' st (E : Z -> Prop),
  rbn_core B G c lyc Sc m mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) m (x_W c) m' (x_s1 c) E ->
  (forall a, E a -> alloc_ceiling <= a \/ x_F c <= a < x_F c + 512) ->
  rbn_stem B G c m st -> rbn_stem B G c m' st.
Proof.
intros c lyc Sc m mdc regs m' md' st E Hc HJ' HK HE Hst.
destruct (cp_lay c lyc Sc m mdc regs Hc) as (HAR & _ & _ & _ & _ & _ & _ & _ & HinF & HF & HF0 & HFc & _ & _ & _ & _ & _ & EF & Hsub).
pose proof (proj1 HJ') as HAR'.
pose proof (Hc) as (_ & HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
destruct Hst as [(Hne & Est & Hcs & cid & pos & Hin & Hlo & Hhi) | (Hnil & Hims)].
- left. split; [exact Hne|]. split; [exact Est|].
  pose proof (Hsub cid pos Hin) as HinS.
  rewrite <- EF in Hlo, Hhi.
  destruct (al_frames _ _ LAWS _ _ _ _ _ cid pos HAR HinS) as (Hal & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hfn.
  assert (Hfb8 : fs_frame_bytes cid mod 8 = 0).
  { destruct (frame_al64 SEGS B _ _ _ _ _ cid pos HAR HinS) as (_ & H64 & _).
    pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D. rewrite H64 in D.
    rewrite D. replace (64 * (fs_frame_bytes cid / 64) + 0) with ((8 * (fs_frame_bytes cid / 64)) * 8) by lia.
    apply Z.mod_mul. lia. }
  set (fa := frame_addr lyc cid pos) in *.
  assert (Hfa8 : fa = 8 * (fa / 8)) by (pose proof (Z.div_mod fa 32 ltac:(lia)); pose proof (Z.div_mod fa 8 ltac:(lia)); pose proof (Z.mod_pos_bound fa 8 ltac:(lia)); lia).
  assert (Hfs8 : fs_frame_bytes cid = 8 * (fs_frame_bytes cid / 8)) by (pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)); lia).
  (* E misses the caller's frame and its shadow *)
  assert (HnE : forall a, (fa <= a < fa + fs_frame_bytes cid \/
     shadow_addr fa <= a < shadow_addr fa + fs_frame_bytes cid / 8) -> ~ E a).
  { intros a Ha He.
    destruct (frame_zone SEGS B LAWS lyc Sc (x_W c) m mdc cid pos a HAR HinS) as (Hz & _);
      [unfold frame_rng, in_zr; cbn [fst snd]; exact Ha|].
    destruct (HE a He) as [Hc' | HFa]; [lia|].
    apply in_split in Hin as (l2 & l3 & El).
    apply (frames_zone_disj SEGS B LAWS lyc Sc (x_W c) m mdc (3, x_fpos c) (cid, pos) [] l2 l3 a HAR).
    - rewrite Hfrs, El. reflexivity.
    - cbn [fst snd]. left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3) with 512. lia.
    - cbn [fst snd]. unfold frame_rng, in_zr. cbn [fst snd]. exact Ha. }
  assert (KF : forall a, (fa <= a < fa + fs_frame_bytes cid \/
     shadow_addr fa <= a < shadow_addr fa + fs_frame_bytes cid / 8) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a)
    by (intros a Ha; exact (cp_kf _ _ _ _ _ _ _ _ cid pos a HK HinS Ha (HnE a Ha))).
  destruct Hcs as (Hch & Hlen & Hpos & Hamr & Gs & Hra & _ & Htail).
  split.
  + split; [exact Hch|]. split; [exact Hlen|]. split; [exact Hpos|]. split; [exact Hamr|].
    split.
    { eapply cp_garr8_kept; [|exact Gs]. intros a Ha. apply KF. left. rewrite length_app in Ha. cbn [length] in Ha. lia. }
    split.
    { eapply cp_ra_kept; [|exact Hra]. intros x Hx. apply KF. right. unfold shadow_of_addr, shadow_addr.
      pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
    split.
    { apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc (x_W c) m' md' cid pos); [exact HAR' | exact HinS | lia | lia | lia]. }
    intros x Hx. rewrite KF by (left; pose proof (Z.mod_pos_bound (st + Z.of_nat (length (x_sd c))) 8 ltac:(lia)); lia).
    exact (Htail x Hx).
  + exists cid, pos. split; [exact Hin|]. rewrite <- EF. fold fa. lia.
- right. split; [exact Hnil|].
  destruct Hims as (H1 & H2 & H3 & Gs & H5 & Hfx & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [|split; [exact H5 | split; [exact Hfx | exact H7]]].
  eapply cp_garr8_kept; [|exact Gs]. intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  destruct (Hfx a ltac:(lia)) as (I1 & I2 & I3). exact (cp_ki _ _ _ _ _ _ _ _ a HK I1 I2 I3).
Qed.
Lemma cp_mod8 : forall x k, x mod 32 = 0 -> (x + 8 * k) mod 8 = 0.
Proof.
intros x k H. pose proof (Z.div_mod x 32 ltac:(lia)) as D.
replace (x + 8 * k) with ((4 * (x / 32) + k) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma cp_mod4096 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D.
rewrite D, H, Z.add_0_r. replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
(* The machine stack is marked usable (AR_zshadow_law on (ly_stk_lo, ly_stk_hi - ly_stk_lo), as
   lib/B/Prog/reac_box_catalogue.v cat_pR_addressable does). *)
Lemma cp_stack_ra : forall lyc Sc (W : world SEGS) m md a n,
  AR SEGS B lyc Sc W m md -> ly_stk_lo lyc <= a -> a + n <= ly_stk_hi lyc ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n.
Proof.
intros lyc Sc W m md a n HAR Hlo Hhi.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS lyc Sc W m md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah.
apply cp_mod4096 in Hpal. apply cp_mod4096 in Hpah.
eapply range_addressable_sub; [apply zero_shadow_range; [exact Hpal | | exact Hz] | lia | lia].
rewrite Zminus_mod, Hpal, Hpah. reflexivity.
Qed.
(* ---- One sb_ch call on nb or db (tsb_ch_spec, HSC), from a cut state's facts, at a memory mK that has the
   cut's bytes (the run from the loop head to the call stores nothing) ---- *)
Lemma cp_call : forall c lyc Sc memc mdc regs mK mdK (regsK : bvmap 5 word) b q cap cs ov ch ra Q,
  rbn_core B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mK mdK 0 ->
  (forall w, mrestrict (w_H (x_W c)) mK w = mrestrict (w_H (x_W c)) memc w) ->
  getr regsK 1 = Z_to_bv 64 (BASE + ra) -> 0 <= ra < 2 ^ 40 -> ra mod 2 = 0 ->
  getr regsK 2 = w64 (x_s1 c) -> getr regsK 3 = w64 (as_gp B) -> getr regsK 4 = w64 (as_tp B) ->
  getr regsK 10 = w64 b -> getr regsK 11 = w64 ch -> 0 <= ch < 256 ->
  (b = x_nb c /\ q = x_NM c /\ cap = 24) \/ (b = x_db c /\ q = x_DP c /\ cap = 48) ->
  rbn_sb c memc b q cap cs ov ->
  range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF q cap ->
  (forall regs2 mem2 md2,
     ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
       [(3, x_fpos c)] lyc Sc (x_W c) mem2 md2 0 ->
     aregs_preserved regsK regs2 ->
     tcj_kept B SB_CH_STK lyc Sc (x_W c) memc (x_W c) mem2 (x_s1 c) (cp_wr b q cap) ->
     rbn_sb c mem2 b q cap (fst (sbm_ch cap (cs, ov) ch)) (snd (sbm_ch cap (cs, ov) ch)) ->
     SRr SEGS (x_W c) (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ra)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_ch) regsK mK mdK) Q.
Proof.
intros c lyc Sc memc mdc regs mK mdK regsK b q cap cs ov ch ra Q Hc HJK Heq R1 Hra Hra2 R2 R3 R4 R10 R11 Hch Hbq Hsb Hrq HK.
destruct (cp_lay c lyc Sc memc mdc regs Hc)
  as (HAR & Hs1al & Hs1 & Hsp0al & Hslo & Hslo2 & Hshi & Hshi2 & HinF & HF & HF0 & HFc & HFal & HFapp & _ & _ & Hpres & EF & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity. assert (HCS : SB_CH_STK = 4112) by reflexivity.
pose proof (proj1 HJK) as HARK.
pose proof HJK as (_ & HlyK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresK & _).
pose proof pa_B_ok as HB. pose proof pa_base_lo as HB0.
assert (KA : forall a, aview SEGS (w_H (x_W c)) mK a = aview SEGS (w_H (x_W c)) memc a)
  by (intros a; apply aview_eq_of; apply Heq).
pose proof Hsb as (Vp & Vc & Vn & Vo & Hov & Hlen & Hrng & Gq).
unfold x_mem_at in Vp, Vc, Vn, Vo, Gq.
assert (Hsp : spZ regsK = x_s1 c) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hn0 : 0 <= Z.of_nat (length cs)) by lia.
assert (Hb : x_s1 c + 88 <= b /\ b + 28 <= x_s1 c + 180 /\ b mod 8 = 0 /\ x_F c + 64 <= q /\ q + cap <= x_F c + 240 /\
  (cap = 24 \/ cap = 48)).
{ destruct Hbq as [(-> & -> & ->) | (-> & -> & ->)]; unfold x_nb, x_db, x_NM, x_DP.
  - split; [lia|]. split; [lia|]. split; [exact (cp_mod8 (x_s1 c) 19 Hs1al)|]. lia.
  - split; [lia|]. split; [lia|]. split; [exact (cp_mod8 (x_s1 c) 11 Hs1al)|]. lia. }
destruct Hb as (Hb1 & Hb2 & Hb8 & Hq1 & Hq2 & Hcap).
assert (PRESK : forall a, x_s1 c - SB_CH_STK <= a < x_s1 c -> apresent (w_H (x_W c)) mK a)
  by (intros a Ha; apply HpresK; lia).
eapply SRr_bind.
{ apply (HSC (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) mK mdK 0 regsK b ch q cap (Z.of_nat (length cs)) ov HJK).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | exact Hra2].
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - exact R3.
  - exact R4.
  - rewrite Hsp. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D.
    replace (x_s1 c) with ((2 * (x_s1 c / 32)) * 16) by lia. apply Z.mod_mul. lia.
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - exact R10.
  - exact R11.
  - exact Hch.
  - exact Hb8.
  - lia.
  - lia.
  - left. rewrite Hsp. lia.
  - right. split; lia.
  - eapply cp_val_mem_kept; [intros x _; apply KA | exact Vp].
  - eapply cp_val_mem_kept; [intros x _; apply KA | exact Vc].
  - eapply cp_val_mem_kept; [intros x _; apply KA | exact Vn].
  - eapply cp_val_mem_kept; [intros x _; apply KA | exact Vo].
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact (cp_stack_ra lyc Sc (x_W c) mK mdK b 28 HARK ltac:(lia) ltac:(lia)).
  - intros a Ha. split; [left; lia|]. split; [apply HpresK; lia|].
    split; [apply (al_stack _ _ LAWS _ _ _ _ _ a HARK); lia | rewrite Hsp; lia].
  - intros Hroom.
    destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HARK HinF) as (_ & _ & Hfb & _).
    rewrite HF in Hfb. change (fs_frame_bytes 3) with 512 in Hfb.
    split; [lia|]. split; [lia|].
    split.
    { intros a Ha. right. exists 3, (x_fpos c). split; [exact HinF|].
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF. change (fs_frame_bytes 3) with 512. lia. }
    split.
    { eapply range_addressable_sub; [eapply cp_ra_kept; [intros x _; apply KA | exact Hrq] | lia | lia]. }
    split.
    { intros a Ha. destruct (Hfb a ltac:(lia)) as [P1 P2].
      split; [right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|]; left;
              unfold in_zr; cbn [fst snd]; rewrite HF; change (fs_frame_bytes 3) with 512; lia|].
      split; [exact P1|]. split; [exact P2|]. rewrite Hsp. lia. }
    split; [left; lia|]. left. rewrite Hsp. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Htcj & Fp & Fcap & Fif).
rewrite Hsp in Htcj. change (0 + EV_SB_CH) with 0 in HJ2.
pose proof (cp_tcj_trans _ _ _ _ _ _ _ _ _ _ (cp_tcj_eq SB_CH_STK lyc Sc (x_W c) memc mK (x_s1 c) Heq PRESK) Htcj) as HT.
assert (KQ : forall a, q <= a < q + Z.of_nat (length cs) ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha. apply (cp_kf _ _ _ _ _ _ _ _ 3 (x_fpos c) a HT HinF).
  - left. rewrite HF. change (fs_frame_bytes 3) with 512. lia.
  - unfold tsb_ch_wr. intros [[] | [Hw | (_ & Hw)]]; lia. }
rewrite R1. apply HK.
- exact HJ2.
- exact HP2.
- eapply cp_tcj_mono; [exact HT|]. intros a [[] | [Hw | (Hlt & Hw)]]; unfold cp_wr; lia.
- destruct (Z.ltb_spec (Z.of_nat (length cs) + 1) cap) as [Hlt | Hge].
  + destruct Fif as (Fn & Fo & G1). rewrite sbm_ch_room by exact Hlt. cbn [fst snd].
    unfold rbn_sb, x_mem_at.
    split; [exact Fp|]. split; [exact Fcap|].
    split; [replace (Z.of_nat (length (cs ++ [ch]))) with (Z.of_nat (length cs) + 1)
              by (rewrite length_app; cbn [length]; lia); exact Fn|].
    split; [exact Fo|]. split; [exact Hov|]. split; [rewrite length_app; cbn [length]; lia|].
    split; [apply Forall_app; split; [exact Hrng | constructor; [lia | constructor]]|].
    apply garr8_app. split; [eapply cp_garr8_kept; [exact KQ | exact Gq] | exact G1].
  + destruct Fif as (Fn & Fo). rewrite sbm_ch_full by lia. cbn [fst snd].
    unfold rbn_sb, x_mem_at.
    split; [exact Fp|]. split; [exact Fcap|]. split; [exact Fn|]. split; [exact Fo|].
    split; [right; reflexivity|]. split; [exact Hlen|]. split; [exact Hrng|].
    eapply cp_garr8_kept; [exact KQ | exact Gq].
Qed.
(* The byte the copy loops read at the cursor register's atom + 1 (lbu a0,0(P) after addi P,P,1): its value is
   the extra atom 32. Read-only (empty window). *)
Definition cp_rgn (n : nat) : YP09.region := YP09.mkRegion (Some n) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
(* The callee-saved registers (YG0d.v acallee_saved) kept by a call. *)
Definition cp_cs : list (bv 5) :=
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma cp_pres : forall (regs regs2 : bvmap 5 word), aregs_preserved regs regs2 ->
  forall r, In r cp_cs -> getr regs2 r = getr regs r.
Proof.
intros regs regs2 HP r Hr. unfold cp_cs in Hr. cbn [In] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ ?x = _ =>
      let z := eval vm_compute in (bv_unsigned x) in
      replace x with (Z_to_bv 5 z) by vm_refl_bv; apply HP; unfold acallee_saved; lia end | ]).
destruct Hr.
Qed.
(* What one sb_ch call on nb (buffer NM) or db (buffer DP) keeps of a cut state's footprint. *)
Lemma cp_keeps : forall c lyc Sc m mdc regs m' b q cap,
  rbn_core B G c lyc Sc m mdc regs ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) m (x_W c) m' (x_s1 c) (cp_wr b q cap) ->
  (b = x_nb c /\ q = x_NM c /\ cap = 24) \/ (b = x_db c /\ q = x_DP c /\ cap = 48) ->
  (forall a, x_sp0 c - 104 <= a < x_sp0 c \/ x_F c + 504 <= a < x_F c + 512 \/ x_s1 c <= a < x_s1 c + 88 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (forall a, inFP (x_FP c) a -> (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (forall a, x_s1 c + 184 <= a < x_s1 c + 212 \/ x_W4 c <= a < x_W4 c + 5 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (forall a, x_s1 c + 120 <= a < x_s1 c + 148 \/ x_TK c <= a < x_TK c + 24 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (forall a, x_FS c + 4 <= a < x_FS c + 30 -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (b = x_db c -> forall a, x_s1 c + 152 <= a < x_s1 c + 180 \/ x_NM c <= a < x_NM c + 24 ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) /\
  (forall a, cp_wr b q cap a -> alloc_ceiling <= a \/ x_F c <= a < x_F c + 512).
Proof.
intros c lyc Sc m mdc regs m' b q cap Hc HK Hbq.
destruct (cp_lay c lyc Sc m mdc regs Hc)
  as (HAR & Hs1al & Hs1 & Hsp0al & Hslo & Hslo2 & Hshi & Hshi2 & HinF & HF & HF0 & HFc & HFal & HFapp & HFS & HF8 & _ & EF & Hsub).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
pose proof Hc as (_ & HJ & Hperm & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (HE : forall a, cp_wr b q cap a ->
  (x_s1 c + 104 <= a < x_s1 c + 116 \/ x_s1 c + 168 <= a < x_s1 c + 180) \/
  (x_F c + 64 <= a < x_F c + 88 \/ x_F c + 192 <= a < x_F c + 240)).
{ intros a Ha. unfold cp_wr, x_nb, x_db, x_NM, x_DP in *. destruct Hbq as [(-> & -> & ->) | (-> & -> & ->)]; lia. }
assert (KW : forall a, x_s1 c <= a < x_sp0 c -> ~ cp_wr b q cap a -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a).
{ intros a Ha Hn. apply (cp_kw _ _ _ _ _ _ _ _ a HK); [lia | lia | exact Hn]. }
assert (KFr : forall a, x_F c <= a < x_F c + 512 -> ~ cp_wr b q cap a -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a).
{ intros a Ha Hn. apply (cp_kf _ _ _ _ _ _ _ _ 3 (x_fpos c) a HK HinF); [|exact Hn].
  left. rewrite HF. change (fs_frame_bytes 3) with 512. exact Ha. }
split.
{ intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
  - apply KW; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia.
  - apply KFr; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia.
  - apply KW; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia. }
split.
{ intros a _ (qq & N & Hin & Ha).
  pose proof (Permutation_in _ (Permutation_sym Hperm) Hin) as Hin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ qq N HAR Hin') as (_ & H4096 & Hce & _).
  pose proof (req_size_pos N) as HR.
  assert (HN : N <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
  replace a with (qq + (a - qq)) by lia.
  apply (cp_kb _ _ _ _ _ _ _ _ qq N (a - qq) HK Hin'); [lia|].
  replace (qq + (a - qq)) with a by lia.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ qq N 3 (x_fpos c) HAR Hin' HinF) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HF in Hd. change (fs_frame_bytes 3) with 512 in Hd.
  intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia. }
split.
{ intros a Ha. unfold x_W4 in Ha. destruct Ha as [Ha | Ha].
  - apply KW; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia.
  - apply KFr; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia. }
split.
{ intros a Ha. unfold x_TK in Ha. destruct Ha as [Ha | Ha].
  - apply KW; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia.
  - apply KFr; [lia|]. intros Hw. destruct (HE a Hw) as [Hw' | Hw']; lia. }
split.
{ intros a Ha. apply (cp_kf _ _ _ _ _ _ _ _ 3 (x_fpos c) a HK HinF).
  - right. rewrite HF. change (fs_frame_bytes 3 / 8) with 64. unfold shadow_addr. rewrite HFS in Ha. lia.
  - intros Hw. destruct (HE a Hw) as [Hw' | Hw']; rewrite HFS in Ha;
    unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *;
    pose proof (Z.div_mod (x_F c) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)); lia. }
split.
{ intros Hdb a Ha. subst b. destruct Hbq as [(Hb & _) | (_ & -> & ->)]; [unfold x_db, x_nb in Hb; lia|].
  unfold x_NM in Ha. destruct Ha as [Ha | Ha].
  - apply KW; [lia|]. unfold cp_wr, x_db, x_DP. lia.
  - apply KFr; [lia|]. unfold cp_wr, x_db, x_DP. lia. }
intros a Hw. destruct (HE a Hw) as [Hw' | Hw']; lia.
Qed.
(* The stem's bytes and the shadow of the bytes the loop reads, from rbn_stem at a state's AR. *)
Lemma cp_stem_src : forall c lyc Sc m md st,
  AR SEGS B lyc Sc (x_W c) m md -> rbn_stem B G c m st ->
  Forall (fun x => 0 < x < 256) (x_stem c) /\ 0 < st /\ st + Z.of_nat (length (x_stem c)) + 1 <= 2 ^ 47 - 1 /\
  garr8 SEGS (mrestrict (w_H (x_W c)) m) st (x_stem c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF st (Z.of_nat (length (x_stem c)) + 1).
Proof.
intros c lyc Sc m md st HAR [(Hne & Est & Hcs & _) | (Hnil & Hims)].
- assert (Es : x_stem c = x_sd c) by (unfold x_stem, bn_stem; destruct (x_sd c); [congruence | reflexivity]).
  rewrite Es. destruct Hcs as (Hch & Hlen & Hpos & Hamr & Gs & Hra & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold amem_range in Hamr. rewrite C3, C4, C5 in Hamr.
  split; [exact Hch|]. split; [exact Hpos|]. split; [lia|]. split; [exact Gs | exact Hra].
- destruct Hims as (H1 & H2 & H3 & Gs & (qq & z & Hin & Hq1 & Hq2) & _).
  split; [exact H3|]. split; [lia|]. split; [lia|]. split; [exact Gs|].
  exact (ro_usable_glob SEGS B G _ _ _ _ _ qq z st _ GM Hin HAR Hq1 Hq2).
Qed.
(* The arrays whose scope is open are addressable (rbn_scope). *)
Lemma cp_scope_ra : forall c m w nm tk dp, rbn_scope c m w nm tk dp ->
  x_F c = 8 * (x_F c / 8) -> x_FS c = SHADOW_OFF + x_F c / 8 ->
  (w = 5 -> range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF (x_W4 c) 5) /\
  (nm = 0 -> range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF (x_NM c) 24) /\
  (tk = 0 -> range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF (x_TK c) 24) /\
  (dp = 0 -> range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF (x_DP c) 48).
Proof.
intros c m w nm tk dp (S4 & S8 & S16 & S24) HF8 HFS.
assert (D : forall k, 0 <= k -> (x_F c + 8 * k) / 8 = x_F c / 8 + k).
{ intros k Hk. rewrite HF8. replace (8 * (x_F c / 8) + 8 * k) with ((x_F c / 8 + k) * 8) by lia.
  rewrite Z.div_mul by lia. replace (8 * (x_F c / 8)) with ((x_F c / 8) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
assert (M : forall k, (x_F c + 8 * k) mod 8 = 0).
{ intros k. rewrite HF8. replace (8 * (x_F c / 8) + 8 * k) with ((x_F c / 8 + k) * 8) by lia. apply Z.mod_mul. lia. }
split.
{ intros ->. apply range_addressable_partial; [| unfold x_W4; exact (M 4) | lia].
  unfold shadow_of_addr, x_W4. replace (x_F c + 32) with (x_F c + 8 * 4) by lia. rewrite (D 4) by lia.
  replace (SHADOW_OFF + (x_F c / 8 + 4)) with (x_FS c + 4) by lia. exact S4. }
split.
{ intros ->. apply zero_shadow_range; [unfold x_NM; exact (M 8) | reflexivity |].
  intros j Hj. change (24 / 8) with 3 in Hj. unfold shadow_of_addr, x_NM.
  replace (x_F c + 64) with (x_F c + 8 * 8) by lia. rewrite (D 8) by lia.
  replace (SHADOW_OFF + (x_F c / 8 + 8) + j) with (x_FS c + (8 + j)) by lia. apply S8. lia. }
split.
{ intros ->. apply zero_shadow_range; [unfold x_TK; exact (M 16) | reflexivity |].
  intros j Hj. change (24 / 8) with 3 in Hj. unfold shadow_of_addr, x_TK.
  replace (x_F c + 128) with (x_F c + 8 * 16) by lia. rewrite (D 16) by lia.
  replace (SHADOW_OFF + (x_F c / 8 + 16) + j) with (x_FS c + (16 + j)) by lia. apply S16. lia. }
intros ->. apply zero_shadow_range; [unfold x_DP; exact (M 24) | reflexivity |].
intros j Hj. change (48 / 8) with 6 in Hj. unfold shadow_of_addr, x_DP.
replace (x_F c + 192) with (x_F c + 8 * 24) by lia. rewrite (D 24) by lia.
replace (SHADOW_OFF + (x_F c / 8 + 24) + j) with (x_FS c + (24 + j)) by lia. apply S24. lia.
Qed.
(* A run whose only region is cp_rgn (no writable window) stored nothing (YI04.v frame_of_one with lo = hi =
   the region's base). *)
Lemma cp_fr_ro : forall E (m m' : word -> option byte) n, frame_of E [cp_rgn n] m m' -> forall w, m' w = m w.
Proof.
intros E m m' n HF w.
destruct (Z.lt_ge_cases (bv_unsigned w) (base_val E (Some n))) as [Hw | Hw];
  apply (frame_of_one E m m' (cp_rgn n) (base_val E (Some n)) (base_val E (Some n)) w HF);
  cbn [cp_rgn YP09.r_base YP09.r_wlo YP09.r_whi]; lia.
Qed.
(* The parts of a cut state that one sb_ch call on nb or db leaves as they were. *)
Lemma cp_carry : forall c lyc Sc m mdc regs m' md' (regs' : bvmap 5 word) b q cap w nm tk dp,
  rbn_live B G c lyc Sc m mdc regs -> rbn_w4done c m regs -> rbn_scope c m w nm tk dp ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) m (x_W c) m' (x_s1 c) (cp_wr b q cap) ->
  (b = x_nb c /\ q = x_NM c /\ cap = 24) \/ (b = x_db c /\ q = x_DP c /\ cap = 48) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 23%bv; 27%bv] -> getr regs' r = getr regs r) ->
  rbn_live B G c lyc Sc m' md' regs' /\ rbn_w4done c m' regs' /\ rbn_scope c m' w nm tk dp.
Proof.
intros c lyc Sc m mdc regs m' md' regs' b q cap w nm tk dp Hl Hw Hs HJ' HT Hbq HR.
pose proof Hl as (Hc & _).
destruct (cp_keeps c lyc Sc m mdc regs m' b q cap Hc HT Hbq) as (KL & KB & KW4 & _ & KSC & _ & _).
split; [apply (cp_live_tr c lyc Sc m mdc regs m' md' regs' Hl HJ'); [| exact KL | exact KB]; intros r Hr; apply HR; cbn [In] in Hr |- *; tauto|].
split; [apply (cp_w4done_tr c m m' regs regs' Hw); [apply HR; cbn [In]; tauto | exact KW4]|].
exact (cp_scope_tr c m m' w nm tk dp Hs KSC).
Qed.
Lemma cp_carry_db : forall c lyc Sc m mdc regs m' (regs' : bvmap 5 word),
  rbn_core B G c lyc Sc m mdc regs -> rbn_nmdone c m regs -> rbn_tkdone c m regs ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) m (x_W c) m' (x_s1 c) (cp_wr (x_db c) (x_DP c) 48) ->
  getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
  rbn_nmdone c m' regs' /\ rbn_tkdone c m' regs'.
Proof.
intros c lyc Sc m mdc regs m' regs' Hc Hn Ht HT R25 R26.
destruct (cp_keeps c lyc Sc m mdc regs m' (x_db c) (x_DP c) 48 Hc HT (or_intror (conj eq_refl (conj eq_refl eq_refl))))
  as (_ & _ & _ & KTK & _ & KNM & _).
split; [exact (cp_nmdone_tr c m m' regs regs' Hn R25 (KNM eq_refl)) | exact (cp_tkdone_tr c m m' regs regs' Ht R26 KTK)].
Qed.
Lemma cp_and255 : forall x, 0 <= x < 256 -> alu64 ALU_AND (Z_to_bv 64 x) (Z_to_bv 64 255) = Z_to_bv 64 x.
Proof.
intros x Hx. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw]. rewrite Z_to_bv64_canon.
rewrite (zcanon_id x) by (unfold M64; lia). change (zcanon 255) with 255. rewrite land255_small by lia.
reflexivity.
Qed.
(* The exit test (beqz a0 on the byte atom 32) as cv = 0 or cv <> 0. *)
Ltac cp_test cv E32 :=
  lazymatch goal with Hx : branch_taken _ (sv_denot ?Ex (SOff 32 0)) _ = _ |- _ =>
    rewrite branch_eq_U in Hx;
    let X32 := fresh "X32" in
    assert (X32 : ew Ex 32 = Z_to_bv 64 cv) by (cbn [ew ewset Nat.eqb]; exact E32);
    rewrite (U_atom Ex 32 cv X32), (U_lit Ex 0) in Hx by lia;
    first [apply Z.eqb_eq in Hx | apply Z.eqb_neq in Hx]; clear X32 end.
(* The run from the exit test to stop and what the iteration kept: HT3 (tcj_kept from memc to the final memory),
   KR3 (the registers KL), Hsb3 (the struct with one more character); the goal's pc as BASE + AF + stop. *)
Ltac cp_fin c lyc Sc memc regs i stop P b q cap st0 s KL Heq2a mem2 ms2 HT2 HS2 HJ3 SHOK2 HAE2 KR2 Hsb2 :=
  paj_run_to_tok RUNTO HS2 HJ3 SHOK2 Bspan (AF_reac_box_name + stop);
  [ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]
  | ];
  let Heq3a := fresh "Heq3a" in let msF := fresh "msF" in let mdF := fresh "mdF" in
  let Heq23 := fresh "Heq23" in let Hp3 := fresh "Hp3" in let HT3 := fresh "HT3" in
  let KK3 := fresh "KK3" in let KR3 := fresh "KR3" in let Hsb3 := fresh "Hsb3" in
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ (ms_mem ms2)) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (cp_fr_ro _ _ _ P HFx) as Heq3a; clear HFx; rename msx into msF end;
  lazymatch goal with HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem msF) ?mdx _ |- _ =>
    set (mdF := mdx) in * end;
  assert (Heq23 : forall ww, mrestrict (w_H (x_W c)) (ms_mem msF) ww = mrestrict (w_H (x_W c)) mem2 ww)
    by (intros ww; rewrite Heq3a; apply Heq2a);
  pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp3 & _);
  assert (HT3 : tcj_kept B SB_CH_STK lyc Sc (x_W c) memc (x_W c) (ms_mem msF) (x_s1 c) (cp_wr b q cap))
    by (eapply cp_tcj_mono;
        [ exact (cp_tcj_trans _ _ _ _ _ _ _ _ _ _ HT2
            (cp_tcj_eq SB_CH_STK lyc Sc (x_W c) mem2 (ms_mem msF) (x_s1 c) Heq23
               ltac:(intros a Ha; apply Hp3; unfold SB_CH_STK in Ha; lia)))
        | intros a [Ha | []]; exact Ha ]);
  lazymatch type of HAE2 with env_agree _ (Ereg ?r2 ?ex) _ =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ r2 ex KL HS2 ltac:(env_agree_chain HAE2) ltac:(vm_compute; reflexivity)) as KK3 end;
  cbn [ms_regs restrict] in KK3;
  assert (KR3 : forall r, In r KL -> getr (ms_regs msF) r = getr regs r)
    by (intros r Hr; rewrite (KK3 r Hr); apply KR2; unfold cp_cs; cbn [In] in Hr |- *; tauto);
  pose proof (cp_sb_tr c mem2 (ms_mem msF) _ _ _ _ _ Hsb2 ltac:(intros a _; apply aview_eq_of; apply Heq23)) as Hsb3;
  rewrite <- surjective_pairing in Hsb3;
  rewrite <- (sbm_str_snoc cap st0 s (Z.to_nat i)) in Hsb3 by lia;
  replace (S (Z.to_nat i)) with (Z.to_nat (i + 1)) in Hsb3 by lia;
  clear KK3 Heq3a;
  pmkst HS2;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?pc)] =>
    replace (BASE + pc) with (BASE + AF_reac_box_name + stop) by (unfold AF_reac_box_name; lia) end.
(* ---- The copy loop's iteration: one proof script (cp_iter) for the three instances ----
   Arguments: the cut's objects (c lyc Sc memc mdc regs i) and facts at the loop head, by name:
     Hcore : rbn_core; HJ : its journal; Ra0 : a0 = w64 (nth (Z.to_nat i) s 0); R2 R3 R4 R9 R22 : sp, gp, tp, s1, s6;
     RP / RQ / RK : the cursor P = src + i, the look-ahead Q = src + i + 1, K = 2 ^ 64 - 1;
     Hsb : rbn_sb c memc b q cap (fst (sbm_str cap st0 (firstn (Z.to_nat i) s))) (snd (...));
     Hdra : the buffer [q, q + cap) addressable (its scope); Hch : Forall (fun x => 0 < x < 256) s;
     SRC2 : the string's bytes s ++ [0] at src and their shadow, at every memory one sb_ch call on (b, q, cap)
       leaves;
   the slots (head h, return slot hc, exit hx), the registers P Q K (nat and bv 5 forms), the struct (b, q, cap),
   the string (src, s, st0 the struct's state before the loop) and KL, the registers the loop keeps.
   The run from h to the call stores nothing (frame_of_nil); the call is cp_call; at hc a fresh state with the next
   byte as atom 32 (the region cp_rgn P); the UBSan trap (beq P,K) is refuted; the ASan check of Q's shadow byte is
   the token engine's obligation range_addressable Q 1 (from SRC2); the exit test's two branches run to hx or back
   to h (cp_fr_ro: no store). It leaves two goals, at hx and at h, with: msF mdF HJ3 (the final journal), HT3
   (tcj_kept from memc to the final memory with cp_wr b q cap), KR3 (the registers KL as at the head), Hsb3 (the
   struct with i + 1 characters); at hx Hend : i + 1 = |s|; at h Hmore : i + 1 < |s| and N10' NP' NQ'. *)
Ltac cp_iter c lyc Sc memc mdc regs i Hcore HJ Ra0 R2 R3 R4 R9 R22 RP RQ RK Hsb Hdra Hch SRC2
    h hc hx P Pb Q Qb K Kb b q cap src s st0 KL :=
  let E := fresh "E" in let HE := fresh "HE" in let HEI := fresh "HEI" in let HAE := fresh "HAE" in
  let E9 := fresh "E9" in let E10 := fresh "E10" in let HS := fresh "HS" in let SHOK := fresh "SHOK" in
  let HJ0 := fresh "HJ0" in let K1 := fresh "K1" in let K10 := fresh "K10" in let K11 := fresh "K11" in
  let KK := fresh "KK" in let Heq := fresh "Heq" in let Hci := fresh "Hci" in
  remember (Eimg (Ereg regs [])) as E eqn:HE;
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
  assert (HAE : env_agree 32 (Ereg regs []) E)
    by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (E9 : ew E 9 = getr regs 9)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl));
  assert (E10 : ew E 10 = getr regs 10)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl));
  assert (HS : st_ok_pi SEGS VAL E (mkSS (AF_reac_box_name + h) sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + h))) memc (seg_rom SEGS))))
    by (rewrite restrict_mkst_fx; apply pa_entry_st_ok_full;
        [ subst E; apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; exact I
        | split; [exact I | split; exact I] ]);
  assert (SHOK : sh_ok SEGS (SOff 22 0) [] E (mrestrict (w_H (x_W c)) memc)) by constructor;
  clear HE;
  replace (BASE + AF_reac_box_name + h) with (BASE + (AF_reac_box_name + h)) by lia;
  pose proof HJ as HJ0;
  change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + h))) memc (seg_rom SEGS))) in HJ0;
  paj_run_tok RUN HS HJ0 SHOK Bspan; [cbn [ss_mem]; apply awr_ok_nil |];
  pmkst HS;
  rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl);
  prreg HS (1%bv : bv 5) K1; prreg HS (10%bv : bv 5) K10; prreg HS (11%bv : bv 5) K11;
  pose proof (regs_kept_of_st_ok SEGS _ _ _ regs [] cp_cs HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as KK;
  cbn [ms_regs restrict] in KK;
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (fun ww => frame_of_nil _ _ _ ww HFx) as Heq; clear HFx end;
  assert (Hci : 0 < nth (Z.to_nat i) s 0 < 256) by (apply (proj1 (Forall_forall _ _) Hch); apply nth_In; lia);
  rewrite E10, Ra0 in K11; unfold w64 in K11; rewrite cp_and255 in K11 by lia;
  rewrite E9, R9 in K10; unfold w64 in K10; rewrite unsigned_lit_small in K10 by lia;
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) ?QQ =>
    change (SRr SEGS (x_W c) (cfg_at SEGS (BASE + AF_sb_ch) rg mm mdx) QQ) end;
  lazymatch type of K1 with _ = Z_to_bv 64 (BASE + ?ra) =>
  eapply (cp_call c lyc Sc memc mdc regs _ _ _ b q cap _ _ (nth (Z.to_nat i) s 0) ra _ Hcore HJ0 Heq K1 ltac:(lia) eq_refl);
  [ rewrite (KK (2%bv : bv 5)) by (unfold cp_cs; cbn [In]; tauto); exact R2
  | rewrite (KK (3%bv : bv 5)) by (unfold cp_cs; cbn [In]; tauto); exact R3
  | rewrite (KK (4%bv : bv 5)) by (unfold cp_cs; cbn [In]; tauto); exact R4
  | unfold x_nb, x_db, w64; exact K10
  | unfold w64; exact K11
  | lia
  | first [left; split; [reflexivity | split; reflexivity] | right; split; [reflexivity | split; reflexivity]]
  | exact Hsb
  | exact Hdra
  | ] end;
  (* ---- back from sb_ch, at hc ---- *)
  let regs2 := fresh "regs2" in let mem2 := fresh "mem2" in let md2 := fresh "md2" in
  let HJ2 := fresh "HJ2" in let HP2 := fresh "HP2" in let HT2 := fresh "HT2" in let Hsb2 := fresh "Hsb2" in
  intros regs2 mem2 md2 HJ2 HP2 HT2 Hsb2;
  let KR2 := fresh "KR2" in let Gs2 := fresh "Gs2" in let Hrs2 := fresh "Hrs2" in let Hlen1 := fresh "Hlen1" in
  let Vcv := fresh "Vcv" in let Hcv := fresh "Hcv" in let cv := fresh "cv" in
  let E2 := fresh "E2" in let HE2 := fresh "HE2" in let HEI2 := fresh "HEI2" in let HAE2 := fresh "HAE2" in
  let ER := fresh "ER" in let EP := fresh "EP" in let E22 := fresh "E22" in let EK := fresh "EK" in
  let EQ := fresh "EQ" in let E32 := fresh "E32" in let UP := fresh "UP" in let U22 := fresh "U22" in
  let UQ := fresh "UQ" in let U32 := fresh "U32" in let HS2 := fresh "HS2" in let SHOK2 := fresh "SHOK2" in
  let HJ3 := fresh "HJ3" in let Heq2a := fresh "Heq2a" in let ms2 := fresh "ms2" in
  assert (KR2 : forall r, In r cp_cs -> getr regs2 r = getr regs r)
    by (intros r Hr; rewrite (cp_pres _ _ HP2 r Hr); exact (KK r Hr));
  destruct (SRC2 mem2 md2 HJ2 HT2) as (Gs2 & Hrs2);
  assert (Hlen1 : (Z.to_nat (i + 1) < length (s ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia);
  destruct (garr8_nthZ SEGS _ src _ (i + 1) Gs2 ltac:(lia) Hlen1) as (Vcv & Hcv);
  set (cv := nth (Z.to_nat (i + 1)) (s ++ [0]) 0) in *;
  remember (Eimg (Ereg regs2 [Z_to_bv 64 cv])) as E2 eqn:HE2;
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env);
  assert (HAE2 : env_agree 32 (Ereg regs2 [Z_to_bv 64 cv]) E2)
    by (subst E2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (ER : forall (r : bv 5) (n : nat), Z.of_nat n = bv_unsigned r -> (n < 32)%nat -> ew E2 n = getr regs2 r)
    by (intros r n Hn Hn32; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs2 _ n r Hn));
  assert (EP : ew E2 P = Z_to_bv 64 (src + i))
    by (rewrite (ER Pb P eq_refl) by lia; rewrite (KR2 Pb) by (unfold cp_cs; cbn [In]; tauto); exact RP);
  assert (E22 : ew E2 22 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite (ER (22%bv : bv 5) 22%nat eq_refl) by lia; rewrite (KR2 (22%bv : bv 5)) by (unfold cp_cs; cbn [In]; tauto); exact R22);
  assert (EK : ew E2 K = Z_to_bv 64 (2 ^ 64 - 1))
    by (rewrite (ER Kb K eq_refl) by lia; rewrite (KR2 Kb) by (unfold cp_cs; cbn [In]; tauto); exact RK);
  assert (EQ : ew E2 Q = Z_to_bv 64 (src + i + 1))
    by (rewrite (ER Qb Q eq_refl) by lia; rewrite (KR2 Qb) by (unfold cp_cs; cbn [In]; tauto); exact RQ);
  assert (E32 : ew E2 32 = Z_to_bv 64 cv) by (subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0));
  assert (UP : bv_unsigned (ew E2 P) = src + i) by (rewrite EP; apply unsigned_lit_small; lia);
  assert (U22 : bv_unsigned (ew E2 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia);
  assert (UQ : bv_unsigned (ew E2 Q) = src + i + 1) by (rewrite EQ; apply unsigned_lit_small; lia);
  assert (U32 : bv_unsigned (ew E2 32) = cv) by (rewrite E32; apply unsigned_lit_small; lia);
  assert (HS2 : st_ok_pi SEGS VAL E2 (mkSS (AF_reac_box_name + hc) sr_atoms [cp_rgn P] None
      (mkFacts [(22%nat, mkAF SB SB 0); (Q, mkAF 0 (2 ^ 47 - 1) 0); (32%nat, mkAF 0 255 0)] [] []))
    (restrict (w_H (x_W c)) (mkst regs2 (Z_to_bv 64 (BASE + (AF_reac_box_name + hc))) mem2 (seg_rom SEGS))))
    by (rewrite restrict_mkst_fx; apply pa_entry_st_ok_full;
        [ subst E2; apply regs_ok_Eimg_Ereg
        | vm_compute; reflexivity
        | constructor; [|constructor]; unfold region_ok, cp_rgn;
          cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          rewrite UP; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
          constructor; [|constructor];
          apply (chunk_ok_val SEGS E2 _ (src + i) 1 1 (SOff 32 0) cv);
          [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | first [zside | lia] | first [zside | lia]
          | replace (src + i + 1) with (src + (i + 1)) by lia; exact Vcv ]
        | cbn [pairwise_disjoint all_disjoint]; repeat split
        | split; [|split; [exact I | exact I]];
          cbn [f_atoms atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite U22, UQ, U32; change (2 ^ 0) with 1; rewrite !Z.mod_1_r; unfold SB, SHADOW_OFF;
          repeat match goal with |- _ /\ _ => split end; try exact I; lia ]);
  assert (SHOK2 : sh_ok SEGS (SOff 22 0) [] E2 (mrestrict (w_H (x_W c)) mem2)) by constructor;
  clear HE2;
  lazymatch goal with |- context [Z_to_bv 64 (BASE + ?ra)] =>
    replace (BASE + ra) with (BASE + (AF_reac_box_name + hc)) by (unfold AF_reac_box_name; lia) end;
  pose proof HJ2 as HJ3;
  change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + (AF_reac_box_name + hc))) mem2 (seg_rom SEGS))) in HJ3;
  psrr_branch_tok RUN BR HS2 SHOK2 Bspan;
  [ exfalso;
    lazymatch goal with Hx : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U, (U_atom E2 P (src + i) EP), (U_atom E2 K (2 ^ 64 - 1) EK) in Hx by lia;
      apply Z.eqb_eq in Hx; lia end
  | ];
  paj_run_tok RUN HS2 HJ3 SHOK2 Bspan;
  [ rewrite (U_atom E2 Q (src + i + 1) EQ) by lia;
    apply (obl_of_range SEGS _ mem2 E2 (SOff 22 0) (src + i + 1) 1 src (Z.of_nat (length s) + 1) Hrs2);
    [exact (U_atom E2 22 SHADOW_OFF E22 ltac:(unfold SHADOW_OFF; lia)) | lia | lia]
  | lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]
  | ];
  lazymatch goal with HFx : frame_of _ _ (mrestrict _ mem2) (mrestrict _ (ms_mem ?msx)) |- _ =>
    pose proof (cp_fr_ro _ _ _ P HFx) as Heq2a; clear HFx; rename msx into ms2 end;
  (* ---- the exit test: cv = 0 exits ---- *)
  psrr_branch_tok RUN BR HS2 SHOK2 Bspan;
  [ cp_test cv E32; cp_fin c lyc Sc memc regs i hx P b q cap st0 s KL Heq2a mem2 ms2 HT2 HS2 HJ3 SHOK2 HAE2 KR2 Hsb2;
    lazymatch goal with Hz : cv = 0 |- _ =>
      assert (Hend : i + 1 = Z.of_nat (length s))
        by (destruct (Z.lt_ge_cases (i + 1) (Z.of_nat (length s))) as [Hl | Hg]; [|lia];
            exfalso; unfold cv in Hz; rewrite app_nth1 in Hz by lia;
            assert (Hnz : 0 < nth (Z.to_nat (i + 1)) s 0 < 256)
              by (apply (proj1 (Forall_forall _ _) Hch); apply nth_In; lia);
            lia) end
  | cp_test cv E32; cp_fin c lyc Sc memc regs i h P b q cap st0 s KL Heq2a mem2 ms2 HT2 HS2 HJ3 SHOK2 HAE2 KR2 Hsb2;
    lazymatch goal with Hz : cv <> 0 |- _ =>
      assert (Hmore : i + 1 < Z.of_nat (length s))
        by (destruct (Z.lt_ge_cases (i + 1) (Z.of_nat (length s))) as [Hl | Hg]; [exact Hl|];
            exfalso; apply Hz; unfold cv; rewrite app_nth2 by lia;
            replace (Z.to_nat (i + 1) - length s)%nat with 0%nat by lia; reflexivity) end;
    let N10 := fresh "N10" in let NP := fresh "NP" in let NQ := fresh "NQ" in
    lazymatch goal with HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ =>
      prreg HSx (10%bv : bv 5) N10; prreg HSx Pb NP; prreg HSx Qb NQ;
      rewrite E32 in N10; rewrite UP in NP; rewrite UQ in NQ;
      assert (N10' : getr (ms_regs msx) 10 = w64 (nth (Z.to_nat (i + 1)) s 0))
        by (rewrite N10; unfold w64, cv; rewrite app_nth1 by lia; reflexivity);
      assert (NP' : getr (ms_regs msx) Pb = w64 (src + (i + 1))) by (rewrite NP; unfold w64; f_equal; lia);
      assert (NQ' : getr (ms_regs msx) Qb = w64 (src + (i + 1) + 1)) by (rewrite NQ; unfold w64; f_equal; lia);
      clear N10 NP NQ end ].
(* The common facts of a cut state, under the names cp_iter's callers use. *)
Ltac cp_common c lyc Sc memc mdc regs Hcore :=
  pose proof Hcore as (Hpre & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsv & Hfl);
  destruct (cp_lay c lyc Sc memc mdc regs Hcore)
    as (HAR & Hs1al & Hs1 & Hsp0al & Hslo & Hslo2 & Hshi & Hshi2 & HinF & HF & HF0 & HFc & HFal & HFapp & HFS & HF8 & Hpres & EF & Hsub);
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  assert (HES : ESTACK = 4096) by reflexivity;
  pose proof pa_B_ok as HB; pose proof pa_base_lo as HB0.
(* ---- C2 -> C3: the stem -> nb (0x83088 .. 0x830cc; cursor s5, look-ahead s10, -1 in s8) ---- *)
Lemma rbn_cp_stem : forall (k : nat) c st i lyc Sc memc mdc regs,
  Z.of_nat k = Z.of_nat (length (x_stem c)) - i ->
  rbn_C2 B G c st i lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x314)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x358)) mem' (seg_rom SEGS)) md' /\
       rbn_C3 B G c st lyc' Sc' mem' md' regs').
Proof.
induction k as [|k IH]; intros c st i lyc Sc memc mdc regs Hk HC2.
{ destruct HC2 as (_ & _ & _ & Hi & _). lia. }
pose proof HC2 as (Hlive & Hstem & Hw4 & Hi & Ra0 & RP & RQ & RK & R20 & R25 & Hscope & Hsb).
pose proof Hlive as (Hcore & Hok & Hbk & Hsl & R22).
cp_common c lyc Sc memc mdc regs Hcore.
destruct (cp_stem_src c lyc Sc memc mdc st HAR Hstem) as (Hch & Hsrc0 & Hsrc & _ & _).
pose proof (proj1 (proj2 (cp_scope_ra c memc 5 0 248 248 Hscope HF8 HFS)) eq_refl) as Hdra.
assert (SRC2 : forall m' md',
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) memc (x_W c) m' (x_s1 c) (cp_wr (x_nb c) (x_NM c) 24) ->
  garr8 SEGS (mrestrict (w_H (x_W c)) m') st (x_stem c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) m') SHADOW_OFF st (Z.of_nat (length (x_stem c)) + 1)).
{ intros m' md' HJ' HT'.
  destruct (cp_keeps c lyc Sc memc mdc regs m' (x_nb c) (x_NM c) 24 Hcore HT'
    (or_introl (conj eq_refl (conj eq_refl eq_refl)))) as (_ & _ & _ & _ & _ & _ & HEw).
  pose proof (cp_stem_tr c lyc Sc memc mdc regs m' md' st _ Hcore HJ' HT' HEw Hstem) as Hst'.
  destruct (cp_stem_src c lyc Sc m' md' st (proj1 HJ') Hst') as (_ & _ & _ & G' & R'). split; assumption. }
cp_iter c lyc Sc memc mdc regs i Hcore HJ Ra0 R2 R3 R4 R9 R22 RP RQ RK Hsb Hdra Hch SRC2
  0x314 0x320 0x358 21%nat (21%bv : bv 5) 26%nat (26%bv : bv 5) 24%nat (24%bv : bv 5)
  (x_nb c) (x_NM c) 24 st (x_stem c) ([] : list Z, 0)
  ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 24%bv; 25%bv; 27%bv] : list (bv 5)).
all: destruct (cp_carry c lyc Sc memc mdc regs (ms_mem msF) _ (ms_regs msF) (x_nb c) (x_NM c) 24 5 0 248 248
    Hlive Hw4 Hscope HJ3 HT3 (or_introl (conj eq_refl (conj eq_refl eq_refl)))
    ltac:(intros r Hr; apply KR3; cbn [In] in Hr |- *; tauto)) as (Hlive3 & Hw43 & Hscope3).
all: destruct (cp_keeps c lyc Sc memc mdc regs (ms_mem msF) (x_nb c) (x_NM c) 24 Hcore HT3
    (or_introl (conj eq_refl (conj eq_refl eq_refl)))) as (_ & _ & _ & _ & _ & _ & HEw).
all: pose proof (cp_stem_tr c lyc Sc memc mdc regs (ms_mem msF) _ st _ Hcore HJ3 HT3 HEw Hstem) as Hstem3.
- apply SRr_ret. split; [reflexivity|].
  exists lyc, Sc, (ms_regs msF), (ms_mem msF), mdF. split; [reflexivity|].
  split; [exact Hlive3|]. split; [exact Hstem3|]. split; [exact Hw43|].
  split; [rewrite (KR3 (20%bv : bv 5)) by (cbn [In]; tauto); exact R20|].
  split; [rewrite (KR3 (25%bv : bv 5)) by (cbn [In]; tauto); exact R25|].
  split; [exact Hscope3|].
  unfold x_nb_stem. rewrite firstn_all2 in Hsb3 by lia. exact Hsb3.
- apply (IH c st (i + 1) lyc Sc (ms_mem msF) mdF (ms_regs msF)); [lia|].
  split; [exact Hlive3|]. split; [exact Hstem3|]. split; [exact Hw43|]. split; [lia|].
  split; [exact N10'|]. split; [exact NP'|]. split; [exact NQ'|].
  split; [rewrite (KR3 (24%bv : bv 5)) by (cbn [In]; tauto); exact RK|].
  split; [rewrite (KR3 (20%bv : bv 5)) by (cbn [In]; tauto); exact R20|].
  split; [rewrite (KR3 (25%bv : bv 5)) by (cbn [In]; tauto); exact R25|].
  split; [exact Hscope3 | exact Hsb3].
Qed.
(* ---- C4 -> C5: w4 -> nb (0x83128 .. 0x8316c; cursor s4, look-ahead s5, -1 in s8). w4 is four digits
   (bn_ok_dec, bn_w4_length), so the loop runs at most four times; its look-ahead reads W4 + j + 1, inside the five
   bytes the scope byte FS + 4 = 5 opens. ---- *)
Lemma rbn_cp_w4 : forall (k : nat) c j lyc Sc memc mdc regs,
  Z.of_nat k = 4 - j ->
  rbn_C4 B G c j lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3b4)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3f8)) mem' (seg_rom SEGS)) md' /\
       rbn_C5 B G c lyc' Sc' mem' md' regs').
Proof.
induction k as [|k IH]; intros c j lyc Sc memc mdc regs Hk HC4.
{ destruct HC4 as (_ & _ & Hj & _). lia. }
pose proof HC4 as (Hlive & Hw4 & Hj & Hfull & Ra0 & RP & RQ & RK & Hscope & Hsb).
pose proof Hlive as (Hcore & Hok & Hbk & Hsl & R22).
cp_common c lyc Sc memc mdc regs Hcore.
destruct (reac_box_name.args_ok_split _ _ _ _ _ _ _ _ Hok) as (_ & _ & _ & _ & _ & _ & Hbi & Hbo & _).
assert (Hlw : length (x_w4 c) = 4%nat) by (unfold x_w4; apply bn_w4_length; assumption).
assert (Hch : Forall (fun x => 0 < x < 256) (x_w4 c)).
{ unfold x_w4, bn_w4.
  destruct (reac_box_name.bn_ok_dec _ Hbi) as (_ & _ & _ & _ & _ & Di & _).
  destruct (reac_box_name.bn_ok_dec _ Hbo) as (_ & _ & _ & _ & _ & Do & _).
  apply Forall_app. split; (eapply Forall_impl; [|eassumption]); intros x Hx; cbv beta in *; lia. }
assert (Hi : 0 <= j < Z.of_nat (length (x_w4 c))) by (rewrite Hlw; lia).
assert (Hsrc : 0 < x_W4 c /\ x_W4 c + Z.of_nat (length (x_w4 c)) + 1 <= 2 ^ 47 - 1) by (unfold x_W4; rewrite Hlw; lia).
pose proof (proj1 (proj2 (cp_scope_ra c memc 5 0 248 248 Hscope HF8 HFS)) eq_refl) as Hdra.
assert (SRC2 : forall m' md',
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) memc (x_W c) m' (x_s1 c) (cp_wr (x_nb c) (x_NM c) 24) ->
  garr8 SEGS (mrestrict (w_H (x_W c)) m') (x_W4 c) (x_w4 c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) m') SHADOW_OFF (x_W4 c) (Z.of_nat (length (x_w4 c)) + 1)).
{ intros m' md' HJ' HT'.
  destruct (cp_keeps c lyc Sc memc mdc regs m' (x_nb c) (x_NM c) 24 Hcore HT'
    (or_introl (conj eq_refl (conj eq_refl eq_refl)))) as (_ & _ & KW4 & _ & KSC & _ & _).
  pose proof Hw4 as (_ & Gw & _). unfold x_mem_at in Gw.
  split.
  - eapply cp_garr8_kept; [|exact Gw]. intros a Ha. apply KW4. right.
    rewrite length_app in Ha. cbn [length] in Ha. rewrite Hlw in Ha. lia.
  - replace (Z.of_nat (length (x_w4 c)) + 1) with 5 by (rewrite Hlw; reflexivity).
    pose proof (cp_scope_tr c memc m' 5 0 248 248 Hscope KSC) as Hsc'.
    exact (proj1 (cp_scope_ra c m' 5 0 248 248 Hsc' HF8 HFS) eq_refl). }
cp_iter c lyc Sc memc mdc regs j Hcore HJ Ra0 R2 R3 R4 R9 R22 RP RQ RK Hsb Hdra Hch SRC2
  0x3b4 0x3c0 0x3f8 20%nat (20%bv : bv 5) 21%nat (21%bv : bv 5) 24%nat (24%bv : bv 5)
  (x_nb c) (x_NM c) 24 (x_W4 c) (x_w4 c) (x_nb_dash c)
  ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] : list (bv 5)).
all: destruct (cp_carry c lyc Sc memc mdc regs (ms_mem msF) _ (ms_regs msF) (x_nb c) (x_NM c) 24 5 0 248 248
    Hlive Hw4 Hscope HJ3 HT3 (or_introl (conj eq_refl (conj eq_refl eq_refl)))
    ltac:(intros r Hr; apply KR3; cbn [In] in Hr |- *; tauto)) as (Hlive3 & Hw43 & Hscope3).
- apply SRr_ret. split; [reflexivity|].
  exists lyc, Sc, (ms_regs msF), (ms_mem msF), mdF. split; [reflexivity|].
  split; [exact Hlive3|]. split; [exact Hw43|]. split; [exact Hscope3|].
  rewrite firstn_all2 in Hsb3 by lia. rewrite <- Hfull in Hsb3. unfold x_nmc. exact Hsb3.
- apply (IH c (j + 1) lyc Sc (ms_mem msF) mdF (ms_regs msF)); [lia|].
  split; [exact Hlive3|]. split; [exact Hw43|]. split; [rewrite Hlw in Hmore; lia|]. split; [exact Hfull|].
  split; [exact N10'|]. split; [exact NP'|]. split; [exact NQ'|].
  split; [rewrite (KR3 (24%bv : bv 5)) by (cbn [In]; tauto); exact RK|].
  split; [exact Hscope3 | exact Hsb3].
Qed.
(* ---- C8 -> C9: nm -> db (0x83298 .. 0x832dc; cursor s8, look-ahead s4, -1 in s5). nm's characters are 1 .. 255
   (rbn_nm_spec; the stem's from rbn_pre's said, else bn_STEM_chars) and at most 23. ---- *)
Lemma rbn_cp_dp : forall (k : nat) c i lyc Sc memc mdc regs,
  Z.of_nat k = Z.of_nat (length (x_nmc c)) - i ->
  rbn_C8 B G c i lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x524)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x568)) mem' (seg_rom SEGS)) md' /\
       rbn_C9 B G c lyc' Sc' mem' md' regs').
Proof.
induction k as [|k IH]; intros c i lyc Sc memc mdc regs Hk HC8.
{ destruct HC8 as (_ & _ & _ & _ & Hi & _). lia. }
pose proof HC8 as (Hlive & Hw4 & Hnm & Htk & Hi & Ra0 & RP & RQ & RK & Hscope & Hsb).
pose proof Hlive as (Hcore & Hok & Hbk & Hsl & R22).
cp_common c lyc Sc memc mdc regs Hcore.
assert (Hsd : Forall (fun x => 0 < x < 256) (x_sd c)).
{ destruct Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsaid & _).
  destruct (Hsaid Hok) as ([(_ & ->) | (_ & (Hc' & _) & _)] & _); [constructor | exact Hc']. }
destruct (reac_box_name.args_ok_split _ _ _ _ _ _ _ _ Hok) as (_ & _ & _ & _ & _ & _ & Hbi & Hbo & _).
destruct (rbn_nm_spec (x_f c) (x_sd c) (x_i c) (x_o c) Hbi Hbo (bn_stem_chars _ _ Hsd)) as (_ & _ & _ & _ & Hln0 & Hch0).
assert (Hln : (length (x_nmc c) <= 23)%nat) by exact Hln0.
assert (Hch : Forall (fun x => 0 < x < 256) (x_nmc c)) by exact Hch0.
assert (Hsrc : 0 < x_NM c /\ x_NM c + Z.of_nat (length (x_nmc c)) + 1 <= 2 ^ 47 - 1) by (unfold x_NM; lia).
pose proof (proj2 (proj2 (proj2 (cp_scope_ra c memc 5 0 0 0 Hscope HF8 HFS))) eq_refl) as Hdra.
assert (SRC2 : forall m' md',
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) m' md' 0 ->
  tcj_kept B SB_CH_STK lyc Sc (x_W c) memc (x_W c) m' (x_s1 c) (cp_wr (x_db c) (x_DP c) 48) ->
  garr8 SEGS (mrestrict (w_H (x_W c)) m') (x_NM c) (x_nmc c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) m') SHADOW_OFF (x_NM c) (Z.of_nat (length (x_nmc c)) + 1)).
{ intros m' md' HJ' HT'.
  destruct (cp_keeps c lyc Sc memc mdc regs m' (x_db c) (x_DP c) 48 Hcore HT'
    (or_intror (conj eq_refl (conj eq_refl eq_refl)))) as (_ & _ & _ & _ & KSC & KNM & _).
  pose proof Hnm as (_ & Gn & _). unfold x_mem_at in Gn.
  split.
  - eapply cp_garr8_kept; [|exact Gn]. intros a Ha. apply (KNM eq_refl). right.
    rewrite length_app in Ha. cbn [length] in Ha. lia.
  - pose proof (cp_scope_tr c memc m' 5 0 0 0 Hscope KSC) as Hsc'.
    eapply range_addressable_sub; [exact (proj1 (proj2 (cp_scope_ra c m' 5 0 0 0 Hsc' HF8 HFS)) eq_refl) | lia | lia]. }
cp_iter c lyc Sc memc mdc regs i Hcore HJ Ra0 R2 R3 R4 R9 R22 RP RQ RK Hsb Hdra Hch SRC2
  0x524 0x530 0x568 24%nat (24%bv : bv 5) 20%nat (20%bv : bv 5) 21%nat (21%bv : bv 5)
  (x_db c) (x_DP c) 48 (x_NM c) (x_nmc c) ([] : list Z, 0)
  ([2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 21%bv; 22%bv; 23%bv; 25%bv; 26%bv; 27%bv] : list (bv 5)).
all: destruct (cp_carry c lyc Sc memc mdc regs (ms_mem msF) _ (ms_regs msF) (x_db c) (x_DP c) 48 5 0 0 0
    Hlive Hw4 Hscope HJ3 HT3 (or_intror (conj eq_refl (conj eq_refl eq_refl)))
    ltac:(intros r Hr; apply KR3; cbn [In] in Hr |- *; tauto)) as (Hlive3 & Hw43 & Hscope3).
all: destruct (cp_carry_db c lyc Sc memc mdc regs (ms_mem msF) (ms_regs msF) Hcore Hnm Htk HT3
    ltac:(apply KR3; cbn [In]; tauto) ltac:(apply KR3; cbn [In]; tauto)) as (Hnm3 & Htk3).
- apply SRr_ret. split; [reflexivity|].
  exists lyc, Sc, (ms_regs msF), (ms_mem msF), mdF. split; [reflexivity|].
  split; [exact Hlive3|]. split; [exact Hw43|]. split; [exact Hnm3|]. split; [exact Htk3|].
  split; [exact Hscope3|].
  rewrite firstn_all2 in Hsb3 by lia. exact Hsb3.
- apply (IH c (i + 1) lyc Sc (ms_mem msF) mdF (ms_regs msF)); [lia|].
  split; [exact Hlive3|]. split; [exact Hw43|]. split; [exact Hnm3|]. split; [exact Htk3|]. split; [lia|].
  split; [exact N10'|]. split; [exact NP'|]. split; [exact NQ'|].
  split; [rewrite (KR3 (21%bv : bv 5)) by (cbn [In]; tauto); exact RK|].
  split; [exact Hscope3 | exact Hsb3].
Qed.
End walk.
End h.
End f.
End d.
