(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, AF_reac_box_name = 0x2600): the last two segments of the program
   walk, between the cut states of lib/B/Prog/reac_box_name_inv.v.
   - rbn_seg_c10_r: C10 (0x833e0, +0x66c) -> R (0x834ac, +0x738): the db.n bound and pointer-overflow traps (dead),
     dp[db.n] := 0, the four over-flag and three length tests (each failing one goes to 0x83474 with s4 = -1), the
     three copies memcpy(name, nm, nb.n + 1), memcpy(token, tk, tb.n + 1), memcpy(display, dp, db.n + 1)
     (__asan_memcpy, aj_intrin_atS), s4 = 0, the scope close (13 shadow stores 0xf8). The listing's test is
     rbn_ok = bn_accept (reac_box_name_sbm.v rbn_accept_spec).
   - rbn_seg_rel: R -> the post: the magic word at F, __asan_set_shadow_f5(FS, 64), the flag-byte store that frees
     the frame (aj_flag_store_pi), a0 = s4, the reload of ra / s0 .. s11, ret; apost_base with rbn_postQ.
   The segments have no inline ASan check and no taken UBSan trap, so they run on the plain engine (st_ok_pi). *)
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
(* Segment 1's symbolic state at C10 (0x833e0): the window (s1 = x9) with the slots and the four structs' n / over
   fields the listing reads, the scope shadow bytes it closes (s2 = x18, FS + 4 .. FS + 30) and the byte
   dp[db.n] it zeroes (atom 44 = DP + db.n). Extra atoms: 32 db.n, 33 db.over, 34 tb.n, 35 tb.over, 36 nb.n,
   37 nb.over, 38 display, 39 name, 40 token, 41 token_len, 42 display_len, 43 name_len, 44 DP + db.n,
   45 the bitwise complement of DP (0x833ec not a0,s10). *)
Definition rbn_r1_win : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 216 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 38 0)); YP09.mkChunk 8 (CVal 8 (SOff 39 0));
     YP09.mkChunk 16 (CVal 8 (SOff 40 0)); YP09.mkChunk 24 (CVal 8 (SOff 41 0));
     YP09.mkChunk 32 (CVal 8 (SOff 42 0)); YP09.mkChunk 56 (CVal 8 (SOff 43 0));
     YP09.mkChunk 104 (CVal 8 (SOff 32 0)); YP09.mkChunk 112 (CVal 4 (SOff 33 0));
     YP09.mkChunk 136 (CVal 8 (SOff 34 0)); YP09.mkChunk 144 (CVal 4 (SOff 35 0));
     YP09.mkChunk 168 (CVal 8 (SOff 36 0)); YP09.mkChunk 176 (CVal 4 (SOff 37 0));
     YP09.mkChunk 208 (CVal 4 (SLit 0))].
Definition rbn_r1_sh : YP09.region :=
  YP09.mkRegion (Some 18%nat) 4 30 4 30
    [YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0)); YP09.mkChunk 10 (CVal 1 (SLit 0));
     YP09.mkChunk 16 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0));
     YP09.mkChunk 24 (CVal 1 (SLit 0)); YP09.mkChunk 25 (CVal 1 (SLit 0)); YP09.mkChunk 26 (CVal 1 (SLit 0));
     YP09.mkChunk 27 (CVal 1 (SLit 0)); YP09.mkChunk 28 (CVal 1 (SLit 0)); YP09.mkChunk 29 (CVal 1 (SLit 0))].
Definition rbn_r1_dpz : YP09.region := YP09.mkRegion (Some 44%nat) 0 1 0 1 [].
Definition rbn_r1_facts : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
           (32%nat, mkAF 0 47 0); (33%nat, mkAF 0 1 0); (35%nat, mkAF 0 1 0); (37%nat, mkAF 0 1 0);
           (45%nat, mkAF (2 ^ 64 - 1 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 26 0) (SOff 32 0), SOff 44 0); (SAlu ALU_XOR (SOff 26 0) (SLit (-1)), SOff 45 0)].
Definition rbn_r1_ss : sstate :=
  mkSS (AF_reac_box_name + 0x66c) sr_atoms [rbn_r1_win; rbn_r1_sh; rbn_r1_dpz] None rbn_r1_facts.
Lemma rbn_r1_ok_iff : forall wb nb tb db nl tl dl,
  rbn_ok wb nb tb db nl tl dl = true <->
  snd wb = 0 /\ snd nb = 0 /\ snd tb = 0 /\ snd db = 0 /\
  Z.of_nat (length (fst nb)) < nl /\ Z.of_nat (length (fst db)) < dl /\ Z.of_nat (length (fst tb)) < tl.
Proof. intros. unfold rbn_ok. rewrite !andb_true_iff, !Z.eqb_eq, !Z.ltb_lt. tauto. Qed.

(* The symbolic state at R (0x834ac, offset AF_reac_box_name + 0x738): the magic word the listing stores at the
   frame F (s3 = x19 = atom 19), the frame's flag slot at F + 504 (s7 = x23 = atom 23; its value is the extra
   atom 32 = flag_addr), and the registers the epilogue reloads from sp0 - 8 .. sp0 - 104 (s0 = x8 = atom 8;
   extras 33 .. 45 = the caller's ra, s0, s1, s2 .. s11).  The flag byte itself (atom 32) is added to the state
   only after the __asan_set_shadow_f5 call, because its write right is not awr_byte but aj_flag_store_pi's
   own premise. *)
Definition rbn_r2_mag : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 8 [].
Definition rbn_r2_slot : YP09.region :=
  YP09.mkRegion (Some 23%nat) 504 512 0 0 [YP09.mkChunk 504 (CVal 8 (SOff 32 0))].
Definition rbn_r2_sav : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition rbn_r2_flag : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition rbn_r2_facts : facts := mkFacts [(23%nat, mkAF 4096 (2 ^ 47) 5)] [] [].
Definition rbn_r2_ss : sstate :=
  mkSS (AF_reac_box_name + 0x738) sr_atoms [rbn_r2_mag; rbn_r2_slot; rbn_r2_sav] None rbn_r2_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Definition rbn_r1_dbn (c : rbx) : Z := Z.of_nat (length (fst (rbn_dp (x_nmc c) (x_i c) (x_o c)))).
Definition rbn_r1_dbov (c : rbx) : Z := snd (rbn_dp (x_nmc c) (x_i c) (x_o c)).
Definition rbn_r1_tbn (c : rbx) : Z := Z.of_nat (length (fst (rbn_tok (x_nmc c)))).
Definition rbn_r1_tbov (c : rbx) : Z := snd (rbn_tok (x_nmc c)).
Definition rbn_r1_nbn (c : rbx) : Z := Z.of_nat (length (x_nmc c)).
Definition rbn_r1_nbov (c : rbx) : Z := snd (x_nb_full c).
Definition rbn_r1_extra (c : rbx) : list word :=
  map (Z_to_bv 64)
    [rbn_r1_dbn c; rbn_r1_dbov c; rbn_r1_tbn c; rbn_r1_tbov c; rbn_r1_nbn c; rbn_r1_nbov c;
     x_display c; x_name c; x_token c; x_token_len c; x_display_len c; x_name_len c;
     x_DP c + rbn_r1_dbn c; 2 ^ 64 - 1 - x_DP c].
Definition rbn_r1_E (c : rbx) (regs : bvmap 5 word) : env := Eimg (Ereg regs (rbn_r1_extra c)).
(* One byte read through aview, as a 1-byte val_mem, and back. *)
Lemma rbn_r1_val_of_aview : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv. destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr).
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8.
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. unfold bv_wrap.
change (bv_modulus 8) with 256. symmetry. rewrite ?Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
Lemma rbn_r1_aview_of_val : forall H (m : word -> option byte) a v,
  val_mem SEGS (mrestrict H m) a 1 v -> 0 <= v < 256 -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hr. specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
unfold bv_wrap. change (bv_modulus 8) with 256. rewrite ?Z.mod_mod by lia. apply Z.mod_small. lia.
Qed.
Lemma rbn_r1_aview_present : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
(* A byte string copied: garr8 at the source, the destination bytes equal the source bytes. *)
Lemma rbn_r1_garr8_copy : forall H (m m' : word -> option byte) x d l,
  garr8 SEGS (mrestrict H m) x l ->
  (forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m' (d + i) = aview SEGS H m (x + i)) ->
  garr8 SEGS (mrestrict H m') d l.
Proof.
intros H m m' x d l Hg Hc j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply rbn_r1_val_of_aview. rewrite Hc by lia. apply rbn_r1_aview_of_val; assumption.
Qed.
(* Zero shadow granules make a 8-aligned range addressable. *)
Lemma rbn_r1_ra_zero : forall (rd : Z -> option Z) x n,
  x mod 8 = 0 -> 0 <= n ->
  (forall j, 0 <= j < (n + 7) / 8 -> rd (SHADOW_OFF + x / 8 + j) = Some 0) ->
  range_addressable rd SHADOW_OFF x n.
Proof.
intros rd x n Hx Hn HZ y Hy. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. rewrite Hx, Z.add_0_r in Dx.
replace y with (x / 8 * 8 + (y - x)) by lia. rewrite Z.div_add_l by lia. rewrite Z.add_assoc. apply HZ.
split; [apply Z.div_pos; lia|].
replace (n + 7) with (n - 1 + 1 * 8) by lia. rewrite Z.div_add by lia.
pose proof (Z.div_le_mono (y - x) (n - 1) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
(* The scope shadow bytes of nm, tk and dp read back from the shadow region's chunks. *)
Lemma rbn_r1_sh_zero : forall E H (m : word -> option byte) FS,
  region_ok SEGS E (mrestrict H m) rbn_r1_sh -> bv_unsigned (ew E 18) = FS ->
  forall j, 8 <= j < 11 \/ 16 <= j < 19 \/ 24 <= j < 30 -> aview SEGS H m (FS + j) = Some 0.
Proof.
intros E H m FS HR HU j Hj. apply rbn_r1_aview_of_val; [|lia].
destruct HR as (_ & _ & _ & Hcs). unfold rbn_r1_sh in Hcs. cbn [YP09.r_chunks YP09.r_base base_val] in Hcs.
rewrite HU in Hcs.
assert (Hj' : j = 8 \/ j = 9 \/ j = 10 \/ j = 16 \/ j = 17 \/ j = 18 \/ j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29)
  by lia.
assert (Hin : In (YP09.mkChunk j (CVal 1 (SLit 0)))
  [YP09.mkChunk 8 (CVal 1 (SLit 0)); YP09.mkChunk 9 (CVal 1 (SLit 0)); YP09.mkChunk 10 (CVal 1 (SLit 0));
   YP09.mkChunk 16 (CVal 1 (SLit 0)); YP09.mkChunk 17 (CVal 1 (SLit 0)); YP09.mkChunk 18 (CVal 1 (SLit 0));
   YP09.mkChunk 24 (CVal 1 (SLit 0)); YP09.mkChunk 25 (CVal 1 (SLit 0)); YP09.mkChunk 26 (CVal 1 (SLit 0));
   YP09.mkChunk 27 (CVal 1 (SLit 0)); YP09.mkChunk 28 (CVal 1 (SLit 0)); YP09.mkChunk 29 (CVal 1 (SLit 0))]).
{ repeat (destruct Hj' as [-> | Hj']; [repeat first [left; reflexivity | right] |]). subst j.
  repeat first [left; reflexivity | right]. }
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
exact (val_of_chunk_ok SEGS E _ FS j 1 (SLit 0) 0 Hck eq_refl ltac:(lia) ltac:(lia)).
Qed.
(* atoms 32 .. 45: the frame's flag address and the thirteen saved registers (rbn_saved_regs' order). *)
Definition rbn_r2_extra (c : rbx) : list word :=
  [Z_to_bv 64 (flag_addr (x_ly c) 3 (x_fpos c));
   getr (x_regs c) 1; getr (x_regs c) 8; getr (x_regs c) 9; getr (x_regs c) 18;
   getr (x_regs c) 19; getr (x_regs c) 20; getr (x_regs c) 21; getr (x_regs c) 22;
   getr (x_regs c) 23; getr (x_regs c) 24; getr (x_regs c) 25; getr (x_regs c) 26;
   getr (x_regs c) 27].
Definition rbn_r2_E (c : rbx) (regs : bvmap 5 word) : env := Eimg (Ereg regs (rbn_r2_extra c)).
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
(* the copies of the accepting path (0x8344c, 0x8345c, 0x8346c) *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA IB___asan_memcpy).
(* the shadow fill of the frame release (0x834c4), lib/B/Rt/SetShadowDef.v; 245 = 0xf5 *)
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IB___asan_set_shadow_f5) 245.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
(* The frame (3, fpos) of the cut states: owned by the journal, at x_F c in the current layout. *)
Lemma rbn_r1_frame : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  In (3, x_fpos c) (frames Sc) /\ frame_addr lyc 3 (x_fpos c) = x_F c /\ AR SEGS B lyc Sc (x_W c) memc mdc /\
  x_F c mod 32 = 0 /\ in_app (x_F c) 512 /\ 4096 <= x_F c /\ x_F c + 512 <= alloc_ceiling.
Proof.
intros c lyc Sc memc mdc regs (HPRE & HJ & _).
pose proof HPRE as ((HAR0 & _) & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ lyc HAR0 Hly) as (_ & EF & _).
assert (EF3 : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; apply EF).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (Hal & Happ & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (H4096 & Hce & _).
change (fs_frame_bytes 3) with 512 in *. rewrite EF3 in *.
exact (conj Hin (conj eq_refl (conj HAR (conj Hal (conj Happ (conj H4096 Hce)))))).
Qed.
(* Where the stack window and the frame lie (the journal's astk_ok and rbn_r1_frame). *)
Lemma rbn_r1_stk : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  x_sp0 c mod 16 = 0 /\ alloc_ceiling + 8528 <= x_sp0 c /\ x_sp0 c <= 2 ^ 47 /\
  x_s1 c mod 32 = 0 /\ x_sp0 c - 352 < x_s1 c <= x_sp0 c - 320 /\
  (forall a, x_sp0 c - 8528 <= a < x_sp0 c -> apresent (w_H (x_W c)) memc a).
Proof.
intros c lyc Sc memc mdc regs (_ & HJ & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes in Hlo, Hpres.
split; [exact Hal|]. split; [clear - Hceil Hlo; lia|]. split; [clear - Hhi H47; lia|].
split; [unfold x_s1; rewrite Z.mul_comm; apply Z_mod_mult|].
split; [unfold x_s1; clear; pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia));
  pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)); lia|].
intros a Ha. apply Hpres. clear - Ha; lia.
Qed.
(* The symbolic state at C10 (offset 0x66c). *)
Lemma rbn_r1_entry : forall c lyc Sc memc mdc regs,
  rbn_C10 B G c lyc Sc memc mdc regs ->
  st_ok_pi SEGS VAL (rbn_r1_E c regs) rbn_r1_ss
    (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x66c))) memc (seg_rom SEGS))).
Proof.
intros c lyc Sc memc mdc regs HC.
destruct HC as ((HCORE & HARGS & HBK & HSL & R22) & (HWB & HW4 & R27) & (HNB & HNM & R25) & (HTB & HTK & R26)
  & HSCO & HDB).
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & HAR & HFal & HFapp & HF4096 & HFce).
destruct (rbn_r1_stk c lyc Sc memc mdc regs HCORE) as (Hsp0al & Hsp0lo & Hsp0hi & Hs1al & Hs1 & Hpres).
pose proof HCORE as (HPRE & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rname & _ & Rnl & _ & Rtok & _ & Rtl & _ & _
  & Rdisp & _ & Rdl & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold rbn_slots in HSL. cbv zeta in HSL. destruct HSL as (V0 & V8 & V16 & V24 & V32 & _ & _ & V56 & _).
unfold rbn_sb in HDB, HTB, HNB, HWB. cbv zeta in HDB, HTB, HNB, HWB.
destruct HDB as (_ & _ & DBn & DBov & DBov01 & DBlen & _).
destruct HTB as (_ & _ & TBn & TBov & TBov01 & TBlen & _).
destruct HNB as (_ & _ & NBn & NBov & NBov01 & NBlen & _).
destruct HWB as (_ & _ & _ & WBov & _).
fold (rbn_r1_dbn c) in DBn, DBlen. fold (rbn_r1_dbov c) in DBov, DBov01.
fold (rbn_r1_tbn c) in TBn, TBlen. fold (rbn_r1_tbov c) in TBov, TBov01.
fold (rbn_r1_nbn c) in NBn, NBlen. fold (rbn_r1_nbov c) in NBov, NBov01.
assert (Hdb0 : 0 <= rbn_r1_dbn c) by (unfold rbn_r1_dbn; lia).
assert (HDP : x_DP c = x_F c + 192) by reflexivity.
assert (RDP : 4096 <= x_DP c /\ x_DP c + 48 <= 2 ^ 47) by (rewrite HDP; clear - HF4096 HFce C1; lia).
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
rewrite restrict_mkst_fx.
set (E := rbn_r1_E c regs).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (rbn_r1_extra c)) i)
  by (intros i Hi; subst E; unfold rbn_r1_E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 (x_FS c))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E26 : ew E 26 = Z_to_bv 64 (x_DP c))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 (rbn_r1_dbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (rbn_r1_dbov c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (rbn_r1_tbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (rbn_r1_tbov c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 (rbn_r1_nbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = Z_to_bv 64 (rbn_r1_nbov c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = Z_to_bv 64 (x_display c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (x_name c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (x_token c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (E41 : ew E 41 = Z_to_bv 64 (x_token_len c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
assert (E42 : ew E 42 = Z_to_bv 64 (x_display_len c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
assert (E43 : ew E 43 = Z_to_bv 64 (x_name_len c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11)).
assert (E44 : ew E 44 = Z_to_bv 64 (x_DP c + rbn_r1_dbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (2 ^ 64 - 1 - x_DP c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 13)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; clear - Hs1 Hsp0lo Hsp0hi C1; lia).
assert (U18 : bv_unsigned (ew E 18) = x_FS c)
  by (rewrite E18; apply unsigned_lit_small; rewrite HFS; unfold SHADOW_OFF; clear - HF4096 HFce C1 HF8d HF8m; lia).
assert (U44 : bv_unsigned (ew E 44) = x_DP c + rbn_r1_dbn c)
  by (rewrite E44; apply unsigned_lit_small; rewrite HDP; clear - HF4096 HFce C1 Hdb0 DBlen; lia).
assert (U45 : bv_unsigned (ew E 45) = 2 ^ 64 - 1 - x_DP c)
  by (rewrite E45; apply unsigned_lit_small; rewrite HDP; clear - HF4096 HFce C1; lia).
apply pa_entry_st_ok_full.
- subst E. unfold rbn_r1_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold region_ok, rbn_r1_win.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [clear - Hs1 Hsp0lo C1; lia|]. split; [clear - Hs1 Hsp0hi; lia|].
    split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 0 8 _ (x_display c));
        [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rdisp | lia |].
      rewrite Z.add_0_r. exact V0.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 8 8 _ (x_name c));
        [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rname | lia | exact V8].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 16 8 _ (x_token c));
        [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rtok | lia | exact V16].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 24 8 _ (x_token_len c));
        [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rtl | lia | exact V24].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 32 8 _ (x_display_len c));
        [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rdl | lia | exact V32].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 56 8 _ (x_name_len c));
        [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Rnl | lia | exact V56].
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 104 8 _ (rbn_r1_dbn c));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hdb0 DBlen; lia | lia |].
      replace (x_s1 c + 104) with (x_db c + 16) by (unfold x_db; lia). exact DBn.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 112 4 _ (rbn_r1_dbov c));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - DBov01; lia | lia |].
      replace (x_s1 c + 112) with (x_db c + 24) by (unfold x_db; lia). exact DBov.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 136 8 _ (rbn_r1_tbn c));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold rbn_r1_tbn in *; clear - TBlen; lia | lia |].
      replace (x_s1 c + 136) with (x_tb c + 16) by (unfold x_tb; lia). exact TBn.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 144 4 _ (rbn_r1_tbov c));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - TBov01; lia | lia |].
      replace (x_s1 c + 144) with (x_tb c + 24) by (unfold x_tb; lia). exact TBov.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 168 8 _ (rbn_r1_nbn c));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold rbn_r1_nbn in *; clear - NBlen; lia | lia |].
      replace (x_s1 c + 168) with (x_nb c + 16) by (unfold x_nb; lia). exact NBn.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 176 4 _ (rbn_r1_nbov c));
        [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - NBov01; lia | lia |].
      replace (x_s1 c + 176) with (x_nb c + 24) by (unfold x_nb; lia). exact NBov.
    * apply (chunk_ok_val SEGS E _ (x_s1 c) 208 4 _ 0); [reflexivity | lia | lia |].
      replace (x_s1 c + 208) with (x_wb c + 24) by (unfold x_wb; lia). exact WBov.
  + unfold region_ok, rbn_r1_sh.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U18.
    split; [rewrite HFS; unfold SHADOW_OFF; clear - HF4096 HF8d HF8m; lia|].
    split; [rewrite HFS; unfold SHADOW_OFF; clear - HFce C1 HF8d HF8m; lia|].
    split.
    * intros o Ho. apply (apresent_writable SEGS).
      destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (_ & _ & _ & HSp).
      rewrite EF in HSp. change (fs_frame_bytes 3 / 8) with 64 in HSp. unfold shadow_addr in HSp. rewrite HFS.
      exact (proj1 (HSp o ltac:(lia))).
    * unfold rbn_scope in HSCO. cbv zeta in HSCO. destruct HSCO as (_ & Z1 & Z2 & Z3).
      repeat apply Forall_cons; try apply Forall_nil;
        (apply (chunk_ok_val SEGS E _ (x_FS c) _ 1 _ 0);
         [reflexivity | lia | lia |
          apply rbn_r1_val_of_aview; first [apply Z1; lia | apply Z2; lia | apply Z3; lia]]).
  + unfold region_ok, rbn_r1_dpz.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U44. rewrite HDP.
    split; [clear - HF4096 Hdb0; lia|]. split; [clear - HFce C1 DBlen; lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS).
    destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HAR Hin) as (_ & _ & HFp & _).
    rewrite EF in HFp. change (fs_frame_bytes 3) with 512 in HFp.
    exact (proj1 (HFp (x_F c + 192 + rbn_r1_dbn c + o) ltac:(clear - Ho Hdb0 DBlen; lia))).
- apply pairwise_disjoint_of_extents.
  unfold rbn_r1_win, rbn_r1_sh, rbn_r1_dpz, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U18, U44.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite HFS, HDP. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  clear - Hs1 Hsp0lo HF4096 HFce HFapp C1 Hdb0 DBlen HF8d HF8m. repeat split; lia.
- unfold facts_ok, rbn_r1_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I|]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9.
    rewrite E32, E33, E35, E37, U45.
    rewrite (unsigned_lit_small (rbn_r1_dbn c)) by (clear - Hdb0 DBlen; lia).
    rewrite (unsigned_lit_small (rbn_r1_dbov c)) by (clear - DBov01; lia).
    rewrite (unsigned_lit_small (rbn_r1_tbov c)) by (clear - TBov01; lia).
    rewrite (unsigned_lit_small (rbn_r1_nbov c)) by (clear - NBov01; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. change (2 ^ 5) with 32. rewrite HDP.
    clear - Hs1 Hs1al Hsp0lo Hsp0hi C1 Hdb0 DBlen DBov01 TBov01 NBov01 HF4096 HFce.
    repeat split; lia.
  + split; [|split; [|exact I]].
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 26 (x_DP c) E26), (U_atom E 32 (rbn_r1_dbn c) E32), (U_atom E 44 _ E44)
        by (clear - RDP Hdb0 DBlen; lia).
      unfold zcanon, M64. rewrite Z.mod_small by (clear - RDP Hdb0 DBlen; lia). reflexivity.
    * apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 26 (x_DP c) E26), (U_atom E 45 _ E45) by (clear - RDP; lia).
      rewrite U_SLit. unfold zcanon, M64. change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
      rewrite lxor_allones by (clear - RDP; lia).
      rewrite Z.mod_small by (clear - RDP; lia). reflexivity.
Qed.
(* The frame's bytes and its shadow bytes are written under the journal's own [(3, fpos)] (awr_byte case 4). *)
Lemma rbn_r1_awr_frame : forall STK sp0 FP bl0 blc lyc fpos F a,
  frame_addr lyc 3 fpos = F -> F <= a < F + 512 ->
  awr_byte STK sp0 FP bl0 blc lyc [(3, fpos)] a.
Proof.
intros STK sp0 FP bl0 blc lyc fpos F a EF Ha. right; right; right. exists 3, fpos. split; [left; reflexivity|].
left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3) with 512. lia.
Qed.
Lemma rbn_r1_awr_fshadow : forall STK sp0 FP bl0 blc lyc fpos F a,
  frame_addr lyc 3 fpos = F -> SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 64 ->
  awr_byte STK sp0 FP bl0 blc lyc [(3, fpos)] a.
Proof.
intros STK sp0 FP bl0 blc lyc fpos F a EF Ha. right; right; right. exists 3, fpos. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 3 / 8) with 64. unfold shadow_addr. lia.
Qed.
(* rbn_core at a later memory: the journal, the registers and the two memory facts it states (the saved
   registers in the window, the flag pointer in the frame) carried over. *)
Lemma rbn_r1_core_kept : forall c lyc Sc memc mdc regs memF mdF regsF,
  rbn_core B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) memF mdF 0 ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 23 = getr regs 23 ->
  (forall a, x_sp0 c - 104 <= a < x_sp0 c -> aview SEGS (w_H (x_W c)) memF a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall a, x_F c + 504 <= a < x_F c + 512 -> aview SEGS (w_H (x_W c)) memF a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_core B G c lyc Sc memF mdF regsF.
Proof.
intros c lyc Sc memc mdc regs memF mdF regsF (HPRE & _ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & HSAV & HFLAG)
  HJ Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q23 KW KF.
unfold rbn_core. rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q23.
do 11 (split; [assumption|]). split.
- unfold rbn_saved in *. apply Forall_forall. intros p Hpin.
  pose proof (proj1 (Forall_forall _ _) HSAV p Hpin) as Hp. cbv beta in Hp |- *.
  assert (Hfst : 8 <= fst p <= 104)
    by (unfold rbn_saved_regs in Hpin; repeat (destruct Hpin as [<- | Hpin]; [cbn; lia|]); destruct Hpin).
  unfold x_mem_at in *. eapply val_mem_kept; [|exact Hp].
  intros k Hk. apply KW. clear - Hk Hfst. lia.
- rewrite (rdword_ext (aview SEGS (w_H (x_W c)) memc) (aview SEGS (w_H (x_W c)) memF) (x_F c + 504));
    [exact HFLAG|].
  intros k Hk. apply KF. clear - Hk. lia.
Qed.
(* The listing's acceptance test is bn_accept (reac_box_name_sbm.v rbn_accept_spec); wb's over flag is 0. *)
Lemma rbn_r1_acc : forall c,
  rbn_pre B G c ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  rbn_ok (rbn_w4 (x_i c) (x_o c)) (x_nb_full c) (rbn_tok (x_nmc c)) (rbn_dp (x_nmc c) (x_i c) (x_o c))
    (x_name_len c) (x_token_len c) (x_display_len c) =
  reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c)
    (x_token_len c) (x_display c) (x_display_len c) /\
  (reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c)
     (x_token_len c) (x_display c) (x_display_len c) = true ->
   x_nmc c = bn_NM (x_f c) (x_sd c) (x_i c) (x_o c) /\
   fst (rbn_tok (x_nmc c)) = bn_TK (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) /\
   fst (rbn_dp (x_nmc c) (x_i c) (x_o c)) = bn_DP (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) (x_i c) (x_o c)) /\
  snd (rbn_w4 (x_i c) (x_o c)) = 0.
Proof.
intros c HPRE HA.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HBUF & _).
destruct (HBUF HA) as (HSD & _).
assert (Hsd : Forall (fun ch => 0 < ch < 256) (x_sd c))
  by (destruct HSD as [(_ & ->) | (_ & (HF & _) & _)]; [constructor | exact HF]).
destruct (rbn_accept_spec (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c) (x_token_len c)
  (x_display c) (x_display_len c) HA Hsd) as (E1 & E2).
unfold x_nmc, x_nb_full. split; [exact E1|]. split; [exact E2|].
destruct (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_box_name.args_ok_split _ _ _ _ _ _ _ _ HA)
  as (_ & _ & _ & _ & _ & _ & Hi & Ho & _).
rewrite (rbn_w4_spec _ _ Hi Ho). reflexivity.
Qed.
(* An FP byte in a heap block of the entry state lies in a heap block of the current state, below the frame or
   above it, and outside the shadow band. *)
Lemma rbn_r1_fp_where : forall c lyc Sc memc mdc regs a q N,
  rbn_core B G c lyc Sc memc mdc regs ->
  In (q, N) (ablocks B (x_ly c) (x_S c)) -> q <= a < q + N ->
  4096 <= a < alloc_ceiling /\ app_addr a /\ (a < x_F c \/ x_F c + 512 <= a) /\
  In (q, N) (ablocks B lyc Sc).
Proof.
intros c lyc Sc memc mdc regs a q N HCORE Hq Ha.
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & HAR & _).
pose proof HCORE as (_ & _ & HPERM & _).
assert (Hq' : In (q, N) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPERM)); exact Hq).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR Hq') as (_ & H4096 & Hce & Happ & _ & _ & HN).
pose proof (req_size_pos N ltac:(lia)) as (_ & HrN).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 (x_fpos c) HAR Hq' Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 3) with 512 in Hd.
split; [lia|]. split; [apply (in_app_addr q (req_size N) a Happ); lia|]. split; [lia | exact Hq'].
Qed.
(* The refusal: s4 = -1 at R, the buffers as at entry. *)
Lemma rbn_r1_refuse : forall c lyc Sc memc mdc regs memF mdF regsF,
  rbn_C10 B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) memF mdF 0 ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 23 = getr regs 23 -> getr regsF 20 = w64 (-1) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_FS c + 4 <= a < x_FS c + 30) -> a <> x_DP c + rbn_r1_dbn c ->
     aview SEGS (w_H (x_W c)) memF a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_ok (rbn_w4 (x_i c) (x_o c)) (x_nb_full c) (rbn_tok (x_nmc c)) (rbn_dp (x_nmc c) (x_i c) (x_o c))
    (x_name_len c) (x_token_len c) (x_display_len c) = false ->
  rbn_R B G c lyc Sc memF mdF regsF.
Proof.
intros c lyc Sc memc mdc regs memF mdF regsF HC HJF Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q23 Q20 KEEP Hok.
destruct HC as ((HCORE & HARGS & HBK & _ & _) & _ & _ & _ & _ & HDB).
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & HAR & HFal & HFapp & HF4096 & HFce).
destruct (rbn_r1_stk c lyc Sc memc mdc regs HCORE) as (Hsp0al & Hsp0lo & Hsp0hi & Hs1al & Hs1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HDP : x_DP c = x_F c + 192) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
unfold rbn_sb in HDB. cbv zeta in HDB. destruct HDB as (_ & _ & _ & _ & _ & DBlen & _).
fold (rbn_r1_dbn c) in DBlen.
assert (Hdb0 : 0 <= rbn_r1_dbn c) by (unfold rbn_r1_dbn; lia).
pose proof HCORE as (HPRE & _).
destruct (rbn_r1_acc c HPRE HARGS) as (Eacc & _ & _).
unfold rbn_R. split.
{ apply (rbn_r1_core_kept c lyc Sc memc mdc regs memF mdF regsF HCORE HJF Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q23).
  - intros a Ha. apply KEEP; [clear - Ha Hsp0lo Hsp0hi C1; lia | | ];
      rewrite ?HFS, ?HDP; unfold SHADOW_OFF; clear - Ha Hsp0lo HFce HF8d HF8m C1 DBlen; lia.
  - intros a Ha. apply KEEP; [clear - Ha HFce C1 HF4096; lia | | ];
      rewrite ?HFS, ?HDP; unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *;
      clear - Ha HFce HF4096 HFapp HF8d HF8m C1 DBlen; lia. }
cbv zeta. rewrite <- Eacc, Hok. split; [exact Q20|].
intros a HFP (q & N & Hq & Hqa).
destruct (rbn_r1_fp_where c lyc Sc memc mdc regs a q N HCORE Hq Hqa) as (Ha & Happ & Haf & _).
rewrite (KEEP a).
- apply HBK; [exact HFP | exists q, N; split; [exact Hq | exact Hqa]].
- clear - Ha C1. lia.
- rewrite HFS. unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  clear - Happ HF8d HF8m HF4096 HFce C1. lia.
- rewrite HDP. clear - Haf DBlen Hdb0. lia.
Qed.
(* The three FP ranges (bn_args_ok: the pointers are non-null). *)
Lemma rbn_r1_fp_rng : forall c,
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  (forall a, x_name c <= a < x_name c + Z.min (x_name_len c) 24 -> inFP (x_FP c) a) /\
  (forall a, x_token c <= a < x_token c + Z.min (x_token_len c) 24 -> inFP (x_FP c) a) /\
  (forall a, x_display c <= a < x_display c + Z.min (x_display_len c) 48 -> inFP (x_FP c) a) /\
  x_name c <> 0 /\ x_token c <> 0 /\ x_display c <> 0.
Proof.
intros c HA.
destruct (OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.reac_box_name.args_ok_split _ _ _ _ _ _ _ _ HA)
  as (Hn & Ht & Hd & _).
unfold x_FP, rbn_fp. rewrite (proj2 (Z.eqb_neq _ _) Hn), (proj2 (Z.eqb_neq _ _) Ht), (proj2 (Z.eqb_neq _ _) Hd).
split; [intros a Ha; eexists; split; [left; reflexivity | cbn [fst snd]; lia]|].
split; [intros a Ha; eexists; split; [right; left; reflexivity | cbn [fst snd]; lia]|].
split; [intros a Ha; eexists; split; [right; right; left; reflexivity | cbn [fst snd]; lia]|].
auto.
Qed.
(* One copy of the accepting path (0x8344c / 0x8345c / 0x8346c): memcpy(d, x, n) with d in an FP range of a heap
   block of the entry state and x a frame array whose scope shadow is 0 (aj_intrin_atS, AMEMCPY). *)
Lemma rbn_r1_cpy_at : forall c lyc Sc memc mdc regs memT mdT regsT raw d x n len cap,
  rbn_core B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) memT mdT 0 ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n ->
  getr regsT 2 = w64 (x_s1 c) -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
  getr regsT 1 = raw -> YK0s.ret_ok raw ->
  0 < n -> n <= Z.min len cap ->
  (forall a, d <= a < d + Z.min len cap -> inFP (x_FP c) a) ->
  (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= d /\ d + Z.min len cap <= q + N) ->
  x_F c <= x -> x + n <= x_F c + 512 -> x mod 8 = 0 ->
  (forall j, 0 <= j < (n + 7) / 8 -> aview SEGS (w_H (x_W c)) memT (SHADOW_OFF + x / 8 + j) = Some 0) ->
  SRr SEGS (x_W c) (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___asan_memcpy)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = x_W c /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
         [(3, x_fpos c)] lyc Sc (x_W c) mem2 md2 0 /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> aview SEGS (w_H (x_W c)) mem2 (d + i) = aview SEGS (w_H (x_W c)) memT (x + i)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (x_s1 c - ESTACK <= a < x_s1 c) ->
          aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memT a) /\
       (forall a, apresent (w_H (x_W c)) memT a -> apresent (w_H (x_W c)) mem2 a)).
Proof.
intros c lyc Sc memc mdc regs memT mdT regsT raw d x n len cap HCORE HJT R10 R11 R12 R2 R3 R4 R1 Hraw Hn Hnl
  HFPr (q & N & Hq & Hqd & HqN) Hx0 Hxn Hx8 HZ.
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & _ & HFal & HFapp & HF4096 & HFce).
destruct (rbn_r1_stk c lyc Sc memc mdc regs HCORE) as (Hsp0al & Hsp0lo & Hsp0hi & Hs1al & Hs1 & _).
assert (Hmin : n <= Z.min len cap) by exact Hnl.
destruct (rbn_r1_fp_where c lyc Sc memc mdc regs d q N HCORE Hq ltac:(lia)) as (_ & _ & _ & Hq').
pose proof HJT as (HART & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HART Hq') as (_ & Hq4096 & Hqce & Hqapp & _ & _ & HN).
pose proof (req_size_pos N ltac:(lia)) as (_ & HrN).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 (x_fpos c) HART Hq' Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EF in Hd. change (fs_frame_bytes 3) with 512 in Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hsp : spZ regsT = x_sp0 c + (x_s1 c - x_sp0 c))
  by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by (clear - Hs1 Hsp0lo Hsp0hi C1; lia); lia).
assert (Ho16 : (x_s1 c - x_sp0 c) mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as Ds. pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as Dp.
  rewrite Hs1al in Ds. rewrite Hsp0al in Dp.
  replace (x_s1 c - x_sp0 c) with ((2 * (x_s1 c / 32) - x_sp0 c / 16) * 16) by lia. apply Z_mod_mult. }
eapply SRr_mono.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy _ AMEMCPY (x_W c) regsT memT _ _ _ _ _ _ _ _ _ lyc Sc mdT 0
    d x n (x_s1 c - x_sp0 c) raw HJT R10 R11 R12).
  - clear - Hn Hxn Hx0. lia.
  - clear - Hq4096 Hqd. lia.
  - clear - Hqce HrN HqN Hmin C1 Hn. lia.
  - exact Hsp.
  - exact Ho16.
  - clear - Hs1. lia.
  - rewrite Hes. clear - Hs1. lia.
  - exact R3.
  - exact R4.
  - exact R1.
  - exact Hraw.
  - intros a Ha. split.
    + right; left. split; [apply HFPr; clear - Ha Hmin; lia|]. exists q, N. split; [exact Hq'|].
      clear - Ha Hqd HqN HrN Hmin. lia.
    + rewrite Hes. clear - Ha Hqce HqN HrN Hmin Hs1 Hsp0lo. lia.
  - apply (amem_range_sub_app q (req_size N) d n Hqapp Hqce); clear - Hqd HqN HrN Hmin Hn; lia.
  - eapply (range_addressable_of_block SEGS B LAWS); [exact HART | exact Hq' | clear - Hqd; lia |
      clear - HqN HrN Hmin; lia].
  - intros _. eapply (shadow_hull_vis_of_block SEGS B LAWS); [exact HART | exact Hq' | clear - Hqd; lia |
      clear - HqN HrN Hmin; lia | exact Hn].
  - split; [clear - Hx0 HF4096; lia|]. split; [clear - Hxn HFce C1; lia|].
    split.
    { intros a Ha. split.
      - apply rbn_r1_aview_present. destruct (al_frames _ _ LAWS _ _ _ _ _ 3 (x_fpos c) HART Hin) as (_ & _ & HFp & _).
        rewrite EF in HFp. change (fs_frame_bytes 3) with 512 in HFp. exact (proj1 (HFp a ltac:(clear - Ha Hx0 Hxn; lia))).
      - rewrite Hsp, Hes. clear - Ha Hxn HFce Hs1 Hsp0lo. lia. }
    split; [clear - Hd Hqd HqN HrN Hmin Hx0 Hxn; lia|].
    split; [apply (amem_range_sub_app (x_F c) 512 x n HFapp HFce); clear - Hx0 Hxn Hn; lia|].
    split; [apply rbn_r1_ra_zero; [exact Hx8 | clear - Hn; lia | exact HZ]|].
    intros _. eapply (shadow_hull_vis_of_frame SEGS B LAWS); [exact HART | exact Hin | rewrite EF; exact Hx0 |
      rewrite EF; change (fs_frame_bytes 3) with 512; exact Hxn | exact Hn]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Heff & Hfr & Hpres & _).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
split; [exact Heff|]. split; [|exact Hpres].
intros a Ha H1 H2. apply Hfr; [exact Ha | exact H1 |]. replace (x_sp0 c + (x_s1 c - x_sp0 c)) with (x_s1 c) by lia.
exact H2.
Qed.
(* The bytes the refusal paths write between C10 and R: the scope shadow bytes and dp[db.n]. *)
Definition rbn_r1_zr (c : rbx) (a : Z) : Prop := (x_FS c + 4 <= a < x_FS c + 30) \/ a = x_DP c + rbn_r1_dbn c.
Lemma rbn_r1_env_agree : forall c regs, env_agree 32 (Ereg regs (rbn_r1_extra c)) (rbn_r1_E c regs).
Proof. intros c regs. split; [intros n Hn; unfold rbn_r1_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* A refusal path at R: the state the run reached, read back as rbn_R. *)
Lemma rbn_r1_refuse_at : forall c lyc Sc memc mdc regs E ss ms md,
  rbn_C10 B G c lyc Sc memc mdc regs -> E = rbn_r1_E c regs ->
  st_ok_pi SEGS VAL E ss (restrict (w_H (x_W c)) ms) -> ss_resv ss = None ->
  ss_pc ss = AF_reac_box_name + 0x738 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 23%bv] = true ->
  sr_get (ss_regs ss) 20 = SLit 18446744073709551615 ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) (ms_mem ms) md 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_zr c a ->
     aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_ok (rbn_w4 (x_i c) (x_o c)) (x_nb_full c) (rbn_tok (x_nmc c)) (rbn_dp (x_nmc c) (x_i c) (x_o c))
    (x_name_len c) (x_token_len c) (x_display_len c) = false ->
  SRr SEGS (x_W c) (mkCfg ms md)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) mem' (seg_rom SEGS)) md' /\
       rbn_R B G c lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs E ss ms md HC -> HS Hrv Hpc Hcs H20 HJ KEEP Hok.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rbn_r1_extra c) _ HS (rbn_r1_env_agree c regs) Hcs) as Hk.
cbn [ms_regs restrict] in Hk.
pose proof (st_ok_pi_restrict_reg _ _ _ _ 20%bv HS) as R20. rewrite H20 in R20. cbn [sv_denot] in R20.
rewrite Hms. apply SRr_ret. split; [reflexivity|].
exists lyc, Sc, (ms_regs ms), (ms_mem ms), md. split; [rewrite Z.add_assoc; reflexivity|].
apply (rbn_r1_refuse c lyc Sc memc mdc regs (ms_mem ms) md (ms_regs ms) HC HJ);
  try (apply Hk; cbn; tauto).
- rewrite R20. apply bv_eq. reflexivity.
- intros a Ha H1 H2. apply KEEP; [exact Ha|]. unfold rbn_r1_zr. tauto.
- exact Hok.
Qed.
(* The bytes the accepting path writes between C10 and R: rbn_r1_zr, the stack below s1 (the three memcpy calls)
   and the three copies. *)
Definition rbn_r1_za (c : rbx) (a : Z) : Prop :=
  rbn_r1_zr c a \/ (x_s1 c - ESTACK <= a < x_s1 c) \/ (x_name c <= a < x_name c + rbn_r1_nbn c + 1) \/
  (x_token c <= a < x_token c + rbn_r1_tbn c + 1) \/ (x_display c <= a < x_display c + rbn_r1_dbn c + 1).
(* Every FP byte lies in a heap block of the entry state (bn_args_ok gives rbn_bufs), below alloc_ceiling, in
   application memory, off the frame. *)
Lemma rbn_r1_fp_blk : forall c lyc Sc memc mdc regs a,
  rbn_core B G c lyc Sc memc mdc regs ->
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  inFP (x_FP c) a ->
  (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N) /\
  4096 <= a < alloc_ceiling /\ app_addr a /\ (a < x_F c \/ x_F c + 512 <= a).
Proof.
intros c lyc Sc memc mdc regs a HCORE HA HFP.
pose proof HCORE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HBUF & _).
destruct (HBUF HA) as (_ & Bn & Bt & Bd & _).
assert (Hq : exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N).
{ unfold x_FP in HFP. apply rbn_fp_in in HFP.
  destruct HFP as [(_ & Ha) | [(_ & Ha) | (_ & Ha)]];
  [destruct Bn as (q & N & HqN & H1 & H2) | destruct Bt as (q & N & HqN & H1 & H2) | destruct Bd as (q & N & HqN & H1 & H2)];
  exists q, N; (split; [exact HqN | clear - Ha H1 H2; lia]). }
destruct Hq as (q & N & HqN & Ha).
destruct (rbn_r1_fp_where c lyc Sc memc mdc regs a q N HCORE HqN Ha) as (H1 & H2 & H3 & _).
split; [exists q, N; auto|]. auto.
Qed.
(* The accepting path at R: s4 = 0, the three strings copied with their NUL, the rest of FP as at entry. *)
Lemma rbn_r1_accept_at : forall c lyc Sc memc mdc regs E ss ms md,
  rbn_C10 B G c lyc Sc memc mdc regs -> env_agree 32 (Ereg regs (rbn_r1_extra c)) E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H (x_W c)) ms) -> ss_resv ss = None ->
  ss_pc ss = AF_reac_box_name + 0x738 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 23%bv] = true ->
  sr_get (ss_regs ss) 20 = SLit 0 ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) (ms_mem ms) md 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_za c a ->
     aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall i, 0 <= i < rbn_r1_nbn c + 1 ->
     aview SEGS (w_H (x_W c)) (ms_mem ms) (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)) ->
  (forall i, 0 <= i < rbn_r1_tbn c + 1 ->
     aview SEGS (w_H (x_W c)) (ms_mem ms) (x_token c + i) = aview SEGS (w_H (x_W c)) memc (x_TK c + i)) ->
  (forall i, 0 <= i < rbn_r1_dbn c ->
     aview SEGS (w_H (x_W c)) (ms_mem ms) (x_display c + i) = aview SEGS (w_H (x_W c)) memc (x_DP c + i)) ->
  aview SEGS (w_H (x_W c)) (ms_mem ms) (x_display c + rbn_r1_dbn c) = Some 0 ->
  rbn_ok (rbn_w4 (x_i c) (x_o c)) (x_nb_full c) (rbn_tok (x_nmc c)) (rbn_dp (x_nmc c) (x_i c) (x_o c))
    (x_name_len c) (x_token_len c) (x_display_len c) = true ->
  SRr SEGS (x_W c) (mkCfg ms md)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) mem' (seg_rom SEGS)) md' /\
       rbn_R B G c lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs E ss ms md HC HAE HS Hrv Hpc Hcs H20 HJ KEEP CN CT CD CZ Hok.
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS Hrv) as Hms. rewrite Hpc in Hms.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs (rbn_r1_extra c) _ HS HAE Hcs) as Hk.
cbn [ms_regs restrict] in Hk.
pose proof (st_ok_pi_restrict_reg _ _ _ _ 20%bv HS) as R20. rewrite H20 in R20. cbn [sv_denot] in R20.
destruct HC as ((HCORE & HARGS & HBK & _ & _) & _ & (HNB & HNM & _) & (HTB & HTK & _) & _ & HDB).
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & HAR & HFal & HFapp & HF4096 & HFce).
destruct (rbn_r1_stk c lyc Sc memc mdc regs HCORE) as (Hsp0al & Hsp0lo & Hsp0hi & Hs1al & Hs1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HDP : x_DP c = x_F c + 192) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
unfold rbn_sb in HDB, HTB, HNB. cbv zeta in HDB, HTB, HNB.
destruct HDB as (_ & _ & _ & _ & _ & DBlen & _ & DBg). fold (rbn_r1_dbn c) in DBlen.
destruct HTB as (_ & _ & _ & _ & _ & TBlen & _). fold (rbn_r1_tbn c) in TBlen.
destruct HNB as (_ & _ & _ & _ & _ & NBlen & _). fold (rbn_r1_nbn c) in NBlen.
pose proof Hok as Hok'. apply rbn_r1_ok_iff in Hok'. destruct Hok' as (_ & _ & _ & _ & Hnl & Hdl & Htl).
change (Z.of_nat (length (fst (x_nb_full c)))) with (rbn_r1_nbn c) in Hnl.
fold (rbn_r1_dbn c) in Hdl. fold (rbn_r1_tbn c) in Htl.
assert (D0 : 0 <= rbn_r1_dbn c) by (unfold rbn_r1_dbn; lia).
assert (T0 : 0 <= rbn_r1_tbn c) by (unfold rbn_r1_tbn; lia).
assert (N0 : 0 <= rbn_r1_nbn c) by (unfold rbn_r1_nbn; lia).
destruct (rbn_r1_fp_rng c HARGS) as (FPn & FPt & FPd & _).
assert (HR : forall a, (x_name c <= a < x_name c + rbn_r1_nbn c + 1) \/ (x_token c <= a < x_token c + rbn_r1_tbn c + 1) \/
  (x_display c <= a < x_display c + rbn_r1_dbn c + 1) -> inFP (x_FP c) a).
{ intros a [Ha | [Ha | Ha]]; [apply FPn | apply FPt | apply FPd]; clear - Ha Hnl Htl Hdl NBlen TBlen DBlen; lia. }
assert (HB : forall a, inFP (x_FP c) a -> 4096 <= a < alloc_ceiling /\ app_addr a /\ (a < x_F c \/ x_F c + 512 <= a))
  by (intros a Ha; exact (proj2 (rbn_r1_fp_blk c lyc Sc memc mdc regs a HCORE HARGS Ha))).
pose proof HCORE as (HPRE & _).
destruct (rbn_r1_acc c HPRE HARGS) as (Eacc & Econt & _).
assert (Hacc : reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c) (x_token c)
  (x_token_len c) (x_display c) (x_display_len c) = true) by (rewrite <- Eacc; exact Hok).
destruct (Econt Hacc) as (ENM & ETK & EDP).
rewrite Hms. apply SRr_ret. split; [reflexivity|].
exists lyc, Sc, (ms_regs ms), (ms_mem ms), md. split; [rewrite Z.add_assoc; reflexivity|].
unfold rbn_R. split.
{ apply (rbn_r1_core_kept c lyc Sc memc mdc regs (ms_mem ms) md (ms_regs ms) HCORE HJ); try (apply Hk; cbn; tauto).
  - intros a Ha. apply KEEP; [clear - Ha Hsp0lo Hsp0hi C1; lia|].
    unfold rbn_r1_za, rbn_r1_zr. intros [[Hz | Hz] | [Hz | Hz]].
    + rewrite HFS in Hz. unfold SHADOW_OFF in Hz. clear - Ha Hz Hsp0lo HFce HF8d HF8m C1. lia.
    + rewrite HDP in Hz. clear - Ha Hz Hsp0lo HFce C1 DBlen. lia.
    + rewrite Hes in Hz. clear - Ha Hz Hs1. lia.
    + destruct (HB a (HR a Hz)) as (Hb & _). clear - Ha Hb Hsp0lo. lia.
  - intros a Ha. apply KEEP; [clear - Ha HFce C1 HF4096; lia|].
    unfold rbn_r1_za, rbn_r1_zr. intros [[Hz | Hz] | [Hz | Hz]].
    + rewrite HFS in Hz. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
      clear - Ha Hz HFce HF4096 HFapp HF8d HF8m C1. lia.
    + rewrite HDP in Hz. clear - Ha Hz DBlen. lia.
    + rewrite Hes in Hz. clear - Ha Hz Hs1 HFce Hsp0lo. lia.
    + destruct (HB a (HR a Hz)) as (_ & _ & Hb). clear - Ha Hb. lia. }
cbv zeta. rewrite <- Eacc, Hok. split; [rewrite R20; reflexivity|].
rewrite <- ENM in ETK, EDP |- *. rewrite <- ETK, <- EDP.
assert (LN : Z.of_nat (length (x_nmc c)) = rbn_r1_nbn c) by reflexivity.
assert (LT : Z.of_nat (length (fst (rbn_tok (x_nmc c)))) = rbn_r1_tbn c) by reflexivity.
assert (LD : Z.of_nat (length (fst (rbn_dp (x_nmc c) (x_i c) (x_o c)))) = rbn_r1_dbn c) by reflexivity.
split.
{ apply (rbn_r1_garr8_copy _ memc (ms_mem ms) (x_NM c) (x_name c) _ HNM).
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply CN. clear - Hi LN. lia. }
split.
{ apply (rbn_r1_garr8_copy _ memc (ms_mem ms) (x_TK c) (x_token c) _ HTK).
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply CT. clear - Hi LT. lia. }
split.
{ apply garr8_app. split.
  - apply (rbn_r1_garr8_copy _ memc (ms_mem ms) (x_DP c) (x_display c) _ DBg).
    intros i Hi. apply CD. clear - Hi LD. lia.
  - intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth]. split; [|lia].
    rewrite LD. cbn [Z.of_nat]. rewrite Z.add_0_r. apply rbn_r1_val_of_aview. exact CZ. }
intros a HFP H1 H2 H3. rewrite LN, LT, LD in *.
destruct (rbn_r1_fp_blk c lyc Sc memc mdc regs a HCORE HARGS HFP) as (Hq & Ha & Happ & Haf).
rewrite (KEEP a).
- apply HBK; [exact HFP | exact Hq].
- clear - Ha C1. lia.
- unfold rbn_r1_za, rbn_r1_zr. intros [[Hz | Hz] | [Hz | [Hz | [Hz | Hz]]]].
  + rewrite HFS in Hz. unfold app_addr, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
    clear - Happ Hz HF8d HF8m HF4096 HFce C1. lia.
  + rewrite HDP in Hz. clear - Haf Hz DBlen D0. lia.
  + rewrite Hes in Hz. clear - Ha Hz Hs1 Hsp0lo. lia.
  + exact (H1 Hz).
  + exact (H2 Hz).
  + exact (H3 Hz).
Qed.
(* Which bytes are outside rbn_r1_zr / the stack below s1. *)
Lemma rbn_r1_notzr_app : forall c a,
  4096 <= x_F c -> in_app (x_F c) 512 -> x_F c + 512 <= alloc_ceiling -> rbn_r1_dbn c <= 47 ->
  app_addr a -> (a < x_F c \/ x_F c + 512 <= a) -> ~ rbn_r1_zr c a.
Proof.
intros c a HF0 HFapp HFce D1 Happ Haf. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
assert (D0 : 0 <= rbn_r1_dbn c) by (unfold rbn_r1_dbn; lia).
unfold rbn_r1_zr, x_FS, x_DP. unfold app_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
lia.
Qed.
Lemma rbn_r1_notzr_frame : forall c a,
  4096 <= x_F c -> in_app (x_F c) 512 -> x_F c <= a < x_F c + 512 -> a <> x_DP c + rbn_r1_dbn c ->
  ~ rbn_r1_zr c a.
Proof.
intros c a HF0 HFapp Ha Hne. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
unfold rbn_r1_zr, x_FS. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
Lemma rbn_r1_sh_notapp : forall c a,
  4096 <= x_F c -> in_app (x_F c) 512 -> x_FS c + 4 <= a < x_FS c + 30 -> ~ app_addr a.
Proof.
intros c a HF0 HFapp Ha. pose proof asan_consts as (C1 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
unfold x_FS in Ha. unfold app_addr, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
Lemma rbn_r1_dpz_zero : forall E H (m : word -> option byte) v,
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some 44%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) ->
  bv_unsigned (ew E 44) = v -> aview SEGS H m v = Some 0.
Proof.
intros E H m v (_ & _ & _ & Hcs) HU. cbn [YP09.r_chunks YP09.r_base base_val] in Hcs. rewrite HU in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ (or_introl eq_refl)) as Hck.
pose proof (val_of_chunk_ok SEGS E _ v 0 1 (SLit 0) 0 Hck eq_refl ltac:(lia) ltac:(lia)) as Hv.
rewrite Z.add_0_r in Hv. exact (rbn_r1_aview_of_val H m v 0 Hv ltac:(lia)).
Qed.
Local Ltac r1_envs :=
  lazymatch goal with HS : st_ok_pi _ _ (havoc ?E0 ?k ?ws) _ _, HEI0 : img_env _ _ ?E0,
    U9 : bv_unsigned (ew ?E0 9%nat) = ?v9, U18 : bv_unsigned (ew ?E0 18%nat) = ?v18,
    U44 : bv_unsigned (ew ?E0 44%nat) = ?v44 |- _ =>
    let h0 := fresh "HEIc" in let h1 := fresh "UE9" in let h2 := fresh "UE18" in let h3 := fresh "UE44" in
    pose proof (img_env_havoc_hi E0 k ws HEI0 ltac:(cbv; lia)) as h0;
    assert (h1 : bv_unsigned (ew (havoc E0 k ws) 9) = v9) by (rewrite ew_havoc_old by (cbv; lia); exact U9);
    assert (h2 : bv_unsigned (ew (havoc E0 k ws) 18) = v18) by (rewrite ew_havoc_old by (cbv; lia); exact U18);
    assert (h3 : bv_unsigned (ew (havoc E0 k ws) 44) = v44) by (rewrite ew_havoc_old by (cbv; lia); exact U44)
  end.
Local Ltac r1_awr :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen;
    [ reflexivity
    | lazymatch goal with |- bv_unsigned (ew ?Ex 18%nat) = _ =>
        match goal with U : bv_unsigned (ew Ex 18%nat) = _ |- _ => exact U end end
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      lazymatch goal with EF : frame_addr _ 3 _ = x_F ?c, HFS : x_FS ?c = _ |- _ =>
        apply (rbn_r1_awr_fshadow _ _ _ _ _ _ _ _ a EF); rewrite HFS in Ha; clear - Ha; lia end
    | ]
  | eapply awr_ok_cons_gen;
    [ reflexivity
    | lazymatch goal with |- bv_unsigned (ew ?Ex 44%nat) = _ =>
        match goal with U : bv_unsigned (ew Ex 44%nat) = _ |- _ => exact U end end
    | let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
      lazymatch goal with EF : frame_addr _ 3 _ = x_F ?c, HDP : x_DP ?c = _, D0 : 0 <= rbn_r1_dbn ?c,
        D1 : rbn_r1_dbn ?c <= 47 |- _ =>
        apply (rbn_r1_awr_frame _ _ _ _ _ _ _ _ a EF); rewrite HDP in Ha; clear - Ha D0 D1; lia end
    | ] ].
Local Ltac r1_win :=
  let bb0 := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hw := fresh "Hw" in let Hr := fresh "Hr" in
  intros bb0 wlo whi x Hw Hr;
  vm_compute in Hw;
  repeat (destruct Hw as [Hw | Hw];
    [ injection Hw as <- <- <-; cbn [base_val] in Hr;
      repeat match goal with Ux : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Ux in Hr end;
      unfold rbn_r1_za, rbn_r1_zr; clear - Hr; lia
    | ]);
  try destruct Hw.
Local Ltac r1_keep :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict ?H ?m0) (mrestrict _ ?m1),
    KP : forall a, _ -> ~ ?Zs a -> aview ?sg ?H ?m0 a = aview _ _ ?mem a |- _ =>
    let K2 := fresh "KEEPn" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview sg H m1 a = aview sg H mem a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
      intros a Ha Hz;
      refine (eq_trans (kept_of_frame Ex rs H m0 m1 Zs HFr _ a Ha Hz) (KP a Ha Hz)); r1_win
    | clear KP; rename K2 into KEEP; repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx end;
      try match goal with Hx : mem_grows _ _ |- _ => clear Hx end ]
  end;
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite ?wvb_collapse in HJ |- * end.
Local Ltac r1_hc Hc :=
  rewrite ?branch_ne_U, ?branch_eq_U, ?branch_ltu_U, ?branch_geu_U in Hc;
  repeat match type of Hc with context [U ?Ex (SOff ?i 0)] =>
    match goal with Ux : U Ex (SOff i 0) = _ |- _ => rewrite Ux in Hc end end;
  rewrite ?(U_lit _ 0) in Hc by (clear; lia);
  rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in Hc;
  rewrite ?Z.eqb_neq, ?Z.eqb_eq, ?Z.ltb_lt, ?Z.ltb_ge in Hc.
Local Ltac r1_ok_false Hc :=
  lazymatch goal with |- rbn_ok ?a ?b ?d ?e ?f ?g ?h = false =>
    let Hk := fresh "Hk" in destruct (rbn_ok a b d e f g h) eqn:Hk; [|reflexivity];
    apply rbn_r1_ok_iff in Hk; exfalso; clear - Hk Hc;
    unfold rbn_r1_nbov, rbn_r1_tbov, rbn_r1_dbov, rbn_r1_nbn, rbn_r1_dbn, rbn_r1_tbn, x_nmc in *; lia end.
Local Ltac r1_refuse Hc :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    paj_run_to_shc RUNTOP HS HJ (AF_reac_box_name + 0x738); [r1_awr|] end;
  r1_keep;
  lazymatch goal with
  | HC : rbn_C10 _ _ ?c ?lyc ?Sc ?memc ?mdc ?regs, HE : ?E = rbn_r1_E _ _, HS : st_ok_pi _ _ ?E _ _,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, KEEP : forall a, _ -> ~ rbn_r1_zr _ a -> _ |- _ =>
    eapply (rbn_r1_refuse_at c lyc Sc memc mdc regs E _ _ _ HC HE HS eq_refl eq_refl
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ KEEP);
    r1_ok_false Hc
  end.
Lemma rbn_seg_c10_r : forall c lyc Sc memc mdc regs,
  rbn_C10 B G c lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x66c)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) mem' (seg_rom SEGS)) md' /\
       rbn_R B G c lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs HC.
pose proof (rbn_r1_entry c lyc Sc memc mdc regs HC) as HS.
pose proof HC as ((HCORE & HARGS & HBK & HSL & R22) & (HWB & HW4 & R27) & (HNB & HNM & R25) & (HTB & HTK & R26)
  & HSCO & HDB).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & HSAV & HFLAG).
destruct (rbn_r1_frame c lyc Sc memc mdc regs HCORE) as (Hin & EF & HAR & HFal & HFapp & HF4096 & HFce).
destruct (rbn_r1_stk c lyc Sc memc mdc regs HCORE) as (Hsp0al & Hsp0lo & Hsp0hi & Hs1al & Hs1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HDP : x_DP c = x_F c + 192) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as HF8d. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as HF8m.
pose proof HDB as HDB'. unfold rbn_sb in HDB'. cbv zeta in HDB'.
destruct HDB' as (_ & _ & _ & _ & DBov01 & DBlen & _).
fold (rbn_r1_dbn c) in DBlen. fold (rbn_r1_dbov c) in DBov01.
assert (D0 : 0 <= rbn_r1_dbn c) by (unfold rbn_r1_dbn; lia).
assert (D1 : rbn_r1_dbn c <= 47) by (clear - DBlen; lia). clear DBlen.
pose proof HTB as HTB'. unfold rbn_sb in HTB'. cbv zeta in HTB'.
destruct HTB' as (_ & _ & _ & _ & TBov01 & TBlen & _).
fold (rbn_r1_tbn c) in TBlen. fold (rbn_r1_tbov c) in TBov01.
pose proof HNB as HNB'. unfold rbn_sb in HNB'. cbv zeta in HNB'.
destruct HNB' as (_ & _ & _ & _ & NBov01 & NBlen & _).
fold (rbn_r1_nbn c) in NBlen. fold (rbn_r1_nbov c) in NBov01.
assert (T0 : 0 <= rbn_r1_tbn c) by (unfold rbn_r1_tbn; lia).
assert (N0 : 0 <= rbn_r1_nbn c) by (unfold rbn_r1_nbn; lia).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rname & _ & Rnl & _ & Rtok & _ & Rtl & _ & _
  & Rdisp & _ & Rdl & _).
remember (rbn_r1_E c regs) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold rbn_r1_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs (rbn_r1_extra c)) i)
  by (intros i Hi; subst E; unfold rbn_r1_E; apply Eimg_low; exact Hi).
assert (U18 : bv_unsigned (ew E 18) = x_FS c)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; apply unsigned_lit_small; rewrite HFS; unfold SHADOW_OFF;
      clear - HF4096 HFce C1 HF8d HF8m; lia).
assert (U44 : bv_unsigned (ew E 44) = x_DP c + rbn_r1_dbn c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_extra regs _ 12); apply unsigned_lit_small;
      rewrite HDP; clear - HF4096 HFce C1 D0 D1; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; clear - Hs1 Hsp0lo Hsp0hi C1; lia).
assert (U32 : U E (SOff 32 0) = rbn_r1_dbn c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0) | clear - D0 D1; lia]).
assert (U33 : U E (SOff 33 0) = rbn_r1_dbov c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1) | clear - DBov01; lia]).
assert (U34 : U E (SOff 34 0) = rbn_r1_tbn c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2) | clear - T0 TBlen; lia]).
assert (U35 : U E (SOff 35 0) = rbn_r1_tbov c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3) | clear - TBov01; lia]).
assert (U36 : U E (SOff 36 0) = rbn_r1_nbn c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4) | clear - N0 NBlen; lia]).
assert (U37 : U E (SOff 37 0) = rbn_r1_nbov c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5) | clear - NBov01; lia]).
assert (U41 : U E (SOff 41 0) = x_token_len c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9) | exact Rtl]).
assert (U42 : U E (SOff 42 0) = x_display_len c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10) | exact Rdl]).
assert (U43 : U E (SOff 43 0) = x_name_len c)
  by (apply U_atom; [rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 11) | exact Rnl]).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_zr c a ->
  aview SEGS (w_H (x_W c)) memc a = aview SEGS (w_H (x_W c)) memc a) by (intros; reflexivity).
replace (BASE + AF_reac_box_name + 0x66c) with (BASE + (AF_reac_box_name + 0x66c)) by lia.
(* to the nb.over test (0x8340c): the two traps are decided by the facts, dp[db.n] := 0, wb.over = 0 *)
paj_run_sh RUNP HS HJ; [r1_awr|]. cbn [ms_mem mkst] in HF, HFr, HG. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok1.
(* tb.over (0x83414), db.over (0x8341c), nb.n < name_len (0x83428), db.n < display_len (0x83430),
   tb.n < token_len (0x8343c): each failing test goes to 0x83474 with s4 = -1 *)
paj_run_sh RUNP HS HJ; [r1_awr|]. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok2.
paj_run_sh RUNP HS HJ; [r1_awr|]. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok3.
paj_run_sh RUNP HS HJ; [r1_awr|]. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok4.
paj_run_sh RUNP HS HJ; [r1_awr|]. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok5.
paj_run_sh RUNP HS HJ; [r1_awr|]. r1_keep.
psrr_branch_pi RUNP BR HS.
{ r1_hc Hc. r1_refuse Hc. }
r1_hc Hc. rename Hc into Hok6.
(* accepted (rbn_ok = true): the three copies *)
assert (Hacc : rbn_ok (rbn_w4 (x_i c) (x_o c)) (x_nb_full c) (rbn_tok (x_nmc c)) (rbn_dp (x_nmc c) (x_i c) (x_o c))
  (x_name_len c) (x_token_len c) (x_display_len c) = true).
{ apply rbn_r1_ok_iff. destruct (rbn_r1_acc c HPRE HARGS) as (_ & _ & Hw0).
  unfold rbn_r1_nbov, rbn_r1_tbov, rbn_r1_dbov, rbn_r1_nbn, rbn_r1_dbn, rbn_r1_tbn, x_nmc in *.
  repeat split; assumption. }
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & HBUF & _).
destruct (HBUF HARGS) as (_ & Bn & Bt & Bd & Dnt & Dnd & Dtd).
destruct (rbn_r1_fp_rng c HARGS) as (FPn & FPt & FPd & _).
assert (HBF : forall a, inFP (x_FP c) a -> 4096 <= a < alloc_ceiling /\ app_addr a /\ (a < x_F c \/ x_F c + 512 <= a))
  by (intros a Ha; exact (proj2 (rbn_r1_fp_blk c lyc Sc memc mdc regs a HCORE HARGS Ha))).
assert (HRn : forall a, x_name c <= a < x_name c + rbn_r1_nbn c + 1 -> inFP (x_FP c) a)
  by (intros a Ha; apply FPn; clear - Ha Hok4 NBlen; lia).
assert (HRt : forall a, x_token c <= a < x_token c + rbn_r1_tbn c + 1 -> inFP (x_FP c) a)
  by (intros a Ha; apply FPt; clear - Ha Hok6 TBlen; lia).
assert (HRd : forall a, x_display c <= a < x_display c + rbn_r1_dbn c + 1 -> inFP (x_FP c) a)
  by (intros a Ha; apply FPd; clear - Ha Hok5 D1; lia).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HF32 : x_F c = 32 * (x_F c / 32))
  by (pose proof (Z.div_mod (x_F c) 32 ltac:(lia)) as D; rewrite HFal in D; lia).
assert (ENM8 : x_NM c / 8 = x_F c / 8 + 8)
  by (unfold x_NM; replace (x_F c + 64) with (x_F c + 8 * 8) by lia; apply Z.div_add; lia).
assert (ETK8 : x_TK c / 8 = x_F c / 8 + 16)
  by (unfold x_TK; replace (x_F c + 128) with (x_F c + 16 * 8) by lia; apply Z.div_add; lia).
assert (EDP8 : x_DP c / 8 = x_F c / 8 + 24)
  by (unfold x_DP; replace (x_F c + 192) with (x_F c + 24 * 8) by lia; apply Z.div_add; lia).
assert (E32 : ew E 32 = Z_to_bv 64 (rbn_r1_dbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E34 : ew E 34 = Z_to_bv 64 (rbn_r1_tbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E36 : ew E 36 = Z_to_bv 64 (rbn_r1_nbn c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E38 : ew E 38 = Z_to_bv 64 (x_display c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = Z_to_bv 64 (x_name c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = Z_to_bv 64 (x_token c)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
(* memcpy(name, nm, nb.n + 1) at 0x8344c *)
paj_run_shc RUNP RUNC HS HJ; [r1_awr|]. r1_keep.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pose proof (st_ok_region_nth _ _ _ 1%nat rbn_r1_sh HS eq_refl) as HRsh. cbn [ms_mem restrict] in HRsh.
pose proof (rbn_r1_sh_zero _ _ _ _ HRsh U18) as SZ.
pmkst HS.
eapply SRr_bind.
{ eapply (rbn_r1_cpy_at c lyc Sc memc mdc regs _ _ _ _ (x_name c) (x_NM c) (rbn_r1_nbn c + 1) (x_name_len c) 24
    HCORE HJ).
  - rewrite Ra0, E39. reflexivity.
  - rewrite Ra1, (EE 27%nat 27%bv eq_refl). exact R27.
  - rewrite Ra2, E36, unsigned_lit_small by (clear - N0 NBlen; lia). reflexivity.
  - rewrite Rsp, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - clear - N0; lia.
  - clear - Hok4 NBlen N0; lia.
  - exact FPn.
  - exact Bn.
  - unfold x_NM; lia.
  - unfold x_NM; clear - NBlen N0; lia.
  - unfold x_NM. rewrite HF32. replace (32 * (x_F c / 32) + 64) with ((4 * (x_F c / 32) + 8) * 8) by lia.
    apply Z_mod_mult.
  - intros j Hj. assert (Hj3 : (rbn_r1_nbn c + 1 + 7) / 8 < 4) by (apply Z.div_lt_upper_bound; clear - NBlen; lia).
    rewrite ENM8. replace (SHADOW_OFF + (x_F c / 8 + 8) + j) with (x_FS c + (8 + j)) by (rewrite HFS; lia).
    apply SZ. clear - Hj Hj3; lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Heff & Hfr & Hpres).
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_za c a ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha Hz. unfold rbn_r1_za in Hz. rewrite Hfr; [apply KEEP; [exact Ha | tauto] | exact Ha | |].
  - intros Hx; apply Hz; right; right; left; clear - Hx; lia.
  - intros Hx; apply Hz; right; left; exact Hx. }
assert (CN : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
  aview SEGS (w_H (x_W c)) mem2 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)).
{ intros i Hi. rewrite Heff by exact Hi. apply KEEP; [unfold x_NM; clear - Hi HF4096 HFce C1 NBlen; lia |].
  apply rbn_r1_notzr_frame; [exact HF4096 | exact HFapp | unfold x_NM; clear - Hi NBlen N0; lia |].
  unfold x_NM, x_DP; clear - Hi NBlen D0; lia. }
clear KEEP Heff.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [0; 1; 2]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_aview E (w_H (x_W c)) _ mem2 9%nat (x_s1 c)); [exact U9 | | exact Hpres].
    intros a Ha. apply Hfr; [clear - Ha Hs1 Hsp0hi Hsp0lo C1; lia | | clear - Ha; lia].
    intros Hd. destruct (HBF a (HRn a ltac:(clear - Hd; lia))) as (Hb & _). clear - Ha Hb Hs1 Hsp0lo; lia.
  - eapply (region_kept_aview E (w_H (x_W c)) _ mem2 18%nat (x_FS c)); [exact U18 | | exact Hpres].
    intros a Ha. apply Hfr.
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HF4096 HFce C1 HF8d HF8m; lia.
    + intros Hd. destruct (HBF a (HRn a ltac:(clear - Hd; lia))) as (_ & Happ & _).
      exact (rbn_r1_sh_notapp c a HF4096 HFapp ltac:(clear - Ha; lia) Happ).
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HFce HF8d HF8m Hs1 Hsp0lo C1 Hes; lia.
  - eapply (region_kept_aview E (w_H (x_W c)) _ mem2 44%nat (x_DP c + rbn_r1_dbn c)); [exact U44 | | exact Hpres].
    intros a Ha. apply Hfr.
    + unfold x_DP in Ha. clear - Ha HF4096 HFce C1 D0 D1; lia.
    + intros Hd. destruct (HBF a (HRn a ltac:(clear - Hd; lia))) as (_ & _ & Haf).
      unfold x_DP in Ha. clear - Ha Haf D0 D1; lia.
    + unfold x_DP in Ha. clear - Ha HFce C1 D0 D1 Hs1 Hsp0lo Hes; lia. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
r1_envs. rename KEEPA into KEEP. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HRsh SZ Hfr Hpres.
(* memcpy(token, tk, tb.n + 1) at 0x8345c *)
paj_run_shc RUNP RUNC HS HJ2; [r1_awr|].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem2) (mrestrict _ ?m1) |- _ =>
  assert (CN2 : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
    aview SEGS (w_H (x_W c)) m1 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)) end.
{ intros i Hi. rewrite <- (CN i Hi).
  destruct (HBF (x_name c + i) (HRn (x_name c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CN. rename CN2 into CN.
r1_keep.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pose proof (st_ok_region_nth _ _ _ 1%nat rbn_r1_sh HS eq_refl) as HRsh. cbn [ms_mem restrict] in HRsh.
lazymatch goal with HS : st_ok _ ?Ex _ _, U : bv_unsigned (ew ?Ex 18%nat) = x_FS c |- _ =>
  pose proof (rbn_r1_sh_zero _ _ _ _ HRsh U) as SZ end.
pmkst HS.
eapply SRr_bind.
{ eapply (rbn_r1_cpy_at c lyc Sc memc mdc regs _ _ _ _ (x_token c) (x_TK c) (rbn_r1_tbn c + 1) (x_token_len c) 24
    HCORE HJ2).
  - rewrite Ra0, E40. reflexivity.
  - rewrite Ra1, (EE 25%nat 25%bv eq_refl). exact R25.
  - rewrite Ra2, E34, unsigned_lit_small by (clear - T0 TBlen; lia). reflexivity.
  - rewrite Rsp, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - clear - T0; lia.
  - clear - Hok6 TBlen T0; lia.
  - exact FPt.
  - exact Bt.
  - unfold x_TK; lia.
  - unfold x_TK; clear - TBlen T0; lia.
  - unfold x_TK. rewrite HF32. replace (32 * (x_F c / 32) + 128) with ((4 * (x_F c / 32) + 16) * 8) by lia.
    apply Z_mod_mult.
  - intros j Hj. assert (Hj3 : (rbn_r1_tbn c + 1 + 7) / 8 < 4) by (apply Z.div_lt_upper_bound; clear - TBlen; lia).
    rewrite ETK8. replace (SHADOW_OFF + (x_F c / 8 + 16) + j) with (x_FS c + (16 + j)) by (rewrite HFS; lia).
    apply SZ. clear - Hj Hj3; lia. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Heff & Hfr & Hpres).
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_za c a ->
  aview SEGS (w_H (x_W c)) mem3 a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha Hz. pose proof Hz as Hz'. unfold rbn_r1_za in Hz'.
  rewrite Hfr; [apply KEEP; [exact Ha | exact Hz] | exact Ha | |].
  - intros Hx; apply Hz'; right; right; right; left; clear - Hx; lia.
  - intros Hx; apply Hz'; right; left; exact Hx. }
assert (CN2 : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
  aview SEGS (w_H (x_W c)) mem3 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)).
{ intros i Hi. rewrite <- (CN i Hi). destruct (HBF (x_name c + i) (HRn (x_name c + i) ltac:(clear - Hi; lia))) as (Hb & _).
  apply Hfr; [clear - Hb C1; lia | clear - Hi Dnt Hok4 NBlen Hok6 TBlen T0 N0; lia |
    clear - Hb Hs1 Hsp0lo Hes; lia]. }
assert (CT : forall i, 0 <= i < rbn_r1_tbn c + 1 ->
  aview SEGS (w_H (x_W c)) mem3 (x_token c + i) = aview SEGS (w_H (x_W c)) memc (x_TK c + i)).
{ intros i Hi. rewrite Heff by exact Hi. apply KEEP; [unfold x_TK; clear - Hi HF4096 HFce C1 TBlen T0; lia |].
  unfold rbn_r1_za. intros [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - exact (rbn_r1_notzr_frame c (x_TK c + i) HF4096 HFapp ltac:(unfold x_TK; clear - Hi TBlen T0; lia)
      ltac:(unfold x_TK, x_DP; clear - Hi TBlen D0; lia) Hz).
  - unfold x_TK in Hz. clear - Hz Hi TBlen HFce Hs1 Hsp0lo Hes C1; lia.
  - destruct (HBF _ (HRn _ Hz)) as (_ & _ & Haf). unfold x_TK in Haf. clear - Haf Hi TBlen T0; lia.
  - destruct (HBF _ (HRt _ Hz)) as (_ & _ & Haf). unfold x_TK in Haf. clear - Haf Hi TBlen T0; lia.
  - destruct (HBF _ (HRd _ Hz)) as (_ & _ & Haf). unfold x_TK in Haf. clear - Haf Hi TBlen T0; lia. }
clear KEEP Heff CN. rename CN2 into CN.
jafter_call_keep_hi HS 528%nat regs3 (mrestrict (w_H (x_W c)) mem3) HP3 [0; 1; 2]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 9%nat) = x_s1 c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem3 9%nat (x_s1 c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr; [clear - Ha Hs1 Hsp0hi Hsp0lo C1; lia | | clear - Ha; lia].
    intros Hd. destruct (HBF a (HRt a ltac:(clear - Hd; lia))) as (Hb & _). clear - Ha Hb Hs1 Hsp0lo; lia.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 18%nat) = x_FS c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem3 18%nat (x_FS c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr.
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HF4096 HFce C1 HF8d HF8m; lia.
    + intros Hd. destruct (HBF a (HRt a ltac:(clear - Hd; lia))) as (_ & Happ & _).
      exact (rbn_r1_sh_notapp c a HF4096 HFapp ltac:(clear - Ha; lia) Happ).
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HFce HF8d HF8m Hs1 Hsp0lo C1 Hes; lia.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 44%nat) = x_DP c + rbn_r1_dbn c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem3 44%nat (x_DP c + rbn_r1_dbn c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr.
    + unfold x_DP in Ha. clear - Ha HF4096 HFce C1 D0 D1; lia.
    + intros Hd. destruct (HBF a (HRt a ltac:(clear - Hd; lia))) as (_ & _ & Haf).
      unfold x_DP in Ha. clear - Ha Haf D0 D1; lia.
    + unfold x_DP in Ha. clear - Ha HFce C1 D0 D1 Hs1 Hsp0lo Hes; lia. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
r1_envs. rename KEEPA into KEEP. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HRsh SZ Hfr Hpres.
(* memcpy(display, dp, db.n + 1) at 0x8346c *)
paj_run_shc RUNP RUNC HS HJ3; [r1_awr|].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem3) (mrestrict _ ?m1) |- _ =>
  assert (CN2 : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
    aview SEGS (w_H (x_W c)) m1 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)) end.
{ intros i Hi. rewrite <- (CN i Hi).
  destruct (HBF (x_name c + i) (HRn (x_name c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CN. rename CN2 into CN.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem3) (mrestrict _ ?m1) |- _ =>
  assert (CT2 : forall i, 0 <= i < rbn_r1_tbn c + 1 ->
    aview SEGS (w_H (x_W c)) m1 (x_token c + i) = aview SEGS (w_H (x_W c)) memc (x_TK c + i)) end.
{ intros i Hi. rewrite <- (CT i Hi).
  destruct (HBF (x_token c + i) (HRt (x_token c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CT. rename CT2 into CT.
r1_keep.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pose proof (st_ok_region_nth _ _ _ 1%nat rbn_r1_sh HS eq_refl) as HRsh. cbn [ms_mem restrict] in HRsh.
lazymatch goal with HS : st_ok _ ?Ex _ _, U : bv_unsigned (ew ?Ex 18%nat) = x_FS c |- _ =>
  pose proof (rbn_r1_sh_zero _ _ _ _ HRsh U) as SZ end.
pose proof (st_ok_region_nth _ _ _ 2%nat
  (YP09.mkRegion (Some 44%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS eq_refl) as HRdp.
cbn [ms_mem restrict] in HRdp.
lazymatch goal with HS : st_ok _ ?Ex _ _, U : bv_unsigned (ew ?Ex 44%nat) = _ |- _ =>
  pose proof (rbn_r1_dpz_zero _ _ _ _ HRdp U) as DZ end.
pmkst HS.
eapply SRr_bind.
{ eapply (rbn_r1_cpy_at c lyc Sc memc mdc regs _ _ _ _ (x_display c) (x_DP c) (rbn_r1_dbn c + 1) (x_display_len c) 48
    HCORE HJ3).
  - rewrite Ra0, E38. reflexivity.
  - rewrite Ra1, (EE 26%nat 26%bv eq_refl). exact R26.
  - rewrite Ra2, E32, unsigned_lit_small by (clear - D0 D1; lia). reflexivity.
  - rewrite Rsp, (EE 2%nat 2%bv eq_refl). exact R2.
  - rewrite Rgp, (EE 3%nat 3%bv eq_refl). exact R3.
  - rewrite Rtp, (EE 4%nat 4%bv eq_refl). exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - clear - D0; lia.
  - clear - Hok5 D1 D0; lia.
  - exact FPd.
  - exact Bd.
  - unfold x_DP; lia.
  - unfold x_DP; clear - D1 D0; lia.
  - unfold x_DP. rewrite HF32. replace (32 * (x_F c / 32) + 192) with ((4 * (x_F c / 32) + 24) * 8) by lia.
    apply Z_mod_mult.
  - intros j Hj. assert (Hj3 : (rbn_r1_dbn c + 1 + 7) / 8 < 7) by (apply Z.div_lt_upper_bound; clear - D1; lia).
    rewrite EDP8. replace (SHADOW_OFF + (x_F c / 8 + 24) + j) with (x_FS c + (24 + j)) by (rewrite HFS; lia).
    apply SZ. clear - Hj Hj3; lia. }
cbv beta. intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Heff & Hfr & Hpres).
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ rbn_r1_za c a ->
  aview SEGS (w_H (x_W c)) mem4 a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha Hz. pose proof Hz as Hz'. unfold rbn_r1_za in Hz'.
  rewrite Hfr; [apply KEEP; [exact Ha | exact Hz] | exact Ha | |].
  - intros Hx; apply Hz'; right; right; right; right; clear - Hx; lia.
  - intros Hx; apply Hz'; right; left; exact Hx. }
assert (CN2 : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
  aview SEGS (w_H (x_W c)) mem4 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)).
{ intros i Hi. rewrite <- (CN i Hi). destruct (HBF (x_name c + i) (HRn (x_name c + i) ltac:(clear - Hi; lia))) as (Hb & _).
  apply Hfr; [clear - Hb C1; lia | clear - Hi Dnd Hok4 NBlen Hok5 D1 D0 N0; lia |
    clear - Hb Hs1 Hsp0lo Hes; lia]. }
assert (CT2 : forall i, 0 <= i < rbn_r1_tbn c + 1 ->
  aview SEGS (w_H (x_W c)) mem4 (x_token c + i) = aview SEGS (w_H (x_W c)) memc (x_TK c + i)).
{ intros i Hi. rewrite <- (CT i Hi). destruct (HBF (x_token c + i) (HRt (x_token c + i) ltac:(clear - Hi; lia))) as (Hb & _).
  apply Hfr; [clear - Hb C1; lia | clear - Hi Dtd Hok6 TBlen Hok5 D1 D0 T0; lia |
    clear - Hb Hs1 Hsp0lo Hes; lia]. }
assert (CD : forall i, 0 <= i < rbn_r1_dbn c ->
  aview SEGS (w_H (x_W c)) mem4 (x_display c + i) = aview SEGS (w_H (x_W c)) memc (x_DP c + i)).
{ intros i Hi. rewrite Heff by (clear - Hi; lia). apply KEEP; [unfold x_DP; clear - Hi HF4096 HFce C1 D1; lia |].
  unfold rbn_r1_za. intros [Hz | [Hz | [Hz | [Hz | Hz]]]].
  - exact (rbn_r1_notzr_frame c (x_DP c + i) HF4096 HFapp ltac:(unfold x_DP; clear - Hi D1; lia)
      ltac:(clear - Hi; lia) Hz).
  - unfold x_DP in Hz. clear - Hz Hi D1 HFce Hs1 Hsp0lo Hes C1; lia.
  - destruct (HBF _ (HRn _ Hz)) as (_ & _ & Haf). unfold x_DP in Haf. clear - Haf Hi D1; lia.
  - destruct (HBF _ (HRt _ Hz)) as (_ & _ & Haf). unfold x_DP in Haf. clear - Haf Hi D1; lia.
  - destruct (HBF _ (HRd _ Hz)) as (_ & _ & Haf). unfold x_DP in Haf. clear - Haf Hi D1; lia. }
assert (CZ : aview SEGS (w_H (x_W c)) mem4 (x_display c + rbn_r1_dbn c) = Some 0)
  by (rewrite Heff by (clear - D0; lia); exact DZ).
clear KEEP Heff CN CT. rename CN2 into CN. rename CT2 into CT.
jafter_call_keep_hi HS 544%nat regs4 (mrestrict (w_H (x_W c)) mem4) HP4 [0; 1; 2]%nat HS2.
match type of HS2 with ?Q -> _ => assert (HQ : Q) end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 9%nat) = x_s1 c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem4 9%nat (x_s1 c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr; [clear - Ha Hs1 Hsp0hi Hsp0lo C1; lia | | clear - Ha; lia].
    intros Hd. destruct (HBF a (HRd a ltac:(clear - Hd; lia))) as (Hb & _). clear - Ha Hb Hs1 Hsp0lo; lia.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 18%nat) = x_FS c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem4 18%nat (x_FS c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr.
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HF4096 HFce C1 HF8d HF8m; lia.
    + intros Hd. destruct (HBF a (HRd a ltac:(clear - Hd; lia))) as (_ & Happ & _).
      exact (rbn_r1_sh_notapp c a HF4096 HFapp ltac:(clear - Ha; lia) Happ).
    + rewrite HFS in Ha. unfold SHADOW_OFF in Ha. clear - Ha HFce HF8d HF8m Hs1 Hsp0lo C1 Hes; lia.
  - lazymatch goal with |- region_kept _ ?Ex _ _ _ =>
      match goal with U : bv_unsigned (ew Ex 44%nat) = x_DP c + rbn_r1_dbn c |- _ =>
        eapply (region_kept_aview Ex (w_H (x_W c)) _ mem4 44%nat (x_DP c + rbn_r1_dbn c)); [exact U | | exact Hpres] end end.
    intros a Ha. apply Hfr.
    + unfold x_DP in Ha. clear - Ha HF4096 HFce C1 D0 D1; lia.
    + intros Hd. destruct (HBF a (HRd a ltac:(clear - Hd; lia))) as (_ & _ & Haf).
      unfold x_DP in Ha. clear - Ha Haf D0 D1; lia.
    + unfold x_DP in Ha. clear - Ha HFce C1 D0 D1 Hs1 Hsp0lo Hes; lia. }
specialize (HS2 HQ). clear HQ HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
r1_envs. rename KEEPA into KEEP. clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HRsh SZ HRdp DZ Hfr Hpres.
(* 0x83470 s4 = 0, the scope close, to R *)
paj_run_to_shc RUNTOP HS HJ4 (AF_reac_box_name + 0x738); [r1_awr|].
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem4) (mrestrict _ ?m1) |- _ =>
  assert (CN2 : forall i, 0 <= i < rbn_r1_nbn c + 1 ->
    aview SEGS (w_H (x_W c)) m1 (x_name c + i) = aview SEGS (w_H (x_W c)) memc (x_NM c + i)) end.
{ intros i Hi. rewrite <- (CN i Hi).
  destruct (HBF (x_name c + i) (HRn (x_name c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CN. rename CN2 into CN.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem4) (mrestrict _ ?m1) |- _ =>
  assert (CT2 : forall i, 0 <= i < rbn_r1_tbn c + 1 ->
    aview SEGS (w_H (x_W c)) m1 (x_token c + i) = aview SEGS (w_H (x_W c)) memc (x_TK c + i)) end.
{ intros i Hi. rewrite <- (CT i Hi).
  destruct (HBF (x_token c + i) (HRt (x_token c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CT. rename CT2 into CT.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem4) (mrestrict _ ?m1) |- _ =>
  assert (CD2 : forall i, 0 <= i < rbn_r1_dbn c ->
    aview SEGS (w_H (x_W c)) m1 (x_display c + i) = aview SEGS (w_H (x_W c)) memc (x_DP c + i)) end.
{ intros i Hi. rewrite <- (CD i Hi).
  destruct (HBF (x_display c + i) (HRd (x_display c + i) ltac:(clear - Hi; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CD. rename CD2 into CD.
lazymatch goal with HFr : frame_of _ _ (mrestrict _ mem4) (mrestrict _ ?m1) |- _ =>
  assert (CZ2 : aview SEGS (w_H (x_W c)) m1 (x_display c + rbn_r1_dbn c) = Some 0) end.
{ rewrite <- CZ. destruct (HBF (x_display c + rbn_r1_dbn c) (HRd (x_display c + rbn_r1_dbn c) ltac:(clear - D0; lia))) as (Hb & Happ & Haf).
  refine (kept_of_frame _ _ _ _ _ (rbn_r1_zr c) HFr _ _ _ _);
    [r1_win | clear - Hb C1; lia | exact (rbn_r1_notzr_app c _ HF4096 HFapp HFce D1 Happ Haf)]. }
clear CZ. rename CZ2 into CZ.
r1_keep.
lazymatch goal with HS : st_ok_pi _ _ ?E3 _ _ |- _ =>
  assert (HAE3 : env_agree 32 (Ereg regs (rbn_r1_extra c)) E3) end.
{ destruct (rbn_r1_env_agree c regs) as (A1 & A2). split.
  - intros n Hn. rewrite !ew_havoc_old by (cbv; lia). rewrite HE. apply A1. exact Hn.
  - cbn [havoc ed]. rewrite HE. exact A2. }
eapply (rbn_r1_accept_at c lyc Sc memc mdc regs _ _ _ _ HC HAE3 HS eq_refl eq_refl
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) HJ4 KEEP CN CT CD CZ Hacc).
Qed.

(* ---------------------------------------------------------------------------------------------------------
   Helpers.
   --------------------------------------------------------------------------------------------------------- *)
(* lia in this tree has the zify euclidean-division equations switched off, so the frame-size facts the
   released proofs got from zify are supplied by hand. *)
Ltac rbn_r2_zlia :=
  repeat match goal with
  | H : context [fs_frame_bytes ?cc] |- _ =>
      lazymatch goal with
      | _ : 0 <= fs_frame_bytes cc |- _ => fail
      | _ => pose proof (fs_frame_bytes_nonneg cc)
      end
  | |- context [fs_frame_bytes ?cc] =>
      lazymatch goal with
      | _ : 0 <= fs_frame_bytes cc |- _ => fail
      | _ => pose proof (fs_frame_bytes_nonneg cc)
      end
  end;
  try appn; lia.

(* A chunk that holds a register value the caller saved. *)
Lemma rbn_r2_chunk_reg : forall E m base off a (n : nat) (w : word) (v : Z),
  ew E n = w -> v = bv_unsigned w -> base + off = a -> val_mem SEGS m a 8 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m base off a n w v He Hv Hba Hvm.
apply (chunk_ok_val SEGS E m base off 8%N (SOff n 0) v).
- cbn [sv_denot]. rewrite He, Z.add_0_r, Hv, Z_to_bv_bv_unsigned. reflexivity.
- subst v. pose proof (bv_unsigned_in_range 64 w) as HU. change (bv_modulus 64) with (2 ^ 64) in HU.
  cbn [Z.of_N N.to_nat Z.mul]. lia.
- cbn [Z.of_N]. lia.
- rewrite Hba. exact Hvm.
Qed.
(* A region the run reads but never writes is kept by any write outside its bytes. *)
Lemma rbn_r2_kept_ro : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b -> whi <= wlo ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
  region_kept SEGS E (mrestrict H m) (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hw Hav.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview SEGS). apply Hav. exact Ha.
- exfalso. lia.
Qed.
(* lib/Reusable/YCbq.v:517 ajournal_after_write with the presence premise narrowed to the stack window, as the
   released cgif copy states it (origin/ossv/candidates proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:38
   ajournal_after_write_win): __asan_set_shadow's contract keeps the bytes it does not write but says nothing
   about the presence of image bytes, and only the window's presence is used. *)
Lemma rbn_r2_after_write_win :
  forall STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' (Wr : Z -> Prop) S' own2,
  ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H Wc) memc' a = aview SEGS (w_H Wc) memc a) ->
  (forall a, sp0 - STK <= a < sp0 -> apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  same_but_materialized mdc mdc' ->
  (forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
     (aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)) ->
  AR SEGS B lyc S' Wc memc' mdc' ->
  ablocks B lyc S' = ablocks B lyc Sc -> st_secs S' = st_secs Sc -> st_nev S' <= st_nev Sc ->
  frames S' = own2 ++ frames S -> qtight S' ->
  ajournal SEGS B STK sp0 FP ly S W mem md own2 lyc S' Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k memc' mdc' Wr S' own2 HJ Heqw Hgr Hsame HW HAR' Eab' Esecs' Hnev' Hfrs' HQT'.
pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HWw : forall a, Wr a ->
(~ aowned B lyc Sc a /\
((alloc_ceiling <= a /\ sp0 - STK <= a < sp0) \/
(app_addr a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n /\ (inFP FP a \/ ~ In (b, n) (ablocks B ly S))) \/
(exists cid pos, In (cid, pos) own /\
((app_addr a /\ in_zr a (frame_rng lyc (cid, pos))) \/
(kLowMemEnd <= a < kHighShadowEnd /\ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))))))
\/ (aowned B lyc Sc a /\ app_addr a /\ ~ in_img SEGS a)).
{ intros a Ha. destruct (HW a Ha) as [Hw | Hx];
  [left; exact (awr_byte_cases SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) | right; exact Hx]. }
split; [exact HAR'|].
split; [exact Hly|]. split; [rewrite Esecs'; exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs'|]. split; [rbn_r2_zlia|]. split; [exact Hk|]. rewrite !Eab'. split.
{
intros a Ha Hs. rewrite <- (F1 a Ha Hs). apply Heqw; [rbn_r2_zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[_ Hs'] | [[[_ Hlow] _] | (cid & pos & _ & [[[_ Hlow] _] | [[_ Hlow] _]])]]) | (_ & Hx)]; [exact (Hs Hs') | rbn_r2_zlia | rbn_r2_zlia | rbn_r2_zlia | rbn_r2_zlia]. }
split.
{
intros p n i H1 H2 Hi Hnf. rewrite <- (F2 p n i H1 H2 Hi Hnf).
destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR H2) as (_ & H4096 & Hceilp & [Hh1 Hh2] & _ & _).
apply Heqw; [rbn_r2_zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & [Hfp | Hnot]) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx)].
- rbn_r2_zlia.
- exact (Hnf Hfp).
-
assert (Hne : (b, m) <> (p, n)) by (intros E; rewrite E in Hnot; exact (Hnot H1)).
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc b m p n HAR Hbin H2 Hne) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. rbn_r2_zlia.
-
assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc p n cid pos HAR H2 Hin') as Hd.
unfold zdisjoint, in_zr, frame_rng in *. cbn [fst snd] in Hd, Hr. rbn_r2_zlia.
- rbn_r2_zlia.
-
exfalso. exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p n HAR H2))))) (p + i) ltac:(rbn_r2_zlia)) Hxo). }
split.
{
intros a Hi Hns He Hsp. rewrite <- (F3 a Hi Hns He Hsp). pose proof (segs_low a Hi) as Hal'.
apply Heqw; [rbn_r2_zlia|]. intros HWa.
destruct (HWw a HWa) as [(_ & [[Hc' _] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] _]])]]) | (Hxo & Hx & Hxi)].
- rbn_r2_zlia.
- exact (blk_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hbin Hr Hi).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (frm_img SEGS B LAWS _ _ _ _ _ _ _ _ HAR Hin' Hr Hi).
- rbn_r2_zlia.
- exact (Hxi Hi). }
split.
{
intros cid pos a Hin Hr Hnf. rewrite <- (F4 cid pos a Hin Hr Hnf).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfh).
assert (Efa : frame_addr lyc cid pos = frame_addr ly cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
rewrite <- Efa in Hr. unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(rbn_r2_zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(rbn_r2_zlia)) as Hsb2.
pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) ltac:(rbn_r2_zlia)) as Hse.
apply Heqw; [rbn_r2_zlia|]. intros HWa.
destruct (HWw _ HWa) as [(_ & [[Hc' _] | [([Hlo0 Hlow] & b & m & Hbin & Hrb & _) | (c' & p' & Hown & Hr')]]) | (Hxo & Hx)].
- rbn_r2_zlia.
- destruct Hr as [Hr | Hr]; [|rbn_r2_zlia].
pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc b m cid pos HAR Hbin HinC) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rbn_r2_zlia.
-
apply in_split in Hown as (o1 & o2 & Eo). apply in_split in Hin as (g1 & g2 & Eg).
assert (Hd : zdisjoint (frame_rng lyc (c', p')) (frame_rng lyc (cid, pos))).
{ eapply (sep_frames_pos SEGS B LAWS lyc Sc Wc memc mdc _ _ o1 (o2 ++ g1) g2 HAR).
rewrite Hfrs, Eo, Eg. repeat (rewrite <- app_assoc; cbn). reflexivity. }
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc c' p' HAR ltac:(rewrite Hfrs; apply in_or_app; left; rewrite Eo; apply in_or_app; right; left; reflexivity)) as (Hf0' & Hfc' & Hfh').
pose proof (YCbq.shadow_range_end (frame_addr lyc c' p') (fs_frame_bytes c') (fs_frame_bytes_nonneg c')) as Hse'.
pose proof (fs_frame_bytes_nonneg c') as Hnn'.
destruct Hr' as [[[Hlo0' Hlo'] Hr'] | [[Hlo1' Hhi'] Hr']]; unfold in_zr, frame_rng in Hr'; cbn [fst snd] in Hr'.
+ destruct Hr as [Hr | Hr]; [rbn_r2_zlia | rbn_r2_zlia].
+ destruct Hr as [Hr | Hr]; [rbn_r2_zlia |].
destruct Hd as [Hd | Hd].
* pose proof (YCbq.shadow_mono _ _ Hd). rbn_r2_zlia.
* pose proof (YCbq.shadow_mono _ _ Hd). rbn_r2_zlia.
-
destruct (al_frames SEGS B LAWS lyc Sc Wc memc mdc cid pos HAR HinC) as (_ & _ & Hfb & Hfsh).
rewrite <- ?Efa in Hr.
exfalso. destruct Hr as [Hr|Hr]; [exact (proj2 (Hfb a Hr) Hxo)|].
specialize (Hfsh (a - shadow_addr (frame_addr lyc cid pos)) ltac:(rbn_r2_zlia)).
replace (shadow_addr (frame_addr lyc cid pos) + (a - shadow_addr (frame_addr lyc cid pos))) with a in Hfsh by rbn_r2_zlia.
exact (proj2 Hfsh Hxo). }
split; [exact Hgone|].
split; [intros a Ha; apply (Hgr a Ha); apply Hpres, Ha|].
split; [exact Hstatic|]. split; [|exact HQT'].
{
intros a HXa He. rewrite <- (F5 a HXa He).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _ & _ & Eextra & _).
assert (HXc : Exists (in_zr a) (ly_extra lyc)) by (rewrite Eextra; exact HXa).
pose proof (YG0p.AR_extra_law_ok SEGS B lyc Sc Wc memc mdc a HAR HXc) as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; rbn_r2_zlia).
apply Heqw; [exact Ha64|]. intros HWa. exfalso.
destruct (HWw a HWa) as [(_ & [[Hc' Hs'] | [(_ & b & m & Hbin & Hr & _) | (cid & pos & Hown & [[_ Hr] | [[Hsl Hsh] Hr]])]]) | (Hxo & Hx)].
- apply Xs. rewrite Eslo, Eshi. rbn_r2_zlia.
- exact (Xb b m Hbin Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr. exact (proj1 (Xf cid pos Hin') Hr).
- assert (Hin' : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
unfold in_zr in Hr; cbn [fst snd] in Hr. exact (proj2 (Xf cid pos Hin') Hr).
- exact (Xo Hxo). }
Qed.
(* The __asan_set_shadow_f5 call of the release, wrapped into the caller's journal (the released cgif
   aj_set_shadow_at, origin/ossv/candidates proofs/cgif/cgif_rgb_fuzzer/lib/YC05.v:206). *)
Lemma rbn_r2_shadow_at :
  forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  In (cid, pos) own ->
  getr regsT 10 = w64 q -> getr regsT 11 = w64 n -> 0 < n ->
  shadow_addr (frame_addr lyc cid pos) <= q ->
  q + n <= shadow_addr (frame_addr lyc cid pos) + fs_frame_bytes cid / 8 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___asan_set_shadow_f5)) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\
       (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (q + i) = Some 245) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + n) -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k cid pos q n o raw
  HJ Hown Ha0 Ha1 Hn Hq1 Hq2 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw.
pose proof pa_segs_low as segs_low.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & _ & HQT).
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply (ecall_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k regsT o); try eassumption.
  rewrite Hra. exact Hraw. }
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
eapply SRr_mono.
{ exact (ASSF5 lyc Sc W regsT memT mdc cid pos q n HPRE Hin Ha0 Ha1 Hn Hq1 Hq2). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Heff & Hfr & Hpres2).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS lyc Sc W memT mdc cid pos HAR Hin) as (Hf0 & Hfc & _).
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(rbn_r2_zlia)) as Hsb1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(rbn_r2_zlia)) as Hsb2.
pose proof (YCbq.shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)) as Hse.
assert (Hoff : forall a, 0 <= a < 2 ^ 64 -> ~ in_img SEGS a -> apresent (w_H W) memT a -> apresent (w_H W) mem2 a).
{ intros a Ha Hni Hp. destruct (Z_le_gt_dec q a) as [Hqa|Hqa]; [destruct (Z_lt_ge_dec a (q + n)) as [Han|Han]|].
  - specialize (Heff (a - q) ltac:(rbn_r2_zlia)). replace (q + (a - q)) with a in Heff by rbn_r2_zlia.
    destruct Hp as [Hh _]. split; [exact Hh|]. unfold aview, mbyte, mrestrict in Heff. rewrite Hh in Heff.
    destruct (mem2 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|]. exfalso.
    rewrite (seg_rom_none SEGS a Ha Hni) in Heff. discriminate.
  - eapply (apresent_transfer SEGS); [exact Ha | exact Hni | apply Hfr; [exact Ha | rbn_r2_zlia] | exact Hp].
  - eapply (apresent_transfer SEGS); [exact Ha | exact Hni | apply Hfr; [exact Ha | rbn_r2_zlia] | exact Hp]. }
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (rbn_r2_after_write_win STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => q <= a < q + n) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha Hna).
  - intros a Ha Hp. apply Hoff; [rbn_r2_zlia | intros Hi; pose proof (segs_low a Hi); rbn_r2_zlia | exact Hp].
  - exact Hsame.
  - intros a Ha. left. right. right. right. exists cid, pos. split; [exact Hown|].
    right. unfold in_zr. cbn [fst snd]. rbn_r2_zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - rbn_r2_zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Heff|]. split; [exact Hfr | exact Hoff].
Qed.

(* ---------------------------------------------------------------------------------------------------------
   The segment: R (0x834ac) -> the post.
   --------------------------------------------------------------------------------------------------------- *)
Lemma rbn_seg_rel : forall c lyc Sc memc mdc regs,
  rbn_R B G c lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x738)) memc (seg_rom SEGS)) mdc)
    (apost_base SEGS B (336 + 2 * ESTACK) (x_FP c) (x_regs c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) 0
       (rbn_postQ B (x_ly c) (x_S c) (x_W c) (x_mem c) (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c)
          (x_token c) (x_token_len c) (x_display c) (x_display_len c))).
Proof.
intros c lyc Sc memc mdc regs HR.
destruct HR as (HCORE & HA20 & HBUF).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & HSAV & HFLG).
pose proof HPRE as (HFN & HRO & P10 & P10b & P11 & P11b & P12 & P12b & P13 & P13b & P14 & P14b & P15 & P15b
  & P16 & P16b & P17 & P17b & PPR & PD & PDb & PDL & PDLb & PIMG & HBUFS & PFR & PNEV & PBB).
pose proof HFN as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & HSTK0 & Hpres0 & Hch0 & HQT0).
pose proof HJ as (HARc & Hly & Jsecs & Jwle & Jio & Hfrsc & Jnev & Jk & JF1 & JF2 & JF3 & JF4 & Jgone
  & Hpresc & HST & JF5 & HQTc).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HSTK0 as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hsp0eq : spZ (x_regs c) = x_sp0 c) by reflexivity.
rewrite Hsp0eq in Hsp0al, Hslo, Hshi, Hbot, Htop2.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
(* the frame (3, fpos) *)
assert (Hin3 : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (al_layout SEGS B LAWS _ _ _ _ _ lyc HAR0 Hly) as (Eab & Efa & Eown).
assert (EFA : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; apply Efa).
assert (EFLG : flag_addr lyc 3 (x_fpos c) = flag_addr (x_ly c) 3 (x_fpos c)).
{ unfold flag_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HARc Hin3) as (HF32 & HFapp & HFby & HFsh).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 (x_fpos c) HARc Hin3) as (HF4096 & HFce & _).
rewrite EFA in HF32, HFapp, HFby, HFsh, HF4096, HFce. rewrite Hfb3 in HFapp, HFby, HFsh, HFce.
destruct (FFL lyc Sc (x_W c) memc mdc 3 (x_fpos c) HARc Hin3) as (HXp & HXo & (HXapp & HXimg) & HX4096 & HXz & HXce).
rewrite EFLG in HXp, HXo, HXapp, HXimg, HX4096, HXz, HXce.
(* arithmetic facts: the stack window, the frame and its shadow are pairwise apart *)
assert (HFd : 0 <= x_F c / 8 <= 17592186044416).
{ split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
assert (HFSsh : shadow_addr (x_F c) = x_FS c) by reflexivity.
assert (HFSlo : 2147450880 <= x_FS c) by (rewrite HFS; unfold SHADOW_OFF; lia).
assert (HFShi : x_FS c + 64 < alloc_ceiling) by (rewrite HFS; unfold SHADOW_OFF; lia).
assert (D320 : x_sp0 c - 320 = 32 * ((x_sp0 c - 320) / 32) + (x_sp0 c - 320) mod 32)
  by (apply Z.div_mod; lia).
assert (M320 : 0 <= (x_sp0 c - 320) mod 32 < 32) by (apply Z.mod_pos_bound; lia).
assert (Hs1e : x_s1 c = 32 * ((x_sp0 c - 320) / 32)) by reflexivity.
assert (D16 : x_sp0 c = 16 * (x_sp0 c / 16)).
{ pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as D. rewrite Hsp0al, Z.add_0_r in D. lia. }
assert (Hs1lo : x_sp0 c - 352 <= x_s1 c) by lia.
assert (Hs1hi : x_s1 c <= x_sp0 c - 320) by lia.
assert (Hom : (x_s1 c - x_sp0 c) mod 16 = 0).
{ replace (x_s1 c - x_sp0 c) with ((2 * ((x_sp0 c - 320) / 32) - x_sp0 c / 16) * 16) by lia.
  apply Z_mod_mult. }
(* the environment *)
remember (rbn_r2_E c regs) as E eqn:HEdef.
assert (HEI : img_env VAL A_LIM E) by (rewrite HEdef; unfold rbn_r2_E; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg regs (rbn_r2_extra c)) E)
  by (rewrite HEdef; unfold rbn_r2_E; split;
      [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; rewrite HEdef; unfold rbn_r2_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j)%nat = nth j (rbn_r2_extra c) (Z_to_bv 64 0)).
{ intros j Hj. rewrite HEdef. unfold rbn_r2_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_extra. }
assert (E1 : ew E 1%nat = getr regs 1) by (exact (EW 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2%nat = getr regs 2) by (exact (EW 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3%nat = getr regs 3) by (exact (EW 3%nat 3%bv eq_refl)).
assert (E4 : ew E 4%nat = getr regs 4) by (exact (EW 4%nat 4%bv eq_refl)).
assert (E8 : ew E 8%nat = getr regs 8) by (exact (EW 8%nat 8%bv eq_refl)).
assert (E18 : ew E 18%nat = getr regs 18) by (exact (EW 18%nat 18%bv eq_refl)).
assert (E19 : ew E 19%nat = getr regs 19) by (exact (EW 19%nat 19%bv eq_refl)).
assert (E20 : ew E 20%nat = getr regs 20) by (exact (EW 20%nat 20%bv eq_refl)).
assert (E23 : ew E 23%nat = getr regs 23) by (exact (EW 23%nat 23%bv eq_refl)).
assert (E32 : ew E 32%nat = Z_to_bv 64 (flag_addr (x_ly c) 3 (x_fpos c)))
  by (change 32%nat with (32 + 0)%nat; rewrite (EX 0%nat ltac:(lia)); reflexivity).
assert (E33 : ew E 33%nat = getr (x_regs c) 1)
  by (change 33%nat with (32 + 1)%nat; rewrite (EX 1%nat ltac:(lia)); reflexivity).
assert (E34 : ew E 34%nat = getr (x_regs c) 8)
  by (change 34%nat with (32 + 2)%nat; rewrite (EX 2%nat ltac:(lia)); reflexivity).
assert (E35 : ew E 35%nat = getr (x_regs c) 9)
  by (change 35%nat with (32 + 3)%nat; rewrite (EX 3%nat ltac:(lia)); reflexivity).
assert (E36 : ew E 36%nat = getr (x_regs c) 18)
  by (change 36%nat with (32 + 4)%nat; rewrite (EX 4%nat ltac:(lia)); reflexivity).
assert (E37 : ew E 37%nat = getr (x_regs c) 19)
  by (change 37%nat with (32 + 5)%nat; rewrite (EX 5%nat ltac:(lia)); reflexivity).
assert (E38 : ew E 38%nat = getr (x_regs c) 20)
  by (change 38%nat with (32 + 6)%nat; rewrite (EX 6%nat ltac:(lia)); reflexivity).
assert (E39 : ew E 39%nat = getr (x_regs c) 21)
  by (change 39%nat with (32 + 7)%nat; rewrite (EX 7%nat ltac:(lia)); reflexivity).
assert (E40 : ew E 40%nat = getr (x_regs c) 22)
  by (change 40%nat with (32 + 8)%nat; rewrite (EX 8%nat ltac:(lia)); reflexivity).
assert (E41 : ew E 41%nat = getr (x_regs c) 23)
  by (change 41%nat with (32 + 9)%nat; rewrite (EX 9%nat ltac:(lia)); reflexivity).
assert (E42 : ew E 42%nat = getr (x_regs c) 24)
  by (change 42%nat with (32 + 10)%nat; rewrite (EX 10%nat ltac:(lia)); reflexivity).
assert (E43 : ew E 43%nat = getr (x_regs c) 25)
  by (change 43%nat with (32 + 11)%nat; rewrite (EX 11%nat ltac:(lia)); reflexivity).
assert (E44 : ew E 44%nat = getr (x_regs c) 26)
  by (change 44%nat with (32 + 12)%nat; rewrite (EX 12%nat ltac:(lia)); reflexivity).
assert (E45 : ew E 45%nat = getr (x_regs c) 27)
  by (change 45%nat with (32 + 13)%nat; rewrite (EX 13%nat ltac:(lia)); reflexivity).
assert (U8 : bv_unsigned (ew E 8%nat) = x_sp0 c)
  by (rewrite E8, R8; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19%nat) = x_F c)
  by (rewrite E19, R19; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23%nat) = x_F c)
  by (rewrite E23, R23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32%nat) = flag_addr (x_ly c) 3 (x_fpos c))
  by (rewrite E32; apply unsigned_lit_small; lia).
(* the saved registers *)
assert (SV : forall p, In p rbn_saved_regs ->
  val_mem SEGS (x_mem_at c memc) (x_sp0 c - fst p) 8 (bv_unsigned (getr (x_regs c) (snd p))))
  by (apply Forall_forall; exact HSAV).
assert (HUR : forall r : bv 5, 0 <= bv_unsigned (getr (x_regs c) r) < 2 ^ 64).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr (x_regs c) r)) as HU.
  change (bv_modulus 64) with (2 ^ 64) in HU. exact HU. }
(* the entry state *)
assert (HS : st_ok_pi SEGS VAL E rbn_r2_ss
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x738))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_r2_ss. apply pa_entry_st_ok_full.
  - rewrite HEdef. unfold rbn_r2_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    + unfold region_ok, rbn_r2_mag.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U19. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFby (x_F c + o) ltac:(lia))).
    + unfold region_ok, rbn_r2_slot.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      eapply (rbn_r2_chunk_reg E _ (x_F c) 504 (x_F c + 504) 32%nat
                (Z_to_bv 64 (flag_addr (x_ly c) 3 (x_fpos c)))
                (flag_addr (x_ly c) 3 (x_fpos c))).
      * exact E32.
      * symmetry. apply unsigned_lit_small. lia.
      * reflexivity.
      * exact (val_mem_of_rdword SEGS (w_H (x_W c)) memc _ _ HFLG).
    + unfold region_ok, rbn_r2_sav.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-8) (x_sp0 c - 8) 33%nat (getr (x_regs c) 1));
        [exact E33 | reflexivity | lia | exact (SV (8, 1%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-16) (x_sp0 c - 16) 34%nat (getr (x_regs c) 8));
        [exact E34 | reflexivity | lia | exact (SV (16, 8%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-24) (x_sp0 c - 24) 35%nat (getr (x_regs c) 9));
        [exact E35 | reflexivity | lia | exact (SV (24, 9%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-32) (x_sp0 c - 32) 36%nat (getr (x_regs c) 18));
        [exact E36 | reflexivity | lia | exact (SV (32, 18%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-40) (x_sp0 c - 40) 37%nat (getr (x_regs c) 19));
        [exact E37 | reflexivity | lia | exact (SV (40, 19%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-48) (x_sp0 c - 48) 38%nat (getr (x_regs c) 20));
        [exact E38 | reflexivity | lia | exact (SV (48, 20%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-56) (x_sp0 c - 56) 39%nat (getr (x_regs c) 21));
        [exact E39 | reflexivity | lia | exact (SV (56, 21%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-64) (x_sp0 c - 64) 40%nat (getr (x_regs c) 22));
        [exact E40 | reflexivity | lia | exact (SV (64, 22%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-72) (x_sp0 c - 72) 41%nat (getr (x_regs c) 23));
        [exact E41 | reflexivity | lia | exact (SV (72, 23%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-80) (x_sp0 c - 80) 42%nat (getr (x_regs c) 24));
        [exact E42 | reflexivity | lia | exact (SV (80, 24%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-88) (x_sp0 c - 88) 43%nat (getr (x_regs c) 25));
        [exact E43 | reflexivity | lia | exact (SV (88, 25%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-96) (x_sp0 c - 96) 44%nat (getr (x_regs c) 26));
        [exact E44 | reflexivity | lia | exact (SV (96, 26%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
      * eapply (rbn_r2_chunk_reg E _ (x_sp0 c) (-104) (x_sp0 c - 104) 45%nat (getr (x_regs c) 27));
        [exact E45 | reflexivity | lia | exact (SV (104, 27%bv) ltac:(unfold rbn_saved_regs; cbn [In]; tauto))].
  - apply pairwise_disjoint_of_extents.
    unfold rbn_r2_mag, rbn_r2_slot, rbn_r2_sav, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite U8, U19, U23.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - unfold rbn_r2_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U23. change (2 ^ 5) with 32.
    split; [lia|]. split; [exact HF32 | lia]. }
replace (BASE + AF_reac_box_name + 0x738) with (BASE + (AF_reac_box_name + 0x738)) by lia.
(* ---- run 1: the magic word and the branch, up to the __asan_set_shadow_f5 call ---- *)
paj_run_shc RUNP RUNC HS HJ.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (x_F c)); [reflexivity | exact U19 | | ].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi rbn_r2_mag] in Ha.
    right. right. right. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, Hfb3. lia.
  - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rbn_r2_slot]; lia|].
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi rbn_r2_sav]; lia|].
    apply awr_ok_nil. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_F c <= a < x_F c + 8) ->
  aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha Hw.
  apply (kept_of_frame E (ss_mem rbn_r2_ss) (w_H (x_W c)) memc (ms_mem ms)
    (fun x => x_F c <= x < x_F c + 8) HFr); [| exact Ha | exact Hw].
  intros bb wlo whi aa Hin Hr. unfold rbn_r2_ss in Hin.
  cbn [ss_mem windows map rbn_r2_mag rbn_r2_slot rbn_r2_sav YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; [rewrite U19 in Hr | rewrite U23 in Hr | rewrite U8 in Hr]; lia. }
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
rewrite E18, R18 in Ra0. rewrite E2, R2 in Rsp. rewrite E3, R3 in Rgp. rewrite E4, R4 in Rtp.
pmkst HS.
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (rbn_r2_shadow_at (x_W c) (ms_regs msX) (ms_mem msX) (336 + 2 * ESTACK) (x_sp0 c) (x_FP c)
    (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] lyc Sc _ 0 3 (x_fpos c)
    (x_FS c) 64 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + 11604)) HJ) end.
  - left. reflexivity.
  - exact Ra0.
  - exact Ra1.
  - lia.
  - rewrite EFA, HFSsh. lia.
  - rewrite EFA, HFSsh, Hfb3. change (512 / 8) with 64. lia.
  - unfold spZ. rewrite Rsp. rewrite unsigned_lit_small by lia. lia.
  - exact Hom.
  - lia.
  - lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hset & Hfr2 & Hpres2).
clear Ra0 Ra1 Rra Rsp Rgp Rtp.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [1%nat; 2%nat] HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
  [ eapply (rbn_r2_kept_ro E (w_H (x_W c)) _ mem2 23%nat (x_F c)); [exact U23 | lia |]
  | eapply (rbn_r2_kept_ro E (w_H (x_W c)) _ mem2 8%nat (x_sp0 c)); [exact U8 | lia |] ];
  intros a Ha; apply Hfr2; [lia | | lia | ];
  (intros Hbad; apply (fshadow_not_app (x_F c) 64 (x_F c) 512 a ltac:(lia) ltac:(lia) HFapp
     ltac:(rewrite HFS in Hbad; unfold SHADOW_OFF in Hbad; lia) ltac:(lia)))
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
clear HF HFr HG.
(* add the frame's flag byte: aj_flag_store_pi's own write right *)
assert (U32' : bv_unsigned (ew (havoc E 512%nat (map (getr regs2) CLOB)) 32%nat)
  = flag_addr (x_ly c) 3 (x_fpos c)) by (rewrite ew_havoc_old by lia; exact U32).
assert (U23' : bv_unsigned (ew (havoc E 512%nat (map (getr regs2) CLOB)) 23%nat) = x_F c)
  by (rewrite ew_havoc_old by lia; exact U23).
assert (U8' : bv_unsigned (ew (havoc E 512%nat (map (getr regs2) CLOB)) 8%nat) = x_sp0 c)
  by (rewrite ew_havoc_old by lia; exact U8).
assert (HXout : flag_addr (x_ly c) 3 (x_fpos c) + 1 <= x_F c
  \/ x_F c + 512 <= flag_addr (x_ly c) 3 (x_fpos c)).
{ destruct (Z_lt_le_dec (flag_addr (x_ly c) 3 (x_fpos c)) (x_F c)) as [HH|HH]; [left; lia|].
  destruct (Z_lt_le_dec (flag_addr (x_ly c) 3 (x_fpos c)) (x_F c + 512)) as [HH2|HH2];
  [exfalso; exact (proj2 (HFby (flag_addr (x_ly c) 3 (x_fpos c)) ltac:(lia)) HXo) | right; lia]. }
assert (HXp2 : apresent (w_H (x_W c)) mem2 (flag_addr (x_ly c) 3 (x_fpos c))).
{ apply Hpres2; [lia | exact HXimg |].
  eapply (apresent_transfer SEGS (w_H (x_W c)) (w_H (x_W c)) memc (ms_mem ms));
  [lia | exact HXimg | apply KEEP1; lia | exact HXp]. }
pose proof (st_ok_pi_add_region _ _ _ rbn_r2_flag HS ltac:(vm_compute; reflexivity)) as HS3.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ms_mem restrict] in HS3.
assert (HRFLAG : region_ok SEGS (havoc E 512%nat (map (getr regs2) CLOB))
  (mrestrict (w_H (x_W c)) mem2) rbn_r2_flag).
{ unfold region_ok, rbn_r2_flag.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U32'.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable SEGS).
    replace (flag_addr (x_ly c) 3 (x_fpos c) + o) with (flag_addr (x_ly c) 3 (x_fpos c)) by lia.
    exact HXp2.
  - apply List.Forall_nil. }
specialize (HS3 HRFLAG).
match type of HS3 with ?A -> _ => assert (HDIS : A) end.
{ apply all_disjoint_of_extents.
  unfold rbn_r2_flag, rbn_r2_slot, rbn_r2_sav, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U32', U23', U8'.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split.
  - destruct HXout as [HH|HH]; [left; lia | right; lia].
  - left. lia. }
specialize (HS3 HDIS).
clear HS. rename HS3 into HS.
(* ---- run 2: the flag byte store, the epilogue, the ret ---- *)
paj_run_flag_sh RUNF HS HJ2.
{ lia. }
{ intros a (r & Hr & Ha). cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi rbn_r2_flag base_val] in Ha;
  [ rewrite U32' in Ha; right; rewrite EFLG; lia
  | cbn [YP09.r_wlo YP09.r_whi] in Ha; exfalso; lia
  | cbn [YP09.r_wlo YP09.r_whi] in Ha; exfalso; lia ]. }
{ intros msr HSm.
  pose proof (st_ok_pi_region_nth _ _ msr 0%nat _ HSm eq_refl) as HR0.
  pose proof (field_of_region _ (ms_mem msr) 32%nat (flag_addr (x_ly c) 3 (x_fpos c)) _ 0 1 0 1 0 1%N (SLit 0) 0
    HR0 U32' ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  specialize (HV 0%nat ltac:(lia)).
  rewrite EFLG.
  replace (flag_addr (x_ly c) 3 (x_fpos c)) with (flag_addr (x_ly c) 3 (x_fpos c) + 0 + Z.of_nat 0) by lia.
  rewrite HV. reflexivity. }
(* the post *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> a <> flag_addr (x_ly c) 3 (x_fpos c) ->
  aview SEGS (w_H (x_W c)) (ms_mem ms0) a = aview SEGS (w_H (x_W c)) mem2 a).
{ intros a Ha Hw.
  apply (kept_of_frame (havoc E 512%nat (map (getr regs2) CLOB)) _ (w_H (x_W c)) mem2 (ms_mem ms0)
    (fun x => x = flag_addr (x_ly c) 3 (x_fpos c)) HFr); [| exact Ha | exact Hw].
  intros bb wlo whi aa Hin Hr.
  cbn [windows map ss_mem YP09.r_base YP09.r_wlo YP09.r_whi rbn_r2_flag] in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; [rewrite U32' in Hr; lia | cbn in Hr; lia | cbn in Hr; lia]. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (x_F c <= a < x_F c + 8) ->
  ~ (x_FS c <= a < x_FS c + 64) -> a <> flag_addr (x_ly c) 3 (x_fpos c) ->
  aview SEGS (w_H (x_W c)) (ms_mem ms0) a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha H1 H2 H3.
  rewrite (KEEP2 a Ha H3). rewrite (Hfr2 a Ha H2). apply KEEP1; [exact Ha | exact H1]. }
assert (KEEPB : forall q N a, In (q, N) (ablocks B lyc Sc) -> q <= a < q + N ->
  aview SEGS (w_H (x_W c)) (ms_mem ms0) a = aview SEGS (w_H (x_W c)) memc a).
{ intros q N a Hin Hr.
  destruct (al_blocks SEGS B LAWS lyc Sc (x_W c) memc mdc q N HARc Hin) as (_ & Hq0 & Hqce & Hqapp & Hqby & _ & HqN).
  pose proof (req_size_pos N ltac:(lia)) as (Hrq1 & Hrq2).
  apply KEEP.
  - lia.
  - pose proof (sep_block_frame SEGS B LAWS lyc Sc (x_W c) memc mdc q N 3 (x_fpos c) HARc Hin Hin3) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA, Hfb3 in Hd. lia.
  - intros Hbad. apply (fshadow_not_app (x_F c) 64 q (req_size N) a ltac:(lia) ltac:(lia) Hqapp
      ltac:(rewrite HFS in Hbad; unfold SHADOW_OFF in Hbad; lia) ltac:(lia)).
  - intros Heq. rewrite Heq in Hr.
    exact (proj2 (Hqby (flag_addr (x_ly c) 3 (x_fpos c)) ltac:(lia)) HXo). }
(* the final registers *)
prreg HS (10%bv : bv 5) Fa0.
prreg HS (1%bv : bv 5) Fra.
rewrite E20, HA20 in Fa0. rewrite E33 in Fra.
prreg HS (Z_to_bv 5 2) T2. prreg HS (Z_to_bv 5 3) T3. prreg HS (Z_to_bv 5 4) T4.
prreg HS (Z_to_bv 5 8) T8. prreg HS (Z_to_bv 5 9) T9.
prreg HS (Z_to_bv 5 18) T18. prreg HS (Z_to_bv 5 19) T19. prreg HS (Z_to_bv 5 20) T20.
prreg HS (Z_to_bv 5 21) T21. prreg HS (Z_to_bv 5 22) T22. prreg HS (Z_to_bv 5 23) T23.
prreg HS (Z_to_bv 5 24) T24. prreg HS (Z_to_bv 5 25) T25. prreg HS (Z_to_bv 5 26) T26.
prreg HS (Z_to_bv 5 27) T27.
assert (HPRES' : aregs_preserved (x_regs c) (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
  - rewrite T2, E8, R8. unfold w64, x_sp0, spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - rewrite T3, E3, R3. exact (eq_sym Hgp0).
  - rewrite T4, E4, R4. exact (eq_sym Htp0).
  - rewrite T8, E34. reflexivity.
  - rewrite T9, E35. reflexivity.
  - assert (HC : r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27)
      by lia.
    destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
    + rewrite T18, E36. reflexivity.
    + rewrite T19, E37. reflexivity.
    + rewrite T20, E38. reflexivity.
    + rewrite T21, E39. reflexivity.
    + rewrite T22, E40. reflexivity.
    + rewrite T23, E41. reflexivity.
    + rewrite T24, E42. reflexivity.
    + rewrite T25, E43. reflexivity.
    + rewrite T26, E44. reflexivity.
    + rewrite T27, E45. reflexivity. }
eapply (RET (x_W c) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem].
unfold apost_base.
exists lyc, (stack_free_state 3 (x_fpos c) Sc). eexists. eexists. eexists.
split; [rewrite Fra; unfold YK0s.ret_ok in Hra0; rewrite Hra0; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ2|].
split; [exact HPRES'|].
(* rbn_postQ *)
split; [reflexivity|].
split.
{ unfold ablocks. rewrite blocks_stack_free_state. exact HPERM. }
destruct (reac_box_name_c.bn_accept (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c)
  (x_token c) (x_token_len c) (x_display c) (x_display_len c)) eqn:Hacc.
- (* acceptance *)
  destruct HBUF as (HGN & HGT & HGD & HFPK).
  assert (HARGS : reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c)
    (x_display c) (x_display_len c) (x_i c) (x_o c) = true).
  { unfold reac_box_name_c.bn_accept in Hacc.
    apply andb_true_iff in Hacc as [Hacc _]. apply andb_true_iff in Hacc as [Hacc _].
    apply andb_true_iff in Hacc as [Hacc _]. apply andb_true_iff in Hacc as [Hacc _]. exact Hacc. }
  pose proof (reac_box_name.acc_eq (x_f c) (x_sd c) (x_i c) (x_o c) (x_name c) (x_name_len c)
    (x_token c) (x_token_len c) (x_display c) (x_display_len c) HARGS) as Hae.
  rewrite Hae in Hacc.
  apply andb_true_iff in Hacc as [Hacc HDL]. apply andb_true_iff in Hacc as [Hacc HTL].
  apply andb_true_iff in Hacc as [HN23 HNL].
  apply Z.leb_le in HN23. apply Z.ltb_lt in HNL. apply Z.ltb_lt in HTL. apply Z.ltb_lt in HDL.
  pose proof HARGS as HAOK. unfold reac_box_name_c.bn_args_ok in HAOK.
  apply andb_true_iff in HAOK as [HAOK Hio0]. apply andb_true_iff in HAOK as [HAOK Hoko].
  apply andb_true_iff in HAOK as [HAOK Hoki]. apply andb_true_iff in HAOK as [HAOK Hdl0].
  apply andb_true_iff in HAOK as [HAOK Htl0]. apply andb_true_iff in HAOK as [HAOK Hnl0].
  apply andb_true_iff in HAOK as [HAOK Hd0]. apply andb_true_iff in HAOK as [Hn0 Ht0].
  pose proof (box_name_lemmas.bn_tk_len (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) false) as HTKlen.
  pose proof (reac_box_name.bn_DP_len (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)) (x_i c) (x_o c) Hoki Hoko)
    as HDPlen.
  destruct (HBUFS HARGS) as (_ & HBN & HBT & HBD & _ & _ & _).
  destruct HBN as (qn & Nn & HinN & HqN1 & HqN2).
  destruct HBT as (qt & Nt & HinT & HqT1 & HqT2).
  destruct HBD as (qd & Nd & HinD & HqD1 & HqD2).
  assert (HinN' : In (qn, Nn) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); exact HinN).
  assert (HinT' : In (qt, Nt) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); exact HinT).
  assert (HinD' : In (qd, Nd) (ablocks B lyc Sc))
    by (apply (Permutation_in _ (Permutation_sym HPERM)); exact HinD).
  split; [rewrite Fa0; reflexivity|].
  split.
  { eapply (garr8_frame SEGS (x_mem_at c memc)); [exact HGN|].
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview SEGS). apply (KEEPB qn Nn a HinN'). lia. }
  split.
  { eapply (garr8_frame SEGS (x_mem_at c memc)); [exact HGT|].
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview SEGS). apply (KEEPB qt Nt a HinT'). unfold bn_TK in *. lia. }
  split.
  { eapply (garr8_frame SEGS (x_mem_at c memc)); [exact HGD|].
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview SEGS). apply (KEEPB qd Nd a HinD'). lia. }
  { intros a HaFP Hn Ht Hd.
    rewrite <- (HFPK a HaFP Hn Ht Hd).
    apply rbn_fp_in in HaFP.
    destruct HaFP as [(_ & Hr) | [(_ & Hr) | (_ & Hr)]].
    - apply (KEEPB qn Nn a HinN'). lia.
    - apply (KEEPB qt Nt a HinT'). lia.
    - apply (KEEPB qd Nd a HinD'). lia. }
- (* refusal *)
  split; [rewrite Fa0; reflexivity|].
  intros a HaFP (q & N & Hin & Hr).
  rewrite <- (HBUF a HaFP (ex_intro _ q (ex_intro _ N (conj Hin Hr)))).
  apply (KEEPB q N a); [apply (Permutation_in _ (Permutation_sym HPERM)); exact Hin | exact Hr].
Qed.
End walk.
End h.
End f.
End d.
