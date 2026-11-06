(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the TAIL segment of fuzz_reply's gestures_end walk (lane W4), from the frozen
   cut point 0x82638 of lib/A/W_gse_cut.v (gse_tail_at), in the form of the cgif loop walks of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (the stretch after a loop as its own lemma from a seated state) and the
   free call sites of lib/A/AC8h.v. *)
(* STRUCTURE PORTED FROM the same run at halts level, a working branch 38a6eaf28b2
   lib/A/Prog/gestures_end_b.v:
     - `gse_tail` (:905): the whole stretch 0x82638 -> ret.  Its step order is this file's:
       (ag_run :941) 0x82638 -> the free trampoline, with the load8 check of s->held and no store;
       (FREE :1031) free (s->held), the live block when hp <> 0 and free(NULL) otherwise - here gt_free over
       AFREE / AFREEN;
       (after the call, :1071) the store8 check and `sd zero,0(s1)`, the store4 check and `sw zero,0(s0)`, the
       epilogue and the return - here the second run and RET.
   Nothing is copied: the vocabulary (SRr over AR, journal ajournal_gx, symbolic seats) is this framework's. *)
(* gestures_end's tail on fuzz_reply.asan (objdump 0x82638-0x82690), every held key already ended and freed:
     0x82638  s3 = (s1 >> 3) + SB; load8 check of s->held (0x826d4 report_load8, NOT TAKEN); a0 = s->held
     0x8264c  free (s->held)  (free trampoline 0x53de8; s->held may be NULL: afree_null_cf_rule)
     0x82650  store8 check of s->held (0x826dc report_store8, NOT TAKEN); `sd zero, 0(s1)`
     0x8265c  store4 check of s->nheld (slow path 0x826a8, NOT TAKEN: s+48's granule is addressable);
              `sw zero, 0(s0)`
     0x82668  epilogue: ra, s0..s7 from sp+72 .. sp+8, sp += 80, ret.
   The state at 0x82638 is gse_inv at i = length (re_keys e); the conclusion is gse_post (W_contract.v).
   The walk is proved over any allocator relation ARx (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)) as
   pb_gse_tail_x : gse_tail_at_x (W_gse_cut.v), in a Section over PST / ARx / hl with the laws LAWS : AR_laws_x, HP0
   (no hidden head in any ARx state), the free rules in their caller-context form AFREE / AFREEN over one context list
   CTX_AFREE with this piece's free site HCTX_gse_tail, IMGC / BLKN (W_kit_x.v Section g, for blk_off_imgP_x), and
   the rest of W_gse_cut.v's list: TL, HG, MTL, HROMO, HOUTG.  pb_gse_tail, the AR statement, is
   re-derived from it at ARi0 (Section cAR). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_frame W_gse_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_contract_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ lists *)
Lemma gt_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) (Z_to_bv 8 0) = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes nth].
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.
(* pairwise disjointness of a block list survives a permutation of it (zdisjoint is symmetric) *)
Lemma gt_pw_perm : forall (l l' : list (Z * Z)), Permutation l l' -> pairwise zdisjoint l -> pairwise zdisjoint l'.
Proof.
intros l l' HP. induction HP as [|x l l' HP IH|x y l|l1 l2 l3 HP1 IH1 HP2 IH2]; cbn [pairwise]; intros H.
- exact H.
- destruct H as [Hf Hp]. split; [|exact (IH Hp)].
  apply Forall_forall. intros z Hz. rewrite Forall_forall in Hf. apply Hf.
  exact (Permutation_in _ (Permutation_sym HP) Hz).
- destruct H as [Hfy [Hfx Hp]]. inversion Hfy as [|u v Hyx Hfyl]; subst.
  split; [constructor; [unfold zdisjoint in *; lia | exact Hfx] | split; [exact Hfyl | exact Hp]].
- exact (IH2 (IH1 H)).
Qed.

(* the held array's block, when it is there *)
Lemma gt_hpblk_cases : forall hp kh (l : list (Z * Z)),
(hp = 0 /\ gse_hpblk hp kh ++ l = l) \/ (hp <> 0 /\ gse_hpblk hp kh ++ l = (hp, kh) :: l).
Proof.
intros hp kh l. unfold gse_hpblk. destruct (Z.eqb_spec hp 0) as [Hz | Hnz];
[left; split; [exact Hz | reflexivity] | right; split; [exact Hnz | reflexivity]].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Notation le8 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
Notation le4 := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.

Lemma gt_garr8_le : forall m a n z, garr8 SEGS m a (bzs (Z_to_le_bytes n z)) -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  val_mem SEGS m a n z.
Proof.
intros m a n z Hg Hz k Hk.
assert (Hl : (k < length (bzs (Z_to_le_bytes n z)))%nat) by (unfold bzs; rewrite length_map, length_Z_to_le_bytes; exact Hk).
destruct (Hg k Hl) as [Hv _]. specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
rewrite Hv. apply f_equal.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hk).
rewrite map_nth, gt_nth_le_bytes by exact Hk. unfold bz.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
Lemma gt_le_garr8 : forall m a n z, val_mem SEGS m a n z -> 0 <= z < 2 ^ (8 * Z.of_nat n) ->
  garr8 SEGS m a (bzs (Z_to_le_bytes n z)).
Proof.
intros m a n z Hv Hz j Hj. unfold bzs in Hj. rewrite length_map, length_Z_to_le_bytes in Hj.
unfold bzs. rewrite (nth_indep _ 0 (bz (Z_to_bv 8 0))) by (rewrite length_map, length_Z_to_le_bytes; exact Hj).
rewrite map_nth, gt_nth_le_bytes by exact Hj. unfold bz. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256.
split; [|apply Z.mod_pos_bound; lia].
intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
rewrite (Hv j Hj). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte. replace (8 * Z.of_nat 1) with 8 by lia. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
lazymatch goal with |- context [z mod 2 ^ ?w] => rewrite (Z.mod_small z (2 ^ w)) by lia end.
change (2 ^ 8) with 256. rewrite !Z.mod_mod by lia. reflexivity.
Qed.
(* the 56 bytes of a source_t: the 40 before held, held, nheld, pad2 *)
Definition gt_epre (e : rentry) : list byte :=
le4 (Z_to_bv 64 (re_fd e)) ++ le4 (Z_to_bv 64 (re_eof e)) ++ le4 (Z_to_bv 64 (re_skip e)) ++ re_pad1 e ++
le8 (Z_to_bv 64 (re_buf e)) ++ le8 (Z_to_bv 64 (re_used e)) ++ le8 (Z_to_bv 64 (re_cap e)).
Lemma gt_epre_len : forall e, length (re_pad1 e) = 4%nat -> length (gt_epre e) = 40%nat.
Proof.
intros e Hp1. unfold gt_epre. rewrite !length_app,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4,
  !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8, Hp1. reflexivity.
Qed.
Lemma gt_entry_split : forall e,
entry_bytes e = gt_epre e ++ le8 (Z_to_bv 64 (re_hp e)) ++ le4 (Z_to_bv 64 (re_nheld e)) ++ re_pad2 e.
Proof. intros e. unfold entry_bytes, gt_epre. rewrite <- !app_assoc. reflexivity. Qed.
Lemma gt_entry_split_cleared : forall e,
entry_bytes (entry_cleared e) = gt_epre e ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ re_pad2 e.
Proof.
intros e. unfold entry_bytes, entry_cleared, gt_epre, re_nheld.
cbn [re_fd re_eof re_skip re_pad1 re_buf re_used re_cap re_hp re_pad2 re_keys length].
rewrite <- !app_assoc. reflexivity.
Qed.
Lemma gt_le8_bytes : forall z, 0 <= z < 2 ^ 64 -> le8 (Z_to_bv 64 z) = Z_to_le_bytes 8 z.
Proof.
intros z Hz. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8, word_to_le_bytes.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma gt_le4_bytes : forall z, 0 <= z < 2 ^ 64 -> le4 (Z_to_bv 64 z) = Z_to_le_bytes 4 z.
Proof.
intros z Hz. unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4.
rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma gt_garr8_kept : forall H H' (m m' : word -> option byte) a l, garr8 SEGS (mrestrict H m) a l ->
(forall b, a <= b < a + Z.of_nat (length l) -> aview SEGS H' m' b = aview SEGS H m b) -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hg Hk. apply (garr8_frame SEGS _ _ a l Hg). intros b Hb. apply (mbyte_of_aview SEGS). exact (Hk b Hb).
Qed.
(* A byte a reader sees, off the read-only segments, is writable (W_gestures_end.v gse_writable_view). *)
Lemma gt_writable_view : forall H (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
aview SEGS H m a = Some v -> ~ in_rom SEGS a -> writable_at SEGS (mrestrict H m) a.
Proof.
intros H m a v Ha Hv Hn. unfold aview, mbyte in Hv. unfold writable_at, wview.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:Em; [discriminate|].
unfold seg_rom, memory_read in Hv.
destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 a)) (Z.of_N 1)) as [sg|] eqn:Ef; [|discriminate].
change (Z.of_N 1) with 1 in Ef. rewrite Ef.
destruct (seg_readable sg); [|discriminate].
destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi). rewrite unsigned_lit_small in Hlo, Hhi by lia.
destruct (seg_writable sg) eqn:Ew.
- destruct (segment_byte_at (seg_bytes sg) (Z.to_N (bv_unsigned (Z_to_bv 64 a) - Z.of_N (seg_base sg)))) eqn:Eb;
  [discriminate|].
  exfalso. change (N.to_nat 1) with 1%nat in Hv. cbn [segment_read_bytes] in Hv. rewrite Eb in Hv. cbn in Hv.
  discriminate Hv.
- exfalso. apply Hn. exists sg. split; [exact Hin|]. split; [exact Ew | lia].
Qed.
Lemma gt_view_some : forall H (m : word -> option byte) a n v k,
val_mem SEGS (mrestrict H m) a n v -> 0 <= k < Z.of_nat n -> aview SEGS H m (a + k) <> None.
Proof.
intros H m a n v k Hv Hk. unfold aview. replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia.
rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma gt_view_garr8 : forall H (m : word -> option byte) a l k,
garr8 SEGS (mrestrict H m) a l -> 0 <= k < Z.of_nat (length l) -> aview SEGS H m (a + k) <> None.
Proof.
intros H m a l k Hg Hk. destruct (Hg (Z.to_nat k) ltac:(lia)) as [Hv _].
pose proof (gt_view_some H m (a + Z.of_nat (Z.to_nat k)) 1 _ 0 Hv ltac:(lia)) as R. rewrite Z.add_0_r in R.
replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia. exact R.
Qed.
(* the shadow address of x, as the prologue computed it (W_gestures_end.v gse_shadow_w) *)
Lemma gt_shadow_w : forall x, 0 <= x < 2 ^ 60 ->
alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 SB) = w64 (x / 8 + SB).
Proof.
intros x Hx. assert (H8 : 0 <= x / 8 <= x) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold w64. apply bv_eq. rewrite !alu64_unsigned. cbn [zalu_raw].
rewrite !unsigned_lit_small by (unfold SB; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (x / 8) (2 ^ 64)) by lia. apply Z.mod_small. unfold SB. lia.
Qed.

(* ------------------------------------------------------------------ the symbolic state at 0x82638 *)
(* Atoms 0..31: the registers there (s0 = SA+48, s1 = SA+40, s2 = shadow (s0), s3 = SB, sp = spZ regs - 80);
   atom 32 = s->held; atoms 33..41 = the nine words the prologue saved at sp+8 .. sp+72 (s7, s6, s5, s4, s3, s2,
   s1, s0, ra of the caller), which the epilogue loads back. *)
Definition BxT : sv := SOff 19 0.
Definition gt_regs : list sv :=
sr_set sr_atoms 18%bv (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 19 0)).
Definition gt_frame : YP09.region := YP09.mkRegion (Some 2%nat) 8 80 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 8 (SOff 35 0));
 YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0)); YP09.mkChunk 48 (CVal 8 (SOff 38 0));
 YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0)); YP09.mkChunk 72 (CVal 8 (SOff 41 0))].
Definition gt_held : YP09.region := YP09.mkRegion (Some 9%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition gt_nheld : YP09.region := YP09.mkRegion (Some 8%nat) 0 4 0 4 [].
Definition gt_regions : smem := [ gt_frame; gt_held; gt_nheld ].
Definition GT_PHI : Z := 140737479966720.
Definition gt_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 4096 GT_PHI 3); (9%nat, mkAF 4096 GT_PHI 3);
  (19%nat, mkAF SB SB 0) ] [] [].
Definition ss_gt : sstate := mkSS A_gse_tail gt_regs gt_regions None gt_facts.
Definition gt_SH : list shent := [ mkSHE 9 0 8; mkSHE 8 0 8 ].
Definition gt_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gt_extra (hp : Z) (regs : bvmap 5 word) : list word :=
Z_to_bv 64 hp :: map (getr regs) [23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
(* the free rules in their caller-context form (a Theorem Labs lane's 21:20Z ruling): one context list per allocator entry,
   and the free call site of this piece, 0x8264c, as a closed singleton of its return address 0x82650 = gestures_end
   + 0xfc (ATopKeeper's K0 table CTX_AFREE, lib/A/ACk0.v) *)
Variable CTX_AFREE : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0xfc] CTX_AFREE.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ------------------------------------------------------------------ free, over ajournal_gx_x (W_gestures_end.v's gse_free_x)
   The room round: the rule's kr, its RM and count premises at the call's state Sc, and its post's RM, are the
   lemma's; the stack room is the inner journal's (aj_stack_room_x). *)
Lemma gt_not_owned_x : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_img SEGS a ->
~ Exists (in_zr a) (as_owned_static B) -> ~ aowned B ly S a.
Proof.
intros ly S Hp W mem md a HAR Hi Ho Hown. apply Ho.
exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W mem md a HAR Hi) Hown).
Qed.
Lemma gt_free_x : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch (kr : nat),
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (gse_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCTX HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_x SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
unfold gse_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRr_mono.
  { exact (AFREEN W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HCTX HRM HCNT MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & _ & HK & HM & HRM2 & HE & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a []]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hp'. apply HPr; [exact Hi | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | exact Hp'].
- assert (Hin : In (hp, kh) (ablocks B lyc Sc))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  eapply SRr_mono.
  { apply (AFREE W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k hp kh o raw ch kr HJi Hin H10 Hsp Hal
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HCTX HRM HCNT); [intros _ i Hi; exact (HFP Hnz i Hi) | exact MOK]. }
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & _ & HK & HM & HRM2 & HE
    & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_x SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|].
  split; [rewrite E2; apply Permutation_sym; apply (@Permutation_cons_app_inv _ l l1 l2 (hp, kh)); rewrite <- E1;
    apply Permutation_sym; exact HP|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a Ha; split; [exact Hnz | exact Ha]]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hp'. apply HPr; [exact Hi | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hp'].
  intros Hr. pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia.
Qed.
Lemma gt_apres_trans : forall W m W1 m1 W2 m2, apres_kept B W m W1 m1 -> apres_kept B W1 m1 W2 m2 -> apres_kept B W m W2 m2.
Proof. intros W m W1 m1 W2 m2 H1 H2 a Hi Ho He Hp. apply H2; [exact Hi | exact Ho | exact He | apply H1; assumption]. Qed.
Lemma gt_apres_grows : forall W (m m2 : word -> option byte),
mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m2) -> apres_kept B W m W m2.
Proof. intros W m m2 Hg a _ _ _ Hp. exact (apresent_grows (w_H W) m m2 a Hg Hp). Qed.

(* ------------------------------------------------------------------ the seat at 0x82638 *)
Lemma gt_entry_x : forall (Wc : world SEGS) lyc Sc Hpc memc mdc (regsc regs : bvmap 5 word) SA TB hp sp0,
ARx lyc Sc Hpc Wc memc mdc ->
In (TB, ATABLE) (ablocks B lyc Sc) ->
TB <= SA -> SA + AENT <= TB + ATABLE -> SA mod 8 = 0 ->
val_mem SEGS (arm Wc memc) (SA + 40) 8 hp -> 0 <= hp < 2 ^ 64 ->
alloc_ceiling + GSE_STK <= sp0 -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 ->
spZ regsc = sp0 - GSE_FRAME ->
getr regsc 8 = w64 (SA + 48) -> getr regsc 9 = w64 (SA + 40) ->
getr regsc 18 = w64 ((SA + 48) / 8 + SB) -> getr regsc 19 = w64 SB ->
val_mem SEGS (arm Wc memc) (sp0 - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm Wc memc) (sp0 - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm Wc memc) (sp0 - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm Wc memc) (sp0 - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm Wc memc) (sp0 - 40) 8 (bv_unsigned (getr regs 19)) ->
val_mem SEGS (arm Wc memc) (sp0 - 48) 8 (bv_unsigned (getr regs 20)) ->
val_mem SEGS (arm Wc memc) (sp0 - 56) 8 (bv_unsigned (getr regs 21)) ->
val_mem SEGS (arm Wc memc) (sp0 - 64) 8 (bv_unsigned (getr regs 22)) ->
val_mem SEGS (arm Wc memc) (sp0 - 72) 8 (bv_unsigned (getr regs 23)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (gt_extra hp regs))) ss_gt
(restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + A_gse_tail)) memc (seg_rom SEGS)))
/\ sh_ok SEGS BxT gt_SH (Eimg (Ereg regsc (gt_extra hp regs))) (mrestrict (w_H Wc) memc).
Proof.
intros Wc lyc Sc Hpc memc mdc regsc regs SA TB hp sp0 HAR HTBin HT1 HT2 HSA8 Mhp Rhp Hsplo Hsphi Hspal Hsp
  R8 R9 R18 R19 V1 V8 V9 V18 V19 V20 V21 V22 V23.
unfold GSE_FRAME in *.
assert (WS : GSE_STK = 16608) by reflexivity. rewrite WS in Hsplo.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc TB ATABLE HAR HTBin) as (HT16 & HT4096 & HTceil & HTia & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTpres, HTia. unfold AENT, ATABLE in HT2.
assert (RSA : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by lia.
assert (HDIV : 0 <= (SA + 48) / 8 <= SA + 48)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (gt_extra hp regs))).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as H5;
      change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j)%nat = nth j (gt_extra hp regs) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E2 : ew E 2 = getr regsc 2) by (apply (EL 2%nat 2%bv); reflexivity).
assert (E8 : ew E 8 = w64 (SA + 48)) by (rewrite (EL 8%nat 8%bv eq_refl); exact R8).
assert (E9 : ew E 9 = w64 (SA + 40)) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 ((SA + 48) / 8 + SB)) by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 SB) by (rewrite (EL 19%nat 19%bv eq_refl); exact R19).
assert (E32 : ew E 32 = Z_to_bv 64 hp) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = getr regs 23) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = getr regs 22) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = getr regs 21) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = getr regs 20) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = getr regs 19) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = getr regs 18) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = getr regs 9) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = getr regs 8) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = getr regs 1) by (exact (EX 9%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 80) by (rewrite E2; exact Hsp).
assert (U9 : bv_unsigned (ew E 9) = SA + 40) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = SA + 48) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
assert (BVR : forall w : word, 0 <= bv_unsigned w < 2 ^ 64)
  by (intros w; pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw; lia).
assert (WRB : forall o, 0 <= o < 12 -> writable_at SEGS (mrestrict (w_H Wc) memc) (SA + 40 + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HTpres (SA + 40 + o) ltac:(lia))). }
split.
- unfold ss_gt, gt_regs. apply pa_entry_st_ok_full.
  + apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    rewrite R18. apply bv_eq. unfold w64 at 1. rewrite unsigned_lit_small by (unfold SB; lia).
    fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 19 0))).
    rewrite !U_SAlu. rewrite (U_atom E 8 (SA + 48) E8) by lia. rewrite (U_atom E 19 SB E19) by (unfold SB; lia).
    rewrite U_lit by lia. cbn [zalu_raw].
    change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite (Z.mod_small ((SA + 48) / 8)) by (unfold SB; lia).
    rewrite Z.mod_small by (unfold SB; lia).
    reflexivity.
  + vm_compute. reflexivity.
  + unfold gt_regions, gt_frame, gt_held, gt_nheld.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 8 8 (SOff 33 0) (bv_unsigned (getr regs 23)));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 23)); zside | zside |].
         replace (sp0 - 80 + 8) with (sp0 - 72) by lia. exact V23.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 16 8 (SOff 34 0) (bv_unsigned (getr regs 22)));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 22)); zside | zside |].
         replace (sp0 - 80 + 16) with (sp0 - 64) by lia. exact V22.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 24 8 (SOff 35 0) (bv_unsigned (getr regs 21)));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 21)); zside | zside |].
         replace (sp0 - 80 + 24) with (sp0 - 56) by lia. exact V21.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 32 8 (SOff 36 0) (bv_unsigned (getr regs 20)));
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 20)); zside | zside |].
         replace (sp0 - 80 + 32) with (sp0 - 48) by lia. exact V20.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 40 8 (SOff 37 0) (bv_unsigned (getr regs 19)));
         [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 19)); zside | zside |].
         replace (sp0 - 80 + 40) with (sp0 - 40) by lia. exact V19.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 48 8 (SOff 38 0) (bv_unsigned (getr regs 18)));
         [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 18)); zside | zside |].
         replace (sp0 - 80 + 48) with (sp0 - 32) by lia. exact V18.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 56 8 (SOff 39 0) (bv_unsigned (getr regs 9)));
         [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 9)); zside | zside |].
         replace (sp0 - 80 + 56) with (sp0 - 24) by lia. exact V9.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 64 8 (SOff 40 0) (bv_unsigned (getr regs 8)));
         [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 8)); zside | zside |].
         replace (sp0 - 80 + 64) with (sp0 - 16) by lia. exact V8.
      -- apply (chunk_ok_val SEGS E _ (sp0 - 80) 72 8 (SOff 41 0) (bv_unsigned (getr regs 1)));
         [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
         | pose proof (BVR (getr regs 1)); zside | zside |].
         replace (sp0 - 80 + 72) with (sp0 - 8) by lia. exact V1.
    * rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. replace (SA + 40 + o) with (SA + 40 + o) by lia. exact (WRB o ltac:(lia)). }
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ (SA + 40) 0 8 (SOff 32 0) hp);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact Mhp.
    * rewrite U8. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. replace (SA + 48 + o) with (SA + 40 + (o + 8)) by lia. exact (WRB (o + 8) ltac:(lia)).
  + apply pairwise_disjoint_of_extents. unfold gt_regions, gt_frame, gt_held, gt_nheld, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U9, U8.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsplo Hsphi RSA C1 HT1 HT2 HT4096 HTceil. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [gt_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U9, U8, E19. unfold w64. rewrite unsigned_lit_small by (unfold SB; lia).
    unfold GT_PHI.
    split; [split; [lia|]; split;
      [replace (2 ^ 4) with 16 by reflexivity; rewrite Zminus_mod, Hspal; reflexivity | lia]|].
    split; [split; [lia|]; split;
      [replace (2 ^ 3) with 8 by reflexivity; rewrite Zplus_mod, HSA8; reflexivity | lia]|].
    split; [split; [lia|]; split;
      [replace (2 ^ 3) with 8 by reflexivity; rewrite Zplus_mod, HSA8; reflexivity | lia]|].
    split; [split; [lia|]; split;
      [replace (2 ^ 0) with 1 by reflexivity; apply Z.mod_1_r | lia] | exact I].
- unfold sh_ok, gt_SH. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E BxT 9 TB 896 (SA + 40) 0 8).
    * exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc Wc memc mdc TB ATABLE TB 896 HAR HTBin ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    * unfold U, BxT. cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned.
      unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  + apply (shent_ok_of_range SEGS (w_H Wc) memc E BxT 8 TB 896 (SA + 48) 0 8).
    * exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc Wc memc mdc TB ATABLE TB 896 HAR HTBin ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    * unfold U, BxT. cbn [sv_denot]. rewrite E19, Z.add_0_r, Z_to_bv_bv_unsigned.
      unfold w64. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    * unfold U. cbn [sv_denot]. rewrite E8, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

(* ------------------------------------------------------------------ the controller's cells (W_gesture_end.v's) *)
Lemma gt_aout_fp_cases : forall cap out r, In r (aout_fp B RG cap out) ->
In r (aout_fp B RG 0 0) \/ (cap <> 0 /\ r = (out, out + cap)).
Proof.
intros cap out r Hr. unfold aout_fp in Hr |- *. cbn [Z.eqb] in *.
do 9 (destruct Hr as [Hr | Hr]; [left; subst r; cbn; tauto|]).
destruct (Z.eqb_spec cap 0); [destruct Hr | destruct Hr as [<- | []]; right; split; [exact n | reflexivity]].
Qed.
Lemma gt_aout_blk : forall ly S W mem c O mx no cap out, aout_at B RG ly S W mem c O mx no cap out ->
(cap = 0 /\ out = 0 /\ no = 0) \/ (0 < cap /\ no <= cap /\ In (out, cap) (ablocks B ly S)).
Proof.
intros ly S W mem c O mx no cap out
(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd).
destruct Hd as [Hd | (H1 & H2 & H3 & _)]; [left; exact Hd | right; split; [exact H1 | split; [exact H2 | exact H3]]].
Qed.
(* every byte the controller's model reads has a view: the cells' val_mem and the out block's bytes *)
Lemma gt_out_seen : forall ly' S' W' mem' c' O' mx' no' cap' out' r a,
aout_at B RG ly' S' W' mem' c' O' mx' no' cap' out' -> In r (aout_fp B RG cap' out') -> fst r <= a < snd r ->
aview SEGS (w_H W') mem' a <> None.
Proof.
intros ly' S' W' mem' c' O' mx' no' cap' out' r a
(H1 & _ & H3 & _ & H5 & _ & H7 & _ & H9 & _ & H11 & _ & H13 & _ & H15 & _ & H17 & _ & _ & _ & _ & _ & _ & _ & H25 & H26)
Hr Ha.
unfold aout_fp in Hr. unfold arm in *.
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_send_max RG + (a - rg_send_max RG)) by lia;
 exact (gt_view_some _ _ _ 8 _ (a - rg_send_max RG) H1 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_nout RG + (a - rg_nout RG)) by lia;
 exact (gt_view_some _ _ _ 8 _ (a - rg_nout RG) H3 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_capout RG + (a - rg_capout RG)) by lia;
 exact (gt_view_some _ _ _ 8 _ (a - rg_capout RG) H5 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_out RG + (a - rg_out RG)) by lia;
 exact (gt_view_some _ _ _ 8 _ (a - rg_out RG) H7 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_client RG + (a - rg_client RG)) by lia;
 exact (gt_view_some _ _ _ 4 _ (a - rg_client RG) H9 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_client_broken RG + (a - rg_client_broken RG)) by lia;
 exact (gt_view_some _ _ _ 1 _ (a - rg_client_broken RG) H11 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_send_dead RG + (a - rg_send_dead RG)) by lia;
 exact (gt_view_some _ _ _ 1 _ (a - rg_send_dead RG) H13 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (rg_send_eintr RG + (a - rg_send_eintr RG)) by lia;
 exact (gt_view_some _ _ _ 1 _ (a - rg_send_eintr RG) H15 ltac:(cbn; lia))|].
destruct Hr as [<- | Hr];
[cbn [fst snd] in Ha; replace a with (as_errno B + (a - as_errno B)) by lia;
 exact (gt_view_some _ _ _ 4 _ (a - as_errno B) H17 ltac:(cbn; lia))|].
destruct (Z.eqb_spec cap' 0) as [-> | Hc0]; [destruct Hr|].
destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct H26 as [(Hc & _) | (_ & _ & _ & junk & Hj & Hg)]; [lia|].
replace a with (out' + (a - out')) by lia. apply (gt_view_garr8 _ _ _ _ (a - out') Hg).
unfold bzs. rewrite length_map, length_app. lia.
Qed.
(* a byte whose view is kept and seen, off the read-only segments, is kept *)
Lemma gt_abyte_kept : forall (W' W'' : world SEGS) (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 ->
aview SEGS (w_H W'') m' a = aview SEGS (w_H W') m a -> aview SEGS (w_H W') m a <> None -> ~ in_rom SEGS a ->
abyte_kept W' m W'' m' a.
Proof.
intros W' W'' m m' a Ha He Hs Hr. split; [exact He|]. intros _. unfold arm.
destruct (aview SEGS (w_H W') m a) as [v|] eqn:Ev; [|exfalso; exact (Hs eq_refl)].
exact (gt_writable_view (w_H W'') m' a v Ha He Hr).
Qed.

(* the runs write only s->held and s->nheld: every other byte is outside the regions' writable windows *)
Ltac gt_outw Usp U9 U8 :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
cbn [ss_mem add_cond ss_gt gt_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val gt_frame gt_held gt_nheld] in Hr;
  rewrite ?Usp, ?U9, ?U8 in Hr; lia | ]);
destruct Hin.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the tail at a world relation R.  The journal ajournal_gx_x becomes
   ajournal_gx_xR R, SRr SEGS becomes SRrG SEGS R, the runs are their SRrG forms (W_journal_x.v paj_run_x_xG), the
   return is the strict step lifted by SRr_SRrG (WLE_R), and the free rules are their R forms (W_journal_x.v Section
   hc: afree_cf_rule_c_xR / afree_null_cf_rule_c_xR .. RO CTX_AFREE R), which also take the call-boundary premise RO
   on the call memory: RO_ARx gives it from the journal's ARx at the call state (part 3c took memnorm out of the free
   rules).  The strict gt_free_x and pb_gse_tail_x keep their proofs. *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :268 gt_free_x *)
Lemma gt_free_xR : forall G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l (o : Z) raw ch (kr : nat),
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
Permutation (ablocks B lyc Sc) (gse_hpblk hp kh ++ l) ->
getr regsT 10 = w64 hp ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX_AFREE ->
rp_RM RP Sc (1 + kr) ->
cnt_ok RP (ablocks B lyc Sc) ->
(hp <> 0 -> forall i, 0 <= i < req_size kh -> inFP FP (hp + i)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal_gx_xR SEGS B PST ARx R G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
aregs_preserved regsT regs2 /\
Permutation (ablocks B ly2 S2) l /\
acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => hp <> 0 /\ hp <= a < hp + req_size kh) /\
mo_le MT Sc S2 (mo_free MT) /\
rp_RM RP S2 kr /\
(forall i, 0 <= i < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + i) = aview SEGS (w_H W) memT (as_errno B + i)) /\
apres_kept B W memT W2 mem2).
Proof.
intros G W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k hp kh l o raw ch kr
  (H0 & H1 & (memS & HJi & Hag) & Hout) HP H10 Hsp Hal Hneg Hst Hgp Htp Hra Hraw Hch HCTX HRM HCNT HFP MOK.
rewrite !Z.add_0_r in HJi.
pose proof (aj_stack_room_xR SEGS B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJi Hsp Hst) as Hroom.
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
unfold gse_hpblk in HP. destruct (Z.eqb_spec hp 0) as [Hz | Hnz].
- subst hp. cbn [app] in HP. eapply SRrG_mono.
  { exact (AFREEN_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k o raw ch kr HJi H10 Hsp Hal Hneg Hst
      Hroom Hgp Htp Hra Hraw Hch HRO HCTX HRM HCNT MOK). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HPm & _ & HK & HM & HRM2 & HE & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|]. split; [eapply Permutation_trans; [exact HPm | exact HP]|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a []]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hp'. apply HPr; [exact Hi | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | exact Hp'].
- assert (Hin : In (hp, kh) (ablocks B lyc Sc))
    by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
  eapply SRrG_mono.
  { apply (AFREE_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k hp kh o raw ch kr HJi Hin H10 Hsp Hal
      Hneg Hst Hroom Hgp Htp Hra Hraw Hch HRO HCTX HRM HCNT); [intros _ i Hi; exact (HFP Hnz i Hi) | exact MOK]. }
  cbv beta.
  intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & E1 & E2) & _ & HK & HM & HRM2 & HE
    & HPr).
  exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
  split; [apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
    [lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia]|].
  split; [exact HP2|].
  split; [rewrite E2; apply Permutation_sym; apply (@Permutation_cons_app_inv _ l l1 l2 (hp, kh)); rewrite <- E1;
    apply Permutation_sym; exact HP|].
  split; [eapply (acall_kept_mono_E SEGS B); [exact HK | intros a Ha; split; [exact Hnz | exact Ha]]|].
  split; [exact HM|]. split; [exact HRM2|]. split; [exact HE|].
  intros a Hi Ho He Hp'. apply HPr; [exact Hi | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJi) Hi Ho)
  | exact (gt_not_owned_x _ _ _ _ _ _ a (proj1 HJ2) Hi Ho) | exact He | | exact Hp'].
  intros Hr. pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc W memT mdc hp kh (proj1 HJi) Hin) as Hoff.
  pose proof (pa_img_range a Hi). unfold off_img in Hoff. lia.
Qed.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_SL B RG) HG 0 [].
(* :661 pb_gse_tail_x *)
Theorem pb_gse_tail_xR : gse_tail_at_xR B PST ARx MT RP MMAX RG R (BASE + A_gse_tail).
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc Hpc regsc memc mdc k outi kr HPRE HINV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as (HERR0 & HERRIMG & _).
unfold gse_pre_x in HPRE.
destruct HPRE as (HAFN & H10 & HTBin & HT1 & HT2 & HSA8 & HEB & HAW & HHELD & HOUT & HPERM & G5 & HROM & ROOM & MOK &
  RM0 & CNT0).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : GSE_STK = 16608) by reflexivity.
unfold gse_inv_xR in HINV. cbv zeta in HINV.
assert (HKlen : length (gse_keys e) = length (re_keys e)) by (unfold gse_keys; apply length_map).
assert (Hfst : firstn (length (re_keys e)) (gse_keys e) = gse_keys e) by (rewrite <- HKlen; apply firstn_all).
assert (Hskp : skipn (length (re_keys e)) (gse_keys e) = []) by (rewrite <- HKlen; apply skipn_all).
assert (Hskr : skipn (length (re_keys e)) (re_keys e) = []) by apply skipn_all.
rewrite Hfst, Hskp, Hskr in HINV.
destruct HINV as (HJ & HPRESc & HMLE & HMOKc & HRMc & HROOMc & HPERMc & HOUTc & HEBc & HAWc & HHPc & HKEYc & G5c & HROMc &
  HSPc & H3c & H4c & H8c & H9c & H18c & H19c & H2427c & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23).
(* the room round: the free's count at Sc, from the entry's (the keys are freed, the output block is at most one) *)
assert (HCNTc : cnt_ok RP (ablocks B lyc Sc)).
{ unfold cnt_ok. eapply (gse_cnt_at RP _ _ e (ablocks B ly S) (ablocks B lyc Sc) TB (length (re_keys e)) cap out);
  [| exact HPERM | rewrite Hskr; exact HPERMc | exact CNT0]; intros P; cbv [gse_pk]; lia. }
(* the room round: the one call left is the free (MT_rk's mo_free is 1) *)
assert (HRM1 : rp_RM RP Sc (1 + kr)) by exact HRMc.
clear HRMc.
cbn [gse_cost kblks map app] in HMOKc, HPERMc.
set (rr := gse_run c O mx no cap (gse_keys e)) in *.
(* the live blocks here, and the table block *)
assert (HARc : ARx lyc Sc Hpc Wc memc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
assert (HTBc : In (TB, ATABLE) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERMc | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc TB ATABLE HARc HTBc) as (HT16 & HT4096 & HTceil & HTia & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTpres, HTia.
unfold AENT, ATABLE in HT2.
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc TB ATABLE HARc HTBc) as HTimg.
change (req_size ATABLE) with 896 in HTimg.
assert (RSA : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by lia.
(* hp = s->held, and its block *)
pose proof HHELD as (Hp1 & Hp2 & Hnh & HHP & _ & _ & _).
assert (Rhp : 0 <= re_hp e < 2 ^ 64).
{ destruct (Z.eqb_spec (re_hp e) 0) as [Hz | Hnz]; [rewrite Hz; lia|].
  assert (Hin : In (re_hp e, re_kh e) (ablocks B lyc Sc)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERMc|]. right.
    unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq _ _) Hnz). cbn [app]. left. reflexivity. }
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (_ & H4 & Hc & _ & _ & _).
  pose proof (BLKN _ _ _ _ _ _ _ _ HARc Hin) as Hn.
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as [Hr1 _]. lia. }
(* s's bytes at the cut: the 40 before held, held, nheld, pad2 *)
pose proof HEBc as HEB2. rewrite gt_entry_split in HEB2. unfold bzs in HEB2. rewrite !map_app in HEB2.
apply garr8_app in HEB2 as [GPRE HEB2]. rewrite length_map, (gt_epre_len e Hp1) in HEB2.
apply garr8_app in HEB2 as [Ghp HEB2].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8 in HEB2.
apply garr8_app in HEB2 as [Gnh GPAD].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in GPAD.
change (SA + Z.of_nat 40) with (SA + 40) in Ghp, Gnh, GPAD.
replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh, GPAD by lia.
replace (SA + 48 + Z.of_nat 4) with (SA + 52) in GPAD by lia.
assert (Mhp : val_mem SEGS (arm Wc memc) (SA + 40) 8 (re_hp e)).
{ apply gt_garr8_le; [|lia]. rewrite <- gt_le8_bytes by lia. exact Ghp. }
(* the seat *)
destruct (gt_entry_x Wc lyc Sc Hpc memc mdc regsc regs SA TB (re_hp e) (spZ regs) HARc HTBc HT1 ltac:(unfold AENT, ATABLE; lia)
  HSA8 Mhp Rhp ltac:(lia) ltac:(lia) Hal16 HSPc H8c H9c H18c H19c V1 V8 V9 V18 V19 V20 V21 V22 V23)
  as [HS SHOK].
remember (Eimg (Ereg regsc (gt_extra (re_hp e) regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (gt_extra (re_hp e) regs)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as H5;
      change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j)%nat = nth j (gt_extra (re_hp e) regs) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regsc 1) by (apply (EL 1%nat 1%bv); reflexivity).
assert (E2 : ew E 2 = getr regsc 2) by (apply (EL 2%nat 2%bv); reflexivity).
assert (E3 : ew E 3 = getr regsc 3) by (apply (EL 3%nat 3%bv); reflexivity).
assert (E4 : ew E 4 = getr regsc 4) by (apply (EL 4%nat 4%bv); reflexivity).
assert (E8 : ew E 8 = w64 (SA + 48)) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8c).
assert (E9 : ew E 9 = w64 (SA + 40)) by (rewrite (EL 9%nat 9%bv eq_refl); exact H9c).
assert (E19 : ew E 19 = w64 SB) by (rewrite (EL 19%nat 19%bv eq_refl); exact H19c).
assert (E24 : ew E 24 = getr regsc 24) by (apply (EL 24%nat 24%bv); reflexivity).
assert (E25 : ew E 25 = getr regsc 25) by (apply (EL 25%nat 25%bv); reflexivity).
assert (E26 : ew E 26 = getr regsc 26) by (apply (EL 26%nat 26%bv); reflexivity).
assert (E27 : ew E 27 = getr regsc 27) by (apply (EL 27%nat 27%bv); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e)) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = getr regs 23) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = getr regs 22) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = getr regs 21) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = getr regs 20) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = getr regs 19) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = getr regs 18) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = getr regs 9) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = getr regs 8) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = getr regs 1) by (exact (EX 9%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - GSE_FRAME) by (rewrite E2; exact HSPc).
assert (U9 : bv_unsigned (ew E 9) = SA + 40) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = SA + 48) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
unfold GSE_FRAME in Usp, HSPc.
clear HE.
(* the write obligation of every run: the two cells lie in s's block and in the journal's footprint *)
assert (AWRT : forall a, SA + 40 <= a < SA + 52 ->
  awr_byte GSE_STK (spZ regs) (gse_FP SA e cap out) (ablocks B ly S) (ablocks B lyc Sc) lyc [] a).
{ intros a Ha. right. left. split.
  - exists (SA + 40, SA + 52). split; [unfold gse_FP; left; reflexivity | cbn [fst snd]; lia].
  - exists TB, ATABLE. split; [exact HTBc | change (req_size ATABLE) with 896; lia]. }
unfold A_gse_tail in *.
(* ---- run 1: 0x82638 -> the free trampoline (the load8 check of s->held, no store) ---- *)
paj_run_tok_xR RUNG HS HJ SHOK gt_Bspan.
{ apply awr_ok_x_of0. intros a Hwr. apply AWRT. revert Hwr.
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gt gt_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val gt_frame gt_held gt_nheld] in Hr;
    rewrite ?Usp, ?U9, ?U8 in Hr; lia | ]); destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Usp1 : spZ (ms_regs ms) = spZ regs - 80)
  by (unfold spZ; rewrite P2; exact Usp).
assert (Hs01 : s0Z (ms_regs ms) = SA + 48)
  by (unfold s0Z; rewrite P8, E8; unfold w64; apply unsigned_lit_small; lia).
assert (Hra1 : 4096 <= raZ (ms_regs ms))
  by (unfold raZ; rewrite P1; rewrite unsigned_lit_small by lia; lia).
(* what run 1 kept: it stored nothing *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr a Ha).
  clear - Usp U9 U8 Hno. gt_outw Usp U9 U8. }
assert (PRES1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a).
{ intros a Hpa. lazymatch goal with
  | K1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    exact (apresent_grows _ _ _ a K1 Hpa) end. }
(* ---- free (s->held) at 0x8264c (gestures_end_b.v's FREE, :1031) ---- *)
rewrite (pal_free B TL).
eapply (SRrG_bind SEGS R R_trans).
{ eapply (gt_free_xR (G_SL B RG) Wc (ms_regs ms) (ms_mem ms) GSE_STK (spZ regs) (gse_FP SA e cap out)
    ly S Hp W mem md [] lyc Sc Hpc _ k (re_hp e) (re_kh e)
    ((TB, ATABLE) :: aout_blks (gse_cap rr) outi ++ rest) (- 80) _ [] kr HJ).
  - eapply perm_trans; [exact HPERMc | apply Permutation_middle].
  - rewrite P10, E32. reflexivity.
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - rewrite P3, E3, H3c. exact Hgp.
  - rewrite P4, E4, H4c. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ (ms_regs ms)) (SA + 48) [] (ms_regs ms));
    [apply achain_low; lia | lia | exact Hs01 | exact Hra1].
  - (* the free's caller context: the chain is [], the trace the singleton [gestures_end + 0xfc] (ra 0x82650) *)
    cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_gestures_end + 0xfc); [exact HCTX_gse_tail|].
    unfold raZ. rewrite P1, unsigned_lit_small by lia. first [lia | unfold AF_fr_gestures_end in *; lia].
  - exact HRM1.
  - exact HCNTc.
  - intros Hnz i Hi.
    destruct (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) (re_hp e) (re_kh e) i
      ltac:(apply in_or_app; left; unfold gse_blks; rewrite (proj2 (Z.eqb_neq _ _) Hnz); left; reflexivity) Hi)
      as (r0 & Hr0 & Hr0a).
    exists r0. split; [unfold gse_FP; right; exact Hr0 | exact Hr0a].
  - exact HMOKc. }
cbv beta.
intros W2 c2 Hwle2 (ly2 & S2 & Hq2 & regs2 & mem2 & md2 & -> & HJ2 & HPRE2 & HPm2 & KFREE & HMfree & HRM2 & HERRK &
  HAPK2).
(* ---- the state after free: s's block is still live, and it is not the block that was freed ---- *)
assert (HAR2 : ARx ly2 S2 Hq2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
assert (HTB2 : In (TB, ATABLE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm2 | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hq2 W2 mem2 md2 TB ATABLE HAR2 HTB2) as (_ & _ & _ & _ & HTpres2 & _).
change (req_size ATABLE) with 896 in HTpres2.
assert (WRB2 : forall a, TB <= a < TB + 896 -> writable_at SEGS (mrestrict (w_H W2) mem2) a)
  by (intros a Ha; apply (apresent_writable SEGS); exact (proj1 (HTpres2 a Ha))).
assert (PWbase : pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b)))
  ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ aout_blks (gse_cap rr) outi ++ rest))).
{ destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HARc) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
  exact (gt_pw_perm _ _ (Permutation_map _ HPERMc) Hpw). }
assert (DTB : forall q m, In (q, m) (aout_blks (gse_cap rr) outi ++ rest) ->
  TB + 896 <= q \/ q + req_size m <= TB).
{ intros q m Hq. pose proof PWbase as PW.
  assert (HFA : Forall (zdisjoint (TB, req_size ATABLE))
    (map (fun b : Z * Z => (fst b, req_size (snd b))) (aout_blks (gse_cap rr) outi ++ rest))).
  { destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (Hnz & Eq)];
    rewrite Eq in PW; cbn [map] in PW.
    - exact (proj1 PW).
    - destruct PW as [Hf _]. inversion Hf as [|u v Hd Hf2]; subst. exact Hf2. }
  rewrite Forall_forall in HFA.
  pose proof (HFA (q, req_size m) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (q, m) Hq)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. lia. }
assert (DHP : re_hp e <> 0 -> TB + 896 <= re_hp e \/ re_hp e + req_size (re_kh e) <= TB).
{ intros Hnz. pose proof PWbase as PW.
  destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (_ & Eq)];
  [exfalso; exact (Hnz Hz)|]. rewrite Eq in PW; cbn [map] in PW.
  destruct PW as [Hf _]. inversion Hf as [|u v Hd Hf2]; subst.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. lia. }
assert (DHPOUT : re_hp e <> 0 -> forall q m, In (q, m) (aout_blks (gse_cap rr) outi ++ rest) ->
  re_hp e + req_size (re_kh e) <= q \/ q + req_size m <= re_hp e).
{ intros Hnz q m Hq. pose proof PWbase as PW.
  destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (_ & Eq)];
  [exfalso; exact (Hnz Hz)|]. rewrite Eq in PW; cbn [map] in PW.
  destruct PW as [_ [Hf _]]. rewrite Forall_forall in Hf.
  pose proof (Hf (q, req_size m) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (q, m) Hq)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the two cells s+40 .. s+52 are none of the bytes the controller's model reads *)
assert (NWIMG : forall a, in_img SEGS a -> ~ (SA + 40 <= a < SA + 52)).
{ intros a Ha Hr. pose proof (pa_img_range a Ha). unfold off_img in HTimg. lia. }
assert (OUTB : gse_cap rr <> 0 -> In (outi, gse_cap rr) (aout_blks (gse_cap rr) outi ++ rest))
  by (intros Hc; apply in_or_app; left; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); left; reflexivity).
assert (FPLO : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 -> 0 <= a < 2 ^ 64).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + pose proof (pa_img_range a (HERRIMG a ltac:(lia))). lia.
    + pose proof (pa_img_range a (proj1 (HOUTG r0 a Hc Ha ltac:(lia)))). lia.
    + pose proof (pa_img_range a (proj1 (HOUTG r0 a Hc Ha ltac:(lia)))). lia.
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hinb) as (_ & Hb4 & Hbc & _).
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs]. lia. }
assert (NWFP : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 ->
  ~ (SA + 40 <= a < SA + 52)).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + apply NWIMG, HERRIMG. lia.
    + apply NWIMG. exact (proj1 (HOUTG r0 a Hc Ha ltac:(lia))).
    + apply NWIMG. exact (proj1 (HOUTG r0 a Hc Ha ltac:(lia))).
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs].
    pose proof (DTB outi (gse_cap rr) (OUTB ltac:(lia))). lia. }
(* their views and their writability across the free *)
assert (KFP2 : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a /\ ~ in_rom SEGS a).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + split.
      * replace a with (as_errno B + (a - as_errno B)) by lia. apply HERRK. lia.
      * intros Hrom. exact (proj1 (proj2 (proj2 (HROMO a Hrom))) ltac:(lia)).
    + destruct (HOUTG r0 a Hc Ha ltac:(lia)) as (Hi & Hnr & Hno).
      split; [exact (proj1 (proj2 (proj2 KFREE)) a Hi Hno ltac:(lia)) | exact Hnr].
    + destruct (HOUTG r0 a Hc Ha ltac:(lia)) as (Hi & Hnr & Hno).
      split; [exact (proj1 (proj2 (proj2 KFREE)) a Hi Hno ltac:(lia)) | exact Hnr].
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs].
    split.
    + replace a with (outi + (a - outi)) by lia.
      apply (proj1 (proj2 KFREE) outi (gse_cap rr) (a - outi) Hinb ltac:(lia)).
      intros (Hnz & Hr). pose proof (DHPOUT Hnz outi (gse_cap rr) (OUTB ltac:(lia))). lia.
    + intros Hrom.
      assert (Hi : in_img SEGS a)
        by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc Wc memc mdc a HARc
        ltac:(left; exists outi, (gse_cap rr); split; [exact Hinb | lia])) as (_ & Hni). exact (Hni Hi). }
assert (HOUT2 : aout_at B RG ly2 S2 W2 mem2 (gse_c rr) (gse_O rr) mx (gse_no rr) (gse_cap rr) outi).
{ apply (aout_at_kept B RG lyc Sc Wc memc ly2 S2 W2 mem2 _ _ _ _ _ _ HOUTc).
  - intros r0 Hr0 a Ha. apply gt_abyte_kept.
    + exact (FPLO r0 a Hr0 Ha).
    + rewrite (proj1 (KFP2 r0 a Hr0 Ha)).
      apply KEEP1; [exact (FPLO r0 a Hr0 Ha) | exact (NWFP r0 a Hr0 Ha)].
    + exact (gt_out_seen lyc Sc Wc memc _ _ _ _ _ _ r0 a HOUTc Hr0 Ha).
    + exact (proj2 (KFP2 r0 a Hr0 Ha)).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (gse_cap rr) 0); [destruct Hb|].
    destruct Hb as [<- | []]. eapply Permutation_in; [apply Permutation_sym; exact HPm2|].
    right. apply in_or_app. left. unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) n). left. reflexivity. }
(* ---- back at 0x82650 (gestures_end_b.v's :1071): the two checked stores and the epilogue ---- *)
assert (AWRT2 : forall a, SA + 40 <= a < SA + 52 ->
  awr_byte GSE_STK (spZ regs) (gse_FP SA e cap out) (ablocks B ly S) (ablocks B ly2 S2) ly2 [] a).
{ intros a Ha. right. left. split.
  - exists (SA + 40, SA + 52). split; [unfold gse_FP; left; reflexivity | cbn [fst snd]; lia].
  - exists TB, ATABLE. split; [exact HTB2 | change (req_size ATABLE) with 896; lia]. }
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H W2) mem2) HPRE2 [0;1;2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 KFREE); unfold ASTACK; lia.
    + intros a Ha _. exfalso. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9.
    + intros a Ha. apply (mbyte_of_aview SEGS). replace a with (TB + (a - TB)) by lia.
      apply (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)).
      intros (Hnz & Hr). pose proof (DHP Hnz). lia.
    + intros a Ha _. apply WRB2. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U8.
    + intros a Ha. apply (mbyte_of_aview SEGS). replace a with (TB + (a - TB)) by lia.
      apply (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)).
      intros (Hnz & Hr). pose proof (DHP Hnz). lia.
    + intros a Ha _. apply WRB2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 42 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 42)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs - 80) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (U9a : bv_unsigned (ew Ea 9) = SA + 40) by (rewrite OLDa by (cbv; lia); exact U9).
assert (U8a : bv_unsigned (ew Ea 8) = SA + 48) by (rewrite OLDa by (cbv; lia); exact U8).
assert (E19a : ew Ea 19 = w64 SB) by (rewrite OLDa by (cbv; lia); exact E19).
assert (E41a : ew Ea 41 = getr regs 1) by (rewrite OLDa by (cbv; lia); exact E41).
assert (SHOKa : sh_ok SEGS BxT gt_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, gt_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxT 9 TB 896 (SA + 40) 0 8).
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hq2 W2 mem2 md2 TB ATABLE TB 896 HAR2 HTB2 ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    + unfold U, BxT. cbn [sv_denot]. rewrite E19a, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9a.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxT 8 TB 896 (SA + 48) 0 8).
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hq2 W2 mem2 md2 TB ATABLE TB 896 HAR2 HTB2 ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    + unfold U, BxT. cbn [sv_denot]. rewrite E19a, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8a.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
(* ---- run 2: 0x82650 -> ret ---- *)
paj_run_tok_xR RUNG HS HJ2 SHOKa gt_Bspan.
{ apply awr_ok_x_of0. intros a Hwr. apply AWRT2. revert Hwr.
  intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Uspa, ?U9a, ?U8a in Hr; lia | ]); destruct Hin. }
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2.
(* the two cells s->held = 0 and s->nheld = 0, and what run 2 kept *)
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRG9.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl) as HRG8.
cbn [ms_mem restrict] in HRG9, HRG8.
assert (M40 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 40) 8 0).
{ pose proof (field_of_region Ea (mrestrict (w_H W2) (ms_mem ms0)) 9%nat (SA + 40) _ 0 8 0 8 0 8%N (SLit 0) 0
    HRG9 U9a (or_introl eq_refl) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (M48 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 48) 4 0).
{ pose proof (field_of_region Ea (mrestrict (w_H W2) (ms_mem ms0)) 8%nat (SA + 48) _ 0 4 0 4 0 4%N (SLit 0) 0
    HRG8 U8a (or_introl eq_refl) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms0) HFr0 a Ha).
  clear - Uspa U9a U8a Hno.
  intros (r0 & Hin & Hr0); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr0;
    rewrite ?Uspa, ?U9a, ?U8a in Hr0; lia | ]); destruct Hin. }
assert (PRES2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms0) a).
{ intros a Hpa. lazymatch goal with
  | K2 : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms0)) |- _ =>
    exact (apresent_grows _ _ _ a K2 Hpa) end. }
(* the controller's model after the two stores *)
assert (HOUT3 : aout_at B RG ly2 S2 W2 (ms_mem ms0) (gse_c rr) (gse_O rr) mx (gse_no rr) (gse_cap rr) outi).
{ apply (aout_at_kept B RG ly2 S2 W2 mem2 ly2 S2 W2 (ms_mem ms0) _ _ _ _ _ _ HOUT2).
  - intros r0 Hr0 a Ha. apply gt_abyte_kept.
    + exact (FPLO r0 a Hr0 Ha).
    + apply KEEP2; [exact (FPLO r0 a Hr0 Ha) | exact (NWFP r0 a Hr0 Ha)].
    + exact (gt_out_seen ly2 S2 W2 mem2 _ _ _ _ _ _ r0 a HOUT2 Hr0 Ha).
    + exact (proj2 (KFP2 r0 a Hr0 Ha)).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (gse_cap rr) 0); [destruct Hb|].
    destruct Hb as [<- | []]. eapply Permutation_in; [apply Permutation_sym; exact HPm2|].
    right. apply in_or_app. left. unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) n). left. reflexivity. }
(* s's other bytes, kept through run 1, the free and run 2 *)
assert (KEEPTB : forall a, TB <= a < TB + 896 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. rewrite (KEEP2 a ltac:(lia) Hno).
  replace a with (TB + (a - TB)) by lia.
  rewrite (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)
    ltac:(intros (Hnz & Hr); pose proof (DHP Hnz); lia)).
  replace (TB + (a - TB)) with a by lia. apply KEEP1; [lia | exact Hno]. }
assert (GPRE2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) SA (bzs (gt_epre e))).
{ apply (gt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem ms0) SA _ GPRE).
  intros b Hb. unfold bzs in Hb. rewrite length_map, (gt_epre_len e Hp1) in Hb. apply KEEPTB; lia. }
assert (GPAD2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 52) (bzs (re_pad2 e))).
{ apply (gt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem ms0) (SA + 52) _ GPAD).
  intros b Hb. unfold bzs in Hb. rewrite length_map, Hp2 in Hb. apply KEEPTB; lia. }
assert (GEND : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) SA (bzs (entry_bytes (entry_cleared e)))).
{ rewrite gt_entry_split_cleared. unfold bzs. rewrite !map_app.
  apply garr8_app. split; [exact GPRE2|].
  rewrite length_map, (gt_epre_len e Hp1). change (SA + Z.of_nat 40) with (SA + 40).
  apply garr8_app. split.
  - rewrite gt_le8_bytes by lia. exact (gt_le_garr8 _ (SA + 40) 8 0 M40 ltac:(cbn; lia)).
  - rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8.
    replace (SA + 40 + Z.of_nat 8) with (SA + 48) by lia.
    apply garr8_app. split.
    + rewrite gt_le4_bytes by lia. exact (gt_le_garr8 _ (SA + 48) 4 0 M48 ltac:(cbn; lia)).
    + rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.
      replace (SA + 48 + Z.of_nat 4) with (SA + 52) by lia. exact GPAD2. }
pose proof HJ2 as HAR3. apply ajournal_gx_AR_xR in HAR3.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hq2 W2 (ms_mem ms0) _ TB ATABLE HAR3 HTB2) as (_ & _ & _ & _ & HTpres3 & _).
change (req_size ATABLE) with 896 in HTpres3.
assert (AWR3 : awr W2 (ms_mem ms0) SA AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  exact (proj1 (HTpres3 (SA + i) ltac:(unfold AENT in Hi; lia))). }
(* the callee-saved registers, back from the frame *)
prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
prreg HS (27%bv : bv 5) T27.
assert (PRESV : aregs_preserved regs (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T2, Uspa. replace (spZ regs - 80 + 80) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T3, (OLDa 3%nat ltac:(cbv; lia)), E3. exact H3c.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T4, (OLDa 4%nat ltac:(cbv; lia)), E4. exact H4c.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T8, (OLDa 40%nat ltac:(cbv; lia)). exact E40.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T9, (OLDa 39%nat ltac:(cbv; lia)). exact E39.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T18, (OLDa 38%nat ltac:(cbv; lia)). exact E38.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T19, (OLDa 37%nat ltac:(cbv; lia)). exact E37.
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T20, (OLDa 36%nat ltac:(cbv; lia)). exact E36.
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T21, (OLDa 35%nat ltac:(cbv; lia)). exact E35.
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T22, (OLDa 34%nat ltac:(cbv; lia)). exact E34.
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T23, (OLDa 33%nat ltac:(cbv; lia)). exact E33.
  - rewrite <- (H2427c 24 ltac:(lia)). replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T24, (OLDa 24%nat ltac:(cbv; lia)). exact E24.
  - rewrite <- (H2427c 25 ltac:(lia)). replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T25, (OLDa 25%nat ltac:(cbv; lia)). exact E25.
  - rewrite <- (H2427c 26 ltac:(lia)). replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T26, (OLDa 26%nat ltac:(cbv; lia)). exact E26.
  - rewrite <- (H2427c 27 ltac:(lia)). replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T27, (OLDa 27%nat ltac:(cbv; lia)). exact E27. }
(* ---- the return ---- *)
(* the return moves no world: the strict step, lifted by SRr_SRrG (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gse_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists ly2, S2, Hq2, r, m, d, (k + 1), outi end.
split; [cbn [ms_regs]; rewrite T1, E41a, Hra; reflexivity|].
split; [cbn [ms_mem]; unfold gse_FP in HJ2; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ2|].
split; [exact PRESV|].
split.
{ eapply gt_apres_trans; [exact HPRESc|].
  eapply gt_apres_trans; [apply (gt_apres_grows Wc memc (ms_mem ms)); lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => exact K1 end|].
  eapply gt_apres_trans; [exact HAPK2|].
  intros a _ _ _ Hpa. exact (PRES2 a Hpa). }
split; [rewrite gse_cost_spent; exact (mo_le_trans MT MTL _ _ _ _ _ HMLE HMfree)|].
split; [exact HRM2|].
split; [exact HPm2|].
split; [exact HOUT3|].
split; [exact GEND | exact AWR3].
Qed.
End wR.
Theorem pb_gse_tail_x : gse_tail_at_x B PST ARx MT RP MMAX RG (BASE + A_gse_tail).
Proof.
intros W ly S Hp regs mem md ch SA TB e c O mx no cap out rest Wc lyc Sc Hpc regsc memc mdc k outi kr HPRE HINV.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (pal_env B TL) as (HERR0 & HERRIMG & _).
unfold gse_pre_x in HPRE.
destruct HPRE as (HAFN & H10 & HTBin & HT1 & HT2 & HSA8 & HEB & HAW & HHELD & HOUT & HPERM & G5 & HROM & ROOM & MOK &
  RM0 & CNT0).
pose proof HAFN as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : GSE_STK = 16608) by reflexivity.
unfold gse_inv_x in HINV. cbv zeta in HINV.
assert (HKlen : length (gse_keys e) = length (re_keys e)) by (unfold gse_keys; apply length_map).
assert (Hfst : firstn (length (re_keys e)) (gse_keys e) = gse_keys e) by (rewrite <- HKlen; apply firstn_all).
assert (Hskp : skipn (length (re_keys e)) (gse_keys e) = []) by (rewrite <- HKlen; apply skipn_all).
assert (Hskr : skipn (length (re_keys e)) (re_keys e) = []) by apply skipn_all.
rewrite Hfst, Hskp, Hskr in HINV.
destruct HINV as (HJ & HPRESc & HMLE & HMOKc & HRMc & HROOMc & HPERMc & HOUTc & HEBc & HAWc & HHPc & HKEYc & G5c & HROMc &
  HSPc & H3c & H4c & H8c & H9c & H18c & H19c & H2427c & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23).
(* the room round: the free's count at Sc, from the entry's (the keys are freed, the output block is at most one) *)
assert (HCNTc : cnt_ok RP (ablocks B lyc Sc)).
{ unfold cnt_ok. eapply (gse_cnt_at RP _ _ e (ablocks B ly S) (ablocks B lyc Sc) TB (length (re_keys e)) cap out);
  [| exact HPERM | rewrite Hskr; exact HPERMc | exact CNT0]; intros P; cbv [gse_pk]; lia. }
(* the room round: the one call left is the free (MT_rk's mo_free is 1) *)
assert (HRM1 : rp_RM RP Sc (1 + kr)) by exact HRMc.
clear HRMc.
cbn [gse_cost kblks map app] in HMOKc, HPERMc.
set (rr := gse_run c O mx no cap (gse_keys e)) in *.
(* the live blocks here, and the table block *)
assert (HARc : ARx lyc Sc Hpc Wc memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
assert (HTBc : In (TB, ATABLE) (ablocks B lyc Sc))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPERMc | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc TB ATABLE HARc HTBc) as (HT16 & HT4096 & HTceil & HTia & HTpres & _).
change (req_size ATABLE) with 896 in HTceil, HTpres, HTia.
unfold AENT, ATABLE in HT2.
pose proof (blk_off_imgP_x B ARx LAWS IMGC BLKN lyc Sc Hpc Wc memc mdc TB ATABLE HARc HTBc) as HTimg.
change (req_size ATABLE) with 896 in HTimg.
assert (RSA : 4096 <= SA /\ SA + 56 <= alloc_ceiling) by lia.
(* hp = s->held, and its block *)
pose proof HHELD as (Hp1 & Hp2 & Hnh & HHP & _ & _ & _).
assert (Rhp : 0 <= re_hp e < 2 ^ 64).
{ destruct (Z.eqb_spec (re_hp e) 0) as [Hz | Hnz]; [rewrite Hz; lia|].
  assert (Hin : In (re_hp e, re_kh e) (ablocks B lyc Sc)).
  { eapply Permutation_in; [apply Permutation_sym; exact HPERMc|]. right.
    unfold gse_hpblk. rewrite (proj2 (Z.eqb_neq _ _) Hnz). cbn [app]. left. reflexivity. }
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hin) as (_ & H4 & Hc & _ & _ & _).
  pose proof (BLKN _ _ _ _ _ _ _ _ HARc Hin) as Hn.
  pose proof (req_size_pos (re_kh e) ltac:(lia)) as [Hr1 _]. lia. }
(* s's bytes at the cut: the 40 before held, held, nheld, pad2 *)
pose proof HEBc as HEB2. rewrite gt_entry_split in HEB2. unfold bzs in HEB2. rewrite !map_app in HEB2.
apply garr8_app in HEB2 as [GPRE HEB2]. rewrite length_map, (gt_epre_len e Hp1) in HEB2.
apply garr8_app in HEB2 as [Ghp HEB2].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8 in HEB2.
apply garr8_app in HEB2 as [Gnh GPAD].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in GPAD.
change (SA + Z.of_nat 40) with (SA + 40) in Ghp, Gnh, GPAD.
replace (SA + 40 + Z.of_nat 8) with (SA + 48) in Gnh, GPAD by lia.
replace (SA + 48 + Z.of_nat 4) with (SA + 52) in GPAD by lia.
assert (Mhp : val_mem SEGS (arm Wc memc) (SA + 40) 8 (re_hp e)).
{ apply gt_garr8_le; [|lia]. rewrite <- gt_le8_bytes by lia. exact Ghp. }
(* the seat *)
destruct (gt_entry_x Wc lyc Sc Hpc memc mdc regsc regs SA TB (re_hp e) (spZ regs) HARc HTBc HT1 ltac:(unfold AENT, ATABLE; lia)
  HSA8 Mhp Rhp ltac:(lia) ltac:(lia) Hal16 HSPc H8c H9c H18c H19c V1 V8 V9 V18 V19 V20 V21 V22 V23)
  as [HS SHOK].
remember (Eimg (Ereg regsc (gt_extra (re_hp e) regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regsc (gt_extra (re_hp e) regs)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (bv_unsigned_in_range 5 r) as H5;
      change (bv_modulus 5) with 32 in H5; unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j)%nat = nth j (gt_extra (re_hp e) regs) (Z_to_bv 64 0))
  by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E1 : ew E 1 = getr regsc 1) by (apply (EL 1%nat 1%bv); reflexivity).
assert (E2 : ew E 2 = getr regsc 2) by (apply (EL 2%nat 2%bv); reflexivity).
assert (E3 : ew E 3 = getr regsc 3) by (apply (EL 3%nat 3%bv); reflexivity).
assert (E4 : ew E 4 = getr regsc 4) by (apply (EL 4%nat 4%bv); reflexivity).
assert (E8 : ew E 8 = w64 (SA + 48)) by (rewrite (EL 8%nat 8%bv eq_refl); exact H8c).
assert (E9 : ew E 9 = w64 (SA + 40)) by (rewrite (EL 9%nat 9%bv eq_refl); exact H9c).
assert (E19 : ew E 19 = w64 SB) by (rewrite (EL 19%nat 19%bv eq_refl); exact H19c).
assert (E24 : ew E 24 = getr regsc 24) by (apply (EL 24%nat 24%bv); reflexivity).
assert (E25 : ew E 25 = getr regsc 25) by (apply (EL 25%nat 25%bv); reflexivity).
assert (E26 : ew E 26 = getr regsc 26) by (apply (EL 26%nat 26%bv); reflexivity).
assert (E27 : ew E 27 = getr regsc 27) by (apply (EL 27%nat 27%bv); reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (re_hp e)) by (exact (EX 0%nat ltac:(lia))).
assert (E33 : ew E 33 = getr regs 23) by (exact (EX 1%nat ltac:(lia))).
assert (E34 : ew E 34 = getr regs 22) by (exact (EX 2%nat ltac:(lia))).
assert (E35 : ew E 35 = getr regs 21) by (exact (EX 3%nat ltac:(lia))).
assert (E36 : ew E 36 = getr regs 20) by (exact (EX 4%nat ltac:(lia))).
assert (E37 : ew E 37 = getr regs 19) by (exact (EX 5%nat ltac:(lia))).
assert (E38 : ew E 38 = getr regs 18) by (exact (EX 6%nat ltac:(lia))).
assert (E39 : ew E 39 = getr regs 9) by (exact (EX 7%nat ltac:(lia))).
assert (E40 : ew E 40 = getr regs 8) by (exact (EX 8%nat ltac:(lia))).
assert (E41 : ew E 41 = getr regs 1) by (exact (EX 9%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - GSE_FRAME) by (rewrite E2; exact HSPc).
assert (U9 : bv_unsigned (ew E 9) = SA + 40) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = SA + 48) by (rewrite E8; unfold w64; apply unsigned_lit_small; lia).
unfold GSE_FRAME in Usp, HSPc.
clear HE.
(* the write obligation of every run: the two cells lie in s's block and in the journal's footprint *)
assert (AWRT : forall a, SA + 40 <= a < SA + 52 ->
  awr_byte GSE_STK (spZ regs) (gse_FP SA e cap out) (ablocks B ly S) (ablocks B lyc Sc) lyc [] a).
{ intros a Ha. right. left. split.
  - exists (SA + 40, SA + 52). split; [unfold gse_FP; left; reflexivity | cbn [fst snd]; lia].
  - exists TB, ATABLE. split; [exact HTBc | change (req_size ATABLE) with 896; lia]. }
unfold A_gse_tail in *.
(* ---- run 1: 0x82638 -> the free trampoline (the load8 check of s->held, no store) ---- *)
paj_run_tok_x RUN HS HJ SHOK gt_Bspan.
{ apply awr_ok_x_of0. intros a Hwr. apply AWRT. revert Hwr.
  intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gt gt_regions In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val gt_frame gt_held gt_nheld] in Hr;
    rewrite ?Usp, ?U9, ?U8 in Hr; lia | ]); destruct Hin. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
assert (Usp1 : spZ (ms_regs ms) = spZ regs - 80)
  by (unfold spZ; rewrite P2; exact Usp).
assert (Hs01 : s0Z (ms_regs ms) = SA + 48)
  by (unfold s0Z; rewrite P8, E8; unfold w64; apply unsigned_lit_small; lia).
assert (Hra1 : 4096 <= raZ (ms_regs ms))
  by (unfold raZ; rewrite P1; rewrite unsigned_lit_small by lia; lia).
(* what run 1 kept: it stored nothing *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. apply (aview_kept_out E _ (w_H Wc) memc (ms_mem ms) HFr a Ha).
  clear - Usp U9 U8 Hno. gt_outw Usp U9 U8. }
assert (PRES1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) (ms_mem ms) a).
{ intros a Hpa. lazymatch goal with
  | K1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ =>
    exact (apresent_grows _ _ _ a K1 Hpa) end. }
(* ---- free (s->held) at 0x8264c (gestures_end_b.v's FREE, :1031) ---- *)
rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (gt_free_x (G_SL B RG) Wc (ms_regs ms) (ms_mem ms) GSE_STK (spZ regs) (gse_FP SA e cap out)
    ly S Hp W mem md [] lyc Sc Hpc _ k (re_hp e) (re_kh e)
    ((TB, ATABLE) :: aout_blks (gse_cap rr) outi ++ rest) (- 80) _ [] kr HJ).
  - eapply perm_trans; [exact HPERMc | apply Permutation_middle].
  - rewrite P10, E32. reflexivity.
  - rewrite Usp1. lia.
  - reflexivity.
  - lia.
  - rewrite WS. unfold ASTACK. lia.
  - rewrite P3, E3, H3c. exact Hgp.
  - rewrite P4, E4, H4c. exact Htp.
  - exact P1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - apply (achain_chain_pre lyc (aview SEGS (w_H Wc) (ms_mem ms)) (spZ (ms_regs ms)) (SA + 48) [] (ms_regs ms));
    [apply achain_low; lia | lia | exact Hs01 | exact Hra1].
  - (* the free's caller context: the chain is [], the trace the singleton [gestures_end + 0xfc] (ra 0x82650) *)
    cbn [spine map]. replace (raZ (ms_regs ms)) with (BASE + AF_fr_gestures_end + 0xfc); [exact HCTX_gse_tail|].
    unfold raZ. rewrite P1, unsigned_lit_small by lia. first [lia | unfold AF_fr_gestures_end in *; lia].
  - exact HRM1.
  - exact HCNTc.
  - intros Hnz i Hi.
    destruct (inFP_ablocks_fp (gse_blks e ++ aout_blks cap out) (re_hp e) (re_kh e) i
      ltac:(apply in_or_app; left; unfold gse_blks; rewrite (proj2 (Z.eqb_neq _ _) Hnz); left; reflexivity) Hi)
      as (r0 & Hr0 & Hr0a).
    exists r0. split; [unfold gse_FP; right; exact Hr0 | exact Hr0a].
  - exact HMOKc. }
cbv beta.
intros W2 c2 Hwle2 (ly2 & S2 & Hq2 & regs2 & mem2 & md2 & -> & HJ2 & HPRE2 & HPm2 & KFREE & HMfree & HRM2 & HERRK &
  HAPK2).
(* ---- the state after free: s's block is still live, and it is not the block that was freed ---- *)
assert (HAR2 : ARx ly2 S2 Hq2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
assert (HTB2 : In (TB, ATABLE) (ablocks B ly2 S2))
  by (eapply Permutation_in; [apply Permutation_sym; exact HPm2 | left; reflexivity]).
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hq2 W2 mem2 md2 TB ATABLE HAR2 HTB2) as (_ & _ & _ & _ & HTpres2 & _).
change (req_size ATABLE) with 896 in HTpres2.
assert (WRB2 : forall a, TB <= a < TB + 896 -> writable_at SEGS (mrestrict (w_H W2) mem2) a)
  by (intros a Ha; apply (apresent_writable SEGS); exact (proj1 (HTpres2 a Ha))).
assert (PWbase : pairwise zdisjoint (map (fun b : Z * Z => (fst b, req_size (snd b)))
  ((TB, ATABLE) :: gse_hpblk (re_hp e) (re_kh e) ++ aout_blks (gse_cap rr) outi ++ rest))).
{ destruct (alx_sep _ _ _ LAWS lyc Sc Hpc Wc memc mdc HARc) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
  exact (gt_pw_perm _ _ (Permutation_map _ HPERMc) Hpw). }
assert (DTB : forall q m, In (q, m) (aout_blks (gse_cap rr) outi ++ rest) ->
  TB + 896 <= q \/ q + req_size m <= TB).
{ intros q m Hq. pose proof PWbase as PW.
  assert (HFA : Forall (zdisjoint (TB, req_size ATABLE))
    (map (fun b : Z * Z => (fst b, req_size (snd b))) (aout_blks (gse_cap rr) outi ++ rest))).
  { destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (Hnz & Eq)];
    rewrite Eq in PW; cbn [map] in PW.
    - exact (proj1 PW).
    - destruct PW as [Hf _]. inversion Hf as [|u v Hd Hf2]; subst. exact Hf2. }
  rewrite Forall_forall in HFA.
  pose proof (HFA (q, req_size m) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (q, m) Hq)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. lia. }
assert (DHP : re_hp e <> 0 -> TB + 896 <= re_hp e \/ re_hp e + req_size (re_kh e) <= TB).
{ intros Hnz. pose proof PWbase as PW.
  destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (_ & Eq)];
  [exfalso; exact (Hnz Hz)|]. rewrite Eq in PW; cbn [map] in PW.
  destruct PW as [Hf _]. inversion Hf as [|u v Hd Hf2]; subst.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. lia. }
assert (DHPOUT : re_hp e <> 0 -> forall q m, In (q, m) (aout_blks (gse_cap rr) outi ++ rest) ->
  re_hp e + req_size (re_kh e) <= q \/ q + req_size m <= re_hp e).
{ intros Hnz q m Hq. pose proof PWbase as PW.
  destruct (gt_hpblk_cases (re_hp e) (re_kh e) (aout_blks (gse_cap rr) outi ++ rest)) as [(Hz & Eq) | (_ & Eq)];
  [exfalso; exact (Hnz Hz)|]. rewrite Eq in PW; cbn [map] in PW.
  destruct PW as [_ [Hf _]]. rewrite Forall_forall in Hf.
  pose proof (Hf (q, req_size m) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ (q, m) Hq)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the two cells s+40 .. s+52 are none of the bytes the controller's model reads *)
assert (NWIMG : forall a, in_img SEGS a -> ~ (SA + 40 <= a < SA + 52)).
{ intros a Ha Hr. pose proof (pa_img_range a Ha). unfold off_img in HTimg. lia. }
assert (OUTB : gse_cap rr <> 0 -> In (outi, gse_cap rr) (aout_blks (gse_cap rr) outi ++ rest))
  by (intros Hc; apply in_or_app; left; unfold aout_blks; rewrite (proj2 (Z.eqb_neq _ _) Hc); left; reflexivity).
assert (FPLO : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 -> 0 <= a < 2 ^ 64).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + pose proof (pa_img_range a (HERRIMG a ltac:(lia))). lia.
    + pose proof (pa_img_range a (proj1 (HOUTG r0 a Hc Ha ltac:(lia)))). lia.
    + pose proof (pa_img_range a (proj1 (HOUTG r0 a Hc Ha ltac:(lia)))). lia.
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HARc Hinb) as (_ & Hb4 & Hbc & _).
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs]. lia. }
assert (NWFP : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 ->
  ~ (SA + 40 <= a < SA + 52)).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + apply NWIMG, HERRIMG. lia.
    + apply NWIMG. exact (proj1 (HOUTG r0 a Hc Ha ltac:(lia))).
    + apply NWIMG. exact (proj1 (HOUTG r0 a Hc Ha ltac:(lia))).
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs].
    pose proof (DTB outi (gse_cap rr) (OUTB ltac:(lia))). lia. }
(* their views and their writability across the free *)
assert (KFP2 : forall r0 a, In r0 (aout_fp B RG (gse_cap rr) outi) -> fst r0 <= a < snd r0 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a /\ ~ in_rom SEGS a).
{ intros r0 a Hr0 Ha. destruct (gt_aout_fp_cases _ _ r0 Hr0) as [Hc | (Hc & ->)].
  - destruct (Z_le_gt_dec (as_errno B) a) as [EA1 | EA1];
    [destruct (Z_lt_ge_dec a (as_errno B + 4)) as [EA2 | EA2]|].
    + split.
      * replace a with (as_errno B + (a - as_errno B)) by lia. apply HERRK. lia.
      * intros Hrom. exact (proj1 (proj2 (proj2 (HROMO a Hrom))) ltac:(lia)).
    + destruct (HOUTG r0 a Hc Ha ltac:(lia)) as (Hi & Hnr & Hno).
      split; [exact (proj1 (proj2 (proj2 KFREE)) a Hi Hno ltac:(lia)) | exact Hnr].
    + destruct (HOUTG r0 a Hc Ha ltac:(lia)) as (Hi & Hnr & Hno).
      split; [exact (proj1 (proj2 (proj2 KFREE)) a Hi Hno ltac:(lia)) | exact Hnr].
  - cbn [fst snd] in Ha.
    destruct (gt_aout_blk _ _ _ _ _ _ _ _ _ _ HOUTc) as [(Hc0 & _) | (Hcp & _ & Hinb)]; [lia|].
    pose proof (req_size_pos (gse_cap rr) ltac:(lia)) as [_ Hrs].
    split.
    + replace a with (outi + (a - outi)) by lia.
      apply (proj1 (proj2 KFREE) outi (gse_cap rr) (a - outi) Hinb ltac:(lia)).
      intros (Hnz & Hr). pose proof (DHPOUT Hnz outi (gse_cap rr) (OUTB ltac:(lia))). lia.
    + intros Hrom.
      assert (Hi : in_img SEGS a)
        by (destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
      destruct (alx_client_img _ _ _ LAWS lyc Sc Hpc Wc memc mdc a HARc
        ltac:(left; exists outi, (gse_cap rr); split; [exact Hinb | lia])) as (_ & Hni). exact (Hni Hi). }
assert (HOUT2 : aout_at B RG ly2 S2 W2 mem2 (gse_c rr) (gse_O rr) mx (gse_no rr) (gse_cap rr) outi).
{ apply (aout_at_kept B RG lyc Sc Wc memc ly2 S2 W2 mem2 _ _ _ _ _ _ HOUTc).
  - intros r0 Hr0 a Ha. apply gt_abyte_kept.
    + exact (FPLO r0 a Hr0 Ha).
    + rewrite (proj1 (KFP2 r0 a Hr0 Ha)).
      apply KEEP1; [exact (FPLO r0 a Hr0 Ha) | exact (NWFP r0 a Hr0 Ha)].
    + exact (gt_out_seen lyc Sc Wc memc _ _ _ _ _ _ r0 a HOUTc Hr0 Ha).
    + exact (proj2 (KFP2 r0 a Hr0 Ha)).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (gse_cap rr) 0); [destruct Hb|].
    destruct Hb as [<- | []]. eapply Permutation_in; [apply Permutation_sym; exact HPm2|].
    right. apply in_or_app. left. unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) n). left. reflexivity. }
(* ---- back at 0x82650 (gestures_end_b.v's :1071): the two checked stores and the epilogue ---- *)
assert (AWRT2 : forall a, SA + 40 <= a < SA + 52 ->
  awr_byte GSE_STK (spZ regs) (gse_FP SA e cap out) (ablocks B ly S) (ablocks B ly2 S2) ly2 [] a).
{ intros a Ha. right. left. split.
  - exists (SA + 40, SA + 52). split; [unfold gse_FP; left; reflexivity | cbn [fst snd]; lia].
  - exists TB, ATABLE. split; [exact HTB2 | change (req_size ATABLE) with 896; lia]. }
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H W2) mem2) HPRE2 [0;1;2]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply (proj1 KFREE); unfold ASTACK; lia.
    + intros a Ha _. exfalso. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9.
    + intros a Ha. apply (mbyte_of_aview SEGS). replace a with (TB + (a - TB)) by lia.
      apply (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)).
      intros (Hnz & Hr). pose proof (DHP Hnz). lia.
    + intros a Ha _. apply WRB2. lia.
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U8.
    + intros a Ha. apply (mbyte_of_aview SEGS). replace a with (TB + (a - TB)) by lia.
      apply (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)).
      intros (Hnz & Hr). pose proof (DHP Hnz). lia.
    + intros a Ha _. apply WRB2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 42 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 42)%nat -> ew Ea n = ew E n)
  by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs - 80) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (U9a : bv_unsigned (ew Ea 9) = SA + 40) by (rewrite OLDa by (cbv; lia); exact U9).
assert (U8a : bv_unsigned (ew Ea 8) = SA + 48) by (rewrite OLDa by (cbv; lia); exact U8).
assert (E19a : ew Ea 19 = w64 SB) by (rewrite OLDa by (cbv; lia); exact E19).
assert (E41a : ew Ea 41 = getr regs 1) by (rewrite OLDa by (cbv; lia); exact E41).
assert (SHOKa : sh_ok SEGS BxT gt_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, gt_SH. constructor; [|constructor; [|constructor]].
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxT 9 TB 896 (SA + 40) 0 8).
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hq2 W2 mem2 md2 TB ATABLE TB 896 HAR2 HTB2 ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    + unfold U, BxT. cbn [sv_denot]. rewrite E19a, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U9a.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
  - apply (shent_ok_of_range SEGS (w_H W2) mem2 Ea BxT 8 TB 896 (SA + 48) 0 8).
    + exact (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hq2 W2 mem2 md2 TB ATABLE TB 896 HAR2 HTB2 ltac:(lia)
        ltac:(change (req_size ATABLE) with 896; lia)).
    + unfold U, BxT. cbn [sv_denot]. rewrite E19a, Z.add_0_r, Z_to_bv_bv_unsigned. unfold w64.
      rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U8a.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
(* ---- run 2: 0x82650 -> ret ---- *)
paj_run_tok_x RUN HS HJ2 SHOKa gt_Bspan.
{ apply awr_ok_x_of0. intros a Hwr. apply AWRT2. revert Hwr.
  intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?Uspa, ?U9a, ?U8a in Hr; lia | ]); destruct Hin. }
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2.
(* the two cells s->held = 0 and s->nheld = 0, and what run 2 kept *)
pose proof (st_ok_pi_region_nth _ _ _ 1%nat _ HS eq_refl) as HRG9.
pose proof (st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl) as HRG8.
cbn [ms_mem restrict] in HRG9, HRG8.
assert (M40 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 40) 8 0).
{ pose proof (field_of_region Ea (mrestrict (w_H W2) (ms_mem ms0)) 9%nat (SA + 40) _ 0 8 0 8 0 8%N (SLit 0) 0
    HRG9 U9a (or_introl eq_refl) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (M48 : val_mem SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 48) 4 0).
{ pose proof (field_of_region Ea (mrestrict (w_H W2) (ms_mem ms0)) 8%nat (SA + 48) _ 0 4 0 4 0 4%N (SLit 0) 0
    HRG8 U8a (or_introl eq_refl) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hno. apply (aview_kept_out Ea _ (w_H W2) mem2 (ms_mem ms0) HFr0 a Ha).
  clear - Uspa U9a U8a Hno.
  intros (r0 & Hin & Hr0); cbn [ss_mem add_cond In] in Hin;
  repeat (destruct Hin as [<- | Hin];
  [ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr0;
    rewrite ?Uspa, ?U9a, ?U8a in Hr0; lia | ]); destruct Hin. }
assert (PRES2 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms0) a).
{ intros a Hpa. lazymatch goal with
  | K2 : mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms0)) |- _ =>
    exact (apresent_grows _ _ _ a K2 Hpa) end. }
(* the controller's model after the two stores *)
assert (HOUT3 : aout_at B RG ly2 S2 W2 (ms_mem ms0) (gse_c rr) (gse_O rr) mx (gse_no rr) (gse_cap rr) outi).
{ apply (aout_at_kept B RG ly2 S2 W2 mem2 ly2 S2 W2 (ms_mem ms0) _ _ _ _ _ _ HOUT2).
  - intros r0 Hr0 a Ha. apply gt_abyte_kept.
    + exact (FPLO r0 a Hr0 Ha).
    + apply KEEP2; [exact (FPLO r0 a Hr0 Ha) | exact (NWFP r0 a Hr0 Ha)].
    + exact (gt_out_seen ly2 S2 W2 mem2 _ _ _ _ _ _ r0 a HOUT2 Hr0 Ha).
    + exact (proj2 (KFP2 r0 a Hr0 Ha)).
  - intros b Hb. unfold aout_blks in Hb. destruct (Z.eqb_spec (gse_cap rr) 0); [destruct Hb|].
    destruct Hb as [<- | []]. eapply Permutation_in; [apply Permutation_sym; exact HPm2|].
    right. apply in_or_app. left. unfold aout_blks. rewrite (proj2 (Z.eqb_neq _ _) n). left. reflexivity. }
(* s's other bytes, kept through run 1, the free and run 2 *)
assert (KEEPTB : forall a, TB <= a < TB + 896 -> ~ (SA + 40 <= a < SA + 52) ->
  aview SEGS (w_H W2) (ms_mem ms0) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hno. rewrite (KEEP2 a ltac:(lia) Hno).
  replace a with (TB + (a - TB)) by lia.
  rewrite (proj1 (proj2 KFREE) TB ATABLE (a - TB) HTBc ltac:(change (req_size ATABLE) with 896; lia)
    ltac:(intros (Hnz & Hr); pose proof (DHP Hnz); lia)).
  replace (TB + (a - TB)) with a by lia. apply KEEP1; [lia | exact Hno]. }
assert (GPRE2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) SA (bzs (gt_epre e))).
{ apply (gt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem ms0) SA _ GPRE).
  intros b Hb. unfold bzs in Hb. rewrite length_map, (gt_epre_len e Hp1) in Hb. apply KEEPTB; lia. }
assert (GPAD2 : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) (SA + 52) (bzs (re_pad2 e))).
{ apply (gt_garr8_kept (w_H Wc) (w_H W2) memc (ms_mem ms0) (SA + 52) _ GPAD).
  intros b Hb. unfold bzs in Hb. rewrite length_map, Hp2 in Hb. apply KEEPTB; lia. }
assert (GEND : garr8 SEGS (mrestrict (w_H W2) (ms_mem ms0)) SA (bzs (entry_bytes (entry_cleared e)))).
{ rewrite gt_entry_split_cleared. unfold bzs. rewrite !map_app.
  apply garr8_app. split; [exact GPRE2|].
  rewrite length_map, (gt_epre_len e Hp1). change (SA + Z.of_nat 40) with (SA + 40).
  apply garr8_app. split.
  - rewrite gt_le8_bytes by lia. exact (gt_le_garr8 _ (SA + 40) 8 0 M40 ltac:(cbn; lia)).
  - rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8.
    replace (SA + 40 + Z.of_nat 8) with (SA + 48) by lia.
    apply garr8_app. split.
    + rewrite gt_le4_bytes by lia. exact (gt_le_garr8 _ (SA + 48) 4 0 M48 ltac:(cbn; lia)).
    + rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4.
      replace (SA + 48 + Z.of_nat 4) with (SA + 52) by lia. exact GPAD2. }
pose proof HJ2 as HAR3. apply ajournal_gx_AR_x in HAR3.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hq2 W2 (ms_mem ms0) _ TB ATABLE HAR3 HTB2) as (_ & _ & _ & _ & HTpres3 & _).
change (req_size ATABLE) with 896 in HTpres3.
assert (AWR3 : awr W2 (ms_mem ms0) SA AENT).
{ intros i Hi. apply (apresent_writable SEGS).
  exact (proj1 (HTpres3 (SA + i) ltac:(unfold AENT in Hi; lia))). }
(* the callee-saved registers, back from the frame *)
prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
prreg HS (27%bv : bv 5) T27.
assert (PRESV : aregs_preserved regs (ms_regs ms0)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T2, Uspa. replace (spZ regs - 80 + 80) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned.
  - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T3, (OLDa 3%nat ltac:(cbv; lia)), E3. exact H3c.
  - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T4, (OLDa 4%nat ltac:(cbv; lia)), E4. exact H4c.
  - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T8, (OLDa 40%nat ltac:(cbv; lia)). exact E40.
  - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T9, (OLDa 39%nat ltac:(cbv; lia)). exact E39.
  - replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T18, (OLDa 38%nat ltac:(cbv; lia)). exact E38.
  - replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T19, (OLDa 37%nat ltac:(cbv; lia)). exact E37.
  - replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T20, (OLDa 36%nat ltac:(cbv; lia)). exact E36.
  - replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T21, (OLDa 35%nat ltac:(cbv; lia)). exact E35.
  - replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T22, (OLDa 34%nat ltac:(cbv; lia)). exact E34.
  - replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T23, (OLDa 33%nat ltac:(cbv; lia)). exact E33.
  - rewrite <- (H2427c 24 ltac:(lia)). replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T24, (OLDa 24%nat ltac:(cbv; lia)). exact E24.
  - rewrite <- (H2427c 25 ltac:(lia)). replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T25, (OLDa 25%nat ltac:(cbv; lia)). exact E25.
  - rewrite <- (H2427c 26 ltac:(lia)). replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T26, (OLDa 26%nat ltac:(cbv; lia)). exact E26.
  - rewrite <- (H2427c 27 ltac:(lia)). replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite T27, (OLDa 27%nat ltac:(cbv; lia)). exact E27. }
(* ---- the return ---- *)
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gse_post_x.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists ly2, S2, Hq2, r, m, d, (k + 1), outi end.
split; [cbn [ms_regs]; rewrite T1, E41a, Hra; reflexivity|].
split; [cbn [ms_mem]; unfold gse_FP in HJ2; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ2|].
split; [exact PRESV|].
split.
{ eapply gt_apres_trans; [exact HPRESc|].
  eapply gt_apres_trans; [apply (gt_apres_grows Wc memc (ms_mem ms)); lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) (ms_mem ms)) |- _ => exact K1 end|].
  eapply gt_apres_trans; [exact HAPK2|].
  intros a _ _ _ Hpa. exact (PRES2 a Hpa). }
split; [rewrite gse_cost_spent; exact (mo_le_trans MT MTL _ _ _ _ _ HMLE HMfree)|].
split; [exact HRM2|].
split; [exact HPm2|].
split; [exact HOUT3|].
split; [exact GEND | exact AWR3].
Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3, CONVERSION.md (sha256 1015972e02a9; internal record) 3.): pb_gse_tail's statement is the AR walk's,
   byte-identical, now a corollary of pb_gse_tail_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].
   Its Section takes LX0 (the laws at ARi0) in place of LAWS: the instance builds it once,
   W_journal_x.AR_laws_x_ARi0 (YCbqG.AR_laws_x_of_AR ..).  The cut bridge is W_gse_cut.gse_tail_at_x_AR0.  The free
   rules stay AR rules here; their caller-context forms at CTX := [[gestures_end + 0xbc]; [gestures_end + 0xfc]] (the
   two free sites of gestures_end) come from W_journal.afree_cf_rule_c_weak / afree_null_cf_rule_c_weak and go to ARi0
   through W_journal_x.afree_cf_rule_c_x_of_AR0 / afree_null_cf_rule_c_x_of_AR0.  HP0 at ARi0 is ARi0_hp0; IMGC /
   BLKN are W_kit_x.AR_imgc / AR_blkn. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis MTL : ameter_laws MT.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AFREEN : afree_null_cf_rule SEGS B MT.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HOUTG : forall r a, In r (aout_fp B RG 0 0) -> fst r <= a < snd r -> ~ (as_errno B <= a < as_errno B + 4) ->
  in_img SEGS a /\ ~ in_rom SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
Theorem pb_gse_tail : gse_tail_at B MT MMAX RG (BASE + A_gse_tail).
Proof.
apply gse_tail_at_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fb000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
pose (CTXL := [[BASE + AF_fr_gestures_end + 0xbc]; [BASE + AF_fr_gestures_end + 0xfc]]).
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_cf_rule_c_weak SEGS B MT CTXL AFREE)) as AFREE_X.
pose proof (afree_null_cf_rule_c_x_of_AR0 SEGS B MT CTXL (afree_null_cf_rule_c_weak SEGS B MT CTXL AFREEN)) as AFREEN_X.
assert (HCTX_gse_tail : In [BASE + AF_fr_gestures_end + 0xfc] CTXL) by (unfold CTXL; cbn [In]; right; left; reflexivity).
eapply (pb_gse_tail_x B [] (ARi0 SEGS B) MT RP_AR MMAX RG) with (CTX_AFREE := CTXL); eassumption.
Qed.
End cAR.
End b.
End a.
