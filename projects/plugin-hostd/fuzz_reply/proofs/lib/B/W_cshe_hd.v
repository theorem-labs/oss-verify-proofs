(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the HEAD of the image-B (fuzz_reply.asan-ubsan) walk of check_shape_ends, a NEW
   walk over lib/B/W_listing.v (B's body is not A's: VERDICT.md (sha256 810ca1df9ca9; internal record)), after lib/A/W_check_shape_ends.v
   (a working branch d6e8218b728: cshe_entry, cshe_head, cshe_l1_state / cshe_l1_run / cshe_l1_loop, cshe_to_tst,
   cshe_gone_l2 / cshe_gone_l3, cshe_n0 and their helpers, ported to B's registers, frame and traps), in the form of
   lib/B/W_check_bounded.v (a B loop with traps: a fresh symbolic state at the loop head, by induction on the
   records left) and lib/B/W_check_shape_event.v (an internal call with the frame kept). *)
(* Proves no function (kind: segment lemma of check_shape_ends's image-B walk, one of three pieces; the composition is
   lib/B/W_check_shape_ends.v).  check_shape_ends at 0x85770 (B), from its entry to the three cut points of
   lib/B/W_cshe_epi.v's interface:
     entry 0x85770: the prologue (addi sp,sp,-112; ra, s0..s10 saved), the UBSan traps on the source pointer
       (0x857a4 `beqz a0` NONNULL, 0x857b0 `andi a1,a0,7; bnez` ALIGN8: the runner decides both from HA's atom fact),
       the shadow base (GOT slot A_OBJ 0 -> cell A_OBJ 30), the ASan checks of held.n (HA + 88, 0x857d4, slow path
       0x85a20) and of held.v (HA + 80, 0x857f0), decided from azs (HA + 64) 32;
     n <= 0 (0x857e0 blez): s6 = 0 (0x85888), on to the g_gone test 0x8588c;
     loop 1 at 0x85814 (hd_l1_run one turn, hd_l1_loop the induction): per record the four UBSan traps
       0x85814 PTR_BLTU (trap_ptr_bltu: v + 16 i >= v), 0x85820 NULL_XOR (trap_null_xor_folded: s10 = (v <> 0) = 1),
       0x85824 NONNULL and 0x8582c ALIGN8 (the runner, from the atom facts of v and v + 16 i), the ASan checks of the
       record's two words, has_prefix(text, len, PF) at 0x85860 through HP (hp_spec), on a match
       `addiw a0,s6,1` with its ADDW1 trap at 0x8586c (s6 < 2^26), and the back-edge `bnez s8` at 0x85880;
     the g_gone test 0x8588c (hd_tst, then hd_fin): g_gone <> 0 -> the DECW trap 0x8589c (n < 2^26) and `bltz a0` 0x858a0:
       n = 0 -> the epilogue 0x8592c (cshe_out_B), n >= 1 -> loop 2's head 0x858ac (cshe_l2_in); g_gone = 0 -> the
       DECW trap 0x85968 (want < 2^26) and loop 3's head 0x8597c (cshe_l3_in).
   Loop 1's count is CheckRep.want_of P (the held records): has_prefix's 1 / 0 is CheckRep.prefixb on each record
   (hd_prefixb_iff, A's cshe_prefixb_iff).  The runner decides 0x85824, 0x8582c and the ADDW1 trap from the seat's
   atom facts; 0x85814 (trap_ptr_bltu), 0x85820 (trap_null_xor_folded) and the two DECW traps (trap_br_ge with
   hd_sg_off: the runner leaves `addiw a0,x,-1` as x - 1 on the 64-bit word) are refuted by lib/B/W_traps.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN0d YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_traps W_shadow_pin W_cshe_epi.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require CheckRep RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
(* ARx conversion (route (b); A's lib/A/W_check_shape_ends.v Section c on a working branch 4f281bf9308): the
   generic allocator relation ARx with its laws, the placement PST, the room record RP; HP0 (every ghost list is []),
   IMGC (the image's cover) and BLKN (a block's size is >= 0) as W_check_no_loss.v's Section c takes them *)
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable G : list (Z * Z).
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis ML : ameter_laws MT.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis TL : PALib B.
Hypothesis HP : hp_spec_x B PST ARx (BASE + AF_fr_has_prefix).
(* g_s's bytes are no errno, GOT slot or shadow cell (W_check_shape_ends.v's HGRR): the held list's head is apart from
   the two cells the shadow check reads (hd_g_apart) *)
Hypothesis HGRR : gx_rt B cshe_ro_B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let BR := paj_branch (PI := PI).
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* ---- the walk at the empty ghost list (HP0: every ARx state's ghost list is []): AR0 / AJ0 / AJi0 / AFP0 are cgif's
   AR / journal / inner journal / afn_pre at Hp = [], and each kit lemma the AR walk cites is its _x twin at [] ---- *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AJi0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_x SEGS B PST ARx STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation ajournal_gx_AR0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0 G0 XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0 G0 G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_x SEGS B PST ARx G0 G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0 Hs G0 STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_x SEGS B PST ARx LAWS Hs G0 STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0 G0 XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_x SEGS B PST ARx G0 XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0 pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_x B PST ARx LAWS pc Hpc G0 XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc k x y n o
     raw).
Local Notation range_addressable_of_block0 ly S W mem md :=
  (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation shadow_hull_vis_of_block0 ly S W mem md :=
  (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation sep_blocks0 ly S W mem md := (sep_blocks_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation sep_block_frame0 ly S W mem md := (sep_block_frame_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation blk_img0 ly S W mem md := (blk_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frm_img0 ly S W mem md := (frm_img_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation frames_bounds0 ly S W mem md := (frames_bounds_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation amem_range_of_block0 ly S W mem md := (amem_range_of_block_x SEGS B ARx LAWS ly S [] W mem md).
Local Notation rom_pinned_view0 ly S W mem md := (rom_pinned_view_x SEGS B ARx LAWS ly S [] W mem md).
(* cgif's al_blocks at AR0: ARx_blocks_law's six conjuncts and BLKN's size *)
Lemma al0_blocks : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p mod 16 = 0 /\ 4096 <= p /\ p + req_size n <= alloc_ceiling /\ in_app p (req_size n) /\
  (forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)) /\ 0 <= n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (alx_blocks _ _ _ LAWS ly S [] W mem md p n HAR Hin) as (H1 & H2 & H3 & H4 & H5 & H6).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (BLKN ly S [] W mem md p n HAR Hin))))))).
Qed.
(* W_kit_x.blk_off_imgP_x's proof, at this file's off_img (lib/B/YCbq.v: IMG_TOP_B = 0x5fc000) *)
Lemma cshe_blk_off_img : forall ly S (W : world SEGS) mem md p n,
  AR0 ly S W mem md -> In (p, n) (ablocks B ly S) -> off_img p (req_size n).
Proof.
  intros ly S W mem md p n HAR Hin. unfold off_img.
  destruct (IMGC ly S [] W mem md HAR) as [C1 C2].
  pose proof (req_size_pos n (BLKN ly S [] W mem md p n HAR Hin)) as [Q _].
  destruct (Z.le_gt_cases (p + req_size n) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 p) as [|H2]; [right; lia|]. exfalso.
  assert (Hc : ~ in_zr (Z.max p 0x10000) (ly_img ly)).
  { refine (proj1 (alx_client_img _ _ _ LAWS ly S [] W mem md (Z.max p 0x10000) HAR _)).
    left. exists p, n. split; [exact Hin | lia]. }
  apply Hc. unfold in_zr. lia.
Qed.

(* ------------------------------------------------------------------ helpers (A's, ported) *)
(* Shadow facts survive a change confined to a window above alloc_ceiling: the shadow of any byte the
   program can address lies below alloc_ceiling (W_contract.v shadow_below_stack / shadow_hull_below_stack). *)
Lemma hd_ra_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y) ->
range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a len ->
range_addressable (aview SEGS (w_H W') m') SHADOW_OFF a len.
Proof.
intros W W' m m' a len lo hi Hlo Hmr Ha0 Hk Hra x Hx. destruct (Hra x Hx) as (sv & Hsv & Hok).
exists sv. split; [|exact Hok].
destruct (shadow_below_stack lo hi x Hlo (amem_range_in a len x Hmr Ha0 ltac:(lia) ltac:(lia))) as [S1 S2].
rewrite <- Hsv. unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x). apply Hk; assumption.
Qed.
Lemma hd_shv_kept : forall (W W' : world SEGS) (m m' : word -> option byte) a len lo hi,
alloc_ceiling <= lo -> amem_range a len -> 0 <= a -> 0 < len ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') m' y = aview SEGS (w_H W) m y) ->
shadow_hull_vis (aview SEGS (w_H W) m) a len -> shadow_hull_vis (aview SEGS (w_H W') m') a len.
Proof.
intros W W' m m' a len lo hi Hlo Hmr Ha0 Hl Hk Hv sa Hsa.
destruct (shadow_hull_below_stack lo hi a len sa Hlo (amem_range_in a len a Hmr Ha0 ltac:(lia) ltac:(lia))
  (amem_range_in a len (a + len - 1) Hmr Ha0 ltac:(lia) ltac:(lia)) Hsa) as [S1 S2].
rewrite Hk by assumption. exact (Hv sa Hsa).
Qed.

(* The bytes of a NUL-terminated string as the walk reads them: the form cshe_spec states P in, and the form
   alist_at's garr8 gives of a record's text (hd_bytes_of_garr8). *)
Definition hd_bytes (W : world SEGS) (mem : word -> option byte) (a : Z) (l : list byte) : Prop :=
forall t, 0 <= t < Z.of_nat (length l) ->
aview SEGS (w_H W) mem (a + t) = Some (bv_unsigned (nth (Z.to_nat t) l (Z_to_bv 8 0))).

Lemma hd_u8 : forall v, 0 <= v < 256 -> bv_unsigned (Z_to_bv 8 v) = v.
Proof.
intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hv.
Qed.
Lemma hd_nth_bzs : forall (l : list byte) (j : nat),
nth j (HarnessRep.bzs l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof.
intros l j. unfold HarnessRep.bzs, HarnessRep.bz.
rewrite <- (map_nth bv_unsigned l (Z_to_bv 8 0) j). reflexivity.
Qed.
Lemma hd_bzs_inj : forall l1 l2 : list byte, HarnessRep.bzs l1 = HarnessRep.bzs l2 -> l1 = l2.
Proof.
induction l1 as [|a l1 IH]; intros [|b l2] H; unfold HarnessRep.bzs in H; cbn [map] in H;
  try discriminate H; [reflexivity|].
injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma hd_bytes_of_garr8 : forall (W : world SEGS) mem a (l : list byte),
garr8 SEGS (mrestrict (w_H W) mem) a (HarnessRep.bzs l) -> hd_bytes W mem a l.
Proof.
intros W mem a l Hg t Ht.
assert (HL : length (HarnessRep.bzs l) = length l) by (unfold HarnessRep.bzs; apply length_map).
assert (Hj : (Z.to_nat t < length (HarnessRep.bzs l))%nat) by lia.
unfold aview. replace (a + t) with (a + Z.of_nat (Z.to_nat t)) by lia.
rewrite (garr8_mbyte SEGS _ a _ (Z.to_nat t) Hg Hj). cbn [option_map].
destruct (Hg (Z.to_nat t) Hj) as (_ & Hr). rewrite (hd_u8 _ Hr). f_equal. apply hd_nth_bzs.
Qed.
Lemma hd_bytes_kept : forall (W W' : world SEGS) mem mem' a (l : list byte) lo hi,
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall t, 0 <= t < Z.of_nat (length l) -> 0 <= a + t < 2 ^ 64 /\ ~ (lo <= a + t < hi)) ->
hd_bytes W mem a l -> hd_bytes W' mem' a l.
Proof.
intros W W' mem mem' a l lo hi Hk Hin Hb t Ht. destruct (Hin t Ht) as [H1 H2].
rewrite (Hk (a + t) H1 H2). exact (Hb t Ht).
Qed.

(* want_of, one record at a time: the plain model's step (lib/Prog/check_shape_ends.v cse_want_step). *)
Lemma hd_firstn_S : forall (l : list (Z * list byte)) (j : nat) (d : Z * list byte), (j < length l)%nat ->
firstn (S j) l = firstn j l ++ [nth j l d].
Proof.
intros l. induction l as [|x l IH]; intros [|j] d Hj; cbn [length] in Hj; try lia.
- reflexivity.
- cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
(* want_of's filter is the stdpp one, as in the plain proof's ce_fcons (lib/Prog/check_shape_ends.v:580). *)
Lemma hd_want_app : forall P (a b : list (Z * list byte)),
CheckRep.want_of P (a ++ b) = (CheckRep.want_of P a + CheckRep.want_of P b)%nat.
Proof.
intros P a b. unfold CheckRep.want_of. rewrite list_basics.list.filter_app, length_app. reflexivity.
Qed.
Lemma hd_want_one : forall P (r : Z * list byte),
CheckRep.want_of P [r] = (if CheckRep.prefixb P (snd r) then 1 else 0)%nat.
Proof.
intros P r. unfold CheckRep.want_of. rewrite list_basics.list.filter_singleton.
destruct (CheckRep.prefixb P (snd r)) eqn:E;
  match goal with |- context [decide ?X] => destruct (decide X) as [D|D] end; cbn in D |- *;
  first [reflexivity | contradiction | (exfalso; apply D; exact I) | (rewrite E in D; cbn in D; contradiction)
        | (exfalso; apply D; rewrite E; exact I)].
Unshelve. all: exact [].
Qed.
Lemma hd_want_le : forall P (l : list (Z * list byte)), (CheckRep.want_of P l <= length l)%nat.
Proof.
intros P l. assert (E0 : CheckRep.want_of P [] = 0%nat) by reflexivity.
induction l as [|x l IH]; [rewrite E0; cbn [length]; lia|].
change (x :: l) with ([x] ++ l). rewrite hd_want_app, hd_want_one, length_app. cbn [length].
destruct (CheckRep.prefixb P (snd x)); lia.
Qed.
Lemma hd_want_step : forall P (recs : list (Z * list byte)) (j : nat), (j < length recs)%nat ->
CheckRep.want_of P (firstn (S j) recs) =
(CheckRep.want_of P (firstn j recs) +
 (if CheckRep.prefixb P (snd (nth j recs (0%Z, []))) then 1 else 0))%nat.
Proof.
intros P recs j Hj. rewrite (hd_firstn_S recs j (0, []) Hj), hd_want_app, hd_want_one. reflexivity.
Qed.
Lemma hd_leqb : forall a b : list Z, RelayModel.list_eqb a b = true <-> a = b.
Proof.
intros a b. unfold RelayModel.list_eqb. destruct (list_eq_dec Z.eq_dec a b) as [E|E].
- split; [intros _; exact E | intros _; reflexivity].
- split; [intros Hc; discriminate Hc | intros Hc; exfalso; exact (E Hc)].
Qed.
(* has_prefix's answer on a record's text is exactly the plain model's prefixb. *)
Lemma hd_prefixb_iff : forall (W : world SEGS) mem (q PF : Z) (x P : list byte),
hd_bytes W mem q (x ++ [Z_to_bv 8 0]) -> hd_bytes W mem PF (P ++ [Z_to_bv 8 0]) ->
((Z.of_nat (length P) <= Z.of_nat (length x) /\ hp_prefix_of W mem q PF (Z.of_nat (length P))) <->
 CheckRep.prefixb P x = true).
Proof.
intros W mem q PF x P Hx HPb.
assert (LX : forall t, 0 <= t < Z.of_nat (length x) ->
  aview SEGS (w_H W) mem (q + t) = Some (bv_unsigned (nth (Z.to_nat t) x (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (Hx t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
assert (LP : forall t, 0 <= t < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + t) = Some (bv_unsigned (nth (Z.to_nat t) P (Z_to_bv 8 0)))).
{ intros t Ht. rewrite (HPb t ltac:(rewrite length_app; cbn [length]; lia)).
  do 2 f_equal. apply app_nth1. lia. }
unfold CheckRep.prefixb. split.
- intros (Hle & Hpre). apply andb_true_iff. split; [apply Nat.leb_le; lia|].
  apply hd_leqb. f_equal.
  assert (LF : length (firstn (length P) x) = length P) by (rewrite length_firstn; lia).
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; lia]. }
  apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [exact LF|].
  intros t Ht. rewrite LF in Ht. rewrite <- (NX t Ht).
  specialize (Hpre (Z.of_nat t) ltac:(lia)).
  rewrite (LX (Z.of_nat t) ltac:(lia)), (LP (Z.of_nat t) ltac:(lia)) in Hpre.
  injection Hpre as Hpre. rewrite !Nat2Z.id in Hpre. apply bv_eq. exact Hpre.
- intros Hb. apply andb_true_iff in Hb as [Hb1 Hb2]. apply Nat.leb_le in Hb1. apply hd_leqb in Hb2.
  apply hd_bzs_inj in Hb2.
  assert (NX : forall t, (t < length P)%nat -> nth t x (Z_to_bv 8 0) = nth t (firstn (length P) x) (Z_to_bv 8 0)).
  { intros t Ht. transitivity (nth t (firstn (length P) x ++ skipn (length P) x) (Z_to_bv 8 0));
    [rewrite firstn_skipn; reflexivity | apply app_nth1; rewrite length_firstn; lia]. }
  split; [lia|]. intros t Ht.
  rewrite (LX t ltac:(lia)), (LP t ltac:(lia)). do 2 f_equal.
  rewrite (NX (Z.to_nat t) ltac:(lia)), Hb2. reflexivity.
Qed.

(* ---- loop 1's invariant at the head 0x85450, for the records v[i..n) still to count ---- *)
(* The prefix at PF, as has_prefix's premises take it.  Every clause is an aview fact, a shadow fact of a
   range below alloc_ceiling, or pure, so the post's frame clause carries it to the next turn
   (hd_l1_pfx_kept). *)
Definition hd_l1_pfx (W : world SEGS) (mem : word -> option byte) (sp0 PF : Z) (P : list byte) : Prop :=
let lp := Z.of_nat (length P) in
hd_bytes W mem PF (P ++ [Z_to_bv 8 0]) /\
(forall a, PF <= a < PF + lp + 8 -> aview SEGS (w_H W) mem a <> None) /\
(forall a, PF <= a < PF + lp + 8 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) /\
amem_range PF (lp + 1) /\ amem_range PF 8 /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (lp + 1) /\
shadow_hull_vis (aview SEGS (w_H W) mem) PF (lp + 1) /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF lp /\
(0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) PF lp) /\
rom_view SEGS W mem.
(* One record of the held vector: its 16-byte slot at V + 16 j, and its text. *)
Definition hd_l1_rec (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
(sp0 V : Z) (P : list byte) (r : Z * list byte) (j : Z) : Prop :=
let lp := Z.of_nat (length P) in
let lx := Z.of_nat (length (snd r)) in
let EA := V + AREC * j in
val_mem SEGS (mrestrict (w_H W) mem) EA 8 (fst r) /\
val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 lx /\
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF EA 16 /\ amem_range EA 16 /\
(forall a, EA <= a < EA + 16 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) /\
(exists VB VL, In (VB, VL) (ablocks B ly S) /\ VB <= EA /\ EA + 16 <= VB + req_size VL) /\
0 <= fst r < 140737479966720 /\ lx < 2 ^ 26 /\
hd_bytes W mem (fst r) (snd r ++ [Z_to_bv 8 0]) /\
(forall a, fst r <= a < fst r + lx + 1 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) /\
(lp <= lx -> amem_range (fst r) lp /\
   range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (fst r) lp /\
   (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) (fst r) lp)).
Definition hd_l1_vec (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
(sp0 V : Z) (P : list byte) (recs : list (Z * list byte)) (i : Z) : Prop :=
forall j, i <= j < Z.of_nat (length recs) -> hd_l1_rec ly S W mem sp0 V P (nth (Z.to_nat j) recs (0, [])) j.

Lemma hd_l1_pfx_kept : forall (W W' : world SEGS) mem mem' sp0 PF P,
alloc_ceiling <= sp0 - 112 - HP_STK ->
0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= y < sp0 - 112) ->
   aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
hd_l1_pfx W mem sp0 PF P -> hd_l1_pfx W' mem' sp0 PF P.
Proof.
intros W W' mem mem' sp0 PF P HCEIL HPF0 HPFk Hk
  (Hby & Hvis & Hoff & Hmr1 & Hmr8 & Hra1 & Hshv1 & Hra0 & Hshv0 & Hrom).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIN : forall a, PF <= a < PF + Z.of_nat (length P) + 8 ->
  0 <= a < 2 ^ 64 /\ ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) by (intros a Ha; split; [lia | apply Hoff; lia]).
split; [apply (hd_bytes_kept W W' mem mem' PF _ (sp0 - 112 - HP_STK) (sp0 - 112) Hk);
        [intros t Ht; apply HIN; rewrite length_app in Ht; cbn [length] in Ht; lia | exact Hby]|].
split; [intros a Ha; destruct (HIN a Ha) as [X1 X2]; rewrite (Hk a X1 X2); exact (Hvis a Ha)|].
split; [exact Hoff|]. split; [exact Hmr1|]. split; [exact Hmr8|].
split; [exact (hd_ra_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) Hk Hra1)|].
split; [exact (hd_shv_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) ltac:(lia) Hk Hshv1)|].
assert (Hmr0 : amem_range PF (Z.of_nat (length P)))
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
split; [exact (hd_ra_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hk Hra0)|].
split; [intros Hp; exact (hd_shv_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hp Hk (Hshv0 Hp))|].
intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; assumption).
destruct (Hsegs a Hi) as [L1 L2]. unfold kLowMemEnd in L2.
rewrite (Hk a ltac:(lia) ltac:(lia)). exact (Hrom a Ha).
Qed.
Lemma hd_l1_rec_kept : forall ly S (W W' : world SEGS) mem mem' sp0 V P r j,
alloc_ceiling <= sp0 - 112 - HP_STK -> 4096 <= V + AREC * j ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= y < sp0 - 112) ->
   aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
hd_l1_rec ly S W mem sp0 V P r j -> hd_l1_rec ly S W' mem' sp0 V P r j.
Proof.
intros ly S W W' mem mem' sp0 V P r j HCEIL HEA Hk
  (Ms & Mn & Hra16 & Hmr16 & Hoffe & Hblk & Hr0 & Hlx & Hby & Hofft & Hlp).
unfold hd_l1_rec. cbv zeta.
assert (KEA : forall t, 0 <= t < 16 -> aview SEGS (w_H W') mem' (V + AREC * j + t) = aview SEGS (w_H W) mem (V + AREC * j + t)).
{ intros t Ht. apply Hk; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr16; lia
                         | apply Hoffe; lia]. }
split; [exact (val_mem_kept SEGS _ _ mem mem' _ 8 _ ltac:(intros t Ht; apply KEA; lia) Ms)|].
split; [refine (val_mem_kept SEGS _ _ mem mem' _ 8 _ _ Mn);
        intros t Ht; replace (V + AREC * j + 8 + t) with (V + AREC * j + (8 + t)) by lia; apply KEA; lia|].
split; [exact (hd_ra_kept W W' mem mem' _ 16 _ _ HCEIL Hmr16 ltac:(lia) Hk Hra16)|].
split; [exact Hmr16|]. split; [exact Hoffe|]. split; [exact Hblk|].
split; [exact Hr0|]. split; [exact Hlx|].
split; [apply (hd_bytes_kept W W' mem mem' (fst r) _ (sp0 - 112 - HP_STK) (sp0 - 112) Hk);
        [intros t Ht; rewrite length_app in Ht; cbn [length] in Ht;
         split; [lia | apply Hofft; lia] | exact Hby]|].
split; [exact Hofft|].
intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
split; [exact Hmrp|].
split; [exact (hd_ra_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hk Hrap)|].
intros Hp. exact (hd_shv_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hp Hk (Hshvp Hp)).
Qed.

(* Reading a region's chunk back out of a symbolic state: what the frame's saved slots and the cells the walk
   stored are worth at the state the run ended in (YN0d's st_ok_chunk / chunk_bytes_cval). *)
Lemma hd_st_chunk : forall E ss (Hh : word -> bool) ms i r c,
st_ok_pi SEGS VAL E ss (restrict Hh ms) -> nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
YP09.chunk_ok SEGS E (mrestrict Hh (ms_mem ms)) (base_val E (YP09.r_base r)) c.
Proof.
intros E ss Hh ms i r c HS Hi Hc. unfold st_ok_pi in HS.
exact (YN0d.st_ok_chunk SEGS E _ (restrict Hh ms) i r c HS Hi Hc).
Qed.
Lemma hd_chunk_val : forall E (m : word -> option byte) base off (w : N) (e : sv) (v : Z),
bv_unsigned (sv_denot E e) = v ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) -> val_mem SEGS m (base + off) (N.to_nat w) v.
Proof.
intros E m base off w e v Hv Hc k Hk.
exact (YN0d.chunk_bytes_cval SEGS E m base off w e v Hc ltac:(rewrite Hv; reflexivity) k Hk).
Qed.
(* An atom's word, as the chunk of a saved slot carries it. *)
Lemma hd_soff_u : forall E n, bv_unsigned (sv_denot E (SOff n 0)) = bv_unsigned (ew E n).
Proof.
intros E n. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
rewrite U_SOff, Z.add_0_r. apply zcanon_id.
pose proof (bv_unsigned_in_range 64 (ew E n)). change (bv_modulus 64) with (2 ^ 64) in *.
unfold M64. lia.
Qed.

(* W_check_no_loss.v's cnl_blk / cnl_vec_len / cnl_rec_len / cnl_src_low / cnl_src_kept, copied: that file's
   lemmas live in its own Section, over its own hypotheses.  What they say: every byte the source's predicate
   reads is an application byte below the allocator's ceiling, so a run that only writes its own frame keeps
   the source - once its bytes keep their ASan view and nothing it had goes absent. *)
Lemma hd_blk : forall ly S W mem md p n, AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ 1 <= req_size n /\ p + req_size n <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\ off_img p (req_size n) /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al0_blocks ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpr & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2]. pose proof asan_consts as (C1 & _).
pose proof (cshe_blk_off_img _ _ _ _ _ p n HAR Hin) as Hoff.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hoff|]. split; [exact Hia|]. exact Hpr.
Qed.
Lemma hd_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma hd_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, hd_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma hd_src_low : forall ly1 S1 W1 mem1 md1 HA1 h1,
AR0 ly1 S1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 4096 <= HA1 -> HA1 + 96 <= kLowMemEnd ->
forall rr, In rr (asrc_fp HA1 h1) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi.
pose proof asan_consts as (C1 & _ & _ & _ & C5).
assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
  4096 <= LA -> LA + 16 <= kLowMemEnd ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros l LA Hl Hlo Hhi rr Hin a Ha.
  assert (HL : alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false) by exact Hl.
  destruct HL as [HA2 | HA2];
  (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
   unfold alist_fp in Hin; cbn [In] in Hin;
   destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; lia|];
   apply in_app_or in Hin as [Hin | Hin];
   [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|];
     destruct Hin as [<- | []];
     destruct Hv as [(Hc0 & _) | (Hc & Hvin & Hj & Hg)]; [apply Z.eqb_neq in Ec; lia|];
     destruct (hd_blk ly1 S1 W1 mem1 md1 _ _ HAR Hvin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     unfold gfp in Ha; cbn [fst snd] in Ha; rewrite (hd_vec_len l Hj) in Ha; lia
   | apply in_map_iff in Hin as (r & <- & Hr);
     rewrite Forall_forall in Hrec; destruct (Hrec r Hr) as (Hin2 & _);
     destruct (hd_blk ly1 S1 W1 mem1 md1 _ _ HAR Hin2) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     cbn [fst snd gfp] in Ha; unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha; lia ]). }
intros rr Hin a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & Hpg & _ & Hexp & Hheld & _).
unfold asrc_fp in Hin. cbn [In] in Hin.
destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; unfold ASRC in Ha; lia|].
destruct Hin as [<- | Hin].
{ destruct (hd_blk ly1 S1 W1 mem1 md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd gfp] in Ha. unfold bzs in Ha. rewrite length_map in Ha. unfold APARTIAL in *. lia. }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) ltac:(lia) ltac:(lia) rr Hin a Ha). }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) ltac:(lia) ltac:(lia) rr Hin a Ha). }
exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) ltac:(lia) ltac:(lia) rr Hin a Ha).
Qed.
Lemma hd_alist_blks_in : forall ly0 S0 W0 m0 LA l lines, alist_at B ly0 S0 W0 m0 LA l lines ->
forall b, In b (alist_blks l) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 LA l lines HL0 b Hb. unfold alist_blks in Hb. apply in_app_or in Hb as [Hb|Hb].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hb|]. destruct Hb as [<- | []].
  destruct HL0 as (_ & _ & _ & _ & _ & [(Hc & _) | (_ & Hin & _)] & _); [apply Z.eqb_neq in Ec; lia | exact Hin].
- apply in_map_iff in Hb as (x & <- & Hx). destruct HL0 as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
  rewrite Forall_forall in HF. exact (proj1 (HF x Hx)).
Qed.
Lemma hd_src_blks : forall ly0 S0 W0 m0 HA0 h0, asrc_at B ly0 S0 W0 m0 HA0 h0 ->
forall b, In b (asrc_blks h0) -> In b (ablocks B ly0 S0).
Proof.
intros ly0 S0 W0 m0 HA0 h0 HS0 b Hb.
pose proof HS0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPd & _ & _ & _ & _ & _ & _ & _ & HPin & _ & _ & _ & HEx & HHl & _).
unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact HPin|].
apply in_app_or in Hb as [Hb | Hb]; [exact (hd_alist_blks_in _ _ _ _ _ _ _ HPd b Hb)|].
apply in_app_or in Hb as [Hb | Hb];
[exact (hd_alist_blks_in _ _ _ _ _ _ _ HEx b Hb) | exact (hd_alist_blks_in _ _ _ _ _ _ _ HHl b Hb)].
Qed.
(* an address stays writable when its presence is kept and the new world hides no more (W_list_drop.v
   writable_kept_w, copied) *)
Lemma hd_writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m') a.
Proof.
intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- rewrite (Hh _ EH') in Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* a value carried over a step that keeps its bytes (W_check_no_loss.v cnl_vm_keep, copied) *)
Lemma hd_vm_keep : forall (W W' : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W') m') a n v.
Proof.
intros W W' m m' a n v Hk Hv i Hi.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat i) (Hk (a + Z.of_nat i) ltac:(lia))).
exact (Hv i Hi).
Qed.
(* The source over one run of this walk: the view of every byte below the ceiling kept, nothing gone absent. *)
Lemma hd_src_kept : forall ly S (W W' : world SEGS) mem mem' md HA h lo,
AR0 ly S W mem md -> asrc_at B ly S W mem HA h -> 4096 <= HA -> HA + 96 <= kLowMemEnd ->
alloc_ceiling <= lo -> wle W W' ->
(forall a, 4096 <= a < lo -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) ->
asrc_at B ly S W' mem' HA h.
Proof.
intros ly S W W' mem mem' md HA h lo HAR HS HAlo HAhi Hlo Hwle Hq Hp.
apply (asrc_at_kept B ly S W mem ly S W' mem' HA h HS).
- intros rr Hin a Ha.
  destruct (hd_src_low ly S W mem md HA h HAR HS HAlo HAhi rr Hin a Ha) as [Hl1 Hl2].
  split; [apply Hq; lia | apply (hd_writable_kept_w W W' mem mem' a); [apply Hp | exact Hwle]].
- intros b Hb. exact (hd_src_blks ly S W mem HA h HS b Hb).
Qed.
Lemma hd_set_held_id : forall h, CheckRep.set_held h (hs_held h) = h.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?]. reflexivity. Qed.

(* The vector's records as 8-byte cells (W1's garr8_val_mem8 / alist_rec_fields, through
   W_check_no_loss.v's copies cnl_garr8_val_mem8 / cnl_rec_fields). *)
Lemma hd_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma hd_rec_fields : forall ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64) /\
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) 8
  (Z.of_nat (length (snd (nth j (HarnessRep.hl_recs l) (0, [])))) mod 2 ^ 64).
Proof.
intros ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, hd_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply hd_garr8_val_mem8 in H1. apply hd_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|].
replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.
(* a shorter range has a shorter shadow hull *)
Lemma hd_shv_sub : forall (rd : reader) x n n', 0 < n' -> n' <= n ->
shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn' Hle Hv s Hs. apply Hv.
pose proof (shadow_mono (x + n' - 1) (x + n - 1) ltac:(lia)) as M.
assert (HD : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; [lia | exact M]).
lia.
Qed.
(* the twelve saved slots over a run that keeps the bytes below the entry sp *)
Lemma hd_saved_kept : forall (W W' : world SEGS) m m' sp0 rs,
(forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
cshe_saved_B W m sp0 rs -> cshe_saved_B W' m' sp0 rs.
Proof.
intros W W' m m' sp0 rs Hk (M1 & M8 & M9 & M18 & M19 & M20 & M21 & M22 & M23 & M24 & M25 & M26).
unfold cshe_saved_B. repeat split;
  (apply (hd_vm_keep W W' m m' _ 8 _);
   [intros x Hx; cbn [Z.of_nat] in Hx; apply Hk; lia | assumption]).
Qed.

(* hd_l1_pfx_kept / hd_l1_rec_kept over any window above the allocator's ceiling: the entry's run writes
   the frame [sp - 112, sp), not has_prefix's scratch, so the i = 0 invariant is carried over that window. *)
Lemma hd_l1_pfx_kept2 : forall (W W' : world SEGS) mem mem' sp0 lo hi PF P,
alloc_ceiling <= lo -> 0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall y, PF <= y < PF + Z.of_nat (length P) + 8 -> ~ (lo <= y < hi)) ->
hd_l1_pfx W mem sp0 PF P -> hd_l1_pfx W' mem' sp0 PF P.
Proof.
intros W W' mem mem' sp0 lo hi PF P HCEIL HPF0 HPFk Hk Hoff2
  (Hby & Hvis & Hoff & Hmr1 & Hmr8 & Hra1 & Hshv1 & Hra0 & Hshv0 & Hrom).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HIN : forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> 0 <= a < 2 ^ 64 /\ ~ (lo <= a < hi))
  by (intros a Ha; split; [lia | apply Hoff2; lia]).
split; [apply (hd_bytes_kept W W' mem mem' PF _ lo hi Hk);
        [intros t Ht; apply HIN; rewrite length_app in Ht; cbn [length] in Ht; lia | exact Hby]|].
split; [intros a Ha; destruct (HIN a Ha) as [X1 X2]; rewrite (Hk a X1 X2); exact (Hvis a Ha)|].
split; [exact Hoff|]. split; [exact Hmr1|]. split; [exact Hmr8|].
split; [exact (hd_ra_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) Hk Hra1)|].
split; [exact (hd_shv_kept W W' mem mem' PF (Z.of_nat (length P) + 1) _ _ HCEIL Hmr1 ltac:(lia) ltac:(lia) Hk Hshv1)|].
assert (Hmr0 : amem_range PF (Z.of_nat (length P)))
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
split; [exact (hd_ra_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hk Hra0)|].
split; [intros Hp; exact (hd_shv_kept W W' mem mem' PF (Z.of_nat (length P)) _ _ HCEIL Hmr0 ltac:(lia) Hp Hk (Hshv0 Hp))|].
intros a Ha. assert (Hi : in_img SEGS a) by (destruct Ha as (sg & Hsg & _ & Hr); exists sg; split; assumption).
destruct (Hsegs a Hi) as [L1 L2]. unfold kLowMemEnd in L2.
rewrite (Hk a ltac:(lia) ltac:(lia)). exact (Hrom a Ha).
Qed.
Lemma hd_l1_rec_kept2 : forall ly S (W W' : world SEGS) mem mem' sp0 lo hi V P r j,
alloc_ceiling <= lo -> 4096 <= V + AREC * j ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (lo <= y < hi) -> aview SEGS (w_H W') mem' y = aview SEGS (w_H W) mem y) ->
(forall y, V + AREC * j <= y < V + AREC * j + 16 -> ~ (lo <= y < hi)) ->
(forall y, fst r <= y < fst r + Z.of_nat (length (snd r)) + 1 -> ~ (lo <= y < hi)) ->
hd_l1_rec ly S W mem sp0 V P r j -> hd_l1_rec ly S W' mem' sp0 V P r j.
Proof.
intros ly S W W' mem mem' sp0 lo hi V P r j HCEIL HEA Hk Hoff16 Hofft2
  (Ms & Mn & Hra16 & Hmr16 & Hoffe & Hblk & Hr0 & Hlx & Hby & Hofft & Hlp).
unfold hd_l1_rec. cbv zeta.
assert (KEA : forall t, 0 <= t < 16 ->
  aview SEGS (w_H W') mem' (V + AREC * j + t) = aview SEGS (w_H W) mem (V + AREC * j + t)).
{ intros t Ht. apply Hk; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hmr16; lia
                         | apply Hoff16; lia]. }
split; [exact (val_mem_kept SEGS _ _ mem mem' _ 8 _ ltac:(intros t Ht; apply KEA; lia) Ms)|].
split; [refine (val_mem_kept SEGS _ _ mem mem' _ 8 _ _ Mn);
        intros t Ht; replace (V + AREC * j + 8 + t) with (V + AREC * j + (8 + t)) by lia; apply KEA; lia|].
split; [exact (hd_ra_kept W W' mem mem' _ 16 _ _ HCEIL Hmr16 ltac:(lia) Hk Hra16)|].
split; [exact Hmr16|]. split; [exact Hoffe|]. split; [exact Hblk|].
split; [exact Hr0|]. split; [exact Hlx|].
split; [apply (hd_bytes_kept W W' mem mem' (fst r) _ lo hi Hk);
        [intros t Ht; rewrite length_app in Ht; cbn [length] in Ht;
         split; [lia | apply Hofft2; lia] | exact Hby]|].
split; [exact Hofft|].
intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
split; [exact Hmrp|].
split; [exact (hd_ra_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hk Hrap)|].
intros Hp. exact (hd_shv_kept W W' mem mem' (fst r) (Z.of_nat (length P)) _ _ HCEIL Hmrp ltac:(lia) Hp Hk (Hshvp Hp)).
Qed.

(* ------------------------------------------------------------------ the entry 0x85770 *)
(* The held list's cells lie in g_s, whose bytes are no GOT slot and no shadow cell (HGRR : gx_rt B cshe_ro_B, g_s
   being cshe_ro_B's fourth range): so they are apart from both cells the shadow check reads.  (The AR walk read this
   off AR's asyms_ok cover; the generic relation carries no symbol table.) *)
Lemma hd_g_apart : forall lo hi, (forall a, lo <= a < hi -> inG cshe_ro_B a) ->
(hi <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= lo \/ hi <= lo) /\
(hi <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= lo \/ hi <= lo).
Proof.
intros lo hi Hro.
split.
- destruct (Z.le_gt_cases hi (VAL (A_OBJ 0))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 0) + 8) lo) as [Hc2|Hc2]; [right; left; exact Hc2|].
  destruct (Z.le_gt_cases hi lo) as [Hc3|Hc3]; [right; right; exact Hc3|].
  exfalso. destruct (HGRR (Z.max lo (VAL (A_OBJ 0))) (Hro (Z.max lo (VAL (A_OBJ 0))) ltac:(lia))) as (_ & Hx & _). apply Hx. lia.
- destruct (Z.le_gt_cases hi (VAL (A_OBJ 30))) as [Hc|Hc]; [left; exact Hc|].
  destruct (Z.le_gt_cases (VAL (A_OBJ 30) + 8) lo) as [Hc2|Hc2]; [right; left; exact Hc2|].
  destruct (Z.le_gt_cases hi lo) as [Hc3|Hc3]; [right; right; exact Hc3|].
  exfalso. destruct (HGRR (Z.max lo (VAL (A_OBJ 30))) (Hro (Z.max lo (VAL (A_OBJ 30))) ltac:(lia))) as (_ & _ & Hx). apply Hx. lia.
Qed.

(* atoms above 31: 32 unused (0), 33 the shadow base, 34 held.v, 35 held.n *)
Definition hd_Bx : sv := SOff 33 0.
Definition hd_hdR : YP09.region := YP09.mkRegion (Some 10%nat) 80 96 0 0
[YP09.mkChunk 80 (CVal 8 (SOff 34 0)); YP09.mkChunk 88 (CVal 4 (SOff 35 0))].
Definition hd_regions : smem := [ stack_region CSHE_FRAME_B; got_regionP; bcell_regionP 33; hd_hdR ].
Definition hd_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 4096 140737479966720 3);
(33%nat, mkAF SB SB 0); (34%nat, mkAF 0 140737479966720 4); (35%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_hd : sstate := mkSS A_csheB sr_atoms hd_regions None hd_facts.
Definition hd_SH : list shent := [ mkSHE 10 64 96 ].
Definition hd_extra (V N : Z) : list word := map (Z_to_bv 64) [0; SB; V; N].

Lemma hd_entry : forall W ly S regs mem md ch HA V N,
AFP0 CSHE_STK_B ly S W regs mem md ch ->
getr regs 10 = w64 HA -> HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd -> azs B (HA + 64) 32 ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
(forall a, HA + 80 <= a < HA + 96 -> inG cshe_ro_B a) ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 80) 8 V -> 0 <= V < 140737479966720 -> V mod 16 = 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 88) 4 N -> 0 <= N < 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (hd_extra V N))) ss_hd
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_csheBP) mem (seg_rom SEGS)))
/\ sh_ok SEGS hd_Bx hd_SH (Eimg (Ereg regs (hd_extra V N))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HA V N HPRE H10 Hal8 Hlo Hhi Hzs HGin HGro MV RV AV MN RN.
unfold ASRC in Hhi.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S [] W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
destruct (hd_g_apart (HA + 80) (HA + 96) HGro) as [Hd0 Hd30].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (hd_extra V N))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E0 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E30 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
split.
- unfold ss_hd, A_csheBP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold hd_regions, stack_region, got_regionP, bcell_regionP, hd_hdR.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [unfold CSHE_FRAME_B; lia|]. split; [unfold CSHE_FRAME_B; lia|].
split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold CSHE_FRAME_B in *. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite E30, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 hd_Bx SB);
[cbn [sv_denot hd_Bx]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat HA E10) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat (constructor; [|]); [| |constructor].
-- apply (chunk_ok_val SEGS E _ HA 80 8 _ V);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MV].
-- apply (chunk_ok_val SEGS E _ HA 88 4 _ N);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact MN].
+ apply pairwise_disjoint_of_extents.
unfold hd_regions, stack_region, got_regionP, bcell_regionP, hd_hdR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat HA E10) by lia.
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E0) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E30) by (pose proof (pa_val_range (A_OBJ 30)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hlo Hhi Hd0 Hd30 C1 C3 C5 WS Hstk0 HcellR HgcD HgotR. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, CSHE_FRAME_B. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [hd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hlo Hhi Hal8 Hal16 C1 C3 C5 WS Hstk0 RV AV RN. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, hd_SH. constructor; [|constructor].
assert (UBx : U E hd_Bx = SHADOW_OFF).
{ unfold U, hd_Bx. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
assert (Up : U E (SOff 10 0) = HA).
{ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity. }
split; cbn [she_m she_lo she_hi].
+ rewrite UBx, Up. replace (96 - 64) with 32 by lia.
  exact (azs_range_addressable_x B ARx LAWS ly S [] W mem md (HA + 64) 32 HAR Hzs).
+ unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up. unfold SHADOW_OFF in *. intros a Ha. lia.
Qed.

(* ------------------------------------------------------------------ the frame's saved slots, read out of a state *)
(* Where the prologue put each callee-saved register, as an offset of the entry sp (ra, s0 .. s10). *)
Definition hd_slot_off (n : nat) : Z :=
match n with
| 1%nat => -8 | 8%nat => -16 | 9%nat => -24 | 18%nat => -32 | 19%nat => -40 | 20%nat => -48
| 21%nat => -56 | 22%nat => -64 | 23%nat => -72 | 24%nat => -80 | 25%nat => -88
| _ => -96
end.
Definition hd_slot_regs : list nat := [1;8;9;18;19;20;21;22;23;24;25;26]%nat.
Lemma hd_saved_of_state : forall E ss (W : world SEGS) ms r (regs0 : bvmap 5 word) sp0,
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
nth_error (ss_mem ss) 0%nat = Some r ->
base_val E (YP09.r_base r) = sp0 ->
(forall n, In n hd_slot_regs ->
   In (YP09.mkChunk (hd_slot_off n) (CVal 8 (SOff n 0))) (YP09.r_chunks r) /\
   ew E n = getr regs0 (Z_to_bv 5 (Z.of_nat n))) ->
cshe_saved_B W (ms_mem ms) sp0 regs0.
Proof.
intros E ss W ms r regs0 sp0 HS Hi Hb Hall.
assert (SL : forall n, In n hd_slot_regs ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (sp0 + hd_slot_off n) 8
    (bv_unsigned (getr regs0 (Z_to_bv 5 (Z.of_nat n))))).
{ intros n Hn. destruct (Hall n Hn) as [Hin He].
  pose proof (hd_st_chunk E ss (w_H W) ms 0%nat r _ HS Hi Hin) as HC.
  rewrite Hb in HC.
  pose proof (hd_chunk_val E _ sp0 (hd_slot_off n) 8 (SOff n 0) _ (hd_soff_u E n) HC) as HV.
  rewrite He in HV. exact HV. }
unfold cshe_saved_B. repeat split;
  [ replace (sp0 - 8) with (sp0 + hd_slot_off 1) by (cbn; lia)
  | replace (sp0 - 16) with (sp0 + hd_slot_off 8) by (cbn; lia)
  | replace (sp0 - 24) with (sp0 + hd_slot_off 9) by (cbn; lia)
  | replace (sp0 - 32) with (sp0 + hd_slot_off 18) by (cbn; lia)
  | replace (sp0 - 40) with (sp0 + hd_slot_off 19) by (cbn; lia)
  | replace (sp0 - 48) with (sp0 + hd_slot_off 20) by (cbn; lia)
  | replace (sp0 - 56) with (sp0 + hd_slot_off 21) by (cbn; lia)
  | replace (sp0 - 64) with (sp0 + hd_slot_off 22) by (cbn; lia)
  | replace (sp0 - 72) with (sp0 + hd_slot_off 23) by (cbn; lia)
  | replace (sp0 - 80) with (sp0 + hd_slot_off 24) by (cbn; lia)
  | replace (sp0 - 88) with (sp0 + hd_slot_off 25) by (cbn; lia)
  | replace (sp0 - 96) with (sp0 + hd_slot_off 26) by (cbn; lia) ];
  first [ exact (SL 1%nat ltac:(cbv; tauto)) | exact (SL 8%nat ltac:(cbv; tauto))
        | exact (SL 9%nat ltac:(cbv; tauto)) | exact (SL 18%nat ltac:(cbv; tauto))
        | exact (SL 19%nat ltac:(cbv; tauto)) | exact (SL 20%nat ltac:(cbv; tauto))
        | exact (SL 21%nat ltac:(cbv; tauto)) | exact (SL 22%nat ltac:(cbv; tauto))
        | exact (SL 23%nat ltac:(cbv; tauto)) | exact (SL 24%nat ltac:(cbv; tauto))
        | exact (SL 25%nat ltac:(cbv; tauto)) | exact (SL 26%nat ltac:(cbv; tauto)) ].
Qed.
Ltac hd_head_saved HS Usp EEo :=
eapply (hd_saved_of_state _ _ _ _ _ _ _ HS);
[ cbn [ss_mem]; reflexivity
| cbn [YP09.r_base base_val]; exact Usp
| intros nn Hnn; cbv [hd_slot_regs] in Hnn; cbn [In] in Hnn;
  destruct Hnn as [Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[Hq|[]]]]]]]]]]]]];
  rewrite <- Hq;
  (split; [cbn [hd_slot_off YP09.r_chunks In]; repeat first [left; reflexivity | right]
         | apply EEo; reflexivity]) ].

(* ---- the entry 0x85770 to loop 1's head 0x85814, or (held.n = 0) to the g_gone test 0x8588c with s6 = 0 ---- *)
(* The run writes the frame only (the prologue's twelve stores) and reads held.v / held.n; s8 = n & -(n > 0) = n and
   s10 = (v <> 0) = 1 at the loop head (v is a live block when n > 0). *)
Lemma hd_head : forall W ly S regs mem md ch HA V N XO AT FP PF,
AFP0 CSHE_STK_B ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd -> azs B (HA + 64) 32 ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
(forall a, HA + 80 <= a < HA + 96 -> inG cshe_ro_B a) ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 80) 8 V -> 0 <= V < 140737479966720 -> V mod 16 = 0 ->
val_mem SEGS (mrestrict (w_H W) mem) (HA + 88) 4 N -> 0 <= N < 2 ^ 26 -> (0 < N -> 4096 <= V) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 A_csheBP) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' pc',
 c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
 AJ0 G XO [(AT, AT + 8)] CSHE_STK_B (spZ regs) FP ly S W mem md [] ly S W' mem' md' 0 /\
 getr regs' 2 = w64 (spZ regs - 112) /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 27 = getr regs 27 /\
 getr regs' 8 = w64 PF /\ getr regs' 9 = w64 (HA + 80) /\ getr regs' 18 = w64 AT /\ getr regs' 19 = w64 N /\
 getr regs' 21 = w64 SB /\ getr regs' 22 = w64 0 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a) /\
 cshe_saved_B W' mem' (spZ regs) regs /\
 ((0 < N /\ pc' = BASE + A_csheB_l1 /\ getr regs' 20 = w64 V /\ getr regs' 23 = w64 V /\
   getr regs' 24 = w64 N /\ getr regs' 25 = w64 (V + 8) /\ getr regs' 26 = w64 1) \/
  (N = 0 /\ pc' = BASE + A_csheB_tst))).
Proof.
intros W ly S regs mem md ch HA V N XO AT FP PF HPRE HXO0 HXO16 HXtop HXp H10 H11 H12
  Hal8 Hlo Hhi Hzs HGin HGro MV RV AV MN RN HVpos.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (hd_entry W ly S regs mem md ch HA V N HPRE H10 Hal8 Hlo Hhi Hzs HGin HGro MV RV AV MN RN) as [HS SHOK].
unfold ASRC in Hhi.
pose proof (ajournal_gx_init0 G XO [(AT, AT + 8)] CSHE_STK_B FP ly S W regs mem md ch HPRE
  HXO0 HXO16 HXtop HXp) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
remember (Eimg (Ereg regs (hd_extra V N))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E2 : ew E 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10b : ew E 10 = Z_to_bv 64 HA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E11b : ew E 11 = Z_to_bv 64 PF) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
assert (E12b : ew E 12 = Z_to_bv 64 AT) by (rewrite (EEo 12%nat 12%bv eq_refl); exact H12).
assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 V) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 N) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (HAE : env_agree 32 (Ereg regs (hd_extra V N)) E)
  by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold A_csheBP, A_csheB.
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ SHOK BspanE.
{ apply awr_ok_x_cons;
  [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region] in Ha; rewrite Usp in Ha;
    left; split; [left; unfold CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK in *; lia | lia] |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi got_regionP] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi bcell_regionP] in Ha; lia|].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_hdR] in Ha; lia|].
  apply awr_ok_x_nil. }
assert (UN : bv_unsigned (sv_denot E (SOff 35 0)) = N) by exact (U_atom E 35 N E35 ltac:(lia)).
assert (SN : bv_signed (sv_denot E (SOff 35 0)) = N)
  by (rewrite bv_signed_small; [exact UN | rewrite UN; lia]).
assert (U0 : bv_unsigned (sv_denot E (SLit 0)) = 0) by exact (U_lit E 0 ltac:(lia)).
assert (S0 : bv_signed (sv_denot E (SLit 0)) = 0)
  by (rewrite bv_signed_small; [exact U0 | rewrite U0; lia]).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose proof HG0 as GROW1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1.
  lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) mem) _ |- _ =>
    apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
  intros (r & Hin & Hr). unfold ss_hd, hd_regions in Hin. cbn [ss_mem In] in Hin.
  destruct Hin as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP bcell_regionP hd_hdR CSHE_FRAME_B] in Hr;
  try (unfold CSHE_FRAME_B in Hr); rewrite ?Usp, ?E10b in Hr;
  try (rewrite unsigned_lit_small in Hr by lia). all: lia. }
psrr_branch_tok RUNx BR HS SHOK BspanE.
- (* the held list is empty: s6 = 0, on to the g_gone test *)
  assert (HN0 : N = 0).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
    apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.ltb_ge in Hc. rewrite SN, S0 in Hc. lia. }
  paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE A_csheB_tst.
  { apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region] in Ha; rewrite Usp in Ha;
      left; split; [left; unfold CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK in *; lia | lia] |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi got_regionP] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi bcell_regionP] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_hdR] in Ha; lia|].
    apply awr_ok_x_nil. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha H1.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?E10b in Hr;
       try (rewrite unsigned_lit_small in Hr by lia); lia|]). destruct Hin. }
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_csheB_tst) end.
  split; [reflexivity|]. split; [exact HJ|].
  split; [cbn [ms_regs]; rewrite P2, Usp; unfold w64; f_equal; lia|].
  split; [cbn [ms_regs]; rewrite P3; exact (EEo 3%nat 3%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P4; exact (EEo 4%nat 4%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P27; exact (EEo 27%nat 27%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P8; exact E11b|].
  split; [cbn [ms_regs]; rewrite P9, E10b, unsigned_lit_small by lia; reflexivity|].
  split; [cbn [ms_regs]; rewrite P18; exact E12b|].
  split; [cbn [ms_regs]; rewrite P19; exact E35|].
  split; [cbn [ms_regs]; rewrite P21; exact E33|].
  split; [cbn [ms_regs]; rewrite P22; reflexivity|].
  split; [cbn [ms_mem]; intros a Ha H1; rewrite (KEEP2 a Ha H1); exact (KEEP1 a Ha H1)|].
  split.
  { cbn [ms_mem]. intros a Hp.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      exact (apresent_grows _ _ _ _ Hg (apresent_grows _ _ _ _ GROW1 Hp)) end. }
  split; [hd_head_saved HS Usp EEo|].
  right. split; [exact HN0 | reflexivity].
- (* a record to count: on to loop 1's head *)
  assert (HNp : 0 < N).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc.
    apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.ltb_lt in Hc. rewrite SN, S0 in Hc. lia. }
  paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE A_csheB_l1.
  { apply awr_ok_x_cons;
    [ intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region] in Ha; rewrite Usp in Ha;
      left; split; [left; unfold CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK in *; lia | lia] |].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi got_regionP] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi bcell_regionP] in Ha; lia|].
    apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_hdR] in Ha; lia|].
    apply awr_ok_x_nil. }
  prreg HS (20%bv : bv 5) P20. prreg HS (23%bv : bv 5) P23. prreg HS (24%bv : bv 5) P24.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha H1.
    lazymatch goal with Hf : frame_of ?Ev ?rs (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      apply (aview_kept_out Ev rs (w_H W) _ _ Hf a Ha) end.
    intros (r & Hin & Hr). cbn [ss_mem In] in Hin.
    repeat (destruct Hin as [<- | Hin];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?E10b in Hr;
       try (rewrite unsigned_lit_small in Hr by lia); lia|]). destruct Hin. }
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (27%bv : bv 5) P27.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
  prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  assert (HV4 : 4096 <= V) by (apply HVpos; exact HNp).
  (* s8 = n & -(n > 0) = n, s10 = (v <> 0) = 1 *)
  assert (Q24 : alu64 ALU_AND (alu64 ALU_SUB (Z_to_bv 64 0) (alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 N)))
    (Z_to_bv 64 N) = Z_to_bv 64 N).
  { assert (QS : alu64 ALU_SLT (Z_to_bv 64 0) (Z_to_bv 64 N) = Z_to_bv 64 1).
    { rewrite zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
      rewrite Zmod_0_l, (Z.mod_small N) by lia.
      rewrite (swrap64_id 0) by (unfold half64; lia).
      rewrite (swrap64_id N) by (unfold half64; lia).
      destruct (Z.ltb_spec 0 N); [reflexivity | lia]. }
    rewrite QS, !zalu64_sound. f_equal. unfold zalu64, zcanon, M64. cbn [zalu_raw].
    rewrite Zmod_0_l, (Z.mod_small 1) by lia.
    change ((0 - 1) mod 2 ^ 64) with (Z.ones 64).
    assert (HO1 : Z.ones 64 mod 2 ^ 64 = Z.ones 64) by reflexivity. rewrite HO1.
    rewrite (Z.mod_small N) by lia. rewrite Z.land_comm, Z.land_ones by lia.
    rewrite Z.mod_mod by lia. apply Z.mod_small. lia. }
  pmkst HS. apply SRr_ret.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_csheB_l1) end.
  split; [reflexivity|]. split; [exact HJ|].
  split; [cbn [ms_regs]; rewrite P2, Usp; unfold w64; f_equal; lia|].
  split; [cbn [ms_regs]; rewrite P3; exact (EEo 3%nat 3%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P4; exact (EEo 4%nat 4%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P27; exact (EEo 27%nat 27%bv eq_refl)|].
  split; [cbn [ms_regs]; rewrite P8; exact E11b|].
  split; [cbn [ms_regs]; rewrite P9, E10b, unsigned_lit_small by lia; reflexivity|].
  split; [cbn [ms_regs]; rewrite P18; exact E12b|].
  split; [cbn [ms_regs]; rewrite P19; exact E35|].
  split; [cbn [ms_regs]; rewrite P21; exact E33|].
  split; [cbn [ms_regs]; rewrite P22; reflexivity|].
  split; [cbn [ms_mem]; intros a Ha H1; rewrite (KEEP2 a Ha H1); exact (KEEP1 a Ha H1)|].
  split.
  { cbn [ms_mem]. intros a Hp.
    lazymatch goal with Hg : mem_grows (mrestrict (w_H W) (ms_mem ms)) _ |- _ =>
      exact (apresent_grows _ _ _ _ Hg (apresent_grows _ _ _ _ GROW1 Hp)) end. }
  split; [hd_head_saved HS Usp EEo|].
  left. split; [exact HNp|]. split; [reflexivity|].
  split; [cbn [ms_regs]; rewrite P20; exact E34|].
  split; [cbn [ms_regs]; rewrite P23; exact E34|].
  split; [cbn [ms_regs]; rewrite P24, E35; exact Q24|].
  split; [cbn [ms_regs]; rewrite P25, E34, unsigned_lit_small by lia; reflexivity|].
  cbn [ms_regs]. rewrite P26, E34. exact (trap_w_snez V ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ loop 1 (0x85814), one record per turn *)
(* At the head: s4 (x20) = v + 16 i (the record), s9 (x25) = s4 + 8 (its length word), s7 (x23) = v, s8 (x24) = the
   records left, s6 (x22) = the count so far, s10 (x26) = (v <> 0) = 1, s5 (x21) = SB, s0 (x8) = the prefix.  Atom
   facts (W_traps.v's seat recipe): R1 for v and v + 16 i (so 0x85824 `beqz s7` and 0x8582c `andi a0,s4,7; bnez`
   are decided, and `seqz a0,s4` folds to 0), R3 for s10, R4 for the count and the records left. *)
Definition hd_elt : YP09.region := YP09.mkRegion (Some 20%nat) 0 16 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SOff 35 0))].
Definition hd_Bx1 : sv := SOff 21 0.
Definition hd_l1_sr : list sv := sr_set sr_atoms 25%bv (SOff 20 8).
Definition hd_l1_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (20%nat, mkAF 4096 140737479966720 4); (21%nat, mkAF SB SB 0);
(22%nat, mkAF 0 (2 ^ 26) 0); (23%nat, mkAF 4096 140737479966720 4); (24%nat, mkAF 1 (2 ^ 26) 0);
(26%nat, mkAF 1 1 0); (34%nat, mkAF 0 140737479966720 0); (35%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_hd_l1 : sstate := mkSS A_csheB_l1 hd_l1_sr [ hd_elt ] None hd_l1_facts.
Definition hd_l1_SH : list shent := [ mkSHE 20 0 16 ].
Definition hd_l1_extra (s n : Z) : list word := map (Z_to_bv 64) [0; SB; s; n].

Lemma hd_l1_state : forall (W : world SEGS) regs mem EA s n SP WANT CNT V,
getr regs 2 = w64 SP -> getr regs 22 = w64 WANT -> getr regs 24 = w64 CNT ->
getr regs 20 = w64 EA -> getr regs 25 = w64 (EA + 8) -> getr regs 21 = w64 SB -> getr regs 23 = w64 V ->
getr regs 26 = w64 1 ->
2 ^ 46 <= SP <= 2 ^ 47 -> SP mod 16 = 0 -> 0 <= WANT < 2 ^ 26 -> 1 <= CNT < 2 ^ 26 ->
4096 <= EA -> EA + 16 <= 140737479966720 -> EA mod 16 = 0 -> 4096 <= V <= EA -> V mod 16 = 0 ->
0 <= s < 140737479966720 -> 0 <= n < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) EA 8 s -> val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 n ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (hd_l1_extra s n))) ss_hd_l1
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_csheB_l1)) mem (seg_rom SEGS))).
Proof.
intros W regs mem EA s n SP WANT CNT V H2 H22 H24 H20 H25 H21 H23 H26 HSP HSPa HW HC Hlo Hhi Hal HV HV16 Hs Hn Ms Mn.
pose proof pa_B_ok as HBASE.
set (E := Eimg (Ereg regs (hd_l1_extra s n))).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E20 : ew E 20 = Z_to_bv 64 EA) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
rewrite restrict_mkst_fx. unfold ss_hd_l1. apply pa_entry_st_ok_full.
- unfold hd_l1_sr. apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  assert (HU2 : U E (SOff 20 8) = EA + 8) by (apply (U_atom_off E 20 EA 8 E20); lia).
  rewrite H25. unfold w64. rewrite <- HU2. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, hd_elt.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst].
  cbn [base_val]. rewrite E20, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat (apply Forall_cons); try apply Forall_nil.
  + apply (chunk_ok_val SEGS E _ EA 0 8 (SOff 34 0) s);
    [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Ms.
  + apply (chunk_ok_val SEGS E _ EA 8 8 (SOff 35 0) n);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
- apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [hd_l1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite (EEo 2%nat 2%bv eq_refl), (EEo 21%nat 21%bv eq_refl), (EEo 22%nat 22%bv eq_refl),
    (EEo 23%nat 23%bv eq_refl), (EEo 24%nat 24%bv eq_refl), (EEo 26%nat 26%bv eq_refl).
  rewrite H2, H21, H22, H23, H24, H26, E20, E34, E35. unfold w64.
  rewrite !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
Qed.

(* presence across the runs: chain every run's mem_grows (lib/B/W_check_bounded.v cb_pres) *)
Ltac hd_pres :=
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
repeat match goal with
| HG' : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2), Hp : apresent ?H ?m1 a |- _ =>
  lazymatch goal with _ : apresent H m2 a |- _ => fail | _ => idtac end;
  assert (apresent H m2 a) by (eapply apresent_grows; [exact HG' | exact Hp])
end; assumption.

Lemma hd_l1_run : forall (W : world SEGS) ly S regs mem md EA s n WANT CNT V ly0 S0 (W0 : world SEGS) mem0 md0
XO AT FP sp0 kk PF lp,
getr regs 2 = w64 (sp0 - 112) -> getr regs 22 = w64 WANT -> getr regs 24 = w64 CNT ->
getr regs 20 = w64 EA -> getr regs 25 = w64 (EA + 8) -> getr regs 21 = w64 SB -> getr regs 23 = w64 V ->
getr regs 26 = w64 1 ->
2 ^ 46 <= sp0 - 112 <= 2 ^ 47 -> (sp0 - 112) mod 16 = 0 -> 0 <= WANT -> WANT + 1 < 2 ^ 26 -> 1 <= CNT < 2 ^ 26 ->
4096 <= EA -> EA + 16 <= 140737479966720 -> EA mod 16 = 0 -> 4096 <= V <= EA -> V mod 16 = 0 ->
0 <= s < 140737479966720 -> 0 <= n < 2 ^ 26 ->
val_mem SEGS (mrestrict (w_H W) mem) EA 8 s -> val_mem SEGS (mrestrict (w_H W) mem) (EA + 8) 8 n ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF EA 16 -> amem_range EA 16 ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
(* the prefix, as has_prefix needs it at the call *)
getr regs 8 = w64 PF ->
0 <= lp -> lp + 1 < 2 ^ 32 -> 0 < PF -> PF + lp + 1 <= 2 ^ 63 ->
first_byte SEGS W mem PF (lp + 1) 0 lp ->
hp_vis W mem PF (lp + 1) -> amem_range PF (lp + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (lp + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (lp + 1) ->
(forall a, PF + lp < a < PF + lp - (PF + lp) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None) ->
rom_view SEGS W mem ->
(forall a, PF <= a < PF + lp + 8 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) ->
(* the record's text, as has_prefix needs it *)
0 <= s -> s + lp <= 2 ^ 63 ->
(lp <= n -> hp_vis W mem s lp /\ (forall a, s <= a < s + lp -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112)) /\
  amem_range s lp /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF s lp /\
  (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) s lp) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF lp /\
  (0 < lp -> shadow_hull_vis (aview SEGS (w_H W) mem) PF lp)) ->
(* the frame budget and the chain *)
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
s0Z regs < alloc_ceiling -> XO mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= sp0 ->
(* the slot [EA, EA + 16) is inside the held vector's block, so it survives the call *)
forall VB VL, In (VB, VL) (ablocks B ly S) -> VB <= EA -> EA + 16 <= VB + req_size VL ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_csheB_l1)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' b pc',
 c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
 ((1 < CNT /\ pc' = BASE + A_csheB_l1) \/ (CNT = 1 /\ pc' = BASE + A_csheB_tst)) /\
 AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W' mem' md' kk /\
 (b = 0 \/ b = 1) /\
 (b = 1 -> lp <= n /\ hp_prefix_of W mem s PF lp) /\ (b = 0 -> lp <= n -> ~ hp_prefix_of W mem s PF lp) /\
 getr regs' 22 = w64 (WANT + b) /\
 getr regs' 20 = w64 (EA + 16) /\ getr regs' 25 = w64 (EA + 24) /\ getr regs' 24 = w64 (CNT - 1) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 21 = getr regs 21 /\ getr regs' 23 = getr regs 23 /\
 getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a)).
Proof.
intros W ly S regs mem md EA s n WANT CNT V ly0 S0 W0 mem0 md0 XO AT FP sp0 kk PF lp
H2 H22 H24 H20 H25 H21 H23 H26 HSP HSPa HW0 HW1 HC Hlo Hhi Hal HV HV16 Hs Hn Ms Mn HRA HMR HJ
H8 Rlp0 Rlp32 RPF0 RPFk HFB HVIS HMRP HM8 HRAP HHVP HTAIL HROM HOFFP Rs0 Rsl HCMP Hgp Htp Hch HXO16 HCL0
VB VL HVIN HVlo HVhi.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HXO0 : 0 <= XO) by (pose proof HJ as (_ & HX & _); exact HX).
pose proof (hd_l1_state W regs mem EA s n (sp0 - 112) WANT CNT V H2 H22 H24 H20 H25 H21 H23 H26 HSP HSPa
  ltac:(lia) HC Hlo Hhi Hal HV HV16 Hs Hn Ms Mn) as HS.
remember (Eimg (Ereg regs (hd_l1_extra s n))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E20 : ew E 20 = Z_to_bv 64 EA) by (rewrite (EEo 20%nat 20%bv eq_refl); exact H20).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact H2).
assert (E22 : ew E 22 = Z_to_bv 64 WANT) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 V) by (rewrite (EEo 23%nat 23%bv eq_refl); exact H23).
assert (E24 : ew E 24 = Z_to_bv 64 CNT) by (rewrite (EEo 24%nat 24%bv eq_refl); exact H24).
assert (E26 : ew E 26 = Z_to_bv 64 1) by (rewrite (EEo 26%nat 26%bv eq_refl); exact H26).
assert (E8 : ew E 8 = Z_to_bv 64 PF) by (rewrite (EEo 8%nat 8%bv eq_refl); exact H8).
assert (E34 : ew E 34 = Z_to_bv 64 s) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (SHOK : sh_ok SEGS hd_Bx1 hd_l1_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, hd_l1_SH. constructor; [|constructor].
  assert (UBx : U E hd_Bx1 = SHADOW_OFF)
    by (unfold U, hd_Bx1; cbn [sv_denot]; rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
  assert (Up : U E (SOff 20 0) = EA) by (apply (U_atom E 20 EA E20); lia).
  split; cbn [she_m she_lo she_hi].
  - rewrite UBx, Up, Z.add_0_r, Z.sub_0_r. exact HRA.
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. intros a Ha. lia. }
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
(* 0x85814 bltu s4,s7: the UBSan pointer-overflow trap, never taken: s4 = v + 16 i >= v *)
psrr_branch_tok RUNx BR HS SHOK BspanE.
{ rewrite (trap_ptr_bltu E (SOff 23 0) (SOff 20 0) V EA (U_atom E 23 V E23 ltac:(lia)) (U_atom E 20 EA E20 ltac:(lia))
    ltac:(lia)) in Hc. discriminate. }
paj_run_tok_x RUNx HS HJ SHOK BspanE.
{ cbn [ss_mem add_cond ss_hd_l1]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
(* 0x85820 beqz (s10 xor seqz s4): the UBSan null-consistency trap; the runner folded seqz s4 to 0 (s4 >= 4096) *)
psrr_branch_tok RUNx BR HS SHOK BspanE.
{ lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite (trap_null_xor_folded E 26 E26) in Hc; discriminate Hc end. }
paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE AF_fr_has_prefix.
{ cbn [ss_mem add_cond ss_hd_l1]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10.
prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
assert (E3 : ew E 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
assert (E4 : ew E 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdc := mdq) in * end.
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W _ _ kk HJ)
  as (memS & HJi & HgS).
assert (HPREh : AFP0 HP_STK ly S W (ms_regs ms0) (ms_mem ms0) mdc []).
{ eapply (afn_pre_at0 (CSHE_STK_B + XO) (sp0 + XO) FP ly0 S0 W0 memS md0 [] ly S W (ms_mem ms0) mdc kk
    (ms_regs ms0) HP_STK (- 112 - XO) [] HJi).
  - unfold spZ. rewrite Q2, E2. rewrite unsigned_lit_small by lia. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact HXO16]].
  - lia.
  - unfold HP_STK, ESTACK. lia.
  - unfold HP_STK, CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK, ESTACK. lia.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
  - rewrite Q3, E3. exact Hgp.
  - rewrite Q4, E4. exact Htp.
  - apply achain_low. unfold s0Z. rewrite Q8, (EEo 8%nat 8%bv eq_refl). exact Hch. }
(* the run to the call wrote nothing: the only region has no writable byte *)
assert (HAV : aview SEGS (w_H W) (ms_mem ms0) = aview SEGS (w_H W) mem).
{ apply functional_extensionality. intros a.
  rewrite (aview_wrap64 (w_H W) (ms_mem ms0) a), (aview_wrap64 (w_H W) mem a).
  pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Ha.
  repeat match goal with
  | Hf : frame_of ?Ev ?rs (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2) |- aview _ _ ?m2 _ = _ =>
      rewrite (aview_kept_out Ev rs (w_H W) m1 m2 Hf _ Ha);
      [ clear Hf
      | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
        intros (r & Hin & Hr); cbn [ss_mem add_cond ss_hd_l1 In] in Hin;
        destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hd_elt] in Hr; lia ]
  end.
  reflexivity. }
assert (Usp1 : spZ (ms_regs ms0) = sp0 - 112) by (unfold spZ; rewrite Q2, E2; apply unsigned_lit_small; lia).
eapply SRr_bind.
{ apply (HP W ly S [] (ms_regs ms0) (ms_mem ms0) mdc [] s n PF lp HPREh).
  - rewrite Q10, E34. reflexivity.
  - rewrite Q11, E35. reflexivity.
  - rewrite Q12, E8. reflexivity.
  - lia.
  - exact Rlp0.
  - exact Rlp32.
  - exact RPF0.
  - exact RPFk.
  - exact Rs0.
  - exact Rsl.
  - unfold first_byte in *. rewrite HAV. exact HFB.
  - unfold hp_vis in *. rewrite HAV. exact HVIS.
  - unfold hp_off. rewrite Usp1. intros a Ha. apply HOFFP. lia.
  - exact HMRP.
  - exact HM8.
  - rewrite HAV. exact HRAP.
  - rewrite HAV. exact HHVP.
  - rewrite HAV. exact HTAIL.
  - unfold rom_view in *. rewrite HAV. exact HROM.
  - intros Hle. destruct (HCMP Hle) as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
    unfold hp_vis, hp_off in *. rewrite HAV, Usp1.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [exact C5|]. split; [exact C6 | exact C7]. }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJc & HP2 & HPR2 & HFRc & HRES).
assert (HB : exists b, (b = 0 \/ b = 1) /\ getr regs2 10 = w64 b /\
  (b = 1 -> lp <= n /\ hp_prefix_of W (ms_mem ms0) s PF lp) /\
  (b = 0 -> lp <= n -> ~ hp_prefix_of W (ms_mem ms0) s PF lp)).
{ destruct HRES as [(Hle & Hpre & Hr10) | (Hnp & Hr10)].
  - exists 1. split; [right; reflexivity|]. split; [exact Hr10|].
    split; [intros _; split; assumption | intros Hc'; discriminate Hc'].
  - exists 0. split; [left; reflexivity|]. split; [exact Hr10|].
    split; [intros Hc'; discriminate Hc' | intros _; exact Hnp]. }
destruct HB as (b & Hb01 & Hb10 & Hb1 & Hb0).
(* the callee's donor journal, composed into this walk's ajournal_gx *)
assert (HJc' : AJ0 G 0 [] HP_STK (sp0 - 112) [] ly S W (ms_mem ms0) mdc [] ly S W2 mem2 md2 0).
{ apply (ajournal_gx_G_mono_x SEGS B PST ARx [] G); [intros a Ha; exfalso; exact (inG_nil a Ha)|].
  apply ajournal_gx_nil_x. rewrite <- Usp1. exact HJc. }
pose proof (ajournal_gx_sub0 Hsegs G CSHE_STK_B sp0 XO [(AT, AT + 8)] FP ly0 S0 W0 mem0 md0 []
  ly S W (ms_mem ms0) mdc kk HP_STK (sp0 - 112) 0 [] [] [] ly S W2 mem2 md2 0 HJ HJc'
  ltac:(unfold CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, HP_STK, ASTACK, ESTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
(* every byte outside has_prefix's own scratch is the byte it was called with *)
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & KEEPb & _).
(* the vector slot is a live block's bytes, so has_prefix kept it *)
assert (KEEPe : forall a, EA <= a < EA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha. replace a with (VB + (a - VB)) by lia.
  apply (KEEPb VB VL (a - VB) HVIN HVIN); [lia | intros Hc'; exact (inFP_nil _ Hc')]. }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val].
  - intros a Ha. apply (mbyte_of_aview SEGS). rewrite E20, unsigned_lit_small in Ha by lia.
    apply KEEPe. lia.
  - intros a Ha _. exfalso. rewrite E20 in Ha. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* has_prefix wrote nothing outside its own scratch *)
assert (HFRh : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem ms0) a).
{ intros a Ha Hno. apply HFRc; [exact Ha|]. rewrite Usp1. exact Hno. }
assert (HCEIL : alloc_ceiling <= sp0 - 112 - HP_STK).
{ unfold HP_STK, ESTACK, CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK in *. lia. }
(* the environment after the call, and the loop state again *)
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m, (m < 36)%nat -> ew Ea m = ew E m)
  by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
assert (F40 : ew Ea 40 = w64 b)
  by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact Hb10).
clear HEa.
assert (SHOKa : sh_ok SEGS hd_Bx1 hd_l1_SH Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, hd_l1_SH. constructor; [|constructor].
  assert (UBx : U Ea hd_Bx1 = SHADOW_OFF)
    by (unfold U, hd_Bx1; cbn [sv_denot]; rewrite OLDa by (cbv; lia); rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned;
        rewrite unsigned_lit_small by (unfold SB; lia); reflexivity).
  assert (Up : U Ea (SOff 20 0) = EA)
    by (apply (U_atom Ea 20 EA); [rewrite OLDa by (cbv; lia); exact E20 | lia]).
  split; cbn [she_m she_lo she_hi].
  - rewrite UBx, Up, Z.add_0_r, Z.sub_0_r.
    apply (hd_ra_kept W W2 (ms_mem ms0) mem2 EA 16 (sp0 - 112 - HP_STK) (sp0 - 112) HCEIL HMR ltac:(lia));
      [intros y Hy Hno; exact (HFRh y Hy Hno) | rewrite HAV; exact HRA].
  - unfold app_apart. cbn [she_m she_lo she_hi]. rewrite UBx, Up.
    unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. intros a Ha. lia. }
rewrite Q1.
assert (HPRMS : forall a, apresent (w_H W) mem a -> apresent (w_H W2) mem2 a).
{ intros a Hp. apply HPR2. apply (apresent_grows _ _ _ _ HG1). apply (apresent_grows _ _ _ _ HG0). exact Hp. }
assert (OLDk : forall m (rr : bv 5), (m < 36)%nat -> Z.of_nat m = bv_unsigned rr -> ew Ea m = getr regs rr).
{ intros m rr Hm Hrr. rewrite OLDa by exact Hm. apply EEo. exact Hrr. }
assert (A20 : ew Ea 20 = Z_to_bv 64 EA) by (rewrite OLDa by (cbv; lia); exact E20).
assert (A22 : ew Ea 22 = Z_to_bv 64 WANT) by (rewrite OLDa by (cbv; lia); exact E22).
assert (A24 : ew Ea 24 = Z_to_bv 64 CNT) by (rewrite OLDa by (cbv; lia); exact E24).
lazymatch goal with |- SRr _ _ _ ?Q =>
assert (FIN : forall regs1 mem1 md1 pc1,
  getr regs1 22 = w64 (WANT + b) ->
  getr regs1 20 = w64 (EA + 16) -> getr regs1 25 = w64 (EA + 24) -> getr regs1 24 = w64 (CNT - 1) ->
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 21; 23; 26; 27]%bv -> getr regs1 r = getr regs r) ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem1 a = aview SEGS (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem1 a) ->
  AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W2 mem1 md1 kk ->
  ((1 < CNT /\ pc1 = BASE + A_csheB_l1) \/ (CNT = 1 /\ pc1 = BASE + A_csheB_tst)) ->
  Q W2 (mkCfg (mkst regs1 (Z_to_bv 64 pc1) mem1 (seg_rom SEGS)) md1)) end.
{ intros regs1 mem1 md1 pc1 R22 R20 R25 R24 RK KEEP3 HG3 HJ3 HPC. cbv beta.
  exists regs1, mem1, md1, b, pc1.
  split; [reflexivity|]. split; [exact HPC|]. split; [exact HJ3|]. split; [exact Hb01|].
  split; [intros Hb; destruct (Hb1 Hb) as [X1 X2]; split; [exact X1|];
          unfold hp_prefix_of in *; intros k Hk; rewrite <- HAV; apply X2; exact Hk|].
  split; [intros Hb Hle Hc'; apply (Hb0 Hb Hle); unfold hp_prefix_of in *;
          intros k Hk; rewrite HAV; apply Hc'; exact Hk|].
  split; [exact R22|]. split; [exact R20|]. split; [exact R25|]. split; [exact R24|].
  do 11 (split; [apply RK; cbv; tauto|]).
  split.
  { intros a Ha Hno. rewrite (KEEP3 a Ha), (HFRh a Ha Hno), HAV. reflexivity. }
  intros a Hp. exact (HG3 a (HPRMS a Hp)). }
(* 0x85864 beqz a0: has_prefix's answer *)
psrr_branch_tok RUNx BR HS SHOKa BspanE.
- (* no match: b = 0 *)
  assert (Hb0' : b = 0).
  { lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc' by lia; apply Z.eqb_eq in Hc'; lia end. }
  paj_run_tok_x RUNx HS HJ2 SHOKa BspanE.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
  psrr_branch_tok RUNx BR HS SHOKa BspanE.
  + (* s8 = CNT - 1 <> 0: back to the head *)
    lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite branch_ne_U, (U_atom_off Ea 24 CNT (-1) A24), U_lit in Hc' by lia;
      assert (Hlt : 1 < CNT) by (destruct (Z.eqb_spec (CNT + -1) 0); [discriminate | lia]) end.
    paj_run_to_tok_x RUNTOx HS HJ2 SHOKa BspanE A_csheB_l1.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha.
      repeat match goal with
      | Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) ?m1) (mrestrict (w_H W2) ?m2) |- aview _ _ ?m2 _ = _ =>
          rewrite (aview_kept_out Ev rs (w_H W2) m1 m2 Hf _ Ha);
          [ clear Hf
          | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hd_elt] in Hr; lia ]
      end.
      reflexivity. }
    assert (PRES3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a) by hd_pres.
    pmkst HS. apply SRr_ret.
    prreg HS (22%bv : bv 5) N22. prreg HS (20%bv : bv 5) N20. prreg HS (25%bv : bv 5) N25. prreg HS (24%bv : bv 5) N24.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (18%bv : bv 5) K18. prreg HS (19%bv : bv 5) K19. prreg HS (21%bv : bv 5) K21. prreg HS (23%bv : bv 5) K23. prreg HS (26%bv : bv 5) K26. prreg HS (27%bv : bv 5) K27.
    apply FIN.
    * cbn [ms_regs]. rewrite N22, A22, Hb0', Z.add_0_r. reflexivity.
    * cbn [ms_regs]. rewrite N20, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N25, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N24, A24, unsigned_lit_small by lia. unfold w64. f_equal; lia.
    * intros r Hr. cbv [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
      cbn [ms_regs]; first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K19 | rewrite K21 | rewrite K23 | rewrite K26 | rewrite K27]; apply OLDk; first [cbv; lia | reflexivity].
    * exact KEEP3.
    * exact PRES3.
    * exact HJ2.
    * left. split; [exact Hlt | unfold A_csheB_l1, AF_fr_check_shape_ends; lia].
  + (* s8 = 0: loop 1 is done, on to the g_gone test *)
    lazymatch goal with Hc' : branch_taken _ _ _ = false |- _ =>
      rewrite branch_ne_U, (U_atom_off Ea 24 CNT (-1) A24), U_lit in Hc' by lia;
      assert (Hlt : CNT = 1) by (destruct (Z.eqb_spec (CNT + -1) 0); [lia | discriminate]) end.
    paj_run_to_tok_x RUNTOx HS HJ2 SHOKa BspanE A_csheB_tst.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha.
      repeat match goal with
      | Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) ?m1) (mrestrict (w_H W2) ?m2) |- aview _ _ ?m2 _ = _ =>
          rewrite (aview_kept_out Ev rs (w_H W2) m1 m2 Hf _ Ha);
          [ clear Hf
          | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hd_elt] in Hr; lia ]
      end.
      reflexivity. }
    assert (PRES3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a) by hd_pres.
    pmkst HS. apply SRr_ret.
    prreg HS (22%bv : bv 5) N22. prreg HS (20%bv : bv 5) N20. prreg HS (25%bv : bv 5) N25. prreg HS (24%bv : bv 5) N24.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (18%bv : bv 5) K18. prreg HS (19%bv : bv 5) K19. prreg HS (21%bv : bv 5) K21. prreg HS (23%bv : bv 5) K23. prreg HS (26%bv : bv 5) K26. prreg HS (27%bv : bv 5) K27.
    apply FIN.
    * cbn [ms_regs]. rewrite N22, A22, Hb0', Z.add_0_r. reflexivity.
    * cbn [ms_regs]. rewrite N20, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N25, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N24, A24, unsigned_lit_small by lia. unfold w64. f_equal; lia.
    * intros r Hr. cbv [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
      cbn [ms_regs]; first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K19 | rewrite K21 | rewrite K23 | rewrite K26 | rewrite K27]; apply OLDk; first [cbv; lia | reflexivity].
    * exact KEEP3.
    * exact PRES3.
    * exact HJ2.
    * right. split; [exact Hlt | unfold A_csheB_tst, AF_fr_check_shape_ends; lia].
- (* a match: b = 1 (the ADDW1 trap at 0x8586c is decided: s6 < 2^26) *)
  assert (Hb1' : b = 1).
  { lazymatch goal with Hc' : branch_taken _ _ _ = false |- _ =>
      rewrite branch_eq_U, (U_atom Ea 40 b F40), U_lit in Hc' by lia; apply Z.eqb_neq in Hc'; lia end. }
  paj_run_tok_x RUNx HS HJ2 SHOKa BspanE.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
  psrr_branch_tok RUNx BR HS SHOKa BspanE.
  + (* s8 = CNT - 1 <> 0: back to the head *)
    lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite branch_ne_U, (U_atom_off Ea 24 CNT (-1) A24), U_lit in Hc' by lia;
      assert (Hlt : 1 < CNT) by (destruct (Z.eqb_spec (CNT + -1) 0); [discriminate | lia]) end.
    paj_run_to_tok_x RUNTOx HS HJ2 SHOKa BspanE A_csheB_l1.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha.
      repeat match goal with
      | Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) ?m1) (mrestrict (w_H W2) ?m2) |- aview _ _ ?m2 _ = _ =>
          rewrite (aview_kept_out Ev rs (w_H W2) m1 m2 Hf _ Ha);
          [ clear Hf
          | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hd_elt] in Hr; lia ]
      end.
      reflexivity. }
    assert (PRES3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a) by hd_pres.
    pmkst HS. apply SRr_ret.
    prreg HS (22%bv : bv 5) N22. prreg HS (20%bv : bv 5) N20. prreg HS (25%bv : bv 5) N25. prreg HS (24%bv : bv 5) N24.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (18%bv : bv 5) K18. prreg HS (19%bv : bv 5) K19. prreg HS (21%bv : bv 5) K21. prreg HS (23%bv : bv 5) K23. prreg HS (26%bv : bv 5) K26. prreg HS (27%bv : bv 5) K27.
    apply FIN.
    * cbn [ms_regs]. rewrite N22, A22, unsigned_lit_small, Hb1' by lia. reflexivity.
    * cbn [ms_regs]. rewrite N20, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N25, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N24, A24, unsigned_lit_small by lia. unfold w64. f_equal; lia.
    * intros r Hr. cbv [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
      cbn [ms_regs]; first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K19 | rewrite K21 | rewrite K23 | rewrite K26 | rewrite K27]; apply OLDk; first [cbv; lia | reflexivity].
    * exact KEEP3.
    * exact PRES3.
    * exact HJ2.
    * left. split; [exact Hlt | unfold A_csheB_l1, AF_fr_check_shape_ends; lia].
  + (* s8 = 0: on to the g_gone test *)
    lazymatch goal with Hc' : branch_taken _ _ _ = false |- _ =>
      rewrite branch_ne_U, (U_atom_off Ea 24 CNT (-1) A24), U_lit in Hc' by lia;
      assert (Hlt : CNT = 1) by (destruct (Z.eqb_spec (CNT + -1) 0); [lia | discriminate]) end.
    paj_run_to_tok_x RUNTOx HS HJ2 SHOKa BspanE A_csheB_tst.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      unfold hd_elt. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. intros a Ha. lia. }
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W2) (ms_mem ms2) a = aview SEGS (w_H W2) mem2 a).
    { intros a Ha.
      repeat match goal with
      | Hf : frame_of ?Ev ?rs (mrestrict (w_H W2) ?m1) (mrestrict (w_H W2) ?m2) |- aview _ _ ?m2 _ = _ =>
          rewrite (aview_kept_out Ev rs (w_H W2) m1 m2 Hf _ Ha);
          [ clear Hf
          | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
            intros (r & Hin & Hr); cbn [ss_mem add_cond In] in Hin;
            destruct Hin as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val hd_elt] in Hr; lia ]
      end.
      reflexivity. }
    assert (PRES3 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms2) a) by hd_pres.
    pmkst HS. apply SRr_ret.
    prreg HS (22%bv : bv 5) N22. prreg HS (20%bv : bv 5) N20. prreg HS (25%bv : bv 5) N25. prreg HS (24%bv : bv 5) N24.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (18%bv : bv 5) K18. prreg HS (19%bv : bv 5) K19. prreg HS (21%bv : bv 5) K21. prreg HS (23%bv : bv 5) K23. prreg HS (26%bv : bv 5) K26. prreg HS (27%bv : bv 5) K27.
    apply FIN.
    * cbn [ms_regs]. rewrite N22, A22, unsigned_lit_small, Hb1' by lia. reflexivity.
    * cbn [ms_regs]. rewrite N20, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N25, A20, unsigned_lit_small by lia. reflexivity.
    * cbn [ms_regs]. rewrite N24, A24, unsigned_lit_small by lia. unfold w64. f_equal; lia.
    * intros r Hr. cbv [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]];
      cbn [ms_regs]; first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K18 | rewrite K19 | rewrite K21 | rewrite K23 | rewrite K26 | rewrite K27]; apply OLDk; first [cbv; lia | reflexivity].
    * exact KEEP3.
    * exact PRES3.
    * exact HJ2.
    * right. split; [exact Hlt | unfold A_csheB_tst, AF_fr_check_shape_ends; lia].
Qed.

(* Loop 1 in full: from the head with i records counted to the g_gone test 0x8588c, with s6 = want_of P (the
   whole vector); every other register the test reads is the head's, and only has_prefix's scratch
   [sp - HP_STK, sp) changed. *)
Lemma hd_l1_loop : forall (k : nat) (i : Z) (W : world SEGS) ly S regs mem md
ly0 S0 (W0 : world SEGS) mem0 md0 XO AT FP sp0 kk PF (P : list byte) (V N : Z) (recs : list (Z * list byte)),
Z.of_nat k = N - i -> 0 <= i < N -> N = Z.of_nat (length recs) -> N < 2 ^ 26 ->
Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 1 <= 2 ^ 63 ->
~ In (Z_to_bv 8 0) P ->
4096 <= V -> V + AREC * N <= 140737479966720 -> V mod 16 = 0 ->
getr regs 2 = w64 (sp0 - 112) ->
getr regs 22 = w64 (Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs))) ->
getr regs 24 = w64 (N - i) ->
getr regs 20 = w64 (V + AREC * i) -> getr regs 25 = w64 (V + AREC * i + 8) ->
getr regs 21 = w64 SB -> getr regs 23 = w64 V -> getr regs 26 = w64 1 -> getr regs 8 = w64 PF ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> s0Z regs < alloc_ceiling ->
2 ^ 46 <= sp0 - 112 <= 2 ^ 47 -> (sp0 - 112) mod 16 = 0 ->
XO mod 16 = 0 -> alloc_ceiling + CSHE_STK_B <= sp0 ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
hd_l1_pfx W mem sp0 PF P -> hd_l1_vec ly S W mem sp0 V P recs i ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_csheB_l1)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md',
 c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_csheB_tst)) mem' (seg_rom SEGS)) md' /\
 AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W' mem' md' kk /\
 getr regs' 22 = w64 (Z.of_nat (CheckRep.want_of P recs)) /\
 getr regs' 2 = getr regs 2 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4 /\
 getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\
 getr regs' 19 = getr regs 19 /\ getr regs' 21 = getr regs 21 /\ getr regs' 27 = getr regs 27 /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - HP_STK <= a < sp0 - 112) ->
   aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) /\
 (forall a, apresent (w_H W) mem a -> apresent (w_H W') mem' a)).
Proof.
induction k as [|k IH]; intros i W ly S regs mem md ly0 S0 W0 mem0 md0 XO AT FP sp0 kk PF P V N recs
Hk Hi HN HN26 HP32 HPF0 HPFk HPnz HV0 HVhiN HV16 H2 H22 H24 H20 H25 H21 H23 H26 H8 Hgp Htp Hch HSP HSPa HXO16 HCL0
HJ HPFX HVEC; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HCEIL : alloc_ceiling <= sp0 - 112 - HP_STK)
  by (unfold HP_STK, ESTACK, CSHE_STK_B, CSHE_FRAME_B, LDROP_STK, LDROP_FRAME, ASTACK in *; lia).
destruct (HVEC i ltac:(lia)) as (Ms & Mn & Hra16 & Hmr16 & Hoffe & (VB & VL & HVIN & HVlo & HVhi) & Hr0 & Hlx & Hby
  & Hofft & Hlp).
pose proof HPFX as (HPby & HPvis & HPoff & HPmr1 & HPmr8 & HPra1 & HPshv1 & HPra0 & HPshv0 & HProm).
(* the bounds of the slot and of the counter *)
assert (HEAlo : 4096 <= V + AREC * i) by (unfold AREC; lia).
assert (HEAhi : V + AREC * i + 16 <= 140737479966720) by (unfold AREC in HVhiN |- *; lia).
assert (HEAal : (V + AREC * i) mod 16 = 0).
{ unfold AREC. apply Z.mod_divide in HV16; [|lia]. destruct HV16 as (qq & Hq). rewrite Hq.
  apply Z.mod_divide; [lia|]. exists (qq + i). lia. }
assert (HWlo : (CheckRep.want_of P (firstn (Z.to_nat i) recs) <= Z.to_nat i)%nat).
{ pose proof (hd_want_le P (firstn (Z.to_nat i) recs)) as HWle. rewrite length_firstn in HWle. lia. }
(* the prefix, in the premises has_prefix takes *)
assert (HFB : first_byte SEGS W mem PF (Z.of_nat (length P) + 1) 0 (Z.of_nat (length P))).
{ split; [lia|]. split.
  - intros t Ht. rewrite (HPby t ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth1 by lia.
    eexists. split; [reflexivity|]. intros Hc. apply HPnz.
    assert (Hz : nth (Z.to_nat t) P (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Hc; reflexivity).
    rewrite <- Hz. apply nth_In. lia.
  - intros _. rewrite (HPby (Z.of_nat (length P)) ltac:(rewrite length_app; cbn [length]; lia)).
    rewrite app_nth2 by lia.
    replace (Z.to_nat (Z.of_nat (length P)) - length P)%nat with 0%nat by lia. cbn [nth].
    reflexivity. }
assert (HVISp : hp_vis W mem PF (Z.of_nat (length P) + 1)) by (intros a Ha; apply HPvis; lia).
assert (HTAILp : forall a, PF + Z.of_nat (length P) < a <
  PF + Z.of_nat (length P) - (PF + Z.of_nat (length P)) mod 8 + 8 -> aview SEGS (w_H W) mem a <> None).
{ intros a Ha. apply HPvis. pose proof (Z.mod_pos_bound (PF + Z.of_nat (length P)) 8 ltac:(lia)). lia. }
(* one turn *)
eapply SRr_bind.
{ refine (hd_l1_run W ly S regs mem md (V + AREC * i) (fst (nth (Z.to_nat i) recs (0, [])))
    (Z.of_nat (length (snd (nth (Z.to_nat i) recs (0, [])))))
    (Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs))) (N - i) V ly0 S0 W0 mem0 md0 XO AT FP sp0 kk PF
    (Z.of_nat (length P))
    H2 H22 H24 H20 H25 H21 H23 H26 HSP HSPa ltac:(lia) ltac:(lia) ltac:(lia) HEAlo HEAhi HEAal
    ltac:(unfold AREC; lia) HV16 ltac:(lia) ltac:(lia) Ms Mn Hra16 Hmr16 HJ H8 ltac:(lia) ltac:(lia) HPF0
    ltac:(lia) HFB HVISp HPmr1 HPmr8 HPra1 HPshv1 HTAILp HProm
    ltac:(intros a Ha; apply HPoff; lia) ltac:(lia) ltac:(lia) _ Hgp Htp Hch HXO16 HCL0
    VB VL HVIN HVlo HVhi).
  intros Hle. destruct (Hlp Hle) as (Hmrp & Hrap & Hshvp).
  split.
  { intros a Ha.
    replace a with (fst (nth (Z.to_nat i) recs (0, [])) + (a - fst (nth (Z.to_nat i) recs (0, [])))) by lia.
    rewrite (Hby (a - fst (nth (Z.to_nat i) recs (0, [])))
      ltac:(rewrite length_app; cbn [length]; lia)). discriminate. }
  split; [intros a Ha; apply Hofft; lia|].
  split; [exact Hmrp|]. split; [exact Hrap|]. split; [exact Hshvp|].
  split; [exact HPra0 | exact HPshv0]. }
cbv beta. intros W' c' Hwle (regs' & mem' & md' & b & pc' & -> & HPC & HJ' & Hb01 & Hb1 & Hb0 & R22
  & R20 & R25 & R24 & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R23 & R26 & R27 & KEEP & PRES).
(* b is the record's prefixb *)
assert (HPB : (if CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, []))) then 1 else 0) = b).
{ destruct Hb01 as [Hb | Hb]; subst b.
  - destruct (CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, [])))) eqn:EP; [|reflexivity]. exfalso.
    destruct (proj2 (hd_prefixb_iff W mem (fst (nth (Z.to_nat i) recs (0, []))) PF
      (snd (nth (Z.to_nat i) recs (0, []))) P Hby HPby) EP) as (Hle & Hpre).
    exact (Hb0 eq_refl Hle Hpre).
  - destruct (Hb1 eq_refl) as (Hle & Hpre).
    rewrite (proj1 (hd_prefixb_iff W mem (fst (nth (Z.to_nat i) recs (0, []))) PF
      (snd (nth (Z.to_nat i) recs (0, []))) P Hby HPby) (conj Hle Hpre)). reflexivity. }
assert (EQW : Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat (i + 1)) recs)) =
  Z.of_nat (CheckRep.want_of P (firstn (Z.to_nat i) recs)) + b).
{ replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia.
  rewrite (hd_want_step P recs (Z.to_nat i) ltac:(lia)), <- HPB.
  destruct (CheckRep.prefixb P (snd (nth (Z.to_nat i) recs (0, [])))); lia. }
destruct HPC as [(HCNT & ->) | (HCNT & ->)].
- (* another record: the induction hypothesis at i + 1 *)
  assert (EQ20 : V + AREC * (i + 1) = V + AREC * i + 16) by (unfold AREC; lia).
  rewrite <- EQ20 in R20.
  replace (V + AREC * i + 24) with (V + AREC * (i + 1) + 8) in R25 by (unfold AREC; lia).
  replace (N - i - 1) with (N - (i + 1)) in R24 by lia.
  rewrite <- EQW in R22.
  eapply SRr_mono.
  { apply (IH (i + 1) W' ly S regs' mem' md' ly0 S0 W0 mem0 md0 XO AT FP sp0 kk PF P V N recs);
    [ lia | lia | exact HN | exact HN26 | exact HP32 | exact HPF0 | exact HPFk | exact HPnz | exact HV0
    | exact HVhiN | exact HV16
    | rewrite R2; exact H2 | exact R22 | exact R24 | exact R20 | exact R25
    | rewrite R21; exact H21 | rewrite R23; exact H23 | rewrite R26; exact H26 | rewrite R8; exact H8
    | rewrite R3; exact Hgp | rewrite R4; exact Htp | unfold s0Z; rewrite R8; exact Hch
    | exact HSP | exact HSPa | exact HXO16 | exact HCL0 | exact HJ'
    | exact (hd_l1_pfx_kept W W' mem mem' sp0 PF P HCEIL HPF0 HPFk KEEP HPFX)
    | intros j Hj; exact (hd_l1_rec_kept ly S W W' mem mem' sp0 V P _ j HCEIL
        ltac:(unfold AREC; lia) KEEP (HVEC j ltac:(lia))) ]. }
  cbv beta. intros W'' c'' Hwle2 (regs'' & mem'' & md'' & -> & HJ'' & T22 & T2 & T3 & T4
    & T8 & T9 & T18 & T19 & T21 & T27 & KEEP2 & PRES2).
  exists regs'', mem'', md''.
  split; [reflexivity|]. split; [exact HJ''|]. split; [exact T22|].
  split; [rewrite T2; exact R2|]. split; [rewrite T3; exact R3|]. split; [rewrite T4; exact R4|].
  split; [rewrite T8; exact R8|]. split; [rewrite T9; exact R9|]. split; [rewrite T18; exact R18|].
  split; [rewrite T19; exact R19|]. split; [rewrite T21; exact R21|]. split; [rewrite T27; exact R27|].
  split; [intros a Ha Hno; rewrite (KEEP2 a Ha Hno); exact (KEEP a Ha Hno)|].
  intros a Hp. exact (PRES2 a (PRES a Hp)).
- (* the last record: at 0x8588c *)
  assert (HiN : i + 1 = N) by lia.
  assert (EQR : firstn (Z.to_nat (i + 1)) recs = recs)
    by (replace (Z.to_nat (i + 1)) with (length recs) by lia; apply firstn_all).
  rewrite EQR in EQW.
  apply SRr_ret. exists regs', mem', md'.
  split; [reflexivity|]. split; [exact HJ'|].
  split; [rewrite R22, EQW; reflexivity|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
  split; [exact R18|]. split; [exact R19|]. split; [exact R21|]. split; [exact R27|].
  split; [exact KEEP | exact PRES].
Qed.

(* ------------------------------------------------------------------ the g_gone test 0x8588c *)
(* From loop 1's join (or the n <= 0 arm): s1 (x9) = &held.v, s3 (x19) = n, s5 (x21) = SB, s6 (x22) = want.  The
   run reads g_gone and writes nothing.  g_gone <> 0: the DECW trap 0x8589c and `bltz a0` 0x858a0 (n - 1 < 0 sends
   n = 0 to the epilogue); g_gone = 0: the DECW trap 0x85968, s5 = 4, s7 = 5, s3 = " end" (A_lit_end5).  The runner
   leaves each DECW compare as (x - 1) >= x on the 64-bit word, refuted by trap_br_ge and hd_sg_off (x < 2^26). *)
Definition hd_goneR : YP09.region := YP09.mkRegion (Some A_g_gone) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition hd_tst_facts : facts :=
mkFacts [ (19%nat, mkAF 0 (2 ^ 26) 0); (22%nat, mkAF 0 (2 ^ 26) 0); (32%nat, mkAF 0 255 0) ] [] [].
Definition ss_hd_tst : sstate := mkSS A_csheB_tst sr_atoms [ hd_goneR ] None hd_tst_facts.
Definition hd_tst_extra (gone : Z) : list word := map (Z_to_bv 64) [gone].

(* a word atom plus a small offset, read signed: what the runner leaves for `addiw a0,x,-1` on a non-negative int32 *)
Lemma hd_sg_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 63 -> - 2 ^ 63 <= v + c < 2 ^ 63 ->
Sg E (SOff n c) = v + c.
Proof.
intros E n v c Hn Hv Hvc. rewrite S_of_U, U_SOff, Hn, unsigned_lit_small by lia. unfold zcanon, M64.
rewrite (trap_swrap64 _ (v + c)) by (apply Z.mod_mod; lia). apply swrap64_id. unfold half64. lia.
Qed.

Lemma hd_sg_lit0 : forall E, Sg E (SLit 0) = 0.
Proof. intros E. rewrite S_of_U, (U_lit E 0) by lia. apply swrap64_id. unfold half64. lia. Qed.
Lemma hd_tst_state : forall (W : world SEGS) regs mem N want gone,
getr regs 19 = w64 N -> getr regs 22 = w64 want ->
0 <= N < 2 ^ 26 -> 0 <= want < 2 ^ 26 -> 0 <= gone < 256 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (hd_tst_extra gone))) ss_hd_tst
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_csheB_tst)) mem (seg_rom SEGS))).
Proof.
intros W regs mem N want gone H19 H22 RN RW Rg Mg.
pose proof pa_B_ok as HBASE.
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
pose proof (pa_val_range A_g_gone) as HgV.
set (E := Eimg (Ereg regs (hd_tst_extra gone))).
assert (E19 : ew E 19 = Z_to_bv 64 N)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact H19).
assert (E22 : ew E 22 = Z_to_bv 64 want)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Eg : ew E A_g_gone = Z_to_bv 64 (VAL A_g_gone))
  by (subst E; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Ugo : base_val E (Some A_g_gone) = VAL A_g_gone)
  by (cbn [base_val]; rewrite Eg; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_hd_tst. apply pa_entry_st_ok_full.
- subst E; apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi hd_goneR ms_mem mkst].
  rewrite Ugo. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Mg.
- apply pairwise_disjoint_of_extents. cbn [map]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [hd_tst_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E19, E22, E32, !unsigned_lit_small by lia.
  rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma hd_tst : forall (W : world SEGS) ly S regs mem md ly0 S0 (W0 : world SEGS) mem0 md0 XO AT FP sp0 kk
HA N want gone,
getr regs 9 = w64 (HA + 80) -> getr regs 19 = w64 N -> getr regs 21 = w64 SB -> getr regs 22 = w64 want ->
0 <= N < 2 ^ 26 -> 0 <= want < 2 ^ 26 -> 0 <= gone < 256 -> 4096 <= HA -> HA + 96 <= kLowMemEnd ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W mem md kk ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_csheB_tst)) mem (seg_rom SEGS)) md)
(fun W' c' => exists regs' mem' md' pc',
 c' = mkCfg (mkst regs' (Z_to_bv 64 pc') mem' (seg_rom SEGS)) md' /\
 AJ0 G XO [(AT, AT + 8)] CSHE_STK_B sp0 FP ly0 S0 W0 mem0 md0 [] ly S W' mem' md' kk /\
 W' = W /\
 (forall x, mrestrict (w_H W) mem' x = mrestrict (w_H W) mem x) /\
 (forall r : bv 5, In r [2; 3; 4; 8; 9; 27]%bv -> getr regs' r = getr regs r) /\
 ((gone <> 0 /\ N = 0 /\ pc' = BASE + A_csheB_ret) \/
  (gone <> 0 /\ 0 < N /\ pc' = BASE + A_csheB_l2 /\ getr regs' 18 = w64 ((HA + 80) / 8 + SB) /\
   getr regs' 19 = w64 N /\ getr regs' 21 = w64 SB) \/
  (gone = 0 /\ pc' = BASE + A_csheB_l3 /\ getr regs' 18 = getr regs 18 /\
   getr regs' 19 = w64 (VAL A_lit_end5) /\ getr regs' 21 = w64 4 /\ getr regs' 23 = w64 5 /\
   getr regs' 22 = w64 want /\ getr regs' 10 = w64 (want - 1)))).
Proof.
intros W ly S regs mem md ly0 S0 W0 mem0 md0 XO AT FP sp0 kk HA N want gone H9 H19 H21 H22 RN RW Rg HAlo HAhi Mg HJ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (hd_tst_state W regs mem N want gone H19 H22 RN RW Rg Mg) as HS.
remember (Eimg (Ereg regs (hd_tst_extra gone))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn. subst E. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E9 : ew E 9 = Z_to_bv 64 (HA + 80)) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 N) by (rewrite (EEo 19%nat 19%bv eq_refl); exact H19).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 want) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E32 : ew E 32 = Z_to_bv 64 gone)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E28 : ew E A_lit_end5 = Z_to_bv 64 (VAL A_lit_end5)) by (subst E; apply Eimg_img; unfold A_lit_end5, A_OBJ, A_TEXT, A_LIM; lia).
clear HE.
assert (SHOK : sh_ok SEGS hd_Bx1 ([] : list shent) E (mrestrict (w_H W) mem)) by constructor.
pose (RUNTOx := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
pose (RUNx := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)]).
paj_run_tok_x RUNx HS HJ SHOK BspanE.
{ apply awr_ok_x_cons; [|apply awr_ok_x_nil].
  intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
psrr_branch_tok RUNx BR HS SHOK BspanE.
- (* g_gone = 0: the want path *)
  assert (Hg0 : gone = 0).
  { lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite branch_eq_U, (U_atom E 32 gone E32), U_lit in Hc' by lia; apply Z.eqb_eq in Hc'; lia end. }
  paj_run_tok_x RUNx HS HJ SHOK BspanE.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
  (* 0x85968 bge a0,s6 (a0 = want - 1): the UBSan DECW trap, never taken (want < 2^26) *)
  psrr_branch_tok RUNx BR HS SHOK BspanE.
  { lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite trap_br_ge, (hd_sg_off E 22 want (-1) E22), (hd_sg_off E 22 want 0 E22) in Hc' by lia;
      apply negb_true_iff in Hc'; apply Z.ltb_ge in Hc'; lia end. }
  paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE A_csheB_l3.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
  assert (MEQ : forall x, mrestrict (w_H W) (ms_mem ms1) x = mrestrict (w_H W) mem x).
  { intros x.
    repeat match goal with
    | Hf : frame_of ?Ev ?rs (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2) |- mrestrict _ ?m2 _ = _ =>
        rewrite (Hf x);
        [ clear Hf
        | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros (r & Hin & Hr); cbn [ss_mem add_cond ss_hd_tst In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Hr; lia ]
    end. reflexivity. }
  pmkst HS. apply SRr_ret.
  prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (27%bv : bv 5) K27.
  prreg HS (10%bv : bv 5) N10. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19.
  prreg HS (21%bv : bv 5) N21. prreg HS (22%bv : bv 5) N22. prreg HS (23%bv : bv 5) N23.
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_csheB_l3) end.
  split; [reflexivity|]. split; [exact HJ|]. split; [reflexivity|]. split; [exact MEQ|].
  split.
  { intros r Hr. cbv [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [ms_regs];
    first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K27]; apply EEo; reflexivity. }
  right. right. split; [exact Hg0|]. split; [reflexivity|].
  split; [cbn [ms_regs]; rewrite N18; apply EEo; reflexivity|].
  split; [cbn [ms_regs]; rewrite N19; exact E28|].
  split; [cbn [ms_regs]; rewrite N21; reflexivity|].
  split; [cbn [ms_regs]; rewrite N23; reflexivity|].
  split; [cbn [ms_regs]; rewrite N22; exact E22|].
  cbn [ms_regs]. rewrite N10, E22, unsigned_lit_small by lia. unfold w64. f_equal; lia.
- (* g_gone <> 0: the gone path *)
  assert (Hg1 : gone <> 0).
  { lazymatch goal with Hc' : branch_taken _ _ _ = false |- _ =>
      rewrite branch_eq_U, (U_atom E 32 gone E32), U_lit in Hc' by lia; apply Z.eqb_neq in Hc'; lia end. }
  paj_run_tok_x RUNx HS HJ SHOK BspanE.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
  (* 0x8589c bge a0,s3 (a0 = n - 1): the UBSan DECW trap, never taken (n < 2^26) *)
  psrr_branch_tok RUNx BR HS SHOK BspanE.
  { lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
      rewrite trap_br_ge, (hd_sg_off E 19 N (-1) E19), (hd_sg_off E 19 N 0 E19) in Hc' by lia;
      apply negb_true_iff in Hc'; apply Z.ltb_ge in Hc'; lia end. }
  paj_run_tok_x RUNx HS HJ SHOK BspanE.
  { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
  psrr_branch_tok RUNx BR HS SHOK BspanE.
  + (* a0 = n - 1 < 0: n = 0, straight to the epilogue *)
    assert (HN0 : N = 0).
    { lazymatch goal with Hc' : branch_taken _ _ _ = true |- _ =>
        rewrite trap_br_lt, (hd_sg_off E 19 N (-1) E19), hd_sg_lit0 in Hc' by lia; apply Z.ltb_lt in Hc'; lia end. }
    paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE A_csheB_ret.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
    assert (MEQ : forall x, mrestrict (w_H W) (ms_mem ms2) x = mrestrict (w_H W) mem x).
  { intros x.
    repeat match goal with
    | Hf : frame_of ?Ev ?rs (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2) |- mrestrict _ ?m2 _ = _ =>
        rewrite (Hf x);
        [ clear Hf
        | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros (r & Hin & Hr); cbn [ss_mem add_cond ss_hd_tst In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Hr; lia ]
    end. reflexivity. }
    pmkst HS. apply SRr_ret.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (27%bv : bv 5) K27.
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_csheB_ret) end.
    split; [reflexivity|]. split; [exact HJ|]. split; [reflexivity|]. split; [exact MEQ|].
    split.
  { intros r Hr. cbv [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [ms_regs];
    first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K27]; apply EEo; reflexivity. }
    left. split; [exact Hg1|]. split; [exact HN0 | reflexivity].
  + (* n >= 1: loop 2's head, with s2 = the shadow byte address of &held.v *)
    assert (HNp : 0 < N).
    { lazymatch goal with Hc' : branch_taken _ _ _ = false |- _ =>
        rewrite trap_br_lt, (hd_sg_off E 19 N (-1) E19), hd_sg_lit0 in Hc' by lia; apply Z.ltb_ge in Hc'; lia end. }
    paj_run_to_tok_x RUNTOx HS HJ SHOK BspanE A_csheB_l2.
    { cbn [ss_mem add_cond]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Ha. lia. }
    assert (MEQ : forall x, mrestrict (w_H W) (ms_mem ms2) x = mrestrict (w_H W) mem x).
  { intros x.
    repeat match goal with
    | Hf : frame_of ?Ev ?rs (mrestrict (w_H W) ?m1) (mrestrict (w_H W) ?m2) |- mrestrict _ ?m2 _ = _ =>
        rewrite (Hf x);
        [ clear Hf
        | let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
          intros (r & Hin & Hr); cbn [ss_mem add_cond ss_hd_tst In] in Hin; destruct Hin as [<- | []];
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi hd_goneR] in Hr; lia ]
    end. reflexivity. }
    pmkst HS. apply SRr_ret.
    prreg HS (2%bv : bv 5) K2. prreg HS (3%bv : bv 5) K3. prreg HS (4%bv : bv 5) K4. prreg HS (8%bv : bv 5) K8. prreg HS (9%bv : bv 5) K9. prreg HS (27%bv : bv 5) K27.
    prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (21%bv : bv 5) N21.
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
      exists (ms_regs msx), (ms_mem msx), mdx, (BASE + A_csheB_l2) end.
    split; [reflexivity|]. split; [exact HJ|]. split; [reflexivity|]. split; [exact MEQ|].
    split.
  { intros r Hr. cbv [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [ms_regs];
    first [rewrite K2 | rewrite K3 | rewrite K4 | rewrite K8 | rewrite K9 | rewrite K27]; apply EEo; reflexivity. }
    right. left. split; [exact Hg1|]. split; [exact HNp|]. split; [reflexivity|].
    assert (HD2 : 0 <= (HA + 80) / 8 <= HA + 80) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (QH : alu64 ALU_SRL (Z_to_bv 64 (HA + 80)) (Z_to_bv 64 3) = Z_to_bv 64 ((HA + 80) / 8)).
    { apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite !unsigned_lit_small by lia.
      change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
      unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
    split.
    { cbn [ms_regs]. rewrite N18, E9, E21, QH, !zalu64_sound. unfold w64. f_equal.
      unfold zalu64, zalu_raw, zcanon, M64.
      rewrite (Z.mod_small SB) by (unfold SB; lia). rewrite (Z.mod_small ((HA + 80) / 8)) by lia.
      apply Z.mod_small. unfold SB in *. lia. }
    split; [cbn [ms_regs]; rewrite N19; exact E19 | cbn [ms_regs]; rewrite N21; exact E21].
Qed.

(* ------------------------------------------------------------------ from the g_gone test to the interface *)
(* The state at 0x8588c, as both arms into it (n = 0 and loop 1's exit) hand it over, to the three cut points of
   W_cshe_epi.v: cshe_out_B (g_gone <> 0, n = 0: nothing was dropped, the source and *at are the caller's),
   cshe_l2_in (g_gone <> 0, n >= 1), cshe_l3_in (g_gone = 0). *)
Lemma hd_fin : forall W ly S regs0 mem md ch XO AT HA PF h P A0 gone ob WT regsT memT mdT (kr : nat),
AFP0 CSHE_STK_B ly S W regs0 mem md ch ->
asrc_at B ly S W mem HA h -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
NoDup (CheckRep.texts (hs_held h)) -> hl_n (hs_held h) < 2 ^ 26 ->
spZ regs0 <= AT -> AT + 8 <= spZ regs0 + XO -> spZ regs0 + XO <= ly_top ly ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
AJ0 G XO [(AT, AT + 8)] CSHE_STK_B (spZ regs0) (blk_FP (list_blks (hs_held h)))
  ly S W mem md [] ly S WT memT mdT 0 ->
wle W WT ->
getr regsT 2 = w64 (spZ regs0 - 112) -> getr regsT 3 = getr regs0 3 -> getr regsT 4 = getr regs0 4 ->
getr regsT 27 = getr regs0 27 ->
getr regsT 8 = w64 PF -> getr regsT 9 = w64 (HA + 80) -> getr regsT 18 = w64 AT ->
getr regsT 19 = w64 (hl_n (hs_held h)) -> getr regsT 21 = w64 SB ->
getr regsT 22 = w64 (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) ->
cshe_saved_B WT memT (spZ regs0) regs0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - CSHE_STK_B <= a < spZ regs0) ->
  aview SEGS (w_H WT) memT a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H WT) memT a) ->
(* the room round: cshe_spec_x's room budget at the entry state (the head allocates nothing) *)
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) ->
SRr SEGS WT (mkCfg (mkst regsT (Z_to_bv 64 (BASE + A_csheB_tst)) memT (seg_rom SEGS)) mdT)
  (fun W1 c1 => cshe_out_B B PST ARx G MT RP regs0 ly S W mem md XO AT HA A0 gone h P ob kr W1 c1 \/
                cshe_l2_in B PST ARx G regs0 ly S W mem md XO AT HA PF gone h W1 c1 \/
                cshe_l3_in B PST ARx G regs0 ly S W mem md XO AT HA PF gone h P W1 c1).
Proof.
intros W ly S regs0 mem md ch XO AT HA PF h P A0 gone ob WT regsT memT mdT kr HPRE HSRC HAlo HAhi HND HnH
  HATlo HAThi HXtop MAT Mg Rg HJT HwleT T2 T3 T4 T27 T8 T9 T18 T19 T21 T22 SAVT KEEPT PREST HRM.
unfold ASRC in HAhi.
pose proof pa_segs_low as Hsegs.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
assert (HWle : (CheckRep.want_of P (hl_recs (hs_held h)) <= length (hl_recs (hs_held h)))%nat)
  by apply hd_want_le.
assert (MgT : val_mem SEGS (mrestrict (w_H WT) memT) (VAL A_g_gone) 1 gone).
{ apply (hd_vm_keep W WT mem memT (VAL A_g_gone) 1 gone); [|exact Mg].
  intros x Hx. cbn [Z.of_nat] in Hx. apply KEEPT; lia. }
eapply SRr_mono.
{ apply (hd_tst WT ly S regsT memT mdT ly S W mem md XO AT (blk_FP (list_blks (hs_held h))) (spZ regs0) 0
    HA (hl_n (hs_held h)) (Z.of_nat (CheckRep.want_of P (hl_recs (hs_held h)))) gone T9 T19 T21 T22
    ltac:(unfold hl_n in *; lia) ltac:(unfold hl_n in *; lia) Rg HAlo HAhi MgT HJT). }
cbv beta. intros W1 c1 _ (regs1 & mem1 & md1 & pc1 & -> & HJ1 & -> & MEQ & RK & HARM).
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - CSHE_STK_B <= a < spZ regs0) ->
  aview SEGS (w_H WT) mem1 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno. rewrite (aview_eq_of SEGS (w_H WT) memT mem1 a (MEQ _)). exact (KEEPT a Ha Hno). }
assert (PRES1 : forall a, apresent (w_H W) mem a -> apresent (w_H WT) mem1 a).
{ intros a Hp. exact (cshe_apres_meq_B WT memT mem1 a (MEQ _) (PREST a Hp)). }
assert (SAV1 : cshe_saved_B WT mem1 (spZ regs0) regs0).
{ apply (hd_saved_kept WT WT memT mem1 (spZ regs0) regs0); [|exact SAVT].
  intros a Ha. apply (aview_eq_of SEGS). apply MEQ. }
assert (R2 : getr regs1 2 = w64 (spZ regs0 - 112)) by (rewrite (RK 2%bv ltac:(cbv; tauto)); exact T2).
assert (R3 : getr regs1 3 = getr regs0 3) by (rewrite (RK 3%bv ltac:(cbv; tauto)); exact T3).
assert (R4 : getr regs1 4 = getr regs0 4) by (rewrite (RK 4%bv ltac:(cbv; tauto)); exact T4).
assert (R27 : getr regs1 27 = getr regs0 27) by (rewrite (RK 27%bv ltac:(cbv; tauto)); exact T27).
assert (R8 : getr regs1 8 = w64 PF) by (rewrite (RK 8%bv ltac:(cbv; tauto)); exact T8).
assert (R9 : getr regs1 9 = w64 (HA + 80)) by (rewrite (RK 9%bv ltac:(cbv; tauto)); exact T9).
destruct HARM as [(Hg & HN0 & ->) | [(Hg & HNp & -> & R18 & R19 & R21) | (Hg & -> & R18 & R19 & R21 & R23 & R22 & R10)]].
- (* g_gone <> 0 and an empty list: the epilogue's entry *)
  left. unfold cshe_out_B.
  assert (HR0 : hl_recs (hs_held h) = []).
  { unfold hl_n in HN0. destruct (hl_recs (hs_held h)) as [|r rs]; [reflexivity | cbn [length] in HN0; lia]. }
  assert (SRC1 : asrc_at B ly S WT mem1 HA h).
  { assert (SRCT : asrc_at B ly S WT memT HA h).
    { apply (hd_src_kept ly S W WT mem memT md HA h (spZ regs0 - CSHE_STK_B) HAR HSRC HAlo HAhi
        ltac:(lia) HwleT ltac:(intros a Ha; apply KEEPT; lia) PREST). }
    apply (asrc_at_kept B ly S WT memT ly S WT mem1 HA h SRCT).
    - intros rr Hin a Ha. apply cshe_byte_meq_B. apply MEQ.
    - intros b Hb. exact (hd_src_blks ly S WT memT HA h SRCT b Hb). }
  exists ly, S, regs1, mem1, md1, 0, (hs_held h), ([] : list (Z * list byte)), 0.
  split; [reflexivity|].
  split; [exact HJ1|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R27|].
  split; [exact SAV1|].
  split; [rewrite hd_set_held_id; exact SRC1|].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HND|].
  split.
  { left. split; [exact Hg|]. rewrite HR0. cbn [filter].
    split; [reflexivity|]. split; [reflexivity | reflexivity]. }
  split; [lia|].
  split.
  { replace (A0 + 0) with A0 by lia.
    apply (hd_vm_keep W WT mem mem1 AT 8 A0); [|exact MAT].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP1; lia. }
  split.
  { apply (hd_vm_keep W WT mem mem1 (VAL A_g_gone) 1 gone); [|exact Mg].
    intros x Hx. cbn [Z.of_nat] in Hx. apply KEEP1; lia. }
  split; [cbn [map app]; intros rest Hp; exact Hp|].
  split; [reflexivity|].
  split; [rewrite HN0, Z.mul_0_l; exact (mo_le_refl MT ML S)|].
  (* errno's view: errno is an image cell (PALib's api_env), so below the frame *)
  split; [intros j0 Hj0; pose proof (proj1 (pal_env B TL)) as [He0 He1]; apply KEEP1; lia|].
  (* the room round: nothing was dropped, the budget past the call is at most the entry's *)
  exact (RMM_of RP S kr (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) ltac:(lia) HRM).
- (* g_gone <> 0 and a record to drop: loop 2's head *)
  right. left. unfold cshe_l2_in.
  exists regs1, mem1, md1.
  split; [reflexivity|]. split; [exact HJ1|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R27|].
  split; [exact R8|]. split; [exact R9|]. split; [exact R18|]. split; [exact R19|]. split; [exact R21|].
  split; [exact SAV1|].
  split; [exact KEEP1|]. split; [exact PRES1|].
  split; [exact Hg | exact HNp].
- (* g_gone = 0: loop 3's head *)
  right. right. unfold cshe_l3_in.
  exists regs1, mem1, md1.
  split; [reflexivity|]. split; [exact HJ1|].
  split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R27|].
  split; [exact R8|]. split; [exact R9|]. split; [rewrite R18; exact T18|].
  split; [exact R19|]. split; [exact R21|]. split; [exact R23|]. split; [exact R22|]. split; [exact R10|].
  split; [exact SAV1|].
  split; [exact KEEP1|]. split; [exact PRES1|].
  exact Hg.
Qed.

(* ------------------------------------------------------------------ the head, as one lemma *)
(* cshe_hd_B: from the entry to the interface's three cut points.  Its premises are cshe_spec's own (lib/B
   W_contract.v Section w3e, CSHE_STK read as CSHE_STK_B, `let H` / `let PLEN` expanded), those the head uses. *)
Lemma cshe_hd_B : forall W ly S regs mem md ch XO AT HA (j : nat) PF h P A0 gone (O OUT : Z) (ob : list byte),
AFP0 CSHE_STK_B ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 PF -> getr regs 12 = w64 AT ->
asrc_at B ly S W mem HA h ->
HA mod 8 = 0 -> 4096 <= HA -> HA + ASRC <= kLowMemEnd ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
HA = VAL (A_OBJ 19) + ASRC * Z.of_nat j -> (j < 4)%nat ->
NoDup (CheckRep.texts (hs_held h)) ->
hl_n (hs_held h) < 2 ^ 26 ->
(forall a, hl_v (hs_held h) <= a < hl_v (hs_held h) + AREC * hl_cap (hs_held h) ->
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
(forall r, In r (hl_recs (hs_held h)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
val_mem SEGS (mrestrict (w_H W) mem) AT 8 A0 ->
~ In (Z_to_bv 8 0) P -> Z.of_nat (length P) + 1 < 2 ^ 32 -> 0 < PF -> PF + Z.of_nat (length P) + 8 <= 2 ^ 63 ->
(forall i, 0 <= i < Z.of_nat (length P) ->
  aview SEGS (w_H W) mem (PF + i) = Some (bv_unsigned (nth (Z.to_nat i) P (Z_to_bv 8 0)))) ->
aview SEGS (w_H W) mem (PF + Z.of_nat (length P)) = Some 0 ->
(forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> aview SEGS (w_H W) mem a <> None /\
  ~ (spZ regs - CSHE_STK_B <= a < spZ regs + XO)) ->
amem_range PF (Z.of_nat (length P) + 1) -> amem_range PF 8 ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF PF (Z.of_nat (length P) + 1) ->
shadow_hull_vis (aview SEGS (w_H W) mem) PF (Z.of_nat (length P) + 1) ->
((forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_rom SEGS a) /\ ashp_x ARx PF (Z.of_nat (length P) + 1) \/
 exists cid pos, In (cid, pos) (frames S) /\
   forall a, PF <= a < PF + Z.of_nat (length P) + 8 -> in_zr a (frame_rng ly (cid, pos))) ->
rom_view SEGS W mem ->
val_mem SEGS (mrestrict (w_H W) mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cshe_cost MT_rk (hs_held h)) + kr) ->
SRr SEGS W (cfg_at SEGS A_csheBP regs mem md)
  (fun W1 c1 => cshe_out_B B PST ARx G MT RP regs ly S W mem md XO AT HA A0 gone h P ob kr W1 c1 \/
                cshe_l2_in B PST ARx G regs ly S W mem md XO AT HA PF gone h W1 c1 \/
                cshe_l3_in B PST ARx G regs ly S W mem md XO AT HA PF gone h P W1 c1).
Proof.
intros W ly S regs mem md ch XO AT HA j PF h P A0 gone O OUT ob HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 HSRC
  Hal8 Hlo Hhi HGin Hzs HAj Hj4 HND HnH HVoff HRoff HAT8 HATlo HAThi MAT HPnz HP32 HPF0 HPFk HPby HPnul HPvis
  HPmr1 HPmr8 HPra1 HPshv1 HPHOME HROM Mg Rg kr HRM.
(* the held list's head lies in g_s = cshe_ro_B's fourth range (HA = g_s + 96 j, j < 4) *)
assert (HGro : forall a, HA + 80 <= a < HA + 96 -> inG cshe_ro_B a).
{ intros a Ha. unfold inG, cshe_ro_B. do 3 apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. rewrite HAj in Ha. unfold ASRC in Ha. lia. }
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_val as ACV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hshlo & Hshhi & H47 & Hbot & Htop & Htop2).
assert (WS : CSHE_STK_B = 16560) by reflexivity.
assert (HhiA : HA + 96 <= kLowMemEnd) by (unfold ASRC in Hhi; lia).
(* the held list: its two cells the head reads, its vector's block, and its records *)
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HHl & _).
pose proof HHl as (M80 & M88 & M92 & HAWR80 & Hcapb & Hvb & _ & _ & HFrec).
replace (HA + 80 + 8) with (HA + 88) in M88 by lia.
unfold arm in M80, M88.
assert (HNn : hl_n (hs_held h) = Z.of_nat (length (hl_recs (hs_held h)))) by reflexivity.
assert (RV : 0 <= hl_v (hs_held h) < 140737479966720 /\ hl_v (hs_held h) mod 16 = 0 /\
  (0 < hl_n (hs_held h) -> 4096 <= hl_v (hs_held h))).
{ destruct Hvb as [(Hc0 & Hv0) | (Hc & Hvin & _)].
  - rewrite Hv0. split; [lia|]. split; [reflexivity|]. intros Hn. unfold hl_n in *. lia.
  - destruct (hd_blk ly S W mem md _ _ HAR Hvin) as (H16 & H4096 & _ & _ & Hr1 & Hc2 & CC & _).
    split; [lia|]. split; [exact H16|]. intros _; lia. }
assert (KEEPw : forall (W1 : world SEGS) mem1, (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
    aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK_B <= a < spZ regs) ->
    aview SEGS (w_H W1) mem1 a = aview SEGS (w_H W) mem a)
  by (intros W1 mem1 Hk a Ha Hno; apply Hk; [exact Ha | lia]).
(* the entry, to loop 1's head or (an empty list) to the g_gone test *)
unfold cfg_at. change (w64 A_csheBP) with (Z_to_bv 64 A_csheBP).
eapply SRr_bind.
{ apply (hd_head W ly S regs mem md ch HA (hl_v (hs_held h)) (hl_n (hs_held h)) XO AT
    (blk_FP (list_blks (hs_held h))) PF HPRE HXO0 HXO16 HXtop HXp H10 H11 H12 Hal8 Hlo Hhi Hzs HGin HGro
    M80 (proj1 RV) (proj1 (proj2 RV)) M88 ltac:(unfold hl_n in *; lia) (proj2 (proj2 RV))). }
cbv beta. intros W1 c1 Hwle1 (regs1 & mem1 & md1 & pc1 & -> & HJ1 & Q2 & Q3 & Q4 & Q27 & Q8 & Q9 & Q18 & Q19
  & Q21 & Q22 & KEEP1 & PRES1 & SAVED1 & HARM).
destruct HARM as [(HNp & -> & R20 & R23 & R24 & R25 & R26) | (HN0 & ->)].
2: { (* the held list is empty: s6 = 0 = want_of P [] *)
  assert (HR0 : hl_recs (hs_held h) = []).
  { unfold hl_n in HN0. destruct (hl_recs (hs_held h)) as [|r rs]; [reflexivity | cbn [length] in HN0; lia]. }
  apply (hd_fin W ly S regs mem md ch XO AT HA PF h P A0 gone ob W1 regs1 mem1 md1 kr HPRE HSRC Hlo Hhi HND HnH
    HATlo HAThi HXtop MAT Mg Rg HJ1 Hwle1 Q2 Q3 Q4 Q27 Q8 Q9 Q18 Q19 Q21 ltac:(rewrite Q22, HR0; reflexivity)
    SAVED1 (KEEPw W1 mem1 KEEP1) PRES1 HRM). }
(* loop 1 *)
destruct Hvb as [(Hc0 & Hv0) | (Hcpos & Hvin & Hjunk & Hgv)]; [unfold hl_n in *; lia|].
destruct (hd_blk ly S W mem md _ _ HAR Hvin) as (Hv16 & Hv4096 & _ & Hvle & Hvreq1 & Hvceil & _ & _ & Hvapp & _).
assert (HCEIL : alloc_ceiling <= spZ regs - 112) by lia.
(* has_prefix's frame chain needs PF below the ceiling: P is a read-only literal (in the image) or a local of one
   of S's fake frames (below alloc_ceiling, frames_bounds) *)
assert (HPFlo : PF < alloc_ceiling).
{ destruct HPHOME as [(HPROM & _) | (cid & pos & Hfin & Hfr)].
  - destruct (HPROM PF ltac:(lia)) as (sg & Hsg & _ & Hr).
    pose proof (pa_img_range PF ltac:(exists sg; split; [exact Hsg | exact Hr])). lia.
  - pose proof (Hfr PF ltac:(lia)) as Hz. unfold in_zr, frame_rng in Hz. cbn [fst snd] in Hz.
    pose proof (frames_bounds0 ly S W mem md cid pos HAR Hfin) as (_ & Hfb & _). lia. }
(* loop 1's prefix invariant, at the entry state and then at the loop head *)
assert (HPFX0 : hd_l1_pfx W mem (spZ regs) PF P).
{ unfold hd_l1_pfx. cbv zeta.
  split.
  { intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
    destruct (Z.lt_ge_cases t (Z.of_nat (length P))) as [Hlt|Hge].
    - rewrite (HPby t ltac:(lia)). do 2 f_equal. symmetry. apply app_nth1. lia.
    - assert (Ht' : t = Z.of_nat (length P)) by lia. subst t.
      rewrite HPnul. rewrite app_nth2 by lia.
      replace (Z.to_nat (Z.of_nat (length P)) - length P)%nat with 0%nat by lia. cbn [nth].
      rewrite (hd_u8 0 ltac:(lia)). reflexivity. }
  split; [intros a Ha; exact (proj1 (HPvis a Ha))|].
  split; [intros a Ha; pose proof (proj2 (HPvis a Ha)); unfold HP_STK, ESTACK in *; lia|].
  split; [exact HPmr1|]. split; [exact HPmr8|]. split; [exact HPra1|]. split; [exact HPshv1|].
  split; [eapply range_addressable_sub; [exact HPra1 | lia | lia]|].
  split; [intros Hp; exact (hd_shv_sub _ PF (Z.of_nat (length P) + 1) (Z.of_nat (length P))
            ltac:(lia) ltac:(lia) HPshv1)|].
  exact HROM. }
assert (HPFX : hd_l1_pfx W1 mem1 (spZ regs) PF P).
{ apply (hd_l1_pfx_kept2 W W1 mem mem1 (spZ regs) (spZ regs - 112) (spZ regs) PF P
    HCEIL HPF0 ltac:(lia) ltac:(intros y Hy Hno; exact (KEEP1 y Hy Hno))
    ltac:(intros y Hy; pose proof (proj2 (HPvis y Hy)); lia) HPFX0). }
(* loop 1's vector invariant at i = 0, likewise *)
assert (HVEC0 : hd_l1_vec ly S W mem (spZ regs) (hl_v (hs_held h)) P (hl_recs (hs_held h)) 0).
{ intros jj Hjj.
  assert (Hjn : (Z.to_nat jj < length (hl_recs (hs_held h)))%nat) by lia.
  assert (Hin : In (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) (hl_recs (hs_held h)))
    by (apply nth_In; exact Hjn).
  rewrite Forall_forall in HFrec. destruct (HFrec _ Hin) as (Hrin & Hrg & Hrlines & _).
  destruct (hd_blk ly S W mem md _ _ HAR Hrin)
    as (_ & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & _ & Hrapp & _).
  destruct (hd_rec_fields ly S W mem (HA + 80) (hs_held h) true (Z.to_nat jj) HHl Hjn) as [Mslot Mlen].
  destruct (Hrlines eq_refl) as (_ & Hrlen).
  assert (HEQ : hl_v (hs_held h) + 16 * Z.of_nat (Z.to_nat jj) = hl_v (hs_held h) + AREC * jj)
    by (unfold AREC; lia).
  rewrite HEQ in Mslot, Mlen.
  unfold hd_l1_rec. cbv zeta.
  split.
  { replace (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
    with (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) mod 2 ^ 64) by (apply Z.mod_small; lia).
    exact Mslot. }
  split.
  { replace (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))))
    with (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) mod 2 ^ 64)
    by (apply Z.mod_small; unfold APARTIAL in Hrlen; lia).
    exact Mlen. }
  split.
  { apply (range_addressable_of_block0 ly S W mem md (hl_v (hs_held h))
      (AREC * hl_cap (hs_held h)) (hl_v (hs_held h) + AREC * jj) 16 HAR Hvin);
    unfold AREC in *; unfold hl_n in *; lia. }
  split.
  { apply (amem_range_of_block0 ly S W mem md (hl_v (hs_held h))
      (AREC * hl_cap (hs_held h)) (hl_v (hs_held h) + AREC * jj) 16 HAR Hvin);
    unfold AREC in *; unfold hl_n in *; lia. }
  split.
  { intros a Ha. pose proof (HVoff a ltac:(unfold AREC in *; unfold hl_n in *; lia)).
    unfold HP_STK, ESTACK in *. lia. }
  split.
  { exists (hl_v (hs_held h)), (AREC * hl_cap (hs_held h)).
    split; [exact Hvin|]. split; [unfold AREC; lia | unfold AREC in *; unfold hl_n in *; lia]. }
  split; [lia|].
  split; [unfold APARTIAL in Hrlen; lia|].
  split; [apply hd_bytes_of_garr8; exact Hrg|].
  split.
  { intros a Ha. pose proof (HRoff _ Hin a ltac:(lia)).
    unfold HP_STK, ESTACK in *. lia. }
  intros Hle.
  split.
  { apply (amem_range_of_block0 ly S W mem md
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
      (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
  split.
  { apply (range_addressable_of_block0 ly S W mem md
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
      (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
      (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
  intros Hp.
  apply (shadow_hull_vis_of_block0 ly S W mem md
    (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))
    (Z.of_nat (length (snd (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])))) + 1)
    (fst (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, []))) (Z.of_nat (length P)) HAR Hrin); lia. }
assert (HVEC : hd_l1_vec ly S W1 mem1 (spZ regs) (hl_v (hs_held h)) P (hl_recs (hs_held h)) 0).
{ intros jj Hjj.
  assert (Hin : In (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) (hl_recs (hs_held h)))
    by (apply nth_In; lia).
  apply (hd_l1_rec_kept2 ly S W W1 mem mem1 (spZ regs) (spZ regs - 112) (spZ regs)
    (hl_v (hs_held h)) P (nth (Z.to_nat jj) (hl_recs (hs_held h)) (0, [])) jj HCEIL
    ltac:(unfold AREC; lia)
    ltac:(intros y Hy Hno; exact (KEEP1 y Hy Hno))
    ltac:(intros y Hy; pose proof (HVoff y ltac:(unfold AREC in *; unfold hl_n in *; lia)); lia)
    ltac:(intros y Hy; pose proof (HRoff _ Hin y ltac:(lia)); lia)
    (HVEC0 jj Hjj)). }
eapply SRr_bind.
{ apply (hd_l1_loop (Z.to_nat (hl_n (hs_held h))) 0 W1 ly S regs1 mem1 md1 ly S W mem md XO AT
    (blk_FP (list_blks (hs_held h))) (spZ regs) 0 PF P (hl_v (hs_held h)) (hl_n (hs_held h))
    (hl_recs (hs_held h)));
  [ lia | lia | exact HNn | exact HnH | exact HP32 | exact HPF0 | lia | exact HPnz
  | lia | unfold AREC in *; unfold hl_n in *; lia | exact Hv16
  | exact Q2
  | rewrite Q22; reflexivity
  | replace (hl_n (hs_held h) - 0) with (hl_n (hs_held h)) by lia; exact R24
  | replace (hl_v (hs_held h) + AREC * 0) with (hl_v (hs_held h)) by (unfold AREC; lia); exact R20
  | replace (hl_v (hs_held h) + AREC * 0 + 8) with (hl_v (hs_held h) + 8) by (unfold AREC; lia); exact R25
  | exact Q21 | exact R23 | exact R26 | exact Q8
  | rewrite Q3; exact Hgp | rewrite Q4; exact Htp
  | unfold s0Z; rewrite Q8; rewrite unsigned_lit_small by lia; lia
  | lia | ( apply Z.mod_divide in Hal16; [|lia]; apply Z.mod_divide; [lia|];
            apply Z.divide_sub_r; [exact Hal16 | exists 7; reflexivity] )
  | exact HXO16 | lia | exact HJ1 | exact HPFX | exact HVEC ]. }
cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJ2 & T22 & T2 & T3 & T4 & T8 & T9 & T18 & T19 & T21
  & T27 & KEEP2 & PRES2).
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CSHE_STK_B <= a < spZ regs) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
  rewrite (KEEP2 a Ha ltac:(unfold HP_STK, ESTACK in *; lia)).
  exact (KEEP1 a Ha ltac:(lia)). }
assert (SAVED2 : cshe_saved_B W2 mem2 (spZ regs) regs).
{ apply (hd_saved_kept W1 W2 mem1 mem2 (spZ regs) regs); [|exact SAVED1].
  intros a Ha. apply KEEP2; [lia | unfold HP_STK, ESTACK in *; lia]. }
apply (hd_fin W ly S regs mem md ch XO AT HA PF h P A0 gone ob W2 regs2 mem2 md2 kr HPRE HSRC Hlo Hhi HND HnH
  HATlo HAThi HXtop MAT Mg Rg HJ2 (wle_trans _ _ _ _ Hwle1 Hwle2)
  ltac:(rewrite T2; exact Q2) ltac:(rewrite T3; exact Q3) ltac:(rewrite T4; exact Q4) ltac:(rewrite T27; exact Q27)
  ltac:(rewrite T8; exact Q8) ltac:(rewrite T9; exact Q9) ltac:(rewrite T18; exact Q18)
  ltac:(rewrite T19; exact Q19) ltac:(rewrite T21; exact Q21) T22 SAVED2 KEEPB
  ltac:(intros a Hp; exact (PRES2 a (PRES1 a Hp))) HRM).
Qed.

(* the closure, printed into every build log: the Section variables (B, MT, G, LAWS, ML, HG, TL, HP and the
   contexts) and the axioms, to be checked against toolchain/allowed-axioms.txt *)
Print Assumptions cshe_hd_B.

End c.
End b.
End a.
