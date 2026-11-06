(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's check_no_loss,
   a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record)), after
   lib/A/W_check_no_loss.v (sha256 8817affe2a55; internal record) and lib/B/W_check_bounded.v (at
   7e062bb9b9c), with the image-B facts (frame, registers, trap sites) of the old-frame walk lib/B/Prog/check_no_loss.v
   (a working branch 0fafbcda68f). *)
(* check_no_loss(s, at) at 0x85e3c (image B; 0x85958 in A; fuzz_reply.c:405-432) checks, for each line the source s still
   expects, that the controller saw it, and feeds it to the reference model: while s->expected.n > 0 it takes the first
   expected text; when g_gone is clear it reads the stream's next line with next_line (cells at, &line = sp + 8,
   &len = sp + 0) and aborts unless it is that text (same length, same bytes by bcmp); then gesture_model(s, text, len);
   then list_drop(&s->expected, 0), which B calls OUT OF LINE (0x85fa4 jal list_drop 0x85b50; A inlines its free and
   memmove).  Frame 112: ra and s0..s10 at sp + 104 .. sp + 16.
   B's UBSan traps (trap mode in this pin, all to `unimp` at 0x86008), two kinds (lib/B/W_traps.v):
     null `beqz` of s at 0x85e70 and of v = s->expected.v at 0x85ed8 / 0x85f38 (trap_nonnull);
     8-alignment `andi r,x,7; bnez r` of s at 0x85e78-0x85e7c and of v at 0x85edc-0x85ee0 / 0x85f3c-0x85f40
     (trap_align8).
   They are refuted from the seat's atom facts (s = g_s[j] is 16-aligned and >= 0x10000; v is a live block's base,
   16-aligned and >= 4096, while n >= 1), which the runner reads; a branch the runner leaves open cites W_traps.v.
   Section hypotheses (what other lanes owe): those of lib/A/W_check_no_loss.v (sha256 8817affe2a55; internal record) -- LAWS, TL, HG,
   CNLAP, ML, HGR / HGRR, ROMNS, NL (next_line), GM (gesture_model, gm_spec_g), ABCMP (bcmp) -- less A's AMOVE / AFREE /
   ALDROP (A's inlined list_drop), plus:
     LDROP (B's out-of-line list_drop: W_contract.v ldrop_spec at the callee's G, in W1's pb_list_drop_ro form), and
     HRO (rom_out of g_s's 384 bytes: gm_spec_g and LDROP take rom_out at their G, a part of g_s; the instance,
     a vm_compute at PB_fr like gx_prog's).
   The walk is stated over a generic allocator relation (pb_check_no_loss_x : W_contract_x.cnl_spec_x, Section c,
   the callees at their B _x specs); pb_check_no_loss, statement unchanged, is its corollary at ARi0 (Section cAR,
   whose proof derives LX0 from LAWS). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep ListRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require next_line_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_tbl W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_img W_traps.
(* the sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) step 3): no sink instance is a hint; this file's sink is its Context SK *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
(* the room round's count and budget bookkeeping of this walk's loop (B's twin of lib/A/W_cnl_cnt.v) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_cnl_cnt.
(* the laws at ARi0 from cgif's laws (Section cAR's proof) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
(* route R: SRrG and the R contract texts (gesture_model and check_no_loss; list_drop) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6 W_contract_xR_g3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the model's side *)
(* The model's vocabulary (capstep, capb, tbytes, hbytes, cnl_cap, cnl_room, txs, bsr, cpos) is the kit's, generated with
   check_no_loss's contract (lib/B/W_contract.v, before Section w3n). *)
Lemma cn_filter_len_aux : forall (T : list (list Z)) x, (length (List.filter (fun y => negb (RelayModel.list_eqb x y)) T) <= length T)%nat.
Proof. intros T x. induction T as [|y T IH]; cbn [List.filter length]; [lia|]. destruct (negb (RelayModel.list_eqb x y)); cbn [length]; lia. Qed.
(* The pure facts the walk uses about the model. *)
Lemma txs_app : forall a b, txs (a ++ b) = txs a ++ txs b.
Proof. intros a b. unfold txs. apply map_app. Qed.
Lemma upds_snoc : forall T a r, RelayModel.upds T (txs (a ++ [r])) = RelayModel.upd (RelayModel.upds T (txs a)) (bzs (snd r)).
Proof. intros T a r. unfold RelayModel.upds. rewrite txs_app, fold_left_app. reflexivity. Qed.
Lemma cnl_cap_snoc : forall T c a r, cnl_cap T c (a ++ [r]) =
capstep (RelayModel.upds T (txs a)) (bzs (snd r)) (cnl_cap T c a).
Proof. intros T c a. revert T c. induction a as [|x a IH]; intros T c r; [reflexivity|]. cbn [app cnl_cap]. rewrite IH. reflexivity. Qed.
Lemma cnl_room_snoc : forall MMAX bb T c a r rs, cnl_room MMAX bb T c (a ++ r :: rs) -> exists bb',
cnl_room MMAX bb' (RelayModel.upds T (txs a)) (cnl_cap T c a) (r :: rs).
Proof.
intros MMAX bb T c a. revert bb T c. induction a as [|x a IH]; intros bb T c r rs H; [exists bb; exact H|].
cbn [app cnl_room] in H. destruct H as (_ & _ & H). destruct (IH _ _ _ r rs H) as (bb' & H'). exists bb'. exact H'.
Qed.
Lemma bzs_length : forall l, length (bzs l) = length l.
Proof. intros l. unfold bzs. apply length_map. Qed.
Lemma tbytes_app : forall a b, tbytes (a ++ b) = tbytes a + tbytes b.
Proof. intros a b. unfold tbytes. induction a as [|x a IH]; cbn [app fold_right]; lia. Qed.
Lemma bsum_recs : forall rs : list (Z * list byte),
bsum (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) rs) = tbytes (map (fun r => bzs (snd r)) rs).
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map]. rewrite bsum_cons, IH. unfold tbytes. cbn [fold_right snd].
rewrite bzs_length. lia.
Qed.
Lemma bsum_list_blks : forall l, bsum (list_blks l) = hbytes (texts l) (hl_cap l).
Proof.
intros l. unfold list_blks, hbytes, texts. rewrite bsum_app, bsum_recs. f_equal.
destruct (hl_cap l =? 0); cbn [bsum fold_right snd]; lia.
Qed.
(* the drop of the first record: its text's block leaves the list's blocks *)
Lemma list_blks_drop0 : forall v cap r rs jk jk',
Permutation (list_blks (HL v cap (r :: rs) jk)) ((fst r, Z.of_nat (length (snd r)) + 1) :: list_blks (HL v cap rs jk')).
Proof.
intros v cap r rs jk jk'. unfold list_blks. cbn [hl_cap hl_v hl_recs map]. apply Permutation_sym, Permutation_middle.
Qed.
(* a duplicate-free list inside another is a part of it *)
Lemma perm_of_incl : forall (l L : list (Z * Z)), List.NoDup l -> incl l L -> exists rest, Permutation L (l ++ rest).
Proof.
induction l as [|x l IH]; intros L ND Hi; [exists L; reflexivity|].
apply List.NoDup_cons_iff in ND as [Hx NDl].
assert (Hin : In x L) by (apply Hi; left; reflexivity).
apply in_split in Hin as (L1 & L2 & ->).
destruct (IH (L1 ++ L2) NDl) as (rest & HP).
{ intros y Hy. assert (Hy' : In y (L1 ++ x :: L2)) by (apply Hi; right; exact Hy).
  apply in_app_or in Hy' as [Hy' | [<- | Hy']]; [apply in_or_app; left; exact Hy' | exfalso; exact (Hx Hy) | apply in_or_app; right; exact Hy']. }
exists rest. rewrite <- Permutation_middle. cbn [app]. apply perm_skip. exact HP.
Qed.
(* the held list's length after one line: at most one more, and one more exactly when the line begins a key *)
Lemma upd_len : forall T l, (length (RelayModel.upd T l) <= S (length T))%nat /\
((length T < length (RelayModel.upd T l))%nat -> is_begin l = true /\ length (RelayModel.upd T l) = S (length T)).
Proof.
intros T l. unfold RelayModel.upd, is_begin. destruct (RelayModel.gesture l) as [[g x]|]; [destruct g|].
- destruct (existsb (RelayModel.list_eqb x) T); [split; [lia | intros H; lia]|]. rewrite length_app. cbn [length].
  split; [lia | intros _; split; [reflexivity | lia]].
- pose proof (cn_filter_len_aux T x) as Hf. split; [lia | intros H; lia].
- split; [lia | intros H; lia].
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_check_no_loss : Z := AF_fr_check_no_loss.
Definition A_check_no_lossP : Z := BASE + A_check_no_loss.

(* ================================================================== THE STATEMENT BLOCK
   check_no_loss's contract is the kit's: lib/B/W_contract.v Section w3n (cnl_post, cnl_spec, cnl_objs_apart, cnl_ro,
   CNL_FRAME, CNL_STK, the meter gmc / cnl_go / cnl_cost), generated by mkbkit.py (sha256 999741ae2b33; internal record) from the shared text, and
   its generic twin lib/B/W_contract_x.v Section w3n (cnl_post_x, cnl_spec_x).
   ARx conversion (route (b); the template is lib/A/W_check_no_loss.v on a working branch e3e586a3b09):
   The room round (ROOM-TEXTS.md v3 (sha256 767baa12f13c; internal record), A's F8 at 6d7aa300374): the spec carries
   the room record RP; the loop keeps the room budget (gesture_model's MT_rk charge and list_drop's one free per
   record still owed, W_cnl_cnt.v cnl_rk_step) and the live counts plus the peak of the plain model's trace still owed
   (W_cnl_cnt.v cnl_cnt / cnl_cntm), which give gesture_model's and list_drop's room and count premises at each call;
   the held list's capacity conjuncts come from the loop's exact capacity law and W_cnl_cnt.v cnl_cap_ge.
   Section c proves pb_check_no_loss_x : cnl_spec_x over a generic allocator relation ARx with the laws LAWS
   (YCbqG.AR_laws_x) and HP0 (every ghost list is []), the callees at their B _x specs (W_contract_x nl_spec_x,
   gm_spec_g_x, ldrop_spec_x; W_sites_x abcmp_realizes_x), plus three facts the generic relation does not carry by
   itself: IMGC (the image's cover, for cnl_blk_off_img), BLKN (a block's size is >= 0, cgif's al_blocks' last
   conjunct) and HPST (the image is off PST, for W_journal_x.ajournal_gx_rom_view_x).  HP0 makes every ghost list of
   the walk empty, so the walk below runs at Hp = []: AR0 / AJ0 / AFP0 (local notations) are cgif's AR / journal /
   afn_pre at [], and each kit lemma the AR walk cited is its _x twin at [] (the ..0 notations).  Section cAR
   re-derives pb_check_no_loss, statement unchanged, at ARx := W_journal_x.ARi0, PST := [] through W_contract_x
   cnl_spec_x_AR0.
   This file adds the Section hypotheses of Section c: those of lib/A/W_check_no_loss.v less A's AMOVE / AFREE /
   ALDROP (B's list_drop is a call), plus LDROP and HRO.  cnl_spec's last premise, the caller's stack readable above
   sp, is what B's walk needs: B keeps `at` in s0 across its calls (0x85e80 mv s0,a1), and each callee's afn_pre walks
   the frame-pointer chain from s0 (achain, Reusable/YCbq.v; fpchain, Reusable/YG00.v). *)
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): cnl_spec_x's room record *)
Variable RP : roomp.
Variable G : list (Z * Z).
Variable MMAX : Z.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* the image's cover (W_kit_x.blk_off_imgP_x's premise, here cnl_blk_off_img's; at ARi0: W_kit_x.AR_imgc) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
(* cgif's al_blocks' size conjunct, which ARx_blocks_law does not state (at ARi0: W_kit_x.AR_blkn) *)
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
(* the image is off the placement PST: a journal's kept-bytes clause keeps a byte only outside PST (at PST = []) *)
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
(* No gx_rt of the caller's G: G_fr / G_SL hold errno, so it could never be discharged (W5, 2026-10-29). *)
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
(* An image read-only byte is not errno, and, if the runtime owns it, it is pinned to its image value (rom_pinned,
   W_journal.v; owned .rodata ranges lie inside image A's read-only LOAD, so `~ owned` was false). *)
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
(* B only: list_drop is a call (0x85fa4 jal list_drop 0x85b50), taken at the callee's own G (s->expected's head), in
   the form of W1's pb_list_drop_ro (lib/A/W_list_drop_top.v) and lib/A/W_gesture_model_g.v's LDROP_RO; B's
   list_drop walk (a Theorem Labs lane) discharges it. *)
Hypothesis LDROP : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_x B PST ARx MT RP G0 (BASE + AF_fr_list_drop).
(* B only: the two callees above take rom_out at their G, a part of g_s (W_journal.v rom_out: no ROM byte in G, the
   owned ROM bytes pinned, no ROM byte errno or the sink's overflow head); the instance, a vm_compute at PB_fr. *)
Hypothesis HRO : rom_out SEGS B [(VAL A_g_s, 384)].
(* ================================================================== END OF THE STATEMENT BLOCK *)
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* ------------------------------------------------------------------ the walk at the empty ghost list
   HP0: every ARx state's ghost list is [], so the walk runs at Hp = []: AR0 is cgif's AR, AJ0 its journal at G,
   AFP0 its afn_pre; each kit lemma the AR walk cites is its _x twin at [] *)
Local Notation AR0 ly S W mem md := (ARx ly S [] W mem md).
Local Notation AJ0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_x SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation AFP0 STK ly S W regs mem md ch := (afn_pre_x SEGS B ARx STK ly S [] W regs mem md ch).
(* a ghost list read off an ARx fact, or off a journal's last state, is [] *)
Ltac hp0a H := let E := fresh "EHp" in pose proof (HP0 _ _ _ _ _ _ H) as E;
  lazymatch type of E with ?h = [] => subst h end.
Ltac hp0g HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation ajournal_gx_AR0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_AR_x SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_inner0 G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_inner_x SEGS B PST ARx G XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_G_mono0 G G' XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k :=
  (ajournal_gx_G_mono_x SEGS B PST ARx G G' XO OUT STK sp0 FP ly S [] W mem md own ly' S' [] W' mem' md' k).
Local Notation ajournal_gx_sub0 Hs G STK sp0 XO0 OUT0 FP ly S W mem md own lyc Sc Wc memc mdc k
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_x SEGS B PST ARx LAWS Hs G STK sp0 XO0 OUT0 FP ly S [] W mem md own lyc Sc [] Wc memc mdc k
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation ajournal_gx_init0 G XO OUT STK FP ly S W regs mem md ch :=
  (ajournal_gx_init_x SEGS B PST ARx G XO OUT STK FP ly S [] W regs mem md ch).
Local Notation afn_pre_at0 STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 :=
  (afn_pre_x_at SEGS B PST ARx STK sp0 FP ly S [] W0 mem md own lyc Sc [] W memc mdc k regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0 pc Hpc G XO OUT W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k x y n o raw :=
  (aj_bcmp_gx_at_x B PST ARx LAWS pc Hpc G XO OUT W regsT memT STK sp0 FP ly S [] W0 mem md own lyc Sc [] mdc k x y n o
     raw).
Local Notation range_addressable_of_block0 ly S W mem md :=
  (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation shadow_hull_vis_of_block0 ly S W mem md :=
  (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S [] W mem md).
Local Notation sep_blocks0 ly S W mem md := (sep_blocks_x SEGS B ARx LAWS ly S [] W mem md).
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
(* W_kit_x.blk_off_imgP_x's proof, at this file's off_img (lib/B/YCbq.v: IMG_TOP_B = 0x5fc000, image B's own top;
   the kit's lemma states the shared core's off_img, at IMG_TOP_A) *)
Lemma cnl_blk_off_img : forall ly S (W : world SEGS) mem md p n,
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
(* W_journal.v ajournal_gx_rom_view at AJ0: W_journal_x's, whose ROM-off-PST premise HPST gives *)
Lemma ajournal_gx_rom_view0 : forall G0 XO0 OUT0 STK sp0 FP ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS)
    mem' md' k,
  AJ0 G0 XO0 OUT0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  rom_out SEGS B G0 -> rom_view SEGS W mem -> rom_view SEGS W' mem'.
Proof.
  intros G0 XO0 OUT0 STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_x SEGS B PST ARx LAWS pa_segs_low G0 XO0 OUT0 STK sp0 FP ly S [] W mem md own ly' S' []
    W' mem' md' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* REMARK (B's drop is a call).  B calls list_drop out of line (0x85fa4 jal list_drop 0x85b50) where A inlines its free
   and memmove, so B replaces A's AFREE / AMOVE / ALDROP by the one hypothesis LDROP (ldrop_spec, B W_contract.v), and
   B's drop step (cnl_drop and cnl_test below) does NOT depend on A's cnl_drop, still open (not Qed) at
   the cited version (lib/A/W_check_no_loss.v sha256 8817affe2a55; internal record).  The listing word at 0x85fa4 is that jal: *)
Remark cnl_b_drop_is_a_call : plookup fr_prog_tpi (AF_fr_check_no_loss + 0x168) = Some (PW 0xbadff0ef).
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ the walk *)
(* The vector's records as 8-byte cells: W1's garr8_val_mem8 / text_recs_length / alist_rec_fields
   (lib/A/W_list_find.v:49-98 on a working branch), as lib/A/W_check_no_loss.v copies them. *)
Lemma cnl_garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
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
Lemma cnl_text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
Lemma cnl_rec_fields : forall ly S W mem LA l lines j,
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
apply garr8_app in Hg as [_ Hg]. rewrite length_map, cnl_text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 Hg]. apply garr8_app in Hg as [H2 _].
rewrite length_map, length_N_to_le_bytes in H2.
apply cnl_garr8_val_mem8 in H1. apply cnl_garr8_val_mem8 in H2.
rewrite Z_to_bv_unsigned in H1, H2. unfold bv_wrap in H1, H2. change (bv_modulus 64) with (2 ^ 64) in H1, H2.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1, H2 by lia.
split; [exact H1|]. replace (HarnessRep.hl_v l + 16 * Z.of_nat j + 8) with (HarnessRep.hl_v l + 16 * Z.of_nat j + Z.of_nat 8) by lia.
exact H2.
Qed.

(* ------------------------------------------------------------------ one placement of the out-parameter window *)
Section d.
Variable XO : Z. Variable AT : Z.
Let RUN := paj_run_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG XO [(AT, AT + 8)].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* The source's address: g_s[j], 16-aligned, in the image, apart from the objects the walk reads. *)
Lemma cnl_ha : forall HA (j : nat), HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) ->
0x10000 <= HA /\ HA + 96 <= 0x5fc000 /\ HA mod 8 = 0 /\ HA mod 16 = 0 /\
(VAL A_g_gone + 1 <= HA + 64 \/ HA + 96 <= VAL A_g_gone) /\
(VAL (A_OBJ 0) + 8 <= HA + 64 \/ HA + 96 <= VAL (A_OBJ 0)) /\ (VAL (A_OBJ 30) + 8 <= HA + 64 \/ HA + 96 <= VAL (A_OBJ 30)).
Proof.
intros HA j EHA Hj HGa.
pose proof CNLAP as (A16 & A1 & _ & _ & A4 & A5 & _). cbv zeta in A16, A1, A4, A5.
pose proof (pa_obj_img 19 ltac:(lia)) as Hs. change (A_OBJ 19) with A_g_s in Hs.
pose proof (pa_img_range (HA + 95) (proj1 (HG (HA + 95) (HGa (HA + 95) ltac:(lia))))) as Hi.
assert (Hm : HA mod 16 = 0).
{ rewrite EHA. unfold ASRC. rewrite Z.add_mod, A16 by lia. cbn [Z.add].
  replace (96 * Z.of_nat j) with ((6 * Z.of_nat j) * 16) by lia. rewrite Z_mod_mult. reflexivity. }
assert (Hm8 : HA mod 8 = 0).
{ apply Z.mod_divide in Hm; [|lia]. apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hm]. }
unfold ASRC in EHA. split; [lia|]. split; [lia|]. split; [exact Hm8|]. split; [exact Hm|].
split; [destruct A1; lia|]. split; [destruct A4; lia | destruct A5; lia].
Qed.
(* What AR says of a live block, in the form the walk uses. *)
Lemma cnl_blk : forall ly S W mem md p n, AR0 ly S W mem md -> In (p, n) (ablocks B ly S) ->
p mod 16 = 0 /\ 4096 <= p /\ 0 <= n /\ n <= req_size n /\ 1 <= req_size n /\ p + req_size n <= alloc_ceiling /\
alloc_ceiling <= 0x7fffff800000 /\ off_img p (req_size n) /\ in_app p (req_size n) /\
(forall a, p <= a < p + req_size n -> apresent (w_H W) mem a /\ ~ aowned B ly S a).
Proof.
intros ly S W mem md p n HAR Hin.
destruct (al0_blocks ly S W mem md p n HAR Hin) as (H16 & H4096 & Hc & Hia & Hpr & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R1 R2]. pose proof asan_consts as (C1 & _).
pose proof (cnl_blk_off_img _ _ _ _ _ p n HAR Hin) as Hoff.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hoff|]. split; [exact Hia|]. exact Hpr.
Qed.
(* the entry 0x85e3c: the frame, the GOT slot and the shadow cell, and s->expected's head (v at +64, n at +72).
   The atom fact of s (atom 10: >= 0x10000, 16-aligned) is what settles the two entry traps (0x85e70 beqz,
   0x85e78-0x85e7c andi/bnez) inside the runner. *)
Definition Bx : sv := SOff 32 0.
Definition cnl_head : YP09.region :=
YP09.mkRegion (Some 10%nat) 64 80 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 4 (SOff 34 0))].
Definition cnl_regions : smem := [ stack_region CNL_FRAME; got_regionP; bcell_regionP 32; cnl_head ].
Definition cnl_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 0x5fc000 4); (32%nat, mkAF SB SB 0);
(33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cnl : sstate := mkSS A_check_no_loss sr_atoms cnl_regions None cnl_facts.
Definition cnl_SH : list shent := [ mkSHE 10 64 80 ].
Definition cnl_extra (v n : Z) : list word := map (Z_to_bv 64) [SB; v; n].
Lemma cnl_entry : forall W ly S regs mem md ch HA (j : nat) E,
AFP0 CNL_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
alist_at B ly S W mem (HA + 64) E true -> hl_n E < 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))) ss_cnl
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_no_lossP) mem (seg_rom SEGS)))
/\ sh_ok SEGS Bx cnl_SH (Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))) (mrestrict (w_H W) mem).
Proof.
intros W ly S regs mem md ch HA j E HPRE H10 EHA Hj HGa Hzs HE HnE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
destruct (alx_const _ _ _ LAWS ly S [] W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof HE as (Mv & Mn & _ & _ & (Hnc & _) & _).
assert (Rv : 0 <= hl_v E < 2 ^ 64).
{ destruct HE as (_ & _ & _ & _ & _ & [(_ & ->) | (_ & Hin & _)] & _); [lia|].
  destruct (cnl_blk ly S W mem md _ _ HAR Hin) as (_ & H4096 & _ & _ & Hr1 & Hc & CC & _). lia. }
assert (Rn : 0 <= hl_n E) by (unfold hl_n; lia).
rewrite restrict_mkst_fx.
set (Ev := Eimg (Ereg regs (cnl_extra (hl_v E) (hl_n E)))). pose proof pa_B_ok as HBASE.
assert (E2 : ew Ev 2 = getr regs 2) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v E)) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n E)) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (EO : forall i, (i < 31)%nat -> ew Ev (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst Ev; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew Ev m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val Ev (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 31)%nat -> base_val Ev (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold ss_cnl, A_check_no_lossP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold cnl_regions, stack_region, got_regionP, bcell_regionP, cnl_head.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. unfold CNL_FRAME. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Ev _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite (EO 30%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 30%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS Ev _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat HA E10) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS Ev _ HA 64 8 (SOff 33 0) (hl_v E));
   [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
-- apply (chunk_ok_val SEGS Ev _ HA 72 4 (SOff 34 0) (hl_n E));
   [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
   replace (HA + 72) with (HA + 64 + 8) by lia. exact Mn.
+ apply pairwise_disjoint_of_extents. unfold cnl_regions, stack_region, got_regionP, bcell_regionP, cnl_head, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VBO 0%nat ltac:(lia)), (VBO 30%nat ltac:(lia)), (VB 10%nat HA E10) by lia. cbn [base_val]. rewrite Usp.
unfold CNL_FRAME. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HAlo HAhi Dgot Dcell. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [cnl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HAlo HAhi HA16 Rv Rn HnE. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnl_SH. constructor; [|constructor].
eapply shent_ok_of_range.
+ apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md (HA + 64) 32 HAR Hzs).
+ unfold Bx. rewrite (U_atom Ev 32 SB E32) by (unfold SB; lia). reflexivity.
+ rewrite (U_atom Ev 10 HA E10) by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* the loop head 0x85ec4 (B; A's 0x859dc) and the return point 0x85f9c of gesture_model: s1 = s, s0 = at,
   s2 = s + 72, s3 = s + 64, s6 = SB, s7 / s9 the shadow cells of s + 72 / s + 64, s8 = the page of g_gone
   (auipc 0x553 at 0x85eb0: A_HI 104, 0x5d8eb0); s4, s5 (len and line of the last next_line arm) and s10
   (the shadow-check bound ((s + 72) & 7) + 3, read only on the slow path the shadow facts refute) are free; the
   frame holds the caller's ra and s0..s10 at sp + 104 .. sp + 16. *)
Definition A_cnl_loop : Z := AF_fr_check_no_loss + 0x88.
Definition A_cnl_back : Z := AF_fr_check_no_loss + 0x160.
Definition BxL : sv := SOff 22 0.
Definition cnl_sr : list sv :=
sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 18 (SOff 9 72)) 19 (SOff 9 64))
  23 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 72) (SLit 3)) (SOff 22 0)))
  24 (SOff (A_HI 104) 0)) 25 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 64) (SLit 3)) (SOff 22 0)).
Definition cnl_saved : YP09.region := YP09.mkRegion (Some 2%nat) 16 112 0 0
[YP09.mkChunk 16 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 32 (CVal 8 (SOff 39 0));
 YP09.mkChunk 40 (CVal 8 (SOff 40 0)); YP09.mkChunk 48 (CVal 8 (SOff 41 0)); YP09.mkChunk 56 (CVal 8 (SOff 42 0));
 YP09.mkChunk 64 (CVal 8 (SOff 43 0)); YP09.mkChunk 72 (CVal 8 (SOff 44 0)); YP09.mkChunk 80 (CVal 8 (SOff 45 0));
 YP09.mkChunk 88 (CVal 8 (SOff 46 0)); YP09.mkChunk 96 (CVal 8 (SOff 47 0)); YP09.mkChunk 104 (CVal 8 (SOff 48 0))].
Definition cnl_gone : YP09.region := YP09.mkRegion (Some A_g_gone) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition cnl_headL : YP09.region :=
YP09.mkRegion (Some 9%nat) 64 80 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 72 (CVal 4 (SOff 34 0))].
Definition cnl_vec : YP09.region :=
YP09.mkRegion (Some 33%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0)); YP09.mkChunk 8 (CVal 8 (SOff 36 0))].
Definition cnl_lregions : smem := [ cnl_saved; cnl_gone; cnl_headL; cnl_vec ].
(* the seat's atom facts: every pointer atom (s, v, v[0].s) with a lower bound, an upper bound and its alignment, so
   that the runner settles the per-pass traps on v (0x85ed8 / 0x85edc-0x85ee0, 0x85f38 / 0x85f3c-0x85f40) itself *)
Definition cnl_lfacts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0x10000 0x5fc000 4); (22%nat, mkAF SB SB 0);
(32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 0x7fffff800000 4); (34%nat, mkAF 1 (2 ^ 26) 0);
(35%nat, mkAF 4096 0x7fffff800000 4); (36%nat, mkAF 0 6000 0) ] [] [].
Definition ss_cnll (pc : Z) : sstate := mkSS pc cnl_sr cnl_lregions None cnl_lfacts.
Definition cnl_lSH : list shent := [ mkSHE 9 64 80; mkSHE 33 0 16 ].
(* The caller's s10..s0 and ra, as the prologue saved them at sp + 16 .. sp + 112 (sp the loop's sp). *)
Definition CNL_SAVED : list (bv 5) := [26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition cnl_svals (regs0 : bvmap 5 word) : list Z := map (fun r => bv_unsigned (getr regs0 r)) CNL_SAVED.
Definition cnl_frame_ok (W : world SEGS) (mem : word -> option byte) (sp0 : Z) (regs0 : bvmap 5 word) : Prop :=
forall i, (i < 12)%nat -> val_mem SEGS (arm W mem) (sp0 - 96 + 8 * Z.of_nat i) 8 (nth i (cnl_svals regs0) 0).
(* The loop's registers (regs0 the entry registers): s11, which B does not save, is the caller's. *)
Definition cnl_regs_ok (regs regs0 : bvmap 5 word) (HA : Z) : Prop :=
getr regs 2 = w64 (spZ regs0 - 112) /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 8 = w64 AT /\ getr regs 9 = w64 HA /\ getr regs 18 = w64 (HA + 72) /\ getr regs 19 = w64 (HA + 64) /\
getr regs 22 = w64 SB /\ getr regs 23 = w64 ((HA + 72) / 8 + SB) /\ getr regs 24 = w64 (VAL (A_HI 104)) /\
getr regs 25 = w64 ((HA + 64) / 8 + SB) /\ getr regs 27 = getr regs0 27.
Definition cnl_lx (gone v n s0 n0 : Z) (sv : list Z) : list word := map (Z_to_bv 64) ([gone; v; n; s0; n0] ++ sv).
Lemma U_shadow_reg : forall E m bx c x, ew E m = Z_to_bv 64 x -> ew E bx = Z_to_bv 64 SB -> 0 <= x < 2 ^ 63 -> x + c < 2 ^ 63 -> 0 <= x + c ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff bx 0)) = Z_to_bv 64 ((x + c) / 8 + SB).
Proof.
intros E m bx c x Hm H22 Hx Hc Hc0. apply bv_eq.
fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff m c) (SLit 3)) (SOff bx 0))).
rewrite !U_SAlu, (U_atom_off E m x c Hm) by lia. rewrite (U_atom E bx SB H22) by (unfold SB; lia). rewrite U_lit by lia.
cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
assert (D : 0 <= (x + c) / 8 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite unsigned_lit_small by (unfold SB; lia).
rewrite Z.mod_small by (unfold SB; lia). reflexivity.
Qed.
Lemma cnl_chunk_saved : forall E (m : word -> option byte) base sp0 regs0 k (o : Z),
(37 <= k < 49)%nat -> o = 16 + 8 * (Z.of_nat k - 37) -> base = sp0 - 112 ->
ew E k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0) ->
(forall i, (i < 12)%nat -> val_mem SEGS m (sp0 - 96 + 8 * Z.of_nat i) 8 (nth i (cnl_svals regs0) 0)) ->
YP09.chunk_ok SEGS E m base (YP09.mkChunk o (CVal 8 (SOff k 0))).
Proof.
intros E m base sp0 regs0 k o Hk -> -> Hek Hf.
assert (Hr : 0 <= nth (k - 37) (cnl_svals regs0) 0 < 2 ^ 64).
{ unfold cnl_svals. destruct (Nat.lt_ge_cases (k - 37) (length (map (fun r => bv_unsigned (getr regs0 r)) CNL_SAVED))) as [Hl|Hl].
  - pose proof (nth_In _ 0 Hl) as Hin. apply in_map_iff in Hin as (r & <- & _). apply bv_unsigned_in_range.
  - rewrite nth_overflow by exact Hl. lia. }
apply (chunk_ok_val SEGS E m (sp0 - 112) (16 + 8 * (Z.of_nat k - 37)) 8 (SOff k 0) (nth (k - 37) (cnl_svals regs0) 0));
[cbn [sv_denot]; rewrite Hek, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | exact Hr | lia |].
replace (sp0 - 112 + (16 + 8 * (Z.of_nat k - 37))) with (sp0 - 96 + 8 * Z.of_nat (k - 37)) by lia.
apply Hf. lia.
Qed.
(* The loop's symbolic state at pc (the head, or the return point of gesture_model), from the facts the loop keeps. *)
Lemma cnl_mk : forall pc W ly S mem md regs regs0 HA gone v n s0 n0 N0,
AR0 ly S W mem md ->
cnl_regs_ok regs regs0 HA ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + 112 <= spZ regs0 <= 2 ^ 47 ->
0x10000 <= HA -> HA + 96 <= 0x5fc000 -> HA mod 16 = 0 -> (VAL A_g_gone + 1 <= HA + 64 \/ HA + 96 <= VAL A_g_gone) ->
azs B (HA + 64) 32 ->
cnl_frame_ok W mem (spZ regs0) regs0 ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (HA + 64) 8 v -> val_mem SEGS (arm W mem) (HA + 72) 4 n -> 1 <= n <= 2 ^ 26 ->
In (v, N0) (ablocks B ly S) -> 16 <= req_size N0 ->
val_mem SEGS (arm W mem) v 8 s0 -> val_mem SEGS (arm W mem) (v + 8) 8 n0 ->
4096 <= s0 <= 0x7fffff800000 -> s0 mod 16 = 0 -> 0 <= n0 <= 6000 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))) (ss_cnll pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxL cnl_lSH (Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))) (mrestrict (w_H W) mem).
Proof.
intros pc W ly S mem md regs regs0 HA gone v n s0 n0 N0 HAR HR Hal Hsp HAlo HAhi HA16 Dgn Hzs Hfr Mg Rg Mv Mn Rn
Hvin Hv16 Ms0 Mn0 Rs0 Hs016 Rn0.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
destruct (cnl_blk ly S W mem md v N0 HAR Hvin) as (Hv0 & Hv4096 & _ & _ & Hvr1 & Hvc & _ & Hvoff & Hvapp & _).
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
rewrite restrict_mkst_fx.
set (Ev := Eimg (Ereg regs (cnl_lx gone v n s0 n0 (cnl_svals regs0)))). pose proof pa_B_ok as HBASE.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 17)%nat -> ew Ev (32 + j) = nth j (cnl_lx gone v n s0 n0 (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros j Hj. subst Ev. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E33 : ew Ev 33 = Z_to_bv 64 v) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew Ev 34 = Z_to_bv 64 n) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 s0) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 n0) by exact (EX 4%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 49)%nat -> ew Ev k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (subst Ev; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall m w, ew Ev m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val Ev (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsp2 : base_val Ev (Some 2%nat) = spZ regs0 - 112) by (apply VB; [exact E2 | lia]).
assert (Hsp9 : base_val Ev (Some 9%nat) = HA) by (apply VB; [exact E9 | lia]).
assert (Hsp33 : base_val Ev (Some 33%nat) = v) by (apply VB; [exact E33 | lia]).
assert (Hspg : base_val Ev (Some A_g_gone) = VAL A_g_gone) by (apply VB; [exact Eg | exact (pa_val_range _)]).
split.
- unfold ss_cnll. apply pa_entry_st_ok_full.
  + unfold cnl_sr.
    apply regs_ok_pin; [| discriminate | rewrite R25, (U_shadow_reg Ev 9 22 64 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R24; cbn [sv_denot]; subst Ev; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia);
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R23, (U_shadow_reg Ev 9 22 72 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R19; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R18; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cnl_lregions, cnl_saved, cnl_gone, cnl_headL, cnl_vec.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite Hsp2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal 8 (SOff ?k 0))) =>
        apply (cnl_chunk_saved Ev _ _ (spZ regs0) regs0 k); [lia | reflexivity | reflexivity | apply ES; lia | exact Hfr] end.
    * rewrite Hspg. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS Ev _ (VAL A_g_gone) 0 1 (SOff 32 0) gone);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Mg.
    * rewrite Hsp9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS Ev _ HA 64 8 (SOff 33 0) v);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
      -- apply (chunk_ok_val SEGS Ev _ HA 72 4 (SOff 34 0) n);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
    * rewrite Hsp33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS Ev _ v 0 8 (SOff 35 0) s0);
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Ms0.
      -- apply (chunk_ok_val SEGS Ev _ v 8 8 (SOff 36 0) n0);
         [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn0].
  + apply pairwise_disjoint_of_extents. unfold cnl_lregions, cnl_saved, cnl_gone, cnl_headL, cnl_vec, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Hsp2, Hspg, Hsp9, Hsp33.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp C1 HgR HAlo HAhi Dgn Hv4096 Hvc Hvr1 Hv16 Hvoff. clear.
    unfold off_img. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cnl_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E22, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hsp16 : (spZ regs0 - 112) mod 16 = 0).
    { rewrite Zminus_mod, Hal. reflexivity. }
    revert Hsp C1 Hsp16 HAlo HAhi HA16 Rg Hv4096 Hvc Hvr1 Hv0 Rn Rs0 Hs016 Rn0. clear.
    unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
  + eapply shent_ok_of_range.
    * apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md (HA + 64) 32 HAR Hzs).
    * unfold BxL. rewrite (U_atom Ev 22 SB E22) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom Ev 9 HA E9) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold SHADOW_OFF in *. lia.
  + eapply shent_ok_of_range.
    * apply (range_addressable_of_block0 ly S W mem md v N0 v 16 HAR Hvin); lia.
    * unfold BxL. rewrite (U_atom Ev 22 SB E22) by (unfold SB; lia). reflexivity.
    * rewrite (U_atom Ev 33 v E33) by lia. reflexivity.
    * lia.
    * lia.
    * intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.
(* ------------------------------------------------------------------ B only: the frame-pointer chain from s0 = at *)
(* B keeps `at` in s0 across its calls, and each callee's afn_pre asks the frame-pointer chain the unwinder walks
   from s0 (achain, Reusable/YCbq.v; fpchain, Reusable/YG00.v).  Over a readable stack that chain exists: from each
   frame pointer it reads the saved ra and the next frame pointer, and it strictly rises below ly_top. *)
Lemma cnl_aview_nonneg : forall (W1 : world SEGS) m x v, aview SEGS (w_H W1) m x = Some v -> 0 <= v.
Proof.
intros W1 m x v H. unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W1) m) x) as [b|]; [|discriminate].
cbn [option_map] in H. injection H as <-. apply bv_unsigned_in_range.
Qed.
Lemma cnl_rdword_nonneg : forall (rd : reader) a w, (forall x v, rd x = Some v -> 0 <= v) -> rdword rd a = Some w -> 0 <= w.
Proof.
intros rd a w Hn H. unfold rdword in H.
destruct (rd a) as [b0|] eqn:E0; [|discriminate]. destruct (rd (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|discriminate]. destruct (rd (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|discriminate]. destruct (rd (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|discriminate]. destruct (rd (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection H as <-.
pose proof (Hn _ _ E0). pose proof (Hn _ _ E1). pose proof (Hn _ _ E2). pose proof (Hn _ _ E3).
pose proof (Hn _ _ E4). pose proof (Hn _ _ E5). pose proof (Hn _ _ E6). pose proof (Hn _ _ E7). lia.
Qed.
Lemma cnl_rdword_some : forall (rd : reader) a, (forall k, 0 <= k < 8 -> rd (a + k) <> None) -> exists w, rdword rd a = Some w.
Proof.
intros rd a H. unfold rdword.
assert (H0 : rd a <> None) by (replace a with (a + 0) by lia; apply H; lia).
destruct (rd a) as [b0|]; [|exfalso; exact (H0 eq_refl)].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (H 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (H 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (H 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (H 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (H 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (H 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (H 7 ltac:(lia) E7)].
eexists. reflexivity.
Qed.
Lemma cnl_fpchain_ex : forall (rd : reader) top (n : nat) fp,
(forall x v, rd x = Some v -> 0 <= v) -> (Z.to_nat (top - fp) <= n)%nat -> fp <= top -> fp mod 8 = 0 ->
(forall a, fp - 16 <= a < top -> rd a <> None) -> exists ch, fpchain (rdword rd) fp top ch.
Proof.
intros rd top n. induction n as [|n IH]; intros fp Hnn Hn Hle H8 Hrd.
- destruct (cnl_rdword_some rd (fp - 8)) as (ra & Hra); [intros k Hk; apply Hrd; lia|].
  assert (Ef : fp = top) by lia. subst fp.
  (* fp = top: the saved ra decides; with ra >= 4096 the next frame pointer is bad (above top - 16) *)
  destruct (Z_lt_le_dec ra 4096) as [Hlt | Hge].
  + exists []. cbn [fpchain]. exists ra. split; [exact Hra|]. split; [exact (cnl_rdword_nonneg rd _ ra Hnn Hra) | exact Hlt].
  + destruct (cnl_rdword_some rd (top - 16)) as (nf & Hnf); [intros k Hk; apply Hrd; lia|].
    exists [(top, ra, nf)]. cbn [fpchain]. split; [reflexivity|]. split; [exact H8|]. split; [exact Hra|]. split; [exact Hnf|].
    split; [exact Hge|]. unfold bad_next. destruct (nf <=? top) eqn:E1; [reflexivity|].
    apply Z.leb_gt in E1. replace (top - 16 <=? nf) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
- destruct (cnl_rdword_some rd (fp - 8)) as (ra & Hra); [intros k Hk; apply Hrd; lia|].
  destruct (Z_lt_le_dec ra 4096) as [Hlt | Hge].
  + exists []. cbn [fpchain]. exists ra. split; [exact Hra|]. split; [exact (cnl_rdword_nonneg rd _ ra Hnn Hra) | exact Hlt].
  + destruct (cnl_rdword_some rd (fp - 16)) as (nf & Hnf); [intros k Hk; apply Hrd; lia|].
    destruct (bad_next fp top nf) eqn:Eb.
    * exists [(fp, ra, nf)]. cbn [fpchain]. rewrite Eb.
      split; [reflexivity|]. split; [exact H8|]. split; [exact Hra|]. split; [exact Hnf|]. split; [exact Hge | reflexivity].
    * unfold bad_next in Eb. apply Bool.orb_false_elim in Eb as [Eb E3]. apply Bool.orb_false_elim in Eb as [E1 E2].
      apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply Bool.negb_false_iff, Z.eqb_eq in E3.
      destruct (IH nf Hnn ltac:(lia) ltac:(lia) E3 ltac:(intros a Ha; apply Hrd; lia)) as (rest & Hrest).
      exists ((fp, ra, nf) :: rest). cbn [fpchain].
      assert (Eb : bad_next fp top nf = false).
      { unfold bad_next. replace (nf <=? fp) with false by (symmetry; apply Z.leb_gt; lia).
        replace (top - 16 <=? nf) with false by (symmetry; apply Z.leb_gt; lia). rewrite E3. reflexivity. }
      rewrite Eb. split; [reflexivity|]. split; [exact H8|]. split; [exact Hra|]. split; [exact Hnf|]. split; [exact Hge | exact Hrest].
Qed.
Lemma cnl_achain_ex : forall ly (rd : reader) sp v,
(forall x w, rd x = Some w -> 0 <= w) -> v mod 8 = 0 -> sp + 16 <= v ->
(forall a, v - 16 <= a < ly_top ly -> rd a <> None) -> exists ch, achain ly rd sp v ch.
Proof.
intros ly rd sp v Hnn H8 Hsp Hrd.
destruct (Z_lt_le_dec v (ly_top ly - 16)) as [Hlt | Hge].
- destruct (cnl_fpchain_ex rd (ly_top ly) (Z.to_nat (ly_top ly - v)) v Hnn ltac:(lia) ltac:(lia) H8 Hrd) as (ch & Hch).
  exists ch. right. split; [lia|]. split; [exact Hlt|]. split; [exact H8|]. split; [exact Hch|].
  eapply Forall_impl; [|exact (fpchain_fps_increase _ _ _ _ Hch)]. intros r Hr. cbn beta in Hr. lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.
(* the layout's top is the entry's along a journal *)
Lemma cnl_ajgx_top : forall G0 XO0 OUT0 STK sp FP ly0 S0 (W0 : world SEGS) mem0 md0 own ly' S' W' mem' md' k,
AJ0 G0 XO0 OUT0 STK sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k -> ly_top ly' = ly_top ly0.
Proof.
intros G0 XO0 OUT0 STK sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _).
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _). exact Et.
Qed.
(* rom_out at a part of g_s (gesture_model's G, the held head; list_drop's G, the expected head) *)
Lemma cnl_rom_out_gs : forall G0, (forall a, inG G0 a -> VAL A_g_s <= a < VAL A_g_s + 384) -> rom_out SEGS B G0.
Proof.
intros G0 HG0 a Hr. destruct (HRO a Hr) as (Hn & Hrest). split; [|exact Hrest].
intros Hg. apply Hn. unfold inG. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact (HG0 a Hg).
Qed.
(* after list_drop returned (0x85fa8, B only): the frame, and s->expected's head with the dropped count (atom 34);
   the loop test reads the count again through its shadow check, then either goes back to the head 0x85ec4 or
   leaves through the epilogue 0x85fc8 *)
Definition A_cnl_drp : Z := AF_fr_check_no_loss + 0x16c.
Definition cnl_dregions : smem := [ cnl_saved; cnl_headL ].
Definition cnl_dfacts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF 0x10000 0x5fc000 4); (22%nat, mkAF SB SB 0);
(33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 26) 0) ] [] [].
Definition ss_cnld (pc : Z) : sstate := mkSS pc cnl_sr cnl_dregions None cnl_dfacts.
Definition cnl_dSH : list shent := [ mkSHE 9 64 80 ].
Lemma cnl_mkd : forall pc W ly S mem md regs regs0 HA v n,
AR0 ly S W mem md ->
cnl_regs_ok regs regs0 HA ->
spZ regs0 mod 16 = 0 -> alloc_ceiling + 112 <= spZ regs0 <= 2 ^ 47 ->
0x10000 <= HA -> HA + 96 <= 0x5fc000 -> HA mod 16 = 0 ->
azs B (HA + 64) 32 ->
cnl_frame_ok W mem (spZ regs0) regs0 ->
val_mem SEGS (arm W mem) (HA + 64) 8 v -> val_mem SEGS (arm W mem) (HA + 72) 4 n -> 0 <= v < 2 ^ 64 -> 0 <= n <= 2 ^ 26 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (cnl_lx 0 v n 0 0 (cnl_svals regs0)))) (ss_cnld pc)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS)))
/\ sh_ok SEGS BxL cnl_dSH (Eimg (Ereg regs (cnl_lx 0 v n 0 0 (cnl_svals regs0)))) (mrestrict (w_H W) mem).
Proof.
intros pc W ly S mem md regs regs0 HA v n HAR HR Hal Hsp HAlo HAhi HA16 Hzs Hfr Mv Mn Rv Rn.
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (Ev := Eimg (Ereg regs (cnl_lx 0 v n 0 0 (cnl_svals regs0)))). pose proof pa_B_ok as HBASE.
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall j, (j < 17)%nat -> ew Ev (32 + j) = nth j (cnl_lx 0 v n 0 0 (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros j Hj. subst Ev. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (spZ regs0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
assert (E33 : ew Ev 33 = Z_to_bv 64 v) by exact (EX 1%nat ltac:(lia)).
assert (E34 : ew Ev 34 = Z_to_bv 64 n) by exact (EX 2%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 49)%nat -> ew Ev k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (VB : forall m w, ew Ev m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val Ev (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (Hsp2 : base_val Ev (Some 2%nat) = spZ regs0 - 112) by (apply VB; [exact E2 | lia]).
assert (Hsp9 : base_val Ev (Some 9%nat) = HA) by (apply VB; [exact E9 | lia]).
split.
- unfold ss_cnld. apply pa_entry_st_ok_full.
  + unfold cnl_sr.
    apply regs_ok_pin; [| discriminate | rewrite R25, (U_shadow_reg Ev 9 22 64 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R24; cbn [sv_denot]; subst Ev; rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia);
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R23, (U_shadow_reg Ev 9 22 72 HA E9 E22) by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R19; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_pin; [| discriminate | rewrite R18; cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
    apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold cnl_dregions, cnl_saved, cnl_headL.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * rewrite Hsp2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
      lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk _ (CVal 8 (SOff ?k 0))) =>
        apply (cnl_chunk_saved Ev _ _ (spZ regs0) regs0 k); [lia | reflexivity | reflexivity | apply ES; lia | exact Hfr] end.
    * rewrite Hsp9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      -- apply (chunk_ok_val SEGS Ev _ HA 64 8 (SOff 33 0) v);
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv].
      -- apply (chunk_ok_val SEGS Ev _ HA 72 4 (SOff 34 0) n);
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mn].
  + apply pairwise_disjoint_of_extents. unfold cnl_dregions, cnl_saved, cnl_headL, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite Hsp2, Hsp9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsp C1 HAlo HAhi. clear. intros. repeat split; lia.
  + split; [|split; [exact I | exact I]].
    cbn [cnl_dfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E22, E33, E34, !unsigned_lit_small by (unfold SB; lia).
    change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    assert (Hsp16 : (spZ regs0 - 112) mod 16 = 0).
    { rewrite Zminus_mod, Hal. reflexivity. }
    revert Hsp C1 Hsp16 HAlo HAhi HA16 Rv Rn. clear.
    unfold SB. intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, cnl_dSH. constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (azs_range_addressable_x B ARx LAWS ly S [] W mem md (HA + 64) 32 HAR Hzs).
  + unfold BxL. rewrite (U_atom Ev 22 SB E22) by (unfold SB; lia). reflexivity.
  + rewrite (U_atom Ev 9 HA E9) by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* awr_ok_tac exists in Reusable.YCbq and in lib/B.YCbq: call it by its full name (VERDICT.md sha256 810ca1df9ca9; internal record) *)
Ltac awr_any := first [ OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable.YCbq.awr_ok_tac
                       | OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.awr_ok_tac ].
(* ------------------------------------------------------------------ keeping the source across a frame-only run *)
(* Two memories that agree at a byte keep its view and its writability. *)
Lemma abyte_kept_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) -> abyte_kept W1 m W1 m' a.
Proof.
intros W1 m m' a Hq. split.
- unfold aview, mbyte. rewrite Hq. reflexivity.
- unfold writable_at, wview, arm. rewrite Hq. exact (fun H => H).
Qed.
Lemma cnl_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cnl_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma cnl_rec_len : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
(* Every byte the source's predicate reads is an application byte below the allocator's ceiling. *)
Lemma cnl_src_low : forall ly1 S1 W1 mem1 md1 HA1 h1,
AR0 ly1 S1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x5fc000 ->
forall rr, In rr (asrc_fp HA1 h1) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling.
Proof.
intros ly1 S1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi.
pose proof asan_consts as (C1 & _).
assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
  0x10000 <= LA -> LA + 16 <= 0x5fc000 ->
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
     destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hvin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     unfold gfp in Ha; cbn [fst snd] in Ha; rewrite (cnl_vec_len l Hj) in Ha; lia
   | apply in_map_iff in Hin as (r & <- & Hr);
     rewrite Forall_forall in Hrec; destruct (Hrec r Hr) as (Hin2 & _);
     destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hin2) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _);
     cbn [fst snd gfp] in Ha; unfold bzs in Ha; rewrite length_map, length_app in Ha; cbn [length] in Ha; lia ]). }
intros rr Hin a Ha.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & Hpg & _ & Hexp & Hheld & _).
unfold asrc_fp in Hin. cbn [In] in Hin.
destruct Hin as [<- | Hin]; [cbn [fst snd] in Ha; unfold ASRC in Ha; lia|].
destruct Hin as [<- | Hin].
{ destruct (cnl_blk ly1 S1 W1 mem1 md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd gfp] in Ha. unfold bzs in Ha. rewrite length_map in Ha. unfold APARTIAL in *. lia. }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) ltac:(lia) ltac:(lia) rr Hin a Ha). }
apply in_app_or in Hin as [Hin | Hin].
{ exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) ltac:(lia) ltac:(lia) rr Hin a Ha). }
exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) ltac:(lia) ltac:(lia) rr Hin a Ha).
Qed.
(* The source survives a step that changes no byte below the allocator's ceiling. *)
Lemma cnl_src_kept : forall ly1 S1 W1 mem1 md1 mem2 HA1 h1 lo,
AR0 ly1 S1 W1 mem1 md1 -> asrc_at B ly1 S1 W1 mem1 HA1 h1 -> 0x10000 <= HA1 -> HA1 + 96 <= 0x5fc000 ->
alloc_ceiling <= lo ->
(forall a, 4096 <= a < lo -> mrestrict (w_H W1) mem2 (Z_to_bv 64 a) = mrestrict (w_H W1) mem1 (Z_to_bv 64 a)) ->
asrc_at B ly1 S1 W1 mem2 HA1 h1.
Proof.
intros ly1 S1 W1 mem1 md1 mem2 HA1 h1 lo HAR HS HAlo HAhi Hlo Hq.
apply (asrc_at_kept B ly1 S1 W1 mem1 ly1 S1 W1 mem2 HA1 h1 HS).
- intros rr Hin a Ha. apply abyte_kept_meq. apply Hq.
  destruct (cnl_src_low ly1 S1 W1 mem1 md1 HA1 h1 HAR HS HAlo HAhi rr Hin a Ha). lia.
- intros b Hb. pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & _ & _ & _ & Hexp & Hheld & _).
  unfold asrc_blks in Hb. cbn [In] in Hb.
  assert (LB : forall (l : hlist) LA, alist_at B ly1 S1 W1 mem1 LA l true \/ alist_at B ly1 S1 W1 mem1 LA l false ->
    In b (alist_blks l) -> In b (ablocks B ly1 S1)).
  { intros l LA Hl Hin. destruct Hl as [HA2 | HA2];
    (destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec);
     unfold alist_blks in Hin; apply in_app_or in Hin as [Hin | Hin];
     [ destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]; destruct Hin as [<- | []];
       destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin]
     | apply in_map_iff in Hin as (r & <- & Hr); rewrite Forall_forall in Hrec; exact (proj1 (Hrec r Hr)) ]). }
  destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (LB (hs_pending h1) (HA1 + 16) (or_intror Hpend) Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (LB (hs_expected h1) (HA1 + 64) (or_introl Hexp) Hb)
  | exact (LB (hs_held h1) (HA1 + 80) (or_introl Hheld) Hb)].
Qed.
Lemma set_exp_held_id : forall hh, set_exp_held hh (hs_expected hh) (hs_held hh) = hh.
Proof. intros [? ? ? ? ? ? ? ? ? ? ? ? ?]. reflexivity. Qed.
Lemma cnl_E_id : forall (l : hlist), HL (hl_v l) (hl_cap l) (hl_recs l) (hl_junk l) = l.
Proof. intros [? ? ? ?]. reflexivity. Qed.
Lemma val_mem_meq : forall (W1 : world SEGS) m m' a n v,
(forall x, a <= x < a + Z.of_nat n -> mrestrict (w_H W1) m' (Z_to_bv 64 x) = mrestrict (w_H W1) m (Z_to_bv 64 x)) ->
val_mem SEGS (arm W1 m) a n v -> val_mem SEGS (arm W1 m') a n v.
Proof.
intros W1 m m' a n v Hq Hv. apply (akept_vm W1 m W1 m' a n v); [|exact Hv].
intros x Hx. apply abyte_kept_meq. apply Hq. exact Hx.
Qed.
Lemma garr8_meq : forall (W1 : world SEGS) m m' a l,
(forall x, a <= x < a + Z.of_nat (length l) -> mrestrict (w_H W1) m' (Z_to_bv 64 x) = mrestrict (w_H W1) m (Z_to_bv 64 x)) ->
garr8 SEGS (arm W1 m) a l -> garr8 SEGS (arm W1 m') a l.
Proof.
intros W1 m m' a l Hq Hg. apply (akept_garr8 W1 m W1 m' a l); [|exact Hg].
intros x Hx. apply abyte_kept_meq. apply Hq. exact Hx.
Qed.
Lemma aview_meq : forall (W1 : world SEGS) m m' a,
mrestrict (w_H W1) m' (Z_to_bv 64 a) = mrestrict (w_H W1) m (Z_to_bv 64 a) ->
aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a.
Proof. intros W1 m m' a Hq. exact (proj1 (abyte_kept_meq W1 m m' a Hq)). Qed.
(* The image bytes the walk keeps are below the allocator's ceiling, so a frame-only step keeps them. *)
Lemma cnl_ro_low : forall a, inG cnl_ro a -> 4096 <= a < alloc_ceiling.
Proof.
intros a Ha. pose proof asan_consts as (C1 & _).
pose proof (pa_img_range a (proj1 (HGR a Ha))) as Hi. lia.
Qed.
Lemma cnl_ro_in : forall b n a, In (b, n) cnl_ro -> b <= a < b + n -> inG cnl_ro a.
Proof.
intros b n a Hin Ha. unfold inG. apply Exists_exists. exists (b, n). split; [exact Hin|].
unfold in_zr. cbn [fst snd]. exact Ha.
Qed.
Lemma cnl_ro_keep : forall b n a, In (b, n) cnl_ro -> b <= a < b + n -> 4096 <= a < alloc_ceiling.
Proof. intros b n a Hin Ha. apply cnl_ro_low. exact (cnl_ro_in b n a Hin Ha). Qed.
(* errno's four bytes are image bytes (PALib's api_env): below the allocator's ceiling and so below every frame *)
Lemma cnl_errno_low : forall i, 0 <= i < 4 ->
0x10000 <= as_errno B + i < 0x5fc000 /\ 4096 <= as_errno B + i < alloc_ceiling.
Proof.
intros i Hi. pose proof (pal_env B TL) as (_ & HeImg & _). pose proof asan_consts as (C1 & _).
pose proof (pa_img_range _ (HeImg (as_errno B + i) ltac:(lia))) as Hr. clear - Hr C1. lia.
Qed.
(* this walk's runs write only its own frame, which is below the out-parameter window *)
Ltac cnl_nowin Uspx :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspx in Hr; unfold CNL_FRAME in Hr; lia|]);
  destruct Hin.
(* The caller's ra and s0..s10, read back from the frame region of the symbolic state at the loop head. *)
Lemma cnl_frame_of_region : forall E (W1 : world SEGS) mem1 regs0 lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W1) mem1) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spZ regs0 ->
(forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs0 rr) ->
Forall (fun p => In (YP09.mkChunk (fst p) (CVal 8 (SOff (snd p) 0))) cs)
  [(-96, 26%nat); (-88, 25%nat); (-80, 24%nat); (-72, 23%nat); (-64, 22%nat); (-56, 21%nat);
   (-48, 20%nat); (-40, 19%nat); (-32, 18%nat); (-24, 9%nat); (-16, 8%nat); (-8, 1%nat)] ->
cnl_frame_ok W1 mem1 (spZ regs0) regs0.
Proof.
intros E W1 mem1 regs0 lo hi wlo whi cs HR Hsp HE HF.
assert (G1 : forall od k (rr : bv 5), In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs -> Z.of_nat k = bv_unsigned rr ->
  val_mem SEGS (mrestrict (w_H W1) mem1) (spZ regs0 + od) 8 (bv_unsigned (getr regs0 rr))).
{ intros od k rr Hc Hk.
  apply (slot_of_region E _ (spZ regs0) cs lo hi wlo whi od (SOff k 0));
  [exact HR | exact Hsp | exact Hc | | apply bv_unsigned_in_range].
  cbn [sv_denot]. rewrite (HE k rr Hk), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
repeat (let Hc := fresh "Hc" in pose proof (Forall_inv HF) as Hc; apply Forall_inv_tail in HF; cbn [fst snd] in Hc).
intros i Hi. unfold arm, cnl_svals, CNL_SAVED.
do 12 (destruct i as [|i]; [cbn [map nth];
  lazymatch goal with |- val_mem _ _ ?a _ (bv_unsigned (getr regs0 ?rr)) =>
    match goal with Hc : In (YP09.mkChunk ?od (CVal 8 (SOff ?k 0))) cs |- _ =>
      replace a with (spZ regs0 + od) by lia; exact (G1 od k rr Hc eq_refl) end end|]).
lia.
Qed.
Lemma cnl_nodup_app_r : forall {A : Type} (l l' : list A), List.NoDup (l ++ l') -> List.NoDup l'.
Proof. intros A l l' H. induction l as [|x l IH]; [exact H|]. apply IH. inversion H; subst. assumption. Qed.
Lemma cnl_list_blks_fst : forall l, map fst (list_blks l) = list_blocks l.
Proof.
intros l. unfold list_blks, list_blocks. rewrite map_app, map_map. cbn [fst].
destruct (hl_cap l =? 0); reflexivity.
Qed.
Section loop.
Variables (regs0 : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (md : Model)
  (ch : list (Z * Z * Z)) (HA : Z) (j : nat) (h : hsrc) (gone A0 NO OUT CO : Z) (ob : list byte).
Local Notation EE := (hs_expected h).
Local Notation HH := (hs_held h).
Local Notation sp0 := (spZ regs0).
Local Notation FPc := (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))).
(* the room round: the caller's room budget past this call (cnl_post_x's kr) *)
Variable kr : nat.
Local Notation Post := (cnl_post_x B PST ARx MT RP G regs0 ly S [] W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
(* What the loop's two halves need of the entry: exactly the premises of cnl_spec that do not move, so the
   main theorem discharges them once before it takes cnl_loop. *)
Hypothesis APRE : AFP0 CNL_STK ly S W regs0 mem md ch.
Hypothesis AX0 : 0 <= XO.
Hypothesis AX16 : XO mod 16 = 0.
Hypothesis AXTOP : sp0 + XO <= ly_top ly.
Hypothesis AXPRES : forall a, sp0 <= a < sp0 + XO -> apresent (w_H W) mem a.
Hypothesis AHAE : HA = VAL A_g_s + ASRC * Z.of_nat j.
Hypothesis AJLT : (j < 4)%nat.
Hypothesis AAT8 : AT mod 8 = 0.
Hypothesis AATL : sp0 <= AT.
Hypothesis AATH : AT + 8 <= sp0 + XO.
Hypothesis AGA : forall a, HA + 64 <= a < HA + 96 -> inG G a.
Hypothesis AZS : azs B (HA + 64) 32.
Hypothesis AEN : hl_n EE < 2 ^ 26.
Hypothesis AHN : hl_n HH + Z.of_nat (count_begin (texts EE)) < 2 ^ 22.
Hypothesis AA0 : 0 <= A0 <= NO.
Hypothesis AGN : 0 <= gone < 256.
Hypothesis AOBN : Z.of_nat (length ob) = NO.
Hypothesis ANO : NO <= 2 ^ 40.
Hypothesis ANO32 : 0 < NO -> NO < 2 ^ 32.
Hypothesis AMRO : amem_range OUT (NO + 8).
Hypothesis AC32 : AREC * capb HH EE < 2 ^ 32.
Hypothesis APERM : exists rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest).
(* the expected list once its first records are gone: same vector, records rs, junk jk *)
Definition cnl_E (rs : list (Z * list byte)) (jk : list byte) : hlist := HL (hl_v EE) (hl_cap EE) rs jk.
(* what the loop keeps unchanged: g_gone, g_nout, g_out, the stream, the rom, gesture_model's literals *)
Definition cnl_consts (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
val_mem SEGS (arm W1 mem1) (VAL A_g_gone) 1 gone /\ val_mem SEGS (arm W1 mem1) (VAL A_g_nout) 8 NO /\
val_mem SEGS (arm W1 mem1) (VAL A_g_out) 8 OUT /\ ob_at W1 mem1 OUT ob /\ rom_view SEGS W1 mem1 /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_gesture) RelayModel.K_GESTURE /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_begin) RelayModel.W_BEGIN /\
garr8 SEGS (arm W1 mem1) (VAL A_lit_end) RelayModel.W_END.
(* errno's view is the entry's: the loop's own stores hit its frame and the at cell, next_line keeps every byte off
   its window and cells, bcmp only reads, and gm_post / ldrop_post keep errno *)
Definition cnl_errno (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
forall i, 0 <= i < 4 -> aview SEGS (w_H W1) mem1 (as_errno B + i) = aview SEGS (w_H W) mem (as_errno B + i).
(* B only: the caller's stack above the loop's frame stays readable (the callees' frame-pointer chain from s0 = at) *)
Definition cnl_stk_rd (W1 : world SEGS) (mem1 : word -> option byte) : Prop :=
forall a, sp0 <= a < ly_top ly -> aview SEGS (w_H W1) mem1 a <> None.
(* the invariant at the loop head: pre consumed, rs left (the plain proof's CI_t, lib/Prog/check_no_loss.v:674) *)
Definition cnl_inv (pre rs : list (Z * list byte)) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ rs /\
AJ0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E rs jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs pre) /\ hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E rs jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) /\ mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) rs /\
(* the room round: the room budget (gesture_model's charge and one free per record left, past the caller's kr) and
   the live counts plus the peak of the trace still owed (W_cnl_cnt.v) *)
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr) /\ cnl_cnt RP rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 pre) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E rs jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 pre)) ob = bsr rs ++ rest) /\
cnl_errno W1 mem1 /\ cnl_stk_rd W1 mem1 /\ cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 regs0 HA.
(* after gesture_model returned (0x85f9c): r is fed to the model, not yet dropped (the plain proof's J1_t) *)
Definition cnl_mid (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) (W1 : world SEGS)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ r :: rs /\
AJ0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E (r :: rs) jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs (pre ++ [r])) /\
hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (pre ++ [r]) /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs (pre ++ [r]))) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]) - mo_free MT) /\
mo_ok MT S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) (texts H1) (hl_cap H1) rs /\
(* the room round: r's drop (list_drop's one free) is still owed, before the rest's budget; its free and the rest
   still owe the counts *)
rp_RM RP S1 (Datatypes.S (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr))%nat /\ cnl_cntm RP r rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 (pre ++ [r])) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) /\
cnl_errno W1 mem1 /\ cnl_stk_rd W1 mem1 /\ cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 regs0 HA.
Definition cnl_midQ (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) :
world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1, c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1 /\
cnl_mid pre r rs W1 regs1 mem1 md1.
(* B only: the frame-pointer chain from s0 = at, at a call made with sp = sp0 - 112: the words it reads are the
   frame's saved registers (sp0 - 96 .. sp0) or the readable stack above sp0 *)
Lemma cnl_val_mem_view : forall (W1 : world SEGS) m a n v k, val_mem SEGS (arm W1 m) a n v -> 0 <= k < Z.of_nat n ->
aview SEGS (w_H W1) m (a + k) <> None.
Proof.
intros W1 m a n v k Hv Hk. unfold aview.
replace (a + k) with (a + Z.of_nat (Z.to_nat k)) by lia. unfold arm in Hv. rewrite (Hv (Z.to_nat k) ltac:(lia)). discriminate.
Qed.
Lemma cnl_chain_at : forall ly1 S1 kk W1 mem1 md1 regs1,
AJ0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
cnl_stk_rd W1 mem1 -> cnl_frame_ok W1 mem1 sp0 regs0 ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 AT ->
exists ch1, achain ly1 (aview SEGS (w_H W1) mem1) (spZ regs1) (s0Z regs1) ch1.
Proof.
intros ly1 S1 kk W1 mem1 md1 regs1 HJ HRD HFR R2 R8.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
assert (Usp : spZ regs1 = sp0 - 112) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
assert (Us0 : s0Z regs1 = AT) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
rewrite Usp, Us0. pose proof (cnl_ajgx_top _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Et.
apply cnl_achain_ex; [exact (cnl_aview_nonneg W1 mem1) | exact AAT8 | lia |].
intros a Ha. rewrite Et in Ha. destruct (Z_lt_le_dec a sp0) as [Hlt | Hge]; [|exact (HRD a ltac:(lia))].
pose proof (Z.div_mod (a - (sp0 - 96)) 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (a - (sp0 - 96)) 8 ltac:(lia)) as Hm.
set (q := (a - (sp0 - 96)) / 8) in *. set (rm := (a - (sp0 - 96)) mod 8) in *.
assert (Hq : 0 <= q < 12) by lia.
pose proof (HFR (Z.to_nat q) ltac:(lia)) as Hv.
replace a with (sp0 - 96 + 8 * Z.of_nat (Z.to_nat q) + rm) by lia.
exact (cnl_val_mem_view W1 mem1 _ 8 _ rm Hv ltac:(cbn; lia)).
Qed.
(* ---------------------------------------------- helpers of cnl_step (hand NLStep) *)
(* the stream's first line is r's text: the NUL-free prefix before the first NUL is unique *)
Lemma nls_nul_split : forall (e ln t rest : list byte),
e ++ Z_to_bv 8 0 :: t = ln ++ Z_to_bv 8 0 :: rest -> ~ In (Z_to_bv 8 0) e -> ~ In (Z_to_bv 8 0) ln -> ln = e.
Proof.
induction e as [|x e IH]; intros [|y ln] t rest Heq He Hl; cbn in Heq.
- reflexivity.
- injection Heq as Hy _. exfalso. apply Hl. left. symmetry. exact Hy.
- injection Heq as Hx _. exfalso. apply He. left. exact Hx.
- injection Heq as -> Heq. f_equal. apply (IH ln t rest Heq); intros Hin; [apply He | apply Hl]; right; exact Hin.
Qed.
(* facts about bytes nobody wrote carry over in the aview form *)
Lemma nls_vm_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W3) m3 (a + i) = aview SEGS (w_H W2) m2 (a + i)) ->
val_mem SEGS (arm W2 m2) a n v -> val_mem SEGS (arm W3 m3) a n v.
Proof.
intros W2 W3 m2 m3 a n v Hk Hv k Hlt. unfold arm.
rewrite (mbyte_of_aview SEGS (w_H W2) (w_H W3) m2 m3); [apply Hv; exact Hlt|]. apply Hk. lia.
Qed.
Lemma nls_garr8_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) a l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W3) m3 (a + i) = aview SEGS (w_H W2) m2 (a + i)) ->
garr8 SEGS (arm W2 m2) a l -> garr8 SEGS (arm W3 m3) a l.
Proof.
intros W2 W3 m2 m3 a l Hk Hg. apply (garr8_frame SEGS (arm W2 m2) (arm W3 m3) a l Hg).
intros x Hx. unfold arm. apply (mbyte_of_aview SEGS). replace x with (a + (x - a)) by lia. apply Hk. lia.
Qed.
Lemma nls_ob_kept : forall (W2 W3 : world SEGS) (m2 m3 : word -> option byte) x l,
(forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS (w_H W3) m3 (x + i) = aview SEGS (w_H W2) m2 (x + i)) ->
ob_at W2 m2 x l -> ob_at W3 m3 x l.
Proof. intros W2 W3 m2 m3 x l Hk Hl i Hi. rewrite Hk by exact Hi. exact (Hl i Hi). Qed.
Lemma nls_shv_sub : forall rd x n n', 0 < n' <= n -> 0 <= x -> shadow_hull_vis rd x n -> shadow_hull_vis rd x n'.
Proof.
intros rd x n n' Hn Hx Hv sa Hsa. apply Hv. split; [lia|].
assert (Hm : shadow_addr (x + n' - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (Hd : shadow_addr (x + n' - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* presence composes, and a writable byte is a present one *)
Lemma nls_apk_trans : forall (Wa : world SEGS) ma (Wb : world SEGS) mb (Wc : world SEGS) mc,
apres_kept B Wa ma Wb mb -> apres_kept B Wb mb Wc mc -> apres_kept B Wa ma Wc mc.
Proof. intros Wa ma Wb mb Wc mc H1 H2 a Hi Ho He Hp. exact (H2 a Hi Ho He (H1 a Hi Ho He Hp)). Qed.
Lemma nls_apk_of_pres : forall (Wa : world SEGS) (ma mb : word -> option byte),
(forall a, apresent (w_H Wa) ma a -> apresent (w_H Wa) mb a) -> apres_kept B Wa ma Wa mb.
Proof. intros Wa ma mb H a _ _ _ Hp. exact (H a Hp). Qed.
(* a byte stays writable when it stays present: where it is not present, writability is the segment's *)
Lemma nls_awr_kept : forall (Wa Wb : world SEGS) (ma mb : word -> option byte) a,
(apresent (w_H Wa) ma a -> apresent (w_H Wb) mb a) ->
writable_at SEGS (arm Wa ma) a -> writable_at SEGS (arm Wb mb) a.
Proof.
intros Wa Wb ma mb a Hp Hw. unfold writable_at, wview, arm, mrestrict in Hw |- *.
destruct (w_H Wb (Z_to_bv 64 a)) eqn:EHb.
- destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [Hh _]. rewrite EHb in Hh. discriminate.
- destruct (mb (Z_to_bv 64 a)) as [b2|] eqn:Emb; [discriminate|].
  destruct (w_H Wa (Z_to_bv 64 a)) eqn:EHa; [exact Hw|].
  destruct (ma (Z_to_bv 64 a)) as [b|] eqn:Ema; [|exact Hw].
  destruct (Hp (conj EHa (ex_intro _ b Ema))) as [_ [b3 Hb3]]. rewrite Emb in Hb3. discriminate.
Qed.
(* the live blocks are pairwise apart (AR): as pairs and by their addresses, they are duplicate-free *)
Lemma nls_pw_nodup_fst : forall (l : list (Z * Z)), (forall b, In b l -> 0 <= snd b) ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup (map fst l).
Proof.
induction l as [|x l IH]; intros HF HP; [constructor|].
cbn [map] in HP |- *. destruct HP as [HAx HP].
assert (Rx : 1 <= req_size (snd x)) by (apply (req_size_pos (snd x)); apply HF; left; reflexivity).
constructor.
- intros Hin. apply in_map_iff in Hin as (y & Hy & Hyl).
  assert (Ry : 1 <= req_size (snd y)) by (apply (req_size_pos (snd y)); apply HF; right; exact Hyl).
  assert (Hin2 : In (fst y, req_size (snd y)) (map (fun b : Z * Z => (fst b, req_size (snd b))) l)).
  { apply in_map_iff. exists y. split; [reflexivity | exact Hyl]. }
  assert (Hd : zdisjoint (fst x, req_size (snd x)) (fst y, req_size (snd y)));
  [ first [ exact (proj1 (Forall_forall _ _) HAx _ Hin2) | exact (HAx _ Hin2) ]
  | unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia ].
- apply IH; [intros b Hb; apply HF; right; exact Hb | exact HP].
Qed.
Lemma nls_nodup_map : forall (A' B' : Type) (f : A' -> B') (l : list A'), List.NoDup (map f l) -> List.NoDup l.
Proof.
intros A' B' f. induction l as [|x l IH]; intros H; [constructor|].
cbn [map] in H. apply List.NoDup_cons_iff in H as [Hx Hl]. constructor; [|exact (IH Hl)].
intros Hin. apply Hx. apply in_map. exact Hin.
Qed.
Lemma nls_nodup_blocks_fst : forall ly1 S1 (W1 : world SEGS) mem1 md1,
AR0 ly1 S1 W1 mem1 md1 -> List.NoDup (map fst (ablocks B ly1 S1)).
Proof.
intros ly1 S1 W1 mem1 md1 HAR. apply nls_pw_nodup_fst.
- intros b Hb. destruct b as [p n].
  destruct (al0_blocks ly1 S1 W1 mem1 md1 p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd]. lia.
- destruct (ablocks B ly1 S1) as [|b l] eqn:Eb; [cbn; exact I|].
  destruct b as [p n].
  destruct (al0_blocks ly1 S1 W1 mem1 md1 p n HAR ltac:(rewrite Eb; left; reflexivity))
    as (_ & _ & _ & _ & _ & Hpw & _).
  rewrite Eb in Hpw. exact Hpw.
Qed.
Lemma nls_nodup_blocks : forall ly1 S1 (W1 : world SEGS) mem1 md1,
AR0 ly1 S1 W1 mem1 md1 -> List.NoDup (ablocks B ly1 S1).
Proof. intros ly1 S1 W1 mem1 md1 HAR. exact (nls_nodup_map _ _ fst _ (nls_nodup_blocks_fst ly1 S1 W1 mem1 md1 HAR)). Qed.
(* a list's blocks are live, and their addresses are the plain side's list_blocks *)
Lemma nls_blks_in : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines,
alist_at B ly1 S1 W1 mem1 LA l lines -> forall b, In b (list_blks l) -> In b (ablocks B ly1 S1).
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & _ & Hv & _ & _ & HF) b Hb.
unfold list_blks in Hb. destruct (hl_cap l =? 0) eqn:Ec; cbn [app] in Hb.
- apply in_map_iff in Hb as (rr & <- & Hrr). exact (proj1 (proj1 (Forall_forall _ _) HF rr Hrr)).
- destruct Hb as [<- | Hb].
  + apply Z.eqb_neq in Ec. destruct Hv as [(Hc0 & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (rr & <- & Hrr). exact (proj1 (proj1 (Forall_forall _ _) HF rr Hrr)).
Qed.
Lemma nls_map_fst_blks : forall l, map fst (list_blks l) = HarnessRep.list_blocks l.
Proof.
intros l. unfold list_blks, HarnessRep.list_blocks. rewrite map_app. f_equal.
- destruct (hl_cap l =? 0); reflexivity.
- rewrite map_map. reflexivity.
Qed.
Lemma nls_cb_app : forall l1 l2, count_begin (l1 ++ l2) = (count_begin l1 + count_begin l2)%nat.
Proof.
intros l1 l2. unfold count_begin. induction l1 as [|x l1 IH]; [reflexivity|].
cbn. destruct (decide (is_begin x)); cbn [length Nat.add]; [f_equal; exact IH | exact IH].
Qed.
Lemma nls_cb_one : forall x, count_begin [x] = (if is_begin x then 1 else 0)%nat.
Proof. intros x. unfold count_begin. cbn. destruct (is_begin x); reflexivity. Qed.
Lemma nls_nodup_disj : forall (T0 : Type) (l1 l2 : list T0) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
intros T0. induction l1 as [|y l1 IH]; intros l2 x H Hx Hy; [destruct Hx|]. cbn [app] in H.
apply List.NoDup_cons_iff in H as [Hn H].
destruct Hx as [<- | Hx]; [apply Hn; apply in_or_app; right; exact Hy | exact (IH l2 x H Hx Hy)].
Qed.
Lemma nls_perm_swap : forall (T0 : Type) (a b c : list T0), Permutation ((a ++ b) ++ c) (b ++ a ++ c).
Proof. intros T0 a b c. rewrite <- app_assoc. apply Permutation_app_swap_app. Qed.
Lemma nls_vec_len : forall l : hlist, Z.of_nat (length (hl_junk l)) = AREC * (hl_cap l - hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (hl_recs l)) ++ hl_junk l))) = AREC * hl_cap l.
Proof.
intros l Hj. unfold bzs. rewrite length_map, length_app, cnl_text_recs_length, Nat2Z.inj_add, Nat2Z.inj_mul.
unfold hl_n in Hj. change (Z.of_nat 16) with 16. unfold AREC in *. lia.
Qed.
Lemma nls_rec_len : forall r : Z * list byte,
Z.of_nat (length (bzs (snd r ++ [Z_to_bv 8 0]))) = Z.of_nat (length (snd r)) + 1.
Proof. intros r. unfold bzs. rewrite length_map, length_app. cbn [length]. lia. Qed.
Lemma nls_alist_blks : forall l, alist_blks l = list_blks l.
Proof. reflexivity. Qed.
(* every byte a list's predicate reads is its head's or one of its blocks' *)
Lemma nls_alist_fp_in : forall ly1 S1 (W1 : world SEGS) mem1 LA l lines, alist_at B ly1 S1 W1 mem1 LA l lines ->
forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr ->
LA <= a < LA + 16 \/ exists b, In b (list_blks l) /\ fst b <= a < fst b + snd b.
Proof.
intros ly1 S1 W1 mem1 LA l lines (_ & _ & _ & _ & Hcap & Hv & _ & _ & _) rr Hin a Ha.
unfold alist_fp in Hin. destruct Hin as [<- | Hin]; [left; cbn [fst snd] in Ha; exact Ha|]. right.
apply in_app_or in Hin as [Hin | Hin].
- destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
  exists (hl_v l, AREC * hl_cap l). split; [unfold list_blks; rewrite Ec; apply in_or_app; left; left; reflexivity|].
  destruct Hv as [(Hc0 & _) | (_ & _ & Hj & _)]; [apply Z.eqb_neq in Ec; lia|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite (nls_vec_len l Hj) in Ha. exact Ha.
- apply in_map_iff in Hin as (r0 & <- & Hr0). exists (fst r0, Z.of_nat (length (snd r0)) + 1).
  split; [unfold list_blks; apply in_or_app; right; apply (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1))); exact Hr0|].
  unfold gfp in Ha. cbn [fst snd] in Ha |- *. rewrite nls_rec_len in Ha. exact Ha.
Qed.
(* the read-only objects: image bytes outside the allocator's statics and errno *)
Lemma nls_ro : forall b n a, In (b, n) cnl_ro -> b <= a < b + n ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Proof.
intros b n a Hin Ha.
assert (HG' : inG cnl_ro a) by (unfold inG; apply Exists_exists; exists (b, n); split; [exact Hin | unfold in_zr; cbn [fst snd]; exact Ha]).
destruct (HGR a HG') as (Hi & Ho & _). destruct (HGRR a HG') as [He _]. split; [exact Hi|]. split; [exact Ho | exact He].
Qed.
Lemma nls_rom_img : forall a, in_rom SEGS a -> in_img SEGS a.
Proof. intros a (sg & Hin & _ & Hr). exists sg. split; [exact Hin | exact Hr]. Qed.
(* the source survives a step that keeps every byte below the allocator's ceiling and every present byte *)
Lemma nls_src_kept_low : forall ly1 S1 (W1 : world SEGS) m m' md1 hs,
AR0 ly1 S1 W1 m md1 -> asrc_at B ly1 S1 W1 m HA hs ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a) ->
asrc_at B ly1 S1 W1 m' HA hs.
Proof.
intros ly1 S1 W1 m m' md1 hs HAR HS Heq Hp.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & _).
pose proof asan_consts as (AC & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & Hexp & Hheld & _).
assert (LB : forall LA l lines, alist_at B ly1 S1 W1 m LA l lines -> HA + 16 <= LA <= HA + 80 ->
  forall rr, In rr (alist_fp LA l) -> forall a, fst rr <= a < snd rr -> 4096 <= a < alloc_ceiling).
{ intros LA l lines Hl HLA rr Hin a Ha.
  destruct (nls_alist_fp_in ly1 S1 W1 m LA l lines Hl rr Hin a Ha) as [Hh | (b & Hb & Hab)]; [lia|].
  destruct b as [p n].
  destruct (cnl_blk ly1 S1 W1 m md1 p n HAR (nls_blks_in ly1 S1 W1 m LA l lines Hl _ Hb)) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
  cbn [fst snd] in Hab. lia. }
apply (asrc_at_kept B ly1 S1 W1 m ly1 S1 W1 m' HA hs HS).
- intros rr Hin a Ha.
  assert (Hlow : 4096 <= a < alloc_ceiling).
  { unfold asrc_fp in Hin. destruct Hin as [<- | [<- | Hin]].
    + cbn [fst snd] in Ha. unfold ASRC in Ha. lia.
    + destruct (cnl_blk ly1 S1 W1 m md1 _ _ HAR Hpin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _).
      unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha. lia.
    + apply in_app_or in Hin as [Hin | Hin]; [exact (LB _ _ _ Hpend ltac:(lia) rr Hin a Ha)|].
      apply in_app_or in Hin as [Hin | Hin]; [exact (LB _ _ _ Hexp ltac:(lia) rr Hin a Ha) | exact (LB _ _ _ Hheld ltac:(lia) rr Hin a Ha)]. }
  split; [exact (Heq a Hlow)|]. apply nls_awr_kept. exact (Hp a).
- intros b Hb. unfold asrc_blks in Hb. rewrite !nls_alist_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpin|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hexp b Hb) | exact (nls_blks_in _ _ _ _ _ _ _ Hheld b Hb)].
Qed.
Lemma nls_lit_len : length RelayModel.K_GESTURE = 13%nat /\ length RelayModel.W_BEGIN = 5%nat /\ length RelayModel.W_END = 3%nat.
Proof. split; [|split]; reflexivity. Qed.
(* the constants survive a step that keeps every byte below the allocator's ceiling *)
Lemma nls_consts_kept_low : forall ly1 S1 (W1 : world SEGS) m m' md1,
AR0 ly1 S1 W1 m md1 -> (ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO) ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
cnl_consts W1 m -> cnl_consts W1 m'.
Proof.
intros ly1 S1 W1 m m' md1 HAR Hob Heq (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
pose proof asan_consts as (AC & _). pose proof nls_lit_len as (L1 & L2 & L3).
assert (Rro : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> 4096 <= x < alloc_ceiling).
{ intros b n x Hin Hx. destruct (nls_ro b n x Hin Hx) as (Hi & _). pose proof (pa_img_range x Hi). lia. }
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C1]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia]|].
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C2]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia]|].
split; [apply (nls_vm_kept W1 W1 m m'); [|exact C3]; intros i Hi; apply Heq;
  apply (Rro (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia]|].
split.
{ apply (nls_ob_kept W1 W1 m m'); [|exact C4]. intros i Hi. apply Heq.
  destruct Hob as [-> | (Hin & HCO)]; [cbn [length] in Hi; lia|].
  destruct (cnl_blk ly1 S1 W1 m md1 OUT CO HAR Hin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
split.
{ intros a Hr. rewrite (Heq a) by (pose proof (pa_img_range a (nls_rom_img a Hr)); lia). exact (C5 a Hr). }
split; [apply (nls_garr8_kept W1 W1 m m'); [|exact C6]; intros i Hi; apply Heq;
  apply (Rro (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia]|].
split; [apply (nls_garr8_kept W1 W1 m m'); [|exact C7]; intros i Hi; apply Heq;
  apply (Rro (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia]|].
apply (nls_garr8_kept W1 W1 m m'); [|exact C8]; intros i Hi; apply Heq.
apply (Rro (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia].
Qed.
Lemma nls_frame_kept : forall (W1 W2 : world SEGS) m m', cnl_frame_ok W1 m sp0 regs0 ->
(forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W2) m' a = aview SEGS (w_H W1) m a) -> cnl_frame_ok W2 m' sp0 regs0.
Proof. intros W1 W2 m m' Hf Hk i Hi. apply (nls_vm_kept W1 W2 m m'); [|exact (Hf i Hi)]. intros k Hk'. apply Hk. lia. Qed.
(* the source with its held list replaced: every other byte and block kept *)
Lemma nls_src_swap : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA0 (h0 : hsrc) (H' : hlist),
asrc_at B ly1 S1 W1 m1 HA0 h0 ->
(forall a, HA0 <= a < HA0 + 80 -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (gfp (hs_partial h0) (bzs (hs_pjunk h0)) :: alist_fp (HA0 + 16) (hs_pending h0) ++ alist_fp (HA0 + 64) (hs_expected h0)) ->
(forall b, In b ((hs_partial h0, APARTIAL) :: alist_blks (hs_pending h0) ++ alist_blks (hs_expected h0)) -> In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 m2 (HA0 + 80) H' true ->
NoDup (hs_blocks (set_exp_held h0 (hs_expected h0) H')) ->
asrc_at B ly2 S2 W2 m2 HA0 (set_exp_held h0 (hs_expected h0) H').
Proof.
intros ly1 S1 W1 m1 ly2 S2 W2 m2 HA0 h0 H'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) HK HF HB HL HND.
assert (Hvm : forall a n v, HA0 <= a -> a + Z.of_nat n <= HA0 + 80 ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply HK; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 80) as [Hi8 | Hi8]; [apply (proj2 (HK (HA0 + i) ltac:(lia))); exact (H5 i Hi)|].
  pose proof HL as (_ & _ & _ & HW & _). replace (HA0 + i) with (HA0 + 80 + (i - 80)) by lia. apply HW. unfold ASRC in Hi. lia. }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H10
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 m1); [intros x Hx; apply (HF (gfp (hs_partial h0) (bzs (hs_pjunk h0))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H22
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb]|].
split; [exact HL | exact HND].
Qed.
(* the model's side of one step *)
Lemma nls_go_snoc : forall T c a r, cnl_go MT T c (a ++ [r]) =
cnl_go MT T c a + gmc MT (RelayModel.upds T (txs a)) (cnl_cap T c a) (snd r) + mo_free MT.
Proof.
intros T c a. revert T c. induction a as [|x a IH]; intros T c r.
- cbn [app cnl_go cnl_cap txs map]. unfold RelayModel.upds. cbn [fold_left]. lia.
- cbn [app cnl_go cnl_cap]. rewrite IH.
  assert (Eu : RelayModel.upds T (txs (x :: a)) = RelayModel.upds (RelayModel.upd T (bzs (snd x))) (txs a)) by reflexivity.
  rewrite Eu. lia.
Qed.
Lemma nls_gmc_nonneg : forall T cap ln, 0 <= cap -> 0 <= gmc MT T cap ln.
Proof.
intros T cap ln Hc. pose proof (mo_free_nonneg MT ML) as Hf.
unfold gmc. destruct (RelayModel.gesture (bzs ln)) as [[[|] x]|]; cbv beta iota; [| |lia].
- destruct (existsb (RelayModel.list_eqb x) T); [lia|].
  pose proof (mo_malloc_nonneg MT ML (Z.of_nat (length x) + 1) ltac:(pose proof (Nat2Z.is_nonneg (length x)); lia)) as Hm.
  destruct (Z.of_nat (length T) =? cap); [|lia].
  assert (Hg : 0 <= AREC * grow_cap (Z.of_nat (length T)) cap)
    by (unfold grow_cap, AREC; destruct (Z.of_nat (length T) =? cap), (cap =? 0); lia).
  pose proof (mo_malloc_nonneg MT ML _ Hg). lia.
- destruct (existsb (RelayModel.list_eqb x) T); lia.
Qed.
Lemma nls_capstep_nonneg : forall T l cap, 0 <= cap -> 0 <= capstep T l cap.
Proof. intros T l cap Hc. unfold capstep, grow_cap. destruct (Nat.ltb (length T) (length (RelayModel.upd T l))); [|lia]. destruct (Z.of_nat (length T) =? cap), (cap =? 0); lia. Qed.
Lemma nls_go_nonneg : forall rs0 T cap, 0 <= cap -> 0 <= cnl_go MT T cap rs0.
Proof.
induction rs0 as [|r0 rs0 IH]; intros T cap Hc; cbn [cnl_go]; [lia|].
pose proof (nls_gmc_nonneg T cap (snd r0) Hc).
pose proof (mo_free_nonneg MT ML). pose proof (IH (RelayModel.upd T (bzs (snd r0))) _ (nls_capstep_nonneg T (bzs (snd r0)) cap Hc)). lia.
Qed.
(* gesture_model's entry (0x86048, ra = 0x85f9c) to its return: either arm reaches it with a0 = s, a1 = the line
   (r's text, at LINE inside the live block (q, k) that is none of the held list's) and a2 = its length; the state
   is cnl_inv's with *at already at r's end.  gesture_model is taken at its own globals, the held list's head. *)
Lemma cnl_gm : forall pre r rs ly1 S1 kk (H1 : hlist) jk W1 regsc memc mdc LINE q k,
hl_recs EE = pre ++ r :: rs ->
AJ0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 memc mdc kk ->
apres_kept B W mem W1 memc ->
asrc_at B ly1 S1 W1 memc HA (set_exp_held h (cnl_E (r :: rs) jk) H1) ->
NoDup (texts H1) -> texts H1 = RelayModel.upds (texts HH) (txs pre) -> hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre ->
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) -> hl_cap H1 <= capb HH EE ->
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) ->
frames S1 = frames S ->
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) -> mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) (r :: rs)) ->
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) (r :: rs) ->
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) (r :: rs)) + kr) -> cnl_cnt RP (r :: rs) H1 (ablocks B ly1 S1) ->
val_mem SEGS (arm W1 memc) AT 8 (cpos gone A0 (pre ++ [r])) -> cnl_consts W1 memc ->
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) ->
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) ->
cnl_errno W1 memc -> cnl_stk_rd W1 memc -> cnl_frame_ok W1 memc sp0 regs0 -> cnl_regs_ok regsc regs0 HA ->
getr regsc 1 = Z_to_bv 64 (BASE + A_cnl_back) -> getr regsc 10 = w64 HA -> getr regsc 11 = w64 LINE ->
getr regsc 12 = w64 (Z.of_nat (length (snd r))) ->
garr8 SEGS (arm W1 memc) LINE (bzs (snd r)) ->
In (q, k) (ablocks B ly1 S1) -> ~ In (q, k) (list_blks H1) -> q <= LINE -> LINE + Z.of_nat (length (snd r)) <= q + req_size k ->
SRr SEGS W1 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_model)) memc (seg_rom SEGS)) mdc) (cnl_midQ pre r rs).
Proof.
intros pre r rs ly1 S1 kk H1 jk W1 regsc memc mdc LINE q k HEQ HJ HPK HSRC HND HTX HCAP HN HCB HPERM HFR HMLE HMOK
  HROOM HRMr HCNTr HAT HCONST HOB HSTR HERR HSRD HFRM HREGS R1 R10 R11 R12 HLG Hqk Hqn Hq1 Hq2.
pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity. assert (WG : GM_STK = 16528) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & _ & _ & _).
(* W4's gesture_model takes this premise once a working branch f58b3f26c80 is merged *)
assert (HA80 : (HA + 80) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 10; reflexivity]. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HAR1 : AR0 ly1 S1 W1 memc mdc) by (eapply ajournal_gx_AR_x; exact HJ).
set (E1 := cnl_E (r :: rs) jk) in *.
assert (HrE1 : hl_recs E1 = r :: rs) by reflexivity.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (_ & _ & _ & _ & _ & _ & _ & _ & HrecE).
rewrite HrE1 in HrecE. apply Forall_cons_iff in HrecE as [(Hrb & Hrg & Hrl & _) _].
destruct (Hrl eq_refl) as [Hr0 HrA].
pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _).
destruct HCONST as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
(* the source's blocks at the call: pending's, the partial buffer, the expected list's, then the held list's *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks E1).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h E1 H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (Hinc : incl (Ab ++ HL1) (ablocks B ly1 S1)).
{ intros b Hb. unfold Ab, HL1 in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 b Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [destruct Hb as [<- | []]; exact Hpin | exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
destruct (perm_of_incl _ _ HNDl Hinc) as (rest0 & Hp0).
assert (Hp1 : Permutation (ablocks B ly1 S1) (HL1 ++ Ab ++ rest0)) by (eapply Permutation_trans; [exact Hp0 | apply nls_perm_swap]).
pose proof (nls_nodup_blocks _ _ _ _ _ HAR1) as HND1b.
(* gesture_model's footprint: a held block live at entry was one of FPc's, by APERM *)
assert (HFP : forall a, inFP (blk_FP HL1) a ->
  (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb). cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly S)) as [Hin0 | Hnin0].
  - left. split; [|exists p, n; split; [exact Hb1 | exact Ha]].
    destruct APERM as (rest & HQ0). pose proof (HPERM rest HQ0) as HP1.
    assert (Hx : In (p, n) (list_blks EE ++ list_blks HH)).
    { pose proof (Permutation_in _ HQ0 Hin0) as Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
      exfalso. pose proof (Permutation_NoDup HP1 HND1b) as HNx. apply NoDup_app_remove_l in HNx.
      exact (nls_nodup_disj _ HL1 rest (p, n) HNx Hb Hx). }
    exists (p, p + req_size n). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n)). exact Hx.
  - right. exists p, n. split; [exact Hb1|]. split; [exact Hnin0 | exact Ha]. }
(* gesture_model's globals: the held list's head only *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG' : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G' a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G' G HG'G HG) as HG'.
(* gx_rt of gesture_model's G' comes from g_s's own placement fact HGRR, never from the caller's G: a caller's G
   (G_fr, G_SL) holds errno, so `gx_rt B G` was unsatisfiable at every caller (W5's finding on re_spec_g). *)
assert (HG'R : forall a, inG G' a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT' : gx_rt B G') by (eapply gx_rt_sub; [exact HG'R | exact HGRR]).
(* rom_out at G' from g_s's (HRO): gm_spec_g takes it, for list_drop's spec inside gesture_model *)
assert (HRO' : rom_out SEGS B G').
{ apply cnl_rom_out_gs. intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. rewrite AHAE in Ha. unfold ASRC in *. lia. }
(* gesture_model's entry *)
assert (Usp : spZ regsc = sp0 - 112).
{ destruct HREGS as (Q2 & _). unfold spZ at 1. rewrite Q2. apply unsigned_lit_small. lia. }
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 memc mdc kk HJ) as (memS & HJi & _).
(* s0 = at: the frame-pointer chain the callee's unwinder walks from it exists, the stack being readable *)
destruct (cnl_chain_at ly1 S1 kk W1 memc mdc regsc HJ HSRD HFRM (proj1 HREGS) (proj1 (proj2 (proj2 (proj2 HREGS))))) as (chg & Hchg).
assert (HPREg : AFP0 GM_STK ly1 S1 W1 regsc memc mdc chg).
{ destruct HREGS as (_ & Q3 & Q4 & Q8 & _).
  eapply (afn_pre_at0 (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 memc mdc kk regsc GM_STK (- 112 - XO) chg HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - rewrite WG; lia.
  - rewrite WS, WG. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cnl_back, AF_fr_check_no_loss; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold A_cnl_back, AF_fr_check_no_loss. destruct HBASE as (B1 & B2 & _).
    rewrite unsigned_lit_small by lia. lia.
  - exact Q3.
  - exact Q4.
  - exact Hchg. }
assert (Hazs : azs B (HA + 80) 16)
  by (destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2); exists zr; split; [exact Hzr|]; split; [exact Hz8|]; split; lia).
assert (HnT1 : Z.of_nat (length (texts H1)) = hl_n H1) by (unfold texts, hl_n; rewrite length_map; reflexivity).
cbn [cnl_room] in HROOM. destruct HROOM as (HRM1 & HRM2 & HRM3).
assert (HGC : gm_cost MT H1 (snd r) = gmc MT (texts H1) (hl_cap H1) (snd r)).
{ unfold gm_cost, lp_cost, gmc, lp_grow, lp_vbytes. rewrite HnT1. reflexivity. }
cbn [cnl_go] in HMOK.
eapply SRr_mono.
{ refine (GM G' HG' HGRT' HRO' W1 ly1 S1 [] regsc memc mdc chg HA LINE (snd r) H1 q k HPREg R10 R11 R12 HH1 HND _ Hazs HA80 HLG Hr0 HrA
    Hqk Hqn Hq1 Hq2 C6 C7 C8 C5 _ _ _ _
    (Datatypes.S (Z.to_nat (cnl_go MT_rk (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
      + kr))%nat _ _).
  - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros Hg. unfold lp_vbytes. rewrite <- HnT1. apply HRM1. unfold lp_grow in Hg. apply Z.eqb_eq in Hg. lia.
  - unfold AREC in *. lia.
  - unfold lp_grow, lp_vbytes. rewrite <- HnT1. exact HRM2.
  - rewrite HGC. eapply (mo_ok_le MT ML); [exact HMOK|]. pose proof (mo_free_nonneg MT ML).
    assert (Hc0 : 0 <= hl_cap H1) by (unfold hl_n in HcapH1; lia).
    pose proof (nls_go_nonneg rs (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1))
      (nls_capstep_nonneg (texts H1) (bzs (snd r)) (hl_cap H1) Hc0)). lia.
  - (* the room: gesture_model's charge, then r's drop (one free), then the rest (W_cnl_cnt.v cnl_rk_step) *)
    rewrite <- (cnl_rk_step H1 r rs kr). exact HRMr.
  - (* the counts: gesture_model's peak is at most 2 (W_cnl_cnt.v cnl_cnt_gm_pre) *)
    exact (cnl_cnt_gm_pre RP r rs H1 _ HCNTr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hpG & regs2 & mem2 & md2 & kk2 & H2 & -> & HJg & HPg & HPKg & HERg & HLH2 & HND2 & HT2 & HC2 & HPm & HFR2 & HMLE2 & HRMg).
hp0g HJg.
set (HL2 := list_blks H2) in *.
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJg).
pose proof (HPm _ Hp1) as Hp2.
pose proof (Permutation_NoDup Hp2 (nls_nodup_blocks _ _ _ _ _ HAR2)) as HNDp2.
(* what gesture_model kept: its journal at G' *)
pose proof HJg as HJg0. eapply ajournal_gx_inner_x in HJg0. destruct HJg0 as (memS2 & HJgi & HgS2).
rewrite Usp in HJgi. destruct HJgi as (_ & _ & _ & _ & _ & _ & _ & _ & KF & KB & KI & _).
assert (Hcl : ~ YI16.sink_open_fp (blk_FP HL1)).
{ apply sink_closed_pos. apply Forall_forall. intros rr Hrr. unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - GM_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Ha Hn. rewrite KF by lia. apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) HL1 ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) memc (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi).
  - apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. unfold off_img in Hoff. lia.
  - intros (rr & Hrr & Hr). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p' & n') & <- & Hb'). cbn [fst snd] in Hr.
    assert (Hne : (p', n') <> (p, n)) by (intros E'; rewrite E' in Hb'; exact (Hn Hb')).
    pose proof (sep_blocks0 ly1 S1 W1 memc mdc p' n' p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb') Hb1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 memc) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 memc mem2 a); [|exact Hw]. intros Hp. exact (HPKg a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the source's own bytes (outside the held head) and the blocks of Ab *)
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W1 memc W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
assert (KAb : forall b a, In b Ab -> fst b <= a < fst b + snd b -> abyte_kept W1 memc W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by (apply Hinc; apply in_or_app; left; exact Hb).
  assert (Hb2 : In (p, n) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (Hn1 : ~ In (p, n) HL1) by exact (nls_nodup_disj _ Ab HL1 (p, n) HNDl Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr & _).
  replace a with (p + (a - p)) by lia.
  split; [apply (Kblk p n); [exact Hb1 | exact Hb2 | exact Hn1 | lia] | intros _; apply (Pblk p n); [exact Hb2 | lia]]. }
assert (HOB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks E1 ++ HL1) /\ ~ In (OUT, CO) HL2)).
{ destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
  assert (HOr : In (OUT, CO) (Ab ++ rest0)).
  { pose proof (Permutation_in _ Hp1 HOin) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
    exfalso. apply HOn. apply in_or_app. right. exact Hx. }
  split; [exact HCO|]. split; [exact HOin|].
  split; [apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; exact HOr|].
  split; [exact HOn|]. intros Hx. exact (nls_nodup_disj _ HL2 (Ab ++ rest0) (OUT, CO) HNDp2 Hx HOr). }
clear HOB.
assert (HnT2 : Z.of_nat (length (texts H2)) = hl_n H2) by (unfold texts, hl_n; rewrite length_map; reflexivity).
assert (HCS : hl_cap H2 = capstep (texts H1) (bzs (snd r)) (hl_cap H1)).
{ unfold capstep. rewrite <- HT2, HC2, <- HnT1, <- HnT2.
  destruct (Nat.ltb_spec (length (texts H1)) (length (texts H2)));
  destruct (Z.ltb_spec (Z.of_nat (length (texts H1))) (Z.of_nat (length (texts H2)))); try reflexivity; lia. }
pose proof (upd_len (texts H1) (bzs (snd r))) as (U1 & U2). rewrite <- HT2 in U1, U2.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) memc x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). exact (Kimg x Hi Ho He Hn). }
(* the state at 0x85f9c *)
exists regs2, mem2, md2. split; [rewrite R1; reflexivity|].
exists ly2, S2, (kk + kk2), H2, jk.
split; [exact HEQ|].
split.
{ pose proof (ajournal_gx_G_mono0 G' G 0 [] GM_STK (spZ regsc) (blk_FP HL1) ly1 S1 W1 memc mdc [] ly2 S2 W2 mem2 md2 kk2
    HG'G HJg) as HJg'. rewrite Usp in HJg'.
  pose proof (ajournal_gx_sub0 Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 memc mdc kk
    GM_STK (sp0 - 112) 0 [] (blk_FP HL1) [] ly2 S2 W2 mem2 md2 kk2 HJ HJg' ltac:(rewrite WS, WG; lia) ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP) as HJ2.
  cbn [app] in HJ2. exact HJ2. }
split; [exact (nls_apk_trans _ _ _ _ _ _ HPK HPKg)|].
split.
{ refine (nls_src_swap ly1 S1 W1 memc ly2 S2 W2 mem2 HA (set_exp_held h E1 H1) H2 HSRC KHd _ _ HLH2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Ab; apply in_or_app; right; apply in_or_app; left; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_expected] in Hb. rewrite !nls_alist_blks in Hb.
    apply (Permutation_in _ (Permutation_sym Hp2)). apply in_or_app. right. apply in_or_app. left. unfold Ab.
    destruct Hb as [<- | Hb]; [apply in_or_app; right; apply in_or_app; left; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup.
    replace (hs_blocks (set_exp_held (set_exp_held h E1 H1) (hs_expected (set_exp_held h E1 H1)) H2)) with (map fst (Ab ++ HL2)).
    + pose proof (nls_nodup_blocks_fst _ _ _ _ _ HAR2) as Hf.
      pose proof (Permutation_NoDup (Permutation_map fst (Permutation_trans Hp2 (Permutation_sym (nls_perm_swap _ Ab HL2 rest0)))) Hf) as Hf2.
      rewrite map_app in Hf2. exact (NoDup_app_remove_r _ _ Hf2).
    + unfold hs_blocks, Ab, HL2. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
split; [exact HND2|].
split; [rewrite upds_snoc, <- HTX; exact HT2|].
split; [rewrite cnl_cap_snoc, <- HTX, <- HCAP; exact HCS|].
split.
{ rewrite txs_app, nls_cb_app. change (txs [r]) with [bzs (snd r)]. rewrite nls_cb_one.
  destruct (is_begin (bzs (snd r))) eqn:Eb; [lia|].
  destruct (Nat.lt_ge_cases (length (texts H1)) (length (texts H2))) as [Hlt | Hge]; [destruct (U2 Hlt) as [Hb _]; congruence | lia]. }
split.
{ rewrite HC2. destruct (Z.ltb_spec (hl_n H1) (hl_n H2)) as [Hlt | Hge]; [|exact HCB].
  destruct (U2 ltac:(lia)) as (Hbeg & _).
  assert (Hcbe : (count_begin (txs pre) + 1 <= count_begin (texts EE))%nat).
  { change (texts EE) with (txs (hl_recs EE)). rewrite HEQ, txs_app, nls_cb_app.
    change (txs (r :: rs)) with ([bzs (snd r)] ++ txs rs). rewrite nls_cb_app, nls_cb_one, Hbeg. lia. }
  unfold capb, grow_cap in *. destruct (hl_n H1 =? hl_cap H1) eqn:Eq; [|lia]. apply Z.eqb_eq in Eq. destruct (hl_cap H1 =? 0); lia. }
split.
{ intros rest HQ0. pose proof (HPERM rest HQ0) as HP1x.
  assert (HP1y : Permutation (ablocks B ly1 S1) (HL1 ++ list_blks E1 ++ rest))
    by (eapply Permutation_trans; [exact HP1x|]; rewrite app_assoc; apply nls_perm_swap).
  eapply Permutation_trans; [exact (HPm _ HP1y)|]. rewrite app_assoc. apply nls_perm_swap. }
split; [rewrite HFR2; exact HFR|].
split.
{ eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLE2)|].
  rewrite nls_go_snoc, HGC, HTX, HCAP. lia. }
split.
{ replace (cnl_go MT (texts H2) (hl_cap H2) rs) with
    (cnl_go MT (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
    by (rewrite <- HT2, <- HCS; reflexivity).
  apply (mo_ok_step MT ML S1 S2 (gm_cost MT H1 (snd r))); [|exact HMLE2].
  rewrite HGC, Z.add_assoc. exact HMOK. }
split.
{ rewrite <- HT2, <- HCS in HRM3.
  assert (BB : blocks_bytes S2 = blocks_bytes S1 - hbytes (texts H1) (hl_cap H1) + hbytes (texts H2) (hl_cap H2)).
  { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hp1), (bsum_perm _ _ Hp2), !bsum_app.
    unfold HL1, HL2. rewrite !bsum_list_blks. lia. }
  rewrite BB. exact HRM3. }
split.
{ (* the room past gesture_model: its post's kr *)
  rewrite HT2, HCS. exact HRMg. }
split.
{ (* the live counts past gesture_model (W_cnl_cnt.v cnl_cnt_gm_post) *)
  apply (cnl_cnt_gm_post RP r rs H1 H2 (ablocks B ly1 S1) (ablocks B ly2 S2) (Ab ++ rest0));
  [first [exact HND | apply NoDup_ListNoDup; exact HND] | exact HT2 | exact HCS | exact Hp1 | exact Hp2 | exact HCNTr]. }
split.
{ apply (nls_vm_kept W1 W2 memc mem2 AT 8); [|exact HAT]. intros i Hi. apply Kstk; [|lia]. split; [lia|]. cbn in Hi. lia. }
split.
{ pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & Arom).
  cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale, Arom.
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C1]; intros i Hi;
    apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C2]; intros i Hi;
    apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C3]; intros i Hi;
    apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split.
  { apply (nls_ob_kept W1 W2 memc mem2); [|exact C4]. intros i Hi.
    destruct HOB2 as [-> | (HCO & HOin & HOin2 & HOn & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly1 S1 W1 memc mdc OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
    apply (Kblk OUT CO); [exact HOin | exact HOin2 | intros Hx; apply HOn; apply in_or_app; right; exact Hx | lia]. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as [He Hrp].
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Ho].
    - exact (rom_pinned_view0 ly2 S2 W2 mem2 md2 a HAR2 (Hrp Hown)).
    - rewrite (Kimg a (nls_rom_img a Hr) Ho He (fun Hn => Arom a ltac:(lia) Hr)). exact (C5 a Hr). }
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C6]; intros i Hi;
    apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C7]; intros i Hi;
    apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
  apply (nls_garr8_kept W1 W2 memc mem2); [|exact C8]; intros i Hi.
  apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
split.
{ destruct HOB2 as [Hob0 | (HCO & _ & HOin2 & HOn & HOn2)]; [left; exact Hob0 | right].
  split; [exact HCO|]. split; [exact HOin2|].
  intros Hx. apply in_app_or in Hx as [Hx | Hx]; [apply HOn; apply in_or_app; left; exact Hx | exact (HOn2 Hx)]. }
split; [exact HSTR|].
split; [intros i Hi; rewrite (HERg i Hi); exact (HERR i Hi)|].
split.
{ intros a Ha. rewrite Kstk by lia. exact (HSRD a Ha). }
split; [apply (nls_frame_kept W1 W2 memc mem2 HFRM); intros a Ha; apply Kstk; lia|].
destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q22 & Q23 & Q24 & Q25 & Q27).
assert (P2 : getr regs2 2 = getr regsc 2) by (apply (HPg 2); unfold acallee_saved; lia).
assert (P3 : getr regs2 3 = getr regsc 3) by (apply (HPg 3); unfold acallee_saved; lia).
assert (P4 : getr regs2 4 = getr regsc 4) by (apply (HPg 4); unfold acallee_saved; lia).
assert (P8 : getr regs2 8 = getr regsc 8) by (apply (HPg 8); unfold acallee_saved; lia).
assert (P9 : getr regs2 9 = getr regsc 9) by (apply (HPg 9); unfold acallee_saved; lia).
assert (P18 : getr regs2 18 = getr regsc 18) by (apply (HPg 18); unfold acallee_saved; lia).
assert (P19 : getr regs2 19 = getr regsc 19) by (apply (HPg 19); unfold acallee_saved; lia).
assert (P22 : getr regs2 22 = getr regsc 22) by (apply (HPg 22); unfold acallee_saved; lia).
assert (P23 : getr regs2 23 = getr regsc 23) by (apply (HPg 23); unfold acallee_saved; lia).
assert (P24 : getr regs2 24 = getr regsc 24) by (apply (HPg 24); unfold acallee_saved; lia).
assert (P25 : getr regs2 25 = getr regsc 25) by (apply (HPg 25); unfold acallee_saved; lia).
assert (P27 : getr regs2 27 = getr regsc 27) by (apply (HPg 27); unfold acallee_saved; lia).
unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P27.
repeat split; assumption.
Qed.
(* next_line's two out cells in this frame: len at sp + 0 (= |r|, atom 36, the atom of v[0].n, so the runner settles
   the length compare 0x85f60) and line at sp + 8 (atom 66) *)
Definition cnl_cells : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0)); YP09.mkChunk 8 (CVal 8 (SOff 66 0))].
Lemma nls_nowin : forall E (rs : smem) (m m' : word -> option byte), frame_of E rs m m' ->
forallb (fun r => Z.eqb (YP09.r_wlo r) (YP09.r_whi r)) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' Hf Hb x. apply Hf. intros (r & Hin & Hr). rewrite forallb_forall in Hb.
pose proof (Hb r Hin) as He. apply Z.eqb_eq in He. lia.
Qed.
Lemma nls_eqv_view : forall (W1 : world SEGS) (m m' : word -> option byte),
(forall x, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
(forall a, aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) /\ (forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a).
Proof.
intros W1 m m' Hq. split.
- intros a. apply aview_eq_of. apply Hq.
- intros a (Hh & b & Hb). split; [exact Hh|]. exists b. pose proof (Hq (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx.
  rewrite Hh in Hx. rewrite Hx. exact Hb.
Qed.
(* the loop's facts survive a step that keeps the bytes below the allocator's ceiling and the saved registers *)
Lemma nls_inv_kept : forall ly1 S1 (W1 : world SEGS) m m' md1 hs,
AR0 ly1 S1 W1 m md1 ->
(forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W1) m' a = aview SEGS (w_H W1) m a) ->
(forall a, apresent (w_H W1) m a -> apresent (w_H W1) m' a) ->
(ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO) ->
asrc_at B ly1 S1 W1 m HA hs -> cnl_consts W1 m -> cnl_frame_ok W1 m sp0 regs0 -> apres_kept B W mem W1 m ->
asrc_at B ly1 S1 W1 m' HA hs /\ cnl_consts W1 m' /\ cnl_frame_ok W1 m' sp0 regs0 /\ apres_kept B W mem W1 m'.
Proof.
intros ly1 S1 W1 m m' md1 hs HAR Hlo Hfr Hp Hob HS HC HF HK.
split; [exact (nls_src_kept_low ly1 S1 W1 m m' md1 hs HAR HS Hlo Hp)|].
split; [exact (nls_consts_kept_low ly1 S1 W1 m m' md1 HAR Hob Hlo HC)|].
split; [exact (nls_frame_kept W1 W1 m m' HF Hfr)|].
exact (nls_apk_trans _ _ _ _ _ _ HK (nls_apk_of_pres W1 m m' Hp)).
Qed.
Lemma nls_exp_held_nodup : forall ly1 S1 (W1 : world SEGS) m1 hs, asrc_at B ly1 S1 W1 m1 HA hs ->
List.NoDup (list_blks (hs_expected hs) ++ list_blks (hs_held hs)).
Proof.
intros ly1 S1 W1 m1 hs HS.
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HND).
apply NoDup_ListNoDup in HND. unfold hs_blocks in HND. rewrite <- !nls_map_fst_blks in HND.
apply NoDup_app_remove_l in HND. cbn [app] in HND. apply List.NoDup_cons_iff in HND as [_ HND].
rewrite <- map_app in HND. exact (nls_nodup_map _ _ fst _ HND).
Qed.
Lemma nls_view_of_garr8 : forall (W1 : world SEGS) m a (l : list byte) i, garr8 SEGS (arm W1 m) a (bzs l) ->
(i < length l)%nat -> aview SEGS (w_H W1) m (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).
Proof.
intros W1 m a l i Hg Hi. unfold aview, arm in *.
rewrite (garr8_mbyte SEGS _ _ _ i Hg) by (unfold bzs; rewrite length_map; exact Hi). cbn [option_map]. f_equal.
unfold bzs. rewrite (nth_indep _ 0 (HarnessRep.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
rewrite map_nth. unfold HarnessRep.bz. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma nls_nth_skipn : forall (T0 : Type) n m (l : list T0) d, nth m (skipn n l) d = nth (n + m) l d.
Proof. intros T0. induction n as [|n IH]; intros m [|x l] d; cbn; try reflexivity; [destruct m; reflexivity | apply IH]. Qed.
Lemma nls_bsr_cons : forall r0 rs0, bsr (r0 :: rs0) = snd r0 ++ Z_to_bv 8 0 :: bsr rs0.
Proof. intros r0 rs0. unfold bsr. cbn [map concat]. rewrite <- app_assoc. reflexivity. Qed.
Lemma nls_bsr_app : forall a b, bsr (a ++ b) = bsr a ++ bsr b.
Proof. intros a b. unfold bsr. rewrite map_app, concat_app. reflexivity. Qed.
(* the stack's shadow is zero: the laws' per-byte zero-shadow field of the real stack (YCbqG.v alx_zshadow_byte) *)
Lemma nls_ra_stack : forall ly1 S1 (W1 : world SEGS) mem1 md1 a len,
AR0 ly1 S1 W1 mem1 md1 -> ly_stk_lo ly1 <= a -> a + len <= ly_stk_hi ly1 -> 0 <= len ->
range_addressable (aview SEGS (w_H W1) mem1) SHADOW_OFF a len.
Proof.
intros ly1 S1 W1 mem1 md1 a len HAR Hlo Hhi Hlen x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr. exact (alx_zshadow_byte _ _ _ LAWS ly1 S1 [] W1 mem1 md1 x HAR ltac:(lia)).
Qed.
(* bytes seen through the ASan view, as a byte array *)
Lemma nls_garr8_of_view : forall (W1 : world SEGS) m a (ln : list byte),
(forall i, (i < length ln)%nat -> aview SEGS (w_H W1) m (a + Z.of_nat i) = Some (bv_unsigned (nth i ln (Z_to_bv 8 0)))) ->
garr8 SEGS (arm W1 m) a (bzs ln).
Proof.
intros W1 m a ln Hv jj Hj. unfold bzs in Hj. rewrite length_map in Hj.
assert (Hn : nth jj (bzs ln) 0 = bv_unsigned (nth jj ln (Z_to_bv 8 0))).
{ unfold bzs. rewrite (nth_indep _ 0 (HarnessRep.bz (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
  rewrite map_nth. reflexivity. }
pose proof (bv_unsigned_in_range 8 (nth jj ln (Z_to_bv 8 0))) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite Hn. split; [|lia].
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
pose proof (Hv jj Hj) as Hj'. unfold aview, arm in *. destruct (mbyte SEGS (mrestrict (w_H W1) m) (a + Z.of_nat jj)) as [b|] eqn:Eb;
  cbn [option_map] in Hj'; [|discriminate]. injection Hj' as Hj'. f_equal. apply bv_eq. rewrite Hj'.
assert (Hlb : forall z, 0 <= z < 256 -> le_byte z 1 0 = z).
{ intros z Hz. unfold le_byte. replace (8 * Z.of_nat 0) with 0 by reflexivity. replace (8 * Z.of_nat 1) with 8 by reflexivity.
  rewrite Z.shiftr_0_r. rewrite (Z.mod_small z (2 ^ 8)) by lia. apply Z.mod_small. lia. }
rewrite Hlb by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.
(* a run over regions with no write window writes nothing *)
Ltac nls_nowin_awr :=
  let a := fresh "a" in let rr := fresh "rr" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (rr & Hin & Hr);
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In rr l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hr; lia|]);
  destruct Hin.
(* one iteration up to gesture_model's return *)Lemma cnl_step : forall pre r rs W1 regs1 mem1 md1, cnl_inv pre (r :: rs) W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) (cnl_midQ pre r rs).
Proof.
intros pre r rs W1 regs1 mem1 md1 HI.
destruct HI as (ly1 & S1 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : AR0 ly1 S1 W1 mem1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE1 & _).
cbn [set_exp_held hs_expected] in HE1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields ly1 S1 W1 mem1 (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_loop W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 17)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 4%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (Vb33 : base_val Ev (Some 33%nat) = hl_v EE) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vbg : base_val Ev (Some 268%nat) = VAL A_g_gone)
  by (change (Some 268%nat) with (Some A_g_gone); cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 112) by (cbn [base_val]; exact Usp).
clear HEv EX.
(* the callee-saved registers at the loop head, as the state names them *)
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (27%bv : bv 5) O27.
assert (HOBx : ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO)
  by (destruct HOB as [H0 | (Hc1 & Hc2 & _)]; [left; exact H0 | right; split; assumption]).
assert (HinR1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk))).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HnH1 : ~ In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks H1)).
{ pose proof (nls_exp_held_nodup _ _ _ _ _ HSRC) as Hnd. cbn [set_exp_held hs_expected hs_held] in Hnd.
  exact (nls_nodup_disj _ _ _ _ Hnd HinR1). }
assert (HgarR0 : garr8 SEGS (arm W1 mem1) (fst r) (bzs (snd r))).
{ unfold bzs in HgarR. rewrite map_app in HgarR. apply garr8_app in HgarR as [Hg _]. exact Hg. }
unfold A_cnl_loop.
(* ---- 0x85ec4: lbu a0, g_gone; beqz ---- *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { nls_nowin_awr. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* g_gone clear: next_line, the two compares, bcmp *)
  assert (Hg0 : gone = 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
  destruct (HSTR Hg0) as (rest0 & Hsk). rewrite nls_bsr_cons, <- app_assoc in Hsk. cbn [app] in Hsk.
  set (An := cpos gone A0 pre) in *.
  assert (HAn0 : 0 <= An) by (unfold An, cpos; rewrite Hg0; cbn; lia).
  assert (HAnO : An + Z.of_nat (length (snd r)) + 1 <= NO).
  { pose proof (f_equal (@length byte) Hsk) as Hl. rewrite length_skipn, length_app in Hl. cbn [length] in Hl. lia. }
  destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [rewrite Hob0 in AOBN; cbn [length] in AOBN; lia|].
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (HO16 & HO4096 & _ & HOle & HOreq1 & HOceil & _ & HOoff & HOapp & HOpres).
  (* ---- 0x85f18: to next_line(at, sp + 8, sp + 0) ---- *)
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_next_line. { nls_nowin_awr. }
  assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ1) as (AV1 & AP1).
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
  prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  assert (UspN : spZ (ms_regs ms0) = sp0 - 112) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
  destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms0) mdN kk HJ)
    as (memS & HJi & _).
  pose proof HJi as (HARN & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRN & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  (* s0 = at: the callee's frame-pointer chain from it *)
  assert (N2w : getr (ms_regs ms0) 2 = w64 (sp0 - 112)) by (rewrite N2, E2; reflexivity).
  assert (N8w : getr (ms_regs ms0) 8 = w64 AT) by (rewrite N8, (EEo 8%nat 8%bv eq_refl); exact R8).
  assert (SRD0 : cnl_stk_rd W1 (ms_mem ms0)) by (intros a Ha; rewrite AV1; exact (HSRD a Ha)).
  destruct (cnl_chain_at ly1 S1 kk W1 (ms_mem ms0) mdN (ms_regs ms0) HJ SRD0
    (nls_frame_kept W1 W1 mem1 (ms_mem ms0) HFRM (fun a _ => AV1 a)) N2w N8w) as (chn & Hchn).
  assert (HPREn : AFP0 NL_STK ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) mdN chn).
  { eapply (afn_pre_at0 (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms0) mdN kk (ms_regs ms0)
      NL_STK (- 112 - XO) chn HJi).
    - rewrite UspN. lia.
    - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
    - lia.
    - unfold NL_STK, NL_FRAME, ESTACK; lia.
    - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
    - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact Hchn. }
  assert (HATn : val_mem SEGS (arm W1 (ms_mem ms0)) AT 8 An) by (apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact HAT]).
  eapply SRr_bind.
  { eapply (NL W1 ly1 S1 [] (ms_regs ms0) (ms_mem ms0) mdN chn (112 + XO) AT (sp0 - 104) (sp0 - 112) An NO OUT ob HPREn).
    - lia.
    - rewrite Z.add_mod, AX16 by lia. reflexivity.
    - rewrite UspN, Etop. lia.
    - intros a Ha. apply HPRN. rewrite UspN in Ha. lia.
    - rewrite N10, (EEo 8%nat 8%bv eq_refl). exact R8.
    - rewrite N11, Usp. f_equal. lia.
    - rewrite N12. first [rewrite Usp; f_equal; lia | rewrite E2; reflexivity].
    - exact AAT8.
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 13; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 14; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - lia.
    - lia.
    - lia.
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - exact HATn.
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cno].
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cout].
    - exact AOBN.
    - apply (nls_ob_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cob].
    - lia.
    - intros _. split; [lia|]. split; [lia|]. split; [apply ANO32; lia|].
      intros a Ha. rewrite UspN. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - intros _. split; [rewrite Hsk; apply in_or_app; right; left; reflexivity|].
      split; [exact AMRO|].
      split; [apply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia]|].
      { exact HOin. }
      split; [apply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia | lia]|].
      { exact HOin. }
      intros a Hr. unfold rom_view in Crom. rewrite (AV1 a). exact (Crom a Hr). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
  subst W2.
  destruct HARM as [(HAO & _) | (ln & _ & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
  assert (Hln : ln = snd r).
  { destruct Hfl as (rest & Hsk2 & Hnz'). rewrite Hsk in Hsk2. exact (nls_nul_split (snd r) ln (bsr rs ++ rest0) rest Hsk2 HnzR Hnz'). }
  subst ln.
  (* next_line's journal inside this one *)
  pose proof HJn as (_ & _ & _ & HXOn). rewrite UspN in HXOn, HFRn.
  pose proof (ajournal_gx_G_mono0 [] G (112 + XO) (nl_cells AT (sp0 - 104) (sp0 - 112)) NL_STK (spZ (ms_regs ms0)) []
    ly1 S1 W1 (ms_mem ms0) mdN [] ly1 S1 W1 mem2 md2 0 (fun a Ha => False_ind _ (inG_nil a Ha)) HJn) as HJn'.
  rewrite UspN in HJn'.
  pose proof (ajournal_gx_sub0 Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms0) mdN kk
    NL_STK (sp0 - 112) (112 + XO) (nl_cells AT (sp0 - 104) (sp0 - 112)) [] [] ly1 S1 W1 mem2 md2 0 HJ HJn'
    ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
  specialize (HJ2 ltac:(intros a (rr & Hrr & Ha); cbn [nl_cells In] in Hrr;
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
    [right; exists (AT, AT + 8); split; [left; reflexivity | cbn [fst snd]; lia] | left; rewrite WS; lia | left; rewrite WS; lia])
    HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))).
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (KEEPn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - NL_STK <= a < sp0 - 112) ->
    ~ inFP (nl_cells AT (sp0 - 104) (sp0 - 112)) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms0) a).
  { intros a Ha Hn Hcx. destruct (Z_lt_le_dec a (sp0 - 112)) as [Hlt | Hge]; [apply HFRn; [exact Ha | lia | exact Hcx]|].
    destruct (Z_lt_le_dec a (sp0 - 112 + (112 + XO))) as [Hlt2 | Hge2]; [apply HXOn; [lia | exact Hcx]|].
    apply HFRn; [exact Ha | lia | exact Hcx]. }
  assert (Hncell : forall a, ~ (sp0 - 112 <= a < sp0 - 96) -> a < AT \/ AT + 8 <= a ->
    ~ inFP (nl_cells AT (sp0 - 104) (sp0 - 112)) a).
  { intros a Hx1 Hx2 (rr & Hrr & Ha). cbn [nl_cells In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia. }
  (* back at 0x85f28: keep the four regions, reseat the frame cells len (sp + 0) and line (sp + 8) *)
  jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); apply KEEPn.
    - rewrite Vb2 in Ha. lia.
    - rewrite Vb2 in Ha. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb2 in Ha; lia.
    - rewrite Vbg in Ha. lia.
    - rewrite Vbg in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vbg in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb9 in Ha. lia.
    - rewrite Vb9 in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb9 in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. unfold AREC in *. lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC, NL_STK, NL_FRAME, ESTACK in *. lia.
    - apply Hncell; rewrite Vb33 in Ha; rewrite HreqV in Hvceil; rewrite WS in Hslo; unfold AREC in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 50)%nat -> ew Ea m = ew Ev m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (F54 : ew Ea 54 = Z_to_bv 64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
  clear HEa.
  (* atom 66: the line's address, the value next_line left at sp + 16 *)
  apply (st_ok_pi_havoc_hi 66 Ea _ _ [Z_to_bv 64 (OUT + An)]) in HS; [|vm_compute; reflexivity].
  remember (havoc Ea 66 [Z_to_bv 64 (OUT + An)]) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 66)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  assert (F66 : ew Eb 66 = Z_to_bv 64 (OUT + An)) by (rewrite HEb; reflexivity).
  clear HEb.
  assert (OLD : forall m, (m < 50)%nat -> ew Eb m = ew Ev m) by (intros m Hm; rewrite OLDb by lia; exact (OLDa m Hm)).
  assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (Vb2b : base_val Eb (Some 2%nat) = sp0 - 112) by (cbn [base_val]; rewrite OLD by lia; exact Usp).
  assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (rewrite <- Vb9; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vb33b : base_val Eb (Some 33%nat) = hl_v EE) by (rewrite <- Vb33; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vbgb : base_val Eb (Some 268%nat) = VAL A_g_gone).
  { cbn [base_val]. assert (Hb : (A_TEXT <= 268 < A_LIM)%nat) by (cbv [A_TEXT A_LIM]; lia). exact (HEIb 268%nat Hb). }
  assert (HAR2 : AR0 ly1 S1 W1 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ2).
  apply (st_ok_pi_add_region Eb _ _ cnl_cells) in HS; [| reflexivity | | ].
  2: { unfold region_ok, cnl_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
    rewrite Vb2b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 112) 0 8 (SOff 36 0) (Z.of_nat (length (snd r))));
      [cbn [sv_denot]; rewrite OLD by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; unfold APARTIAL in HlenR; lia | cbn; lia |].
      replace (sp0 - 112 + 0) with (sp0 - 112) by lia. exact Vlen2.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 112) 8 8 (SOff 66 0) (OUT + An));
      [cbn [sv_denot]; rewrite F66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (sp0 - 112 + 8) with (sp0 - 104) by lia. exact Vln2. }
  2: { apply all_disjoint_of_extents. unfold cnl_cells, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
    rewrite Vb2b, Vbgb, Vb9b, Vb33b. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC in *. repeat split; lia. }
  assert (SHOK2 : sh_ok SEGS BxL cnl_lSH Eb (mrestrict (w_H W1) mem2)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem2 md2 (HA + 64) 32 HAR2 AZS).
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 9 HA) by (first [rewrite OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block0 ly1 S1 W1 mem2 md2 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR2 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 33 (hl_v EE)) by (first [rewrite OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85f28: beqz a0 (abort); the traps on v (0x85f38, 0x85f3c-0x85f40); the length compare 0x85f60 (abort) ---- *)
  rewrite N1. paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUN BR HS SHOK2 Bspan.
  { (* next_line returned 0: impossible, it found r's line *)
    exfalso. rewrite branch_eq_U, (U_atom Eb 54 1), U_lit in Hc0 by (first [rewrite OLDb by lia; exact F54 | lia]).
    apply Z.eqb_eq in Hc0. lia. }
  clear Hc0. paj_run_tok_x RUN HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  (* ---- bcmp(line, v[0].s, len) at 0x85f84, returning to 0x85f88 ---- *)
  assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr2 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem2 (ms_mem ms2) MQ2) as (AV2 & AP2).
  assert (AVc : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite AV2, KEEPn; [apply AV1 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; rewrite WS in Hslo; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  assert (UspB : spZ (ms_regs ms2) = sp0 - 112) by (unfold spZ at 1; rewrite T2, OLD by lia; rewrite E2; apply unsigned_lit_small; lia).
  assert (HARB : AR0 ly1 S1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2
    (with_vm_backing (m_vm_lazy md2) mat1 md2))) by (eapply ajournal_gx_AR_x; exact HJ2).
  eapply SRr_bind.
  { eapply (aj_bcmp_gx_at0 (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CNL_STK sp0 FPc ly S W mem md []
      ly1 S1 _ kk (OUT + An) (fst r) (Z.of_nat (length (snd r))) (-112) (Z_to_bv 64 (BASE + 15428)) HG AX16 HJ2).
    - rewrite T10. exact F66.
    - rewrite T11, OLD by lia. exact E35.
    - rewrite T12, OLD by lia. exact E36.
    - unfold APARTIAL in HlenR. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite UspB. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite T3, OLD by lia. rewrite (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite T4, OLD by lia. rewrite (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AV2. replace a with (OUT + (a - OUT)) by lia. rewrite (Hob2 (a - OUT)) by lia. discriminate.
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AVc by lia. unfold aview, arm in *. replace a with (fst r + Z.of_nat (Z.to_nat (a - fst r))) by lia.
      rewrite (garr8_mbyte SEGS _ _ _ _ HgarR0) by (unfold bzs; rewrite length_map; lia). discriminate.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - unfold amem_range in *. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
    - apply (range_addressable_of_block0 _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - intros Hp. apply (shadow_hull_vis_of_block0 _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - apply (range_addressable_of_block0 _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia.
    - intros Hp. apply (shadow_hull_vis_of_block0 _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
  (* r's line in the stream, as next_line left it *)
  assert (STR : forall i, (i < length (snd r))%nat ->
    aview SEGS (w_H W1) mem2 (OUT + An + Z.of_nat i) = Some (bv_unsigned (nth i (snd r) (Z_to_bv 8 0)))).
  { intros i Hi. replace (OUT + An + Z.of_nat i) with (OUT + (An + Z.of_nat i)) by lia.
    rewrite (Hob2 (An + Z.of_nat i)) by lia. do 2 f_equal.
    replace (Z.to_nat (An + Z.of_nat i)) with (Z.to_nat An + i)%nat by lia.
    rewrite <- nls_nth_skipn, Hsk. rewrite app_nth1 by exact Hi. reflexivity. }
  (* the line is v[0].s's text: bcmp returned 0 *)
  assert (Hv0 : vb = w64 0).
  { apply Hcmp. intros i Hi. rewrite AV2, AVc by lia.
    replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite STR by lia.
    rewrite (nls_view_of_garr8 W1 mem1 (fst r) (snd r) (Z.to_nat i) HgarR0) by lia. reflexivity. }
  assert (HAR3 : AR0 ly1 S1 W1 mem3 md3) by (eapply ajournal_gx_AR_x; exact HJ3).
  jafter_call_keep_pi HS 67%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); rewrite ?Vb2b, ?Vbgb, ?Vb9b, ?Vb33b in Ha; apply Hfr3;
    rewrite ?HreqV in Hvceil; rewrite ?WS in Hslo; unfold AREC, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Eb 67 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
  assert (OLDc : forall m, (m < 67)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
  assert (F71 : ew Ec 71 = Z_to_bv 64 0) by (rewrite HEc; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv, Hv0; reflexivity).
  clear HEc.
  assert (SHOK3 : sh_ok SEGS BxL cnl_lSH Ec (mrestrict (w_H W1) mem3)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem3 md3 (HA + 64) 32 HAR3 AZS).
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 9 HA) by (first [rewrite OLDc, OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block0 ly1 S1 W1 mem3 md3 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR3 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 33 (hl_v EE)) by (first [rewrite OLDc, OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85f88: bnez a0 (abort), then gesture_model(s, line, len) at 0x85f98 ---- *)
  paj_run_tok_x RUN HS HJ3 SHOK3 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUN BR HS SHOK3 Bspan.
  { exfalso. rewrite branch_ne_U, (U_atom Ec 71 0 F71), U_lit in Hc0 by lia. cbn in Hc0. discriminate. }
  clear Hc0. paj_run_to_tok_x RUNTO HS HJ3 SHOK3 Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ3 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr4 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem3 (ms_mem ms4) MQ3) as (AV3 & AP3).
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - 2 * ESTACK <= a < sp0 - 112) ->
    aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) (ms_mem ms2) a).
  { intros a Ha Hn. rewrite AV3. apply Hfr3; [exact Ha | lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  assert (LOW : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). exact (AVc a Ha). }
  assert (FRM : forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (unfold ESTACK; lia). rewrite AV2, KEEPn; [apply AV1 | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; lia. }
  assert (PRS : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms4) a)
    by (intros a Hp; apply AP3, Hpres3, AP2, HPn, AP1, Hp).
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms4) md1 _ HAR1 LOW FRM PRS (or_intror (conj HOin HCO)) HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  assert (Ecp' : cpos gone A0 (pre ++ [r]) = An + Z.of_nat (length (snd r)) + 1).
  { unfold An, cpos. rewrite Hg0. cbn [Z.eqb]. rewrite nls_bsr_app, length_app, nls_bsr_cons, length_app. cbn [length].
    change (bsr []) with (@nil byte). cbn [length]. lia. }
  eapply (cnl_gm pre r rs ly1 S1 kk H1 jk W1 (ms_regs ms4) (ms_mem ms4) _ (OUT + An) OUT CO
    HEQ HJ3 HPK' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite Ecp'. apply (nls_vm_kept W1 W1 mem2 (ms_mem ms4)); [|exact Vat2].
    intros i Hi. rewrite KEEPb by (cbn in Hi; unfold ESTACK; lia). exact (AV2 _).
  + exact HCONST'.
  + right. split; [exact HCO|]. split; [exact HOin | exact HOn].
  + intros _. exists rest0. rewrite Ecp'.
    replace (Z.to_nat (An + Z.of_nat (length (snd r)) + 1)) with ((length (snd r) + 1) + Z.to_nat An)%nat by lia.
    rewrite <- skipn_skipn, Hsk, skipn_app, skipn_all2 by lia.
    replace (length (snd r) + 1 - length (snd r))%nat with 1%nat by lia. reflexivity.
  + intros i Hi. rewrite LOW by exact (proj2 (cnl_errno_low i Hi)). exact (HERR i Hi).
  + intros a Ha. rewrite KEEPb by lia. rewrite AV2.
    destruct (Z_lt_le_dec a AT) as [Hl | Hg]; [|destruct (Z_lt_le_dec a (AT + 8)) as [Hl2 | Hg2]].
    * rewrite KEEPn by (try lia; apply Hncell; lia). rewrite AV1. exact (HSRD a Ha).
    * replace a with (AT + (a - AT)) by lia. exact (cnl_val_mem_view W1 mem2 AT 8 _ (a - AT) Vat2 ltac:(cbn; lia)).
    * rewrite KEEPn by (try lia; apply Hncell; lia). rewrite AV1. exact (HSRD a Ha).
  + exact HFRM'.
  + unfold cnl_regs_ok.
    assert (OLDx : forall m, (m < 50)%nat -> ew Ec m = ew Ev m) by (intros m Hm; rewrite OLDc, OLD by lia; reflexivity).
    assert (P24 : getr (ms_regs ms4) 24 = getr regs1 24).
    { rewrite Q24, O24. apply bv_eq. rewrite (HEIc 384%nat ltac:(cbv [A_TEXT A_LIM]; lia)), (HEI 384%nat ltac:(cbv [A_TEXT A_LIM]; lia)).
      reflexivity. }
    rewrite P24.
    assert (P2 : getr (ms_regs ms4) 2 = getr regs1 2) by (rewrite Q2, O2; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P3 : getr (ms_regs ms4) 3 = getr regs1 3) by (rewrite Q3, O3; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P4 : getr (ms_regs ms4) 4 = getr regs1 4) by (rewrite Q4, O4; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P8 : getr (ms_regs ms4) 8 = getr regs1 8) by (rewrite Q8, O8; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P9 : getr (ms_regs ms4) 9 = getr regs1 9) by (rewrite Q9, O9; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P18 : getr (ms_regs ms4) 18 = getr regs1 18) by (rewrite Q18, O18; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P19 : getr (ms_regs ms4) 19 = getr regs1 19) by (rewrite Q19, O19; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P22 : getr (ms_regs ms4) 22 = getr regs1 22) by (rewrite Q22, O22; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P23 : getr (ms_regs ms4) 23 = getr regs1 23) by (rewrite Q23, O23; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P25 : getr (ms_regs ms4) 25 = getr regs1 25) by (rewrite Q25, O25; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P27 : getr (ms_regs ms4) 27 = getr regs1 27) by (rewrite Q27, O27; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P25, P27.
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10, OLDc, OLD by lia. exact E9.
  + rewrite Q11, OLDc by lia. exact F66.
  + rewrite Q12, OLDc, OLD by lia. exact E36.
  + apply nls_garr8_of_view. intros i Hi. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). rewrite AV2. exact (STR i Hi).
  + exact HOin.
  + intros Hx. apply HOn. apply in_or_app. right. exact Hx.
  + lia.
  + lia.
- (* g_gone set: the text v[0] goes to gesture_model unread (the traps on v, 0x85ed8 / 0x85edc-0x85ee0, on the way) *)
  assert (Hg1 : gone <> 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_neq in Hc; exact Hc).
  assert (Ecp : forall p, cpos gone A0 p = A0) by (intros p; unfold cpos; destruct (Z.eqb_spec gone 0); [contradiction | reflexivity]).
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ) as (AV & AP).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms0) md1 _ HAR1 (fun a _ => AV a) (fun a _ => AV a) AP HOBx HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  eapply (cnl_gm pre r rs ly1 S1 kk H1 jk W1 (ms_regs ms0) (ms_mem ms0) _ (fst r) (fst r) (Z.of_nat (length (snd r)) + 1)
    HEQ HJ HPK' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite !Ecp in *. apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HAT].
  + exact HCONST'.
  + exact HOB.
  + intros Hg0. contradiction.
  + intros i Hi. rewrite AV. exact (HERR i Hi).
  + intros a Ha. rewrite AV. exact (HSRD a Ha).
  + exact HFRM'.
  + unfold cnl_regs_ok.
    rewrite (eq_trans Q2 (eq_sym O2)), (eq_trans Q3 (eq_sym O3)), (eq_trans Q4 (eq_sym O4)), (eq_trans Q8 (eq_sym O8)),
      (eq_trans Q9 (eq_sym O9)), (eq_trans Q18 (eq_sym O18)), (eq_trans Q19 (eq_sym O19)), (eq_trans Q22 (eq_sym O22)),
      (eq_trans Q23 (eq_sym O23)), (eq_trans Q24 (eq_sym O24)), (eq_trans Q25 (eq_sym O25)), (eq_trans Q27 (eq_sym O27)).
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10. exact E9.
  + rewrite Q11. exact E35.
  + rewrite Q12. exact E36.
  + apply (nls_garr8_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HgarR0].
  + exact HinR.
  + exact HnH1.
  + lia.
  + lia.
Qed.
(* ------------------------------------------------------------------ the drop (B only: list_drop is a call) *)
(* the source with its expected list replaced: every other byte and block kept *)
Lemma nls_src_swap_e : forall ly1 S1 (W1 : world SEGS) m1 ly2 S2 (W2 : world SEGS) m2 HA0 (h0 : hsrc) (E' : hlist),
asrc_at B ly1 S1 W1 m1 HA0 h0 ->
(forall a, HA0 <= a < HA0 + 64 \/ HA0 + 80 <= a < HA0 + 96 -> abyte_kept W1 m1 W2 m2 a) ->
akept W1 m1 W2 m2 (gfp (hs_partial h0) (bzs (hs_pjunk h0)) :: alist_fp (HA0 + 16) (hs_pending h0) ++ alist_fp (HA0 + 80) (hs_held h0)) ->
(forall b, In b ((hs_partial h0, APARTIAL) :: alist_blks (hs_pending h0) ++ alist_blks (hs_held h0)) -> In b (ablocks B ly2 S2)) ->
alist_at B ly2 S2 W2 m2 (HA0 + 64) E' true ->
NoDup (hs_blocks (set_exp_held h0 E' (hs_held h0))) ->
asrc_at B ly2 S2 W2 m2 HA0 (set_exp_held h0 E' (hs_held h0)).
Proof.
intros ly1 S1 W1 m1 ly2 S2 W2 m2 HA0 h0 E'
  (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19 & H20 &
   H21 & H22 & H23 & H24) HK HF HB HL HND.
assert (Hvm : forall a n v, HA0 <= a -> a + Z.of_nat n <= HA0 + 64 ->
  val_mem SEGS (arm W1 m1) a n v -> val_mem SEGS (arm W2 m2) a n v)
  by (intros a n v Ha Hn Hv; apply (akept_vm W1 m1); [intros x Hx; apply HK; lia | exact Hv]).
split; [apply Hvm; [lia | cbn; lia | exact H1]|].
split; [apply Hvm; [lia | cbn; lia | exact H2]|].
split; [apply Hvm; [lia | cbn; lia | exact H3]|].
split; [apply Hvm; [lia | cbn; lia | exact H4]|].
split.
{ intros i Hi. destruct (Z_lt_le_dec i 64) as [Hi6 | Hi6]; [apply (proj2 (HK (HA0 + i) ltac:(lia))); exact (H5 i Hi)|].
  destruct (Z_lt_le_dec i 80) as [Hi8 | Hi8].
  - pose proof HL as (_ & _ & _ & HW & _). replace (HA0 + i) with (HA0 + 64 + (i - 64)) by lia. apply HW. lia.
  - apply (proj2 (HK (HA0 + i) ltac:(unfold ASRC in Hi; lia))). exact (H5 i Hi). }
split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H10
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; left; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; left; exact Hb]|].
split; [apply Hvm; [lia | cbn; lia | exact H11]|].
split; [apply Hvm; [lia | cbn; lia | exact H12]|].
split; [apply Hvm; [lia | cbn; lia | exact H13]|].
split; [apply Hvm; [lia | cbn; lia | exact H14]|].
split; [exact H15|]. split; [exact H16|]. split; [exact H17|].
split; [apply HB; left; reflexivity|].
split; [exact H19|].
split; [apply (akept_garr8 W1 m1); [intros x Hx; apply (HF (gfp (hs_partial h0) (bzs (hs_pjunk h0))));
  [left; reflexivity | exact Hx] | exact H20]|].
split; [exact H21|].
split; [exact HL|].
split; [apply (alist_at_kept B ly1 S1 W1 m1); [exact H23
  | eapply akept_sub; [exact HF | intros r Hr; right; apply in_or_app; right; exact Hr]
  | intros b Hb; apply HB; right; apply in_or_app; right; exact Hb] | exact HND].
Qed.
(* a permutation with one element taken out of the middle *)
Lemma cnl_perm_drop : forall (T0 : Type) (b1 b2 L : list T0) x, Permutation (b1 ++ x :: b2) (x :: L) -> Permutation (b1 ++ b2) L.
Proof. intros T0 b1 b2 L x H. apply (Permutation_cons_inv (a := x)). rewrite Permutation_middle. exact H. Qed.
Lemma cnl_nodup_mid : forall (T0 : Type) (l1 l2 l3 : list T0) x, List.NoDup ((l1 ++ l2) ++ l3) -> In x (l1 ++ l3) -> ~ In x l2.
Proof.
intros T0 l1 l2 l3 x H Hx. apply (nls_nodup_disj _ (l1 ++ l3) l2 x); [|exact Hx].
apply (Permutation_NoDup (l := (l1 ++ l2) ++ l3)); [|exact H].
rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.
(* the constants survive a run that changes no byte *)
Lemma cnl_consts_meq : forall (W1 : world SEGS) m m', (forall x, mrestrict (w_H W1) m' x = mrestrict (w_H W1) m x) ->
cnl_consts W1 m -> cnl_consts W1 m'.
Proof.
intros W1 m m' Hq (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
destruct (nls_eqv_view W1 m m' Hq) as (AV & _).
split; [apply (nls_vm_kept W1 W1 m m'); [intros i _; apply AV | exact C1]|].
split; [apply (nls_vm_kept W1 W1 m m'); [intros i _; apply AV | exact C2]|].
split; [apply (nls_vm_kept W1 W1 m m'); [intros i _; apply AV | exact C3]|].
split; [apply (nls_ob_kept W1 W1 m m'); [intros i _; apply AV | exact C4]|].
split; [intros a Hr; rewrite AV; exact (C5 a Hr)|].
split; [apply (nls_garr8_kept W1 W1 m m'); [intros i _; apply AV | exact C6]|].
split; [apply (nls_garr8_kept W1 W1 m m'); [intros i _; apply AV | exact C7]|].
apply (nls_garr8_kept W1 W1 m m'); [intros i _; apply AV | exact C8].
Qed.
(* the loop test after list_drop (0x85fa8 .. 0x85fb4, B only): back to the head 0x85ec4 while s->expected.n > 0,
   else the epilogue 0x85fc8 and the return *)
Lemma cnl_test : forall pre r rs W2 regs2 mem2 md2,
(rs <> [] -> forall W3 regs3 mem3 md3, cnl_inv (pre ++ [r]) rs W3 regs3 mem3 md3 ->
  SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + A_cnl_loop)) mem3 (seg_rom SEGS)) md3) Post) ->
cnl_inv (pre ++ [r]) rs W2 regs2 mem2 md2 ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_drp)) mem2 (seg_rom SEGS)) md2) Post.
Proof.
intros pre r rs W2 regs2 mem2 md2 IHL HI.
destruct HI as (ly2 & S2 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE2 & _).
cbn [set_exp_held hs_expected] in HE2.
pose proof HE2 as (MvE & MnE & _ & _ & (HnleC & HcapLt) & HvvE & _).
unfold cnl_E, hl_n in MvE, MnE, HnleC, HcapLt, HvvE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, HnleC, HcapLt, HvvE.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
assert (Hrs26 : Z.of_nat (length rs) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, !length_app in HnE. lia. }
assert (Rv : 0 <= hl_v EE < 2 ^ 64).
{ destruct HvvE as [(_ & ->) | (_ & Hvin & _)]; [lia|].
  destruct (cnl_blk ly2 S2 W2 mem2 md2 _ _ HAR2 Hvin) as (_ & H4096 & _ & _ & Hr1 & Hc & CC & _). lia. }
destruct (cnl_mkd A_cnl_drp W2 ly2 S2 mem2 md2 regs2 regs0 HA (hl_v EE) (Z.of_nat (length rs))
  HAR2 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 AZS HFRM MvE MnE Rv ltac:(lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs2 (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0)))) as Ed eqn:HEd.
assert (HEI : img_env VAL A_LIM Ed) by (rewrite HEd; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ed m = getr regs2 rr).
{ intros m rr Hm. rewrite HEd. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 17)%nat -> ew Ed (32 + k) = nth k (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEd. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ed 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E34 : ew Ed 34 = Z_to_bv 64 (Z.of_nat (length rs))) by exact (EX 2%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 49)%nat -> ew Ed k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (HAE : env_agree 32 (Ereg regs2 (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0))) Ed)
  by (rewrite HEd; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HEd.
prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24.
prreg HS (25%bv : bv 5) O25.
unfold A_cnl_drp.
(* ---- 0x85fa8: lb a0,0(s7) (shadow of s + 72: zero); lw a0,0(s2); bgtz a0 -> the head 0x85ec4 ---- *)
paj_run_tok_x RUN HS HJ SHOK Bspan. { nls_nowin_awr. }
assert (MQ : forall x, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x)
  by (intros x; exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x)).
destruct (nls_eqv_view W2 mem2 (ms_mem ms) MQ) as (AV & AP).
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s->expected.n > 0: the next pass, from the head *)
  assert (Hne : rs <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ed (SOff 34 0)) = Z.of_nat (length rs)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length rs))) = Z.of_nat (length rs)) by (apply unsigned_lit_small; lia).
      rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
    rewrite Hs in Hc. intros E0. rewrite E0 in Hc. cbn in Hc. lia. }
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x88). { nls_nowin_awr. }
  assert (MQ0 : forall x, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x). apply MQ. }
  destruct (nls_eqv_view W2 mem2 (ms_mem ms0) MQ0) as (AV0 & AP0).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 22; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
  prreg HS (25%bv : bv 5) F25.
  pmkst HS.
  unfold A_cnl_loop in IHL.
  apply (IHL Hne).
  exists ly2, S2, kk, H1, jk.
  split; [exact HEQ|].
  split; [exact HJ|].
  split; [exact (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W2 mem2 (ms_mem ms0) AP0))|].
  split; [exact (nls_src_kept_low ly2 S2 W2 mem2 (ms_mem ms0) md2 _ HAR2 HSRC (fun a _ => AV0 a) AP0)|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HN|]. split; [exact HCB|].
  split; [exact HPERM|]. split; [exact HFR|]. split; [exact HMLE|]. split; [exact HMOK|]. split; [exact HROOM|].
  split; [exact HRMr|]. split; [exact HCNTr|].
  split; [apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV0 | exact HAT]|].
  split; [exact (cnl_consts_meq W2 mem2 (ms_mem ms0) MQ0 HCONST)|].
  split; [exact HOB|]. split; [exact HSTR|].
  split; [intros i Hi; rewrite AV0; exact (HERR i Hi)|].
  split; [intros a Ha; rewrite AV0; exact (HSRD a Ha)|].
  split; [exact (nls_frame_kept W2 W2 mem2 (ms_mem ms0) HFRM (fun a _ => AV0 a))|].
  unfold cnl_regs_ok.
  rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)), (HK 8%bv ltac:(cbv; tauto)),
    (HK 9%bv ltac:(cbv; tauto)), (HK 22%bv ltac:(cbv; tauto)), (HK 27%bv ltac:(cbv; tauto)).
  rewrite (eq_trans F18 (eq_sym O18)), (eq_trans F19 (eq_sym O19)), (eq_trans F23 (eq_sym O23)), (eq_trans F24 (eq_sym O24)),
    (eq_trans F25 (eq_sym O25)).
  exact HREGS.
- (* s->expected.n = 0: the epilogue 0x85fc8 restores ra and s0..s10 and returns *)
  assert (Hrs0 : rs = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ed (SOff 34 0)) = Z.of_nat (length rs)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length rs))) = Z.of_nat (length rs)) by (apply unsigned_lit_small; lia).
      rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
    rewrite Hs in Hc. destruct rs; [reflexivity | cbn [length] in Hc; lia]. }
  subst rs.
  paj_run_tok_x RUN HS HJ SHOK Bspan. { nls_nowin_awr. }
  assert (MQ2 : forall x, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x). apply MQ. }
  destruct (nls_eqv_view W2 mem2 (ms_mem ms0) MQ2) as (AV2 & AP2).
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
  prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  assert (SV : forall k (rr : bv 5), (37 <= k < 49)%nat -> nth (k - 37) CNL_SAVED 0%bv = rr ->
    ew Ed k = getr regs0 rr).
  { intros k rr Hk Hn. rewrite (ES k Hk). unfold cnl_svals. rewrite (nth_indep _ 0 (bv_unsigned (getr regs0 0%bv)))
      by (cbn [length CNL_SAVED map]; lia).
    rewrite (map_nth (fun r0 => bv_unsigned (getr regs0 r0))). rewrite Hn. apply Z_to_bv_bv_unsigned. }
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?rr _ ?m _) ?d = _ /\ _ =>
    exists ly2, S2, [], rr, m, d, kk, (cnl_E [] jk), H1 end.
  split.
  { cbn [ms_regs]. rewrite F1, (SV 48%nat 1%bv ltac:(lia) eq_refl). rewrite Hra. reflexivity. }
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { intros rr Hr. unfold acallee_saved in Hr. cbn [ms_regs].
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite F2, E2, (unsigned_lit_small (sp0 - 112)) by lia. replace (sp0 - 112 + 112) with sp0 by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F3, (EEo 3%nat 3%bv eq_refl), R3. symmetry. exact Hgp.
    - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F4, (EEo 4%nat 4%bv eq_refl), R4. symmetry. exact Htp.
    - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F8. exact (SV 47%nat 8%bv ltac:(lia) eq_refl).
    - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F9. exact (SV 46%nat 9%bv ltac:(lia) eq_refl).
    - assert (rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)
        as Hr' by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
      + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F18. exact (SV 45%nat 18%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F19. exact (SV 44%nat 19%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F20. exact (SV 43%nat 20%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F21. exact (SV 42%nat 21%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F22. exact (SV 41%nat 22%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F23. exact (SV 40%nat 23%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F24. exact (SV 39%nat 24%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F25. exact (SV 38%nat 25%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F26. exact (SV 37%nat 26%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F27, (EEo 27%nat 27%bv eq_refl). exact R27. }
  split; [exact (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W2 mem2 (ms_mem ms0) AP2))|].
  split; [cbn [ms_mem]; intros i Hi; rewrite AV2; exact (HERR i Hi)|].
  split; [cbn [ms_mem]; exact (nls_src_kept_low ly2 S2 W2 mem2 (ms_mem ms0) md2 _ HAR2 HSRC (fun a _ => AV2 a) AP2)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [rewrite HTX; f_equal; change (texts EE) with (txs (hl_recs EE)); rewrite HEQ, app_nil_r; reflexivity|].
  split; [unfold capb in HCB; exact HCB|].
  pose proof HCONST as (Cgone & Cno & Cout & Cob & _).
  split.
  { cbn [ms_mem]. apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2|].
    replace (if gone =? 0 then A0 + Z.of_nat (length (bstream EE)) else A0) with (cpos gone A0 (pre ++ [r])); [exact HAT|].
    unfold cpos, bstream, bsr. rewrite HEQ, app_nil_r. reflexivity. }
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cgone]|].
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cno]|].
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cout]|].
  split; [cbn [ms_mem]; apply (nls_ob_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cob]|].
  split; [exact HPERM|].
  split; [exact HFR|].
  split; [unfold cnl_cost; rewrite HEQ, app_nil_r; exact HMLE|].
  split; [exact HRMr|].
  (* the held list's capacity (cnl_post_x's last two conjuncts): H' = H1, whose capacity is cnl_cap over every
     record (cnl_inv's HCAP at pre ++ [r] = hl_recs EE, rs = []); it never shrinks (W_cnl_cnt.v cnl_cap_ge) *)
  assert (ECAP : hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (hl_recs EE)) by (rewrite HCAP, HEQ, app_nil_r; reflexivity).
  split; [rewrite ECAP; apply cnl_cap_ge | exact ECAP].
Qed.
(* the rest of the iteration: list_drop(&s->expected, 0) at 0x85fa4, then the loop test 0x85fa8 .. 0x85fb4 *)
Lemma cnl_drop : forall pre r rs W1 regs1 mem1 md1,
(rs <> [] -> forall W2 regs2 mem2 md2, cnl_inv (pre ++ [r]) rs W2 regs2 mem2 md2 ->
  SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_loop)) mem2 (seg_rom SEGS)) md2) Post) ->
cnl_mid pre r rs W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros pre r rs W1 regs1 mem1 md1 IHL HM.
destruct HM as (ly1 & S1 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : AR0 ly1 S1 W1 mem1 md1) by (eapply ajournal_gx_AR_x; exact HJ).
set (EL := cnl_E (r :: rs) jk) in *.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold EL, cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields ly1 S1 W1 mem1 (HA + 64) EL true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v EL + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v EL + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_back W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
clear HEv.
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (27%bv : bv 5) O27.
unfold A_cnl_back.
(* ---- 0x85f9c: mv a0,s3; li a1,0; jal list_drop (0x85b50) ---- *)
paj_run_to_tok_x RUNTO HS HJ SHOK Bspan AF_fr_list_drop. { nls_nowin_awr. }
assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x)
  by (intros x; exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x)).
destruct (nls_eqv_view W1 mem1 (ms_mem ms) MQ) as (AV & AP).
pmkst HS.
prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (22%bv : bv 5) N22.
prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25. prreg HS (27%bv : bv 5) N27.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
assert (UspN : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
(* the registers list_drop is called with are the loop's *)
assert (HREGSN : cnl_regs_ok (ms_regs ms) regs0 HA).
{ unfold cnl_regs_ok.
  rewrite (eq_trans N2 (eq_sym O2)), (eq_trans N3 (eq_sym O3)), (eq_trans N4 (eq_sym O4)), (eq_trans N8 (eq_sym O8)),
    (eq_trans N9 (eq_sym O9)), (eq_trans N18 (eq_sym O18)), (eq_trans N19 (eq_sym O19)), (eq_trans N22 (eq_sym O22)),
    (eq_trans N23 (eq_sym O23)), (eq_trans N24 (eq_sym O24)), (eq_trans N25 (eq_sym O25)), (eq_trans N27 (eq_sym O27)).
  exact HREGS. }
(* list_drop's globals: s->expected's head only *)
set (G2 := [(HA + 64, 16)]).
assert (HG2G : forall a, inG G2 a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG2 : forall a, ~ (HA + 64 <= a < HA + 80) -> ~ inG G2 a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G2 G HG2G HG) as HG2.
assert (HG2R : forall a, inG G2 a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT2 : gx_rt B G2) by (eapply gx_rt_sub; [exact HG2R | exact HGRR]).
assert (HRO2 : rom_out SEGS B G2).
{ apply cnl_rom_out_gs. intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. rewrite AHAE in Ha. unfold ASRC in *. lia. }
(* list_drop's entry *)
destruct (ajournal_gx_inner0 G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms) mdN kk HJ)
  as (memS & HJi & _).
assert (SRD0 : cnl_stk_rd W1 (ms_mem ms)) by (intros a Ha; rewrite AV; exact (HSRD a Ha)).
assert (HFRM0 : cnl_frame_ok W1 (ms_mem ms) sp0 regs0) by exact (nls_frame_kept W1 W1 mem1 (ms_mem ms) HFRM (fun a _ => AV a)).
destruct (cnl_chain_at ly1 S1 kk W1 (ms_mem ms) mdN (ms_regs ms) HJ SRD0 HFRM0
  (proj1 HREGSN) (proj1 (proj2 (proj2 (proj2 HREGSN))))) as (chd & Hchd).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W1 (ms_regs ms) (ms_mem ms) mdN chd).
{ eapply (afn_pre_at0 (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms) mdN kk (ms_regs ms)
    LDROP_STK (- 112 - XO) chd HJi).
  - rewrite UspN. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - unfold LDROP_STK, LDROP_FRAME, ASTACK; lia.
  - rewrite WS. unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
  - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
  - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
  - exact Hchd. }
assert (HEL : alist_at B ly1 S1 W1 (ms_mem ms) (HA + 64) EL true).
{ apply (alist_at_kept B ly1 S1 W1 mem1 ly1 S1 W1 (ms_mem ms) (HA + 64) EL true HE1).
  - intros rr _ a _. apply abyte_kept_meq. apply MQ.
  - intros b Hb. exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb). }
assert (HZ0 : 0 <= cnl_go MT (texts H1) (hl_cap H1) rs).
{ pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _). apply nls_go_nonneg. unfold hl_n in HcapH1. lia. }
eapply SRr_bind.
{ refine (LDROP G2 HG2 HGRT2 HRO2 W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdN chd (HA + 64) EL true 0%nat HPREd _ _ HEL _ _ _ _ _ _ _ _
    (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)%nat _ _ _).
  - rewrite N10. first [rewrite <- O19; exact R19 | cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
  - rewrite N11. reflexivity.
  - unfold EL, cnl_E. cbn [hl_recs length]. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 8; reflexivity].
  - lia.
  - unfold EL, cnl_E, hl_n. cbn [hl_recs length]. pose proof AEN as Hn. unfold hl_n in Hn.
    rewrite HEQ, length_app in Hn. cbn [length] in Hn. unfold AREC. lia.
  - destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2). exists zr. split; [exact Hzr|]. split; [exact Hz8|]. split; lia.
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia | rewrite UspN; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia].
  - intros a Ha. unfold EL, cnl_E in Ha. cbn [hl_v hl_cap] in Ha. rewrite UspN. rewrite HreqV in Hvceil. unfold AREC, LDROP_STK, LDROP_FRAME, ASTACK in *. lia.
  - eapply (mo_ok_le MT ML); [exact HMOK|]. lia.
  - (* the room round: r's drop is the one free the budget owes before the rest *)
    exact HRMr.
  - (* list_drop's count premise (ldrop_pk = 0, cnt_ok) from the invariant (W_cnl_cnt.v cnl_cntm_free_pre) *)
    exact (cnl_cntm_free_pre RP r rs H1 _ HCNTr).
  - intros a Hr. rewrite AV. exact (Crom a Hr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hpD & regs2 & mem2 & md2 & -> & HJd & HPd & HPKd & HERd & HL2 & (b1 & b2 & Eb1 & Eb2) & HMLEd & HRMd).
hp0g HJd.
unfold EL in HJd, Eb1, Eb2. cbn [cnl_E hl_recs hl_v hl_cap nth fst snd] in HJd, Eb1, Eb2.
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_x; exact HJd).
(* what list_drop kept: its journal at G2 *)
pose proof HJd as HJd0. eapply ajournal_gx_inner_x in HJd0. destruct HJd0 as (memS2 & HJdi & HgS2).
rewrite UspN in HJdi. destruct HJdi as (_ & HlyD & _ & _ & _ & HfrD & _ & _ & KF & KB & KI & _).
set (FPd := [(hl_v EE, hl_v EE + AREC * hl_cap EE);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in *.
assert (Hcl : ~ YI16.sink_open_fp FPd).
{ apply sink_closed_pos. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - LDROP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Ha Hn. rewrite KF by (rewrite ?Z.add_0_r; lia). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 64 <= a < HA + 80) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ inFP FPd (p + i) ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) (ms_mem ms) (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi Hn). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. unfold off_img in Hoff. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 (ms_mem ms)) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 (ms_mem ms) mem2 a); [|exact Hw]. intros Hp. exact (HPKd a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the blocks: list_drop took r's text out of the live ones *)
set (rb := (fst r, Z.of_nat (length (snd r)) + 1)) in *.
assert (HND1b : List.NoDup (ablocks B ly1 S1)) by exact (nls_nodup_blocks _ _ _ _ _ HAR1).
assert (Hlive : forall b, In b (ablocks B ly1 S1) -> b <> rb -> In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Eb2. rewrite Eb1 in Hb. apply in_app_or in Hb as [Hb | [<- | Hb]];
  [apply in_or_app; left; exact Hb | exfalso; exact (Hne eq_refl) | apply in_or_app; right; exact Hb]. }
(* the expected list after the drop *)
set (jk' := HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk).
assert (EL2 : ldrop_list EL 0 = cnl_E rs jk') by reflexivity.
rewrite EL2 in HL2.
(* the source's blocks, as in cnl_gm *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks EL).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h EL H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (HrbEL : In rb (list_blks EL)).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HvbEL : In (hl_v EE, AREC * hl_cap EE) (list_blks EL)).
{ unfold list_blks, EL, cnl_E. cbn [hl_cap hl_v]. destruct (hl_cap EE =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|].
  apply in_or_app. left. left. reflexivity. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HNDl' : List.NoDup (((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL) ++ HL1)).
{ assert (Ex : ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL) ++ HL1 = Ab ++ HL1)
    by (unfold Ab; rewrite <- !app_assoc; reflexivity).
  rewrite Ex. exact HNDl. }
set (Oth := (list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ HL1).
assert (Hoth1 : forall b, In b Oth -> In b (ablocks B ly1 S1)).
{ intros b Hb. unfold Oth in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend _ Hb) | destruct Hb as [<- | []]; exact Hpin]. }
assert (Hoth2 : forall b, In b Oth -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Hlive b (Hoth1 b Hb)). intros E'. subst b.
  exact (cnl_nodup_mid _ _ _ _ rb HNDl' Hb HrbEL). }
(* a byte of a block of the source other than r's text and the vector is outside list_drop's footprint *)
assert (KAb : forall b a, In b Oth -> fst b <= a < fst b + snd b -> abyte_kept W1 (ms_mem ms) W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  pose proof (Hoth1 _ Hb) as Hb1. pose proof (Hoth2 _ Hb) as Hb2.
  pose proof (cnl_nodup_mid _ _ _ _ (p, n) HNDl' Hb) as HnE.
  assert (Hnr : (p, n) <> rb) by (intros E'; rewrite E' in HnE; exact (HnE HrbEL)).
  assert (Hnv : (p, n) <> (hl_v EE, AREC * hl_cap EE)) by (intros E'; rewrite E' in HnE; exact (HnE HvbEL)).
  destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr' & _).
  replace a with (p + (a - p)) by lia.
  split; [|intros _; apply (Pblk p n); [exact Hb2 | lia]].
  apply (Kblk p n); [exact Hb1 | exact Hb2 | | lia].
  intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
  - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ p n HAR1 HvinE Hb1 ltac:(intros E'; apply Hnv; symmetry; exact E')) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
  - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ p n HAR1 HinR Hb1 ltac:(intros E'; apply Hnr; symmetry; exact E')) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the source's own bytes outside the expected head *)
assert (KHd : forall a, HA <= a < HA + 64 \/ HA + 80 <= a < HA + 96 -> abyte_kept W1 (ms_mem ms) W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
(* the expected list without r's record: its blocks and its source *)
assert (HPdrop : Permutation (list_blks EL) (rb :: list_blks (cnl_E rs jk'))) by exact (list_blks_drop0 (hl_v EE) (hl_cap EE) r rs jk jk').
pose proof (nls_src_kept_low ly1 S1 W1 mem1 (ms_mem ms) md1 _ HAR1 HSRC (fun a _ => AV a) AP) as HSRC0.
assert (HSRC2 : asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h (cnl_E rs jk') H1)).
{ change (set_exp_held h (cnl_E rs jk') H1) with
    (set_exp_held (set_exp_held h EL H1) (cnl_E rs jk') (hs_held (set_exp_held h EL H1))).
  refine (nls_src_swap_e ly1 S1 W1 (ms_mem ms) ly2 S2 W2 mem2 HA (set_exp_held h EL H1) (cnl_E rs jk') HSRC0 KHd _ _ HL2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_held] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Oth; apply in_or_app; left; apply in_or_app; right; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Oth; apply in_or_app; left; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HH1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Oth; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_held] in Hb. rewrite !nls_alist_blks in Hb.
    apply Hoth2. unfold Oth. destruct Hb as [<- | Hb]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; left; exact Hb | apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDB.
    replace (hs_blocks (set_exp_held (set_exp_held h EL H1) (cnl_E rs jk') (hs_held (set_exp_held h EL H1))))
      with (map fst ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks (cnl_E rs jk') ++ HL1)).
    2: { unfold hs_blocks, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
         rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
    replace (hs_blocks (set_exp_held h EL H1))
      with (map fst ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL ++ HL1)) in HNDB.
    2: { unfold hs_blocks, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
         rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
    assert (HP : Permutation ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL ++ HL1)
      (rb :: (list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks (cnl_E rs jk') ++ HL1)).
    { rewrite HPdrop. apply Permutation_sym, Permutation_middle. }
    pose proof (Permutation_NoDup (Permutation_map fst HP) HNDB) as Hx. cbn [map] in Hx.
    apply List.NoDup_cons_iff in Hx as [_ Hx]. exact Hx. }
(* the journal: list_drop's inside this one *)
assert (HvbEE : In (hl_v EE, AREC * hl_cap EE) (list_blks EE)).
{ unfold list_blks. destruct (hl_cap EE =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity. }
assert (HrbEE : In rb (list_blks EE)).
{ unfold list_blks. apply in_or_app. right. rewrite HEQ. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))).
  apply in_or_app. right. left. reflexivity. }
assert (HFPd : forall a, inFP FPd a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). left. cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha.
  - split; [|exists (hl_v EE), (AREC * hl_cap EE); split; [exact HvinE | rewrite HreqV; exact Ha]].
    exists (hl_v EE, hl_v EE + req_size (AREC * hl_cap EE)). split; [|cbn [fst snd]; rewrite HreqV; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v EE, AREC * hl_cap EE)).
    apply in_or_app. left. exact HvbEE.
  - split; [|exists (fst r), (Z.of_nat (length (snd r)) + 1); split; [exact HinR | exact Ha]].
    exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ rb). apply in_or_app. left. exact HrbEE. }
pose proof (ajournal_gx_G_mono0 G2 G 0 [] LDROP_STK (spZ (ms_regs ms)) FPd ly1 S1 W1 (ms_mem ms) mdN [] ly2 S2 W2 mem2 md2 1
  HG2G HJd) as HJd'. rewrite UspN in HJd'.
pose proof (ajournal_gx_sub0 Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms) mdN kk
  LDROP_STK (sp0 - 112) 0 [] FPd [] ly2 S2 W2 mem2 md2 1 HJ HJd'
  ltac:(rewrite WS; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPd) as HJ2.
cbn [app] in HJ2.
(* the loop's facts after the drop *)
pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & _).
cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 64 <= x < HA + 80) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) mem1 x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). rewrite (Kimg x Hi Ho He Hn). apply AV. }
assert (KS : forall a, sp0 - 96 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite Kstk by (unfold LDROP_STK, LDROP_FRAME, ASTACK; lia). apply AV. }
assert (HREGS2 : cnl_regs_ok regs2 regs0 HA).
{ assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by (apply (HPd 2); unfold acallee_saved; lia).
  assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HPd 3); unfold acallee_saved; lia).
  assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HPd 4); unfold acallee_saved; lia).
  assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HPd 8); unfold acallee_saved; lia).
  assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by (apply (HPd 9); unfold acallee_saved; lia).
  assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HPd 18); unfold acallee_saved; lia).
  assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by (apply (HPd 19); unfold acallee_saved; lia).
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by (apply (HPd 22); unfold acallee_saved; lia).
  assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by (apply (HPd 23); unfold acallee_saved; lia).
  assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HPd 24); unfold acallee_saved; lia).
  assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by (apply (HPd 25); unfold acallee_saved; lia).
  assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by (apply (HPd 27); unfold acallee_saved; lia).
  unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P27. exact HREGSN. }
assert (HI2 : cnl_inv (pre ++ [r]) rs W2 regs2 mem2 md2).
{ exists ly2, S2, (kk + 1), H1, jk'.
  split; [rewrite HEQ, <- app_assoc; reflexivity|].
  split; [exact HJ2|].
  split; [exact (nls_apk_trans _ _ _ _ _ _ (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W1 mem1 (ms_mem ms) AP)) HPKd)|].
  split; [exact HSRC2|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HN|]. split; [exact HCB|].
  split.
  { intros rest HQ0. pose proof (HPERM rest HQ0) as HP1. rewrite Eb2. rewrite Eb1 in HP1.
    apply (cnl_perm_drop _ b1 b2 _ rb). eapply Permutation_trans; [exact HP1|].
    rewrite HPdrop. reflexivity. }
  split; [rewrite HfrD; exact HFR|].
  split; [eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLEd)|]; lia|].
  split; [apply (mo_ok_step MT ML S1 S2 (mo_free MT)); [exact HMOK | exact HMLEd]|].
  split.
  { assert (BB : blocks_bytes S2 = blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)).
    { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), Eb1, Eb2, !bsum_app, bsum_cons. unfold rb. cbn [snd]. lia. }
    rewrite BB. exact HROOM. }
  (* the room round: list_drop's post room is the rest's budget; the counts fell by r's line (W_cnl_cnt.v
     cnl_cnt_free) *)
  split; [exact HRMd|].
  split; [rewrite Eb2; rewrite Eb1 in HCNTr; exact (cnl_cnt_free RP r rs H1 b1 b2 (fst r) HCNTr)|].
  split; [apply (nls_vm_kept W1 W2 mem1 mem2); [intros i Hi; apply KS; cbn in Hi; lia | exact HAT]|].
  split.
  { split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cgone]; intros i Hi;
      apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cno]; intros i Hi;
      apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cout]; intros i Hi;
      apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split.
    { apply (nls_ob_kept W1 W2 mem1 mem2); [|exact Cob]. intros i Hi.
      destruct HOB as [-> | (HCO & HOin & HOn)]; [cbn [length] in Hi; lia|].
      assert (HOr : (OUT, CO) <> rb) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HrbEL).
      assert (HOv : (OUT, CO) <> (hl_v EE, AREC * hl_cap EE)) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HvbEL).
      destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
      rewrite (Kblk OUT CO i HOin (Hlive _ HOin HOr)); [apply AV | | lia].
      intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
      - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ OUT CO HAR1 HvinE HOin ltac:(intros E'; apply HOv; symmetry; exact E')) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
      - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ OUT CO HAR1 HinR HOin ltac:(intros E'; apply HOr; symmetry; exact E')) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    split; [eapply ajournal_gx_rom_view0; [exact HJd | exact HRO2 | intros a Hr; rewrite AV; exact (Crom a Hr)]|].
    split; [apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Clg]; intros i Hi;
      apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
    split; [apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Clb]; intros i Hi;
      apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
    apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Cle]; intros i Hi.
    apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
  split.
  { destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
    assert (HOr : (OUT, CO) <> rb) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HrbEL).
    split; [exact HCO|]. split; [exact (Hlive _ HOin HOr)|].
    intros Hx. apply HOn. apply in_app_or in Hx as [Hx | Hx]; [|apply in_or_app; right; exact Hx].
    apply in_or_app. left. apply (Permutation_in _ (Permutation_sym HPdrop)). right. exact Hx. }
  split; [exact HSTR|].
  split; [intros i Hi; rewrite (HERd i Hi), AV; exact (HERR i Hi)|].
  split; [intros a Ha; rewrite KS by lia; exact (HSRD a Ha)|].
  split; [apply (nls_frame_kept W1 W2 mem1 mem2 HFRM); intros a Ha; apply KS; lia|].
  exact HREGS2. }
rewrite N1.
exact (cnl_test pre r rs W2 regs2 mem2 md2 IHL HI2).
Qed.
Lemma cnl_loop : forall k pre rs W1 regs1 mem1 md1, length rs = k -> rs <> [] ->
cnl_inv pre rs W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
induction k as [|k IH]; intros pre rs W1 regs1 mem1 md1 Hk Hne HI; [destruct rs; [exfalso; exact (Hne eq_refl) | discriminate Hk]|].
destruct rs as [|r rs]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hk. injection Hk as Hk.
eapply SRr_bind; [exact (cnl_step pre r rs W1 regs1 mem1 md1 HI)|].
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HM).
apply (cnl_drop pre r rs W2 regs2 mem2 md2); [|exact HM].
intros Hne2 W3 regs3 mem3 md3 HI3. exact (IH (pre ++ [r]) rs W3 regs3 mem3 md3 Hk Hne2 HI3).
Qed.
Lemma cnl_enter : forall W1 regs1 mem1 md1, hl_recs EE <> [] -> cnl_inv [] (hl_recs EE) W1 regs1 mem1 md1 ->
SRr SEGS W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post.
Proof.
intros W1 regs1 mem1 md1 Hne HI.
exact (cnl_loop (length (hl_recs EE)) [] (hl_recs EE) W1 regs1 mem1 md1 eq_refl Hne HI).
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sections 0, 3, 4): the loop at a world relation R, for pb_check_no_loss_xR below.
   cnl_inv / cnl_mid / cnl_midQ / Post get R twins (the journal ajournal_gx_xR R, the post cnl_post_xR R); each loop
   lemma is its strict proof with the journal at R (AJ0R and the kit's _xR lemmas), the step relation SRrG SEGS R, and:
    the runs over the R journal concluding SRrG (RUNg / RUNTOg := W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, tactics
     W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR, branches BRg := W_kit.v paj_branch_xR);
    gesture_model at its R contract GM_R (it calls list_push's realloc and list_drop's free) and list_drop at its R
     contract LDROP_R (it calls free), both composed by SRrG_bind (R_trans) and their post journals by
     ajournal_gx_sub_xR (R_trans);
    next_line and bcmp stay strict leaves: next_line's SRr fact and the return step lift by SRr_SRrG (WLE_R),
     next_line's post journal by cnl_gx_lift_xR; bcmp by W_sites_x.v aj_bcmp_gx_at_xR.
   The strict loop lemmas above keep their proofs. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis LDROP_R : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_xR B PST ARx R MT RP G0 (BASE + AF_fr_list_drop).
Let RUNg := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let RUNTOg := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let BRg := paj_branch_xR (PI := PI) (R := R).
(* the empty-ghost-list notations of Section c at R *)
Local Notation AJ0R Gq XOq OUTq STKq spq FPq lyq Sq Wq memq mdq ownq lyq' Sq' Wq' memq' mdq' kq :=
  (ajournal_gx_xR SEGS B PST ARx R Gq XOq OUTq STKq spq FPq lyq Sq [] Wq memq mdq ownq lyq' Sq' [] Wq' memq' mdq' kq).
Local Notation ajournal_gx_inner0R Gq XOq OUTq STKq spq FPq lyq Sq Wq memq mdq ownq lyq' Sq' Wq' memq' mdq' kq :=
  (ajournal_gx_inner_xR SEGS B PST ARx Gq XOq OUTq STKq spq FPq lyq Sq [] Wq memq mdq ownq lyq' Sq' [] Wq' memq' mdq' kq).
Local Notation ajournal_gx_G_mono0R Gq Gq' XOq OUTq STKq spq FPq lyq Sq Wq memq mdq ownq lyq' Sq' Wq' memq' mdq' kq :=
  (ajournal_gx_G_mono_xR SEGS B PST ARx Gq Gq' XOq OUTq STKq spq FPq lyq Sq [] Wq memq mdq ownq lyq' Sq' [] Wq' memq' mdq' kq).
Local Notation ajournal_gx_sub0R Hs Gq STKq spq XOq0 OUTq0 FPq lyq Sq Wq memq mdq ownq lyc Sc Wc memc mdc kq
    STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 W2 mem2 md2 k1 :=
  (ajournal_gx_sub_xR SEGS B PST ARx LAWS Hs R_trans Gq STKq spq XOq0 OUTq0 FPq lyq Sq [] Wq memq mdq ownq lyc Sc [] Wc memc mdc kq
     STK1 sp1 XO1 OUT1 FP1 nf ly2 S2 [] W2 mem2 md2 k1).
Local Notation afn_pre_at0R STKq spq FPq lyq Sq W0 memq mdq ownq lyc Sc Wq memc mdc kq regsc STK1 o ch1 :=
  (afn_pre_x_atR SEGS B PST ARx STKq spq FPq lyq Sq [] W0 memq mdq ownq lyc Sc [] Wq memc mdc kq regsc STK1 o ch1).
Local Notation aj_bcmp_gx_at0R pc Hpc Gq XOq OUTq Wq regsT memT STKq spq FPq lyq Sq W0 memq mdq ownq lyc Sc mdc kq x y n o raw :=
  (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R pc Hpc Gq XOq OUTq Wq regsT memT STKq spq FPq lyq Sq [] W0 memq mdq ownq lyc Sc []
     mdc kq x y n o raw).
(* a ghost list read off the last state of an R journal is [] *)
Ltac hp0gR HJ := let H := fresh "HARg" in pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as H;
  hp0a H; clear H.
Local Notation Post_xR := (cnl_post_xR B PST ARx R MT RP G regs0 ly S [] W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
(* a strict gx journal (a strict callee's post journal) is one at R (W_journal_x.v ajournal_gx_xR_mono, WLE_R) *)
Lemma cnl_gx_lift_xR {Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq} :
ajournal_gx_x SEGS B PST ARx Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq ->
ajournal_gx_xR SEGS B PST ARx R Gq XOq OUTq STKq spq FPq lyq Sq Hpq Wq memq mdq ownq lyq' Sq' Hpq' Wq' memq' mdq' kq.
Proof. intros HJ. eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ]. Qed.
(* cnl_ajgx_top / ajournal_gx_rom_view0 over the R journal *)
Lemma cnl_ajgx_top_xR : forall G0 XO0 OUT0 STK sp FP ly0 S0 (W0 : world SEGS) mem0 md0 own ly' S' W' mem' md' k,
AJ0R G0 XO0 OUT0 STK sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k -> ly_top ly' = ly_top ly0.
Proof.
intros G0 XO0 OUT0 STK sp FP ly0 S0 W0 mem0 md0 own ly' S' W' mem' md' k (_ & _ & (memS & HJ & _) & _).
destruct HJ as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Et & _). exact Et.
Qed.
Lemma ajournal_gx_rom_view0R : forall G0 XO0 OUT0 STK spq FP lyq Sq (Wq : world SEGS) memq mdq own lyq' Sq' (Wq' : world SEGS)
    memq' mdq' k,
  AJ0R G0 XO0 OUT0 STK spq FP lyq Sq Wq memq mdq own lyq' Sq' Wq' memq' mdq' k ->
  rom_out SEGS B G0 -> rom_view SEGS Wq memq -> rom_view SEGS Wq' memq'.
Proof.
  intros G0 XO0 OUT0 STK spq FP lyq Sq Wq memq mdq own lyq' Sq' Wq' memq' mdq' k HJ HR Hrv.
  apply (ajournal_gx_rom_view_xR SEGS B PST ARx LAWS pa_segs_low G0 XO0 OUT0 STK spq FP lyq Sq [] Wq memq mdq own lyq' Sq' []
    Wq' memq' mdq' k HJ HR); [|exact Hrv].
  intros a (sg & Hin & _ & Hr). apply HPST. exists sg. split; [exact Hin | exact Hr].
Qed.
(* cnl_inv at R: the journal from the entry is ajournal_gx_xR R *)
Definition cnl_inv_xR (pre rs : list (Z * list byte)) (W1 : world SEGS) (regs1 : bvmap 5 word) (mem1 : word -> option byte)
(md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ rs /\
AJ0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E rs jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs pre) /\ hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E rs jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) /\ mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) rs /\
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr) /\ cnl_cnt RP rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 pre) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E rs jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 pre)) ob = bsr rs ++ rest) /\
cnl_errno W1 mem1 /\ cnl_stk_rd W1 mem1 /\ cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 regs0 HA.
(* cnl_mid at R *)
Definition cnl_mid_xR (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) (W1 : world SEGS)
(regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
exists ly1 S1 kk (H1 : hlist) (jk : list byte),
hl_recs EE = pre ++ r :: rs /\
AJ0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk /\
apres_kept B W mem W1 mem1 /\
asrc_at B ly1 S1 W1 mem1 HA (set_exp_held h (cnl_E (r :: rs) jk) H1) /\
NoDup (texts H1) /\ texts H1 = RelayModel.upds (texts HH) (txs (pre ++ [r])) /\
hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (pre ++ [r]) /\
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs (pre ++ [r]))) /\ hl_cap H1 <= capb HH EE /\
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) /\
frames S1 = frames S /\
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) (pre ++ [r]) - mo_free MT) /\
mo_ok MT S1 (mo_free MT + cnl_go MT (texts H1) (hl_cap H1) rs) /\
cnl_room MMAX (blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)) (texts H1) (hl_cap H1) rs /\
rp_RM RP S1 (Datatypes.S (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr))%nat /\ cnl_cntm RP r rs H1 (ablocks B ly1 S1) /\
val_mem SEGS (arm W1 mem1) AT 8 (cpos gone A0 (pre ++ [r])) /\ cnl_consts W1 mem1 /\
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) /\
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) /\
cnl_errno W1 mem1 /\ cnl_stk_rd W1 mem1 /\ cnl_frame_ok W1 mem1 sp0 regs0 /\ cnl_regs_ok regs1 regs0 HA.
Definition cnl_midQ_xR (pre : list (Z * list byte)) (r : Z * list byte) (rs : list (Z * list byte)) :
world SEGS -> config -> Prop :=
fun W1 c1 => exists regs1 mem1 md1, c1 = mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1 /\
cnl_mid_xR pre r rs W1 regs1 mem1 md1.
(* cnl_chain_at over the R journal *)
Lemma cnl_chain_at_xR : forall ly1 S1 kk W1 mem1 md1 regs1,
AJ0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 mem1 md1 kk ->
cnl_stk_rd W1 mem1 -> cnl_frame_ok W1 mem1 sp0 regs0 ->
getr regs1 2 = w64 (sp0 - 112) -> getr regs1 8 = w64 AT ->
exists ch1, achain ly1 (aview SEGS (w_H W1) mem1) (spZ regs1) (s0Z regs1) ch1.
Proof.
intros ly1 S1 kk W1 mem1 md1 regs1 HJ HRD HFR R2 R8.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
assert (Usp : spZ regs1 = sp0 - 112) by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
assert (Us0 : s0Z regs1 = AT) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; lia).
rewrite Usp, Us0. pose proof (cnl_ajgx_top_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Et.
apply cnl_achain_ex; [exact (cnl_aview_nonneg W1 mem1) | exact AAT8 | lia |].
intros a Ha. rewrite Et in Ha. destruct (Z_lt_le_dec a sp0) as [Hlt | Hge]; [|exact (HRD a ltac:(lia))].
pose proof (Z.div_mod (a - (sp0 - 96)) 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound (a - (sp0 - 96)) 8 ltac:(lia)) as Hm.
set (q := (a - (sp0 - 96)) / 8) in *. set (rm := (a - (sp0 - 96)) mod 8) in *.
assert (Hq : 0 <= q < 12) by lia.
pose proof (HFR (Z.to_nat q) ltac:(lia)) as Hv.
replace a with (sp0 - 96 + 8 * Z.of_nat (Z.to_nat q) + rm) by lia.
exact (cnl_val_mem_view W1 mem1 _ 8 _ rm Hv ltac:(cbn; lia)).
Qed.
(* cnl_gm at R: gesture_model by GM_R *)
Lemma cnl_gm_xR : forall pre r rs ly1 S1 kk (H1 : hlist) jk W1 regsc memc mdc LINE q k,
hl_recs EE = pre ++ r :: rs ->
AJ0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 memc mdc kk ->
apres_kept B W mem W1 memc ->
asrc_at B ly1 S1 W1 memc HA (set_exp_held h (cnl_E (r :: rs) jk) H1) ->
NoDup (texts H1) -> texts H1 = RelayModel.upds (texts HH) (txs pre) -> hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) pre ->
hl_n H1 <= hl_n HH + Z.of_nat (count_begin (txs pre)) -> hl_cap H1 <= capb HH EE ->
(forall rest, Permutation (ablocks B ly S) (list_blks EE ++ list_blks HH ++ rest) ->
  Permutation (ablocks B ly1 S1) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1 ++ rest)) ->
frames S1 = frames S ->
mo_le MT S S1 (cnl_go MT (texts HH) (hl_cap HH) pre) -> mo_ok MT S1 (cnl_go MT (texts H1) (hl_cap H1) (r :: rs)) ->
cnl_room MMAX (blocks_bytes S1) (texts H1) (hl_cap H1) (r :: rs) ->
rp_RM RP S1 (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) (r :: rs)) + kr) -> cnl_cnt RP (r :: rs) H1 (ablocks B ly1 S1) ->
val_mem SEGS (arm W1 memc) AT 8 (cpos gone A0 (pre ++ [r])) -> cnl_consts W1 memc ->
(ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ ~ In (OUT, CO) (list_blks (cnl_E (r :: rs) jk) ++ list_blks H1))) ->
(gone = 0 -> exists rest, skipn (Z.to_nat (cpos gone A0 (pre ++ [r]))) ob = bsr rs ++ rest) ->
cnl_errno W1 memc -> cnl_stk_rd W1 memc -> cnl_frame_ok W1 memc sp0 regs0 -> cnl_regs_ok regsc regs0 HA ->
getr regsc 1 = Z_to_bv 64 (BASE + A_cnl_back) -> getr regsc 10 = w64 HA -> getr regsc 11 = w64 LINE ->
getr regsc 12 = w64 (Z.of_nat (length (snd r))) ->
garr8 SEGS (arm W1 memc) LINE (bzs (snd r)) ->
In (q, k) (ablocks B ly1 S1) -> ~ In (q, k) (list_blks H1) -> q <= LINE -> LINE + Z.of_nat (length (snd r)) <= q + req_size k ->
SRrG SEGS R W1 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_fr_gesture_model)) memc (seg_rom SEGS)) mdc) (cnl_midQ_xR pre r rs).
Proof.
intros pre r rs ly1 S1 kk H1 jk W1 regsc memc mdc LINE q k HEQ HJ HPK HSRC HND HTX HCAP HN HCB HPERM HFR HMLE HMOK
  HROOM HRMr HCNTr HAT HCONST HOB HSTR HERR HSRD HFRM HREGS R1 R10 R11 R12 HLG Hqk Hqn Hq1 Hq2.
pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof APRE as (_ & _ & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity. assert (WG : GM_STK = 16528) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & _ & _ & _).
(* gesture_model's premise (HA + 80) mod 8 = 0 *)
assert (HA80 : (HA + 80) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 10; reflexivity]. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HAR1 : AR0 ly1 S1 W1 memc mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
set (E1 := cnl_E (r :: rs) jk) in *.
assert (HrE1 : hl_recs E1 = r :: rs) by reflexivity.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (_ & _ & _ & _ & _ & _ & _ & _ & HrecE).
rewrite HrE1 in HrecE. apply Forall_cons_iff in HrecE as [(Hrb & Hrg & Hrl & _) _].
destruct (Hrl eq_refl) as [Hr0 HrA].
pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _).
destruct HCONST as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
(* the source's blocks at the call: pending's, the partial buffer, the expected list's, then the held list's *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks E1).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h E1 H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (Hinc : incl (Ab ++ HL1) (ablocks B ly1 S1)).
{ intros b Hb. unfold Ab, HL1 in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 b Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend b Hb)|].
  apply in_app_or in Hb as [Hb | Hb]; [destruct Hb as [<- | []]; exact Hpin | exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb)]. }
destruct (perm_of_incl _ _ HNDl Hinc) as (rest0 & Hp0).
assert (Hp1 : Permutation (ablocks B ly1 S1) (HL1 ++ Ab ++ rest0)) by (eapply Permutation_trans; [exact Hp0 | apply nls_perm_swap]).
pose proof (nls_nodup_blocks _ _ _ _ _ HAR1) as HND1b.
(* gesture_model's footprint: a held block live at entry was one of FPc's, by APERM *)
assert (HFP : forall a, inFP (blk_FP HL1) a ->
  (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb). cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb).
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) (ablocks B ly S)) as [Hin0 | Hnin0].
  - left. split; [|exists p, n; split; [exact Hb1 | exact Ha]].
    destruct APERM as (rest & HQ0). pose proof (HPERM rest HQ0) as HP1.
    assert (Hx : In (p, n) (list_blks EE ++ list_blks HH)).
    { pose proof (Permutation_in _ HQ0 Hin0) as Hx. rewrite app_assoc in Hx. apply in_app_or in Hx as [Hx | Hx]; [exact Hx|].
      exfalso. pose proof (Permutation_NoDup HP1 HND1b) as HNx. apply NoDup_app_remove_l in HNx.
      exact (nls_nodup_disj _ HL1 rest (p, n) HNx Hb Hx). }
    exists (p, p + req_size n). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n)). exact Hx.
  - right. exists p, n. split; [exact Hb1|]. split; [exact Hnin0 | exact Ha]. }
(* gesture_model's globals: the held list's head only *)
set (G' := [(HA + 80, 16)]).
assert (HG'G : forall a, inG G' a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG' : forall a, ~ (HA + 80 <= a < HA + 96) -> ~ inG G' a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G' G HG'G HG) as HG'.
(* gx_rt of gesture_model's G' comes from g_s's own placement fact HGRR, never from the caller's G: a caller's G
   (G_fr, G_SL) holds errno *)
assert (HG'R : forall a, inG G' a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT' : gx_rt B G') by (eapply gx_rt_sub; [exact HG'R | exact HGRR]).
(* rom_out at G' from g_s's (HRO): gm_spec_g takes it, for list_drop's spec inside gesture_model *)
assert (HRO' : rom_out SEGS B G').
{ apply cnl_rom_out_gs. intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. rewrite AHAE in Ha. unfold ASRC in *. lia. }
(* gesture_model's entry *)
assert (Usp : spZ regsc = sp0 - 112).
{ destruct HREGS as (Q2 & _). unfold spZ at 1. rewrite Q2. apply unsigned_lit_small. lia. }
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 memc mdc kk HJ) as (memS & HJi & _).
(* s0 = at: the frame-pointer chain the callee's unwinder walks from it exists, the stack being readable *)
destruct (cnl_chain_at_xR ly1 S1 kk W1 memc mdc regsc HJ HSRD HFRM (proj1 HREGS) (proj1 (proj2 (proj2 (proj2 HREGS))))) as (chg & Hchg).
assert (HPREg : AFP0 GM_STK ly1 S1 W1 regsc memc mdc chg).
{ destruct HREGS as (_ & Q3 & Q4 & Q8 & _).
  eapply (afn_pre_at0R (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 memc mdc kk regsc GM_STK (- 112 - XO) chg HJi).
  - rewrite Usp. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - rewrite WG; lia.
  - rewrite WS, WG. lia.
  - rewrite R1. apply ret_ok_codeptr_v; [unfold A_cnl_back, AF_fr_check_no_loss; lia | reflexivity].
  - unfold raZ. rewrite R1. unfold A_cnl_back, AF_fr_check_no_loss. destruct HBASE as (B1 & B2 & _).
    rewrite unsigned_lit_small by lia. lia.
  - exact Q3.
  - exact Q4.
  - exact Hchg. }
assert (Hazs : azs B (HA + 80) 16)
  by (destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2); exists zr; split; [exact Hzr|]; split; [exact Hz8|]; split; lia).
assert (HnT1 : Z.of_nat (length (texts H1)) = hl_n H1) by (unfold texts, hl_n; rewrite length_map; reflexivity).
cbn [cnl_room] in HROOM. destruct HROOM as (HRM1 & HRM2 & HRM3).
assert (HGC : gm_cost MT H1 (snd r) = gmc MT (texts H1) (hl_cap H1) (snd r)).
{ unfold gm_cost, lp_cost, gmc, lp_grow, lp_vbytes. rewrite HnT1. reflexivity. }
cbn [cnl_go] in HMOK.
eapply SRrG_mono.
{ refine (GM_R G' HG' HGRT' HRO' W1 ly1 S1 [] regsc memc mdc chg HA LINE (snd r) H1 q k HPREg R10 R11 R12 HH1 HND _ Hazs HA80 HLG Hr0 HrA
    Hqk Hqn Hq1 Hq2 C6 C7 C8 C5 _ _ _ _
    (Datatypes.S (Z.to_nat (cnl_go MT_rk (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
      + kr))%nat _ _).
  - intros a Ha. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros Hg. unfold lp_vbytes. rewrite <- HnT1. apply HRM1. unfold lp_grow in Hg. apply Z.eqb_eq in Hg. lia.
  - unfold AREC in *. lia.
  - unfold lp_grow, lp_vbytes. rewrite <- HnT1. exact HRM2.
  - rewrite HGC. eapply (mo_ok_le MT ML); [exact HMOK|]. pose proof (mo_free_nonneg MT ML).
    assert (Hc0 : 0 <= hl_cap H1) by (unfold hl_n in HcapH1; lia).
    pose proof (nls_go_nonneg rs (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1))
      (nls_capstep_nonneg (texts H1) (bzs (snd r)) (hl_cap H1) Hc0)). lia.
  - (* the room: gesture_model's charge, then r's drop (one free), then the rest (W_cnl_cnt.v cnl_rk_step) *)
    rewrite <- (cnl_rk_step H1 r rs kr). exact HRMr.
  - (* the counts: gesture_model's peak is at most 2 (W_cnl_cnt.v cnl_cnt_gm_pre) *)
    exact (cnl_cnt_gm_pre RP r rs H1 _ HCNTr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hpG & regs2 & mem2 & md2 & kk2 & H2 & -> & HJg & HPg & HPKg & HERg & HLH2 & HND2 & HT2 & HC2 & HPm & HFR2 & HMLE2 & HRMg).
hp0gR HJg.
set (HL2 := list_blks H2) in *.
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJg).
pose proof (HPm _ Hp1) as Hp2.
pose proof (Permutation_NoDup Hp2 (nls_nodup_blocks _ _ _ _ _ HAR2)) as HNDp2.
(* what gesture_model kept: its journal at G' *)
pose proof HJg as HJg0. eapply ajournal_gx_inner_xR in HJg0. destruct HJg0 as (memS2 & HJgi & HgS2).
rewrite Usp in HJgi. destruct HJgi as (_ & _ & _ & _ & _ & _ & _ & _ & KF & KB & KI & _).
assert (Hcl : ~ YI16.sink_open_fp (blk_FP HL1)).
{ apply sink_closed_pos. apply Forall_forall. intros rr Hrr. unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p & n) & <- & Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)) as (_ & H4096 & _). cbn [fst]. lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - GM_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Ha Hn. rewrite KF by lia. apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 80 <= a < HA + 96) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) memc a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ In (p, n) HL1 ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) memc (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi).
  - apply HgS2. rewrite unsigned_lit_small by lia. apply HnG'. unfold off_img in Hoff. lia.
  - intros (rr & Hrr & Hr). unfold blk_FP in Hrr. apply in_map_iff in Hrr as ((p' & n') & <- & Hb'). cbn [fst snd] in Hr.
    assert (Hne : (p', n') <> (p, n)) by (intros E'; rewrite E' in Hb'; exact (Hn Hb')).
    pose proof (sep_blocks0 ly1 S1 W1 memc mdc p' n' p n HAR1 (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb') Hb1 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 memc) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 memc mem2 a); [|exact Hw]. intros Hp. exact (HPKg a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the source's own bytes (outside the held head) and the blocks of Ab *)
assert (KHd : forall a, HA <= a < HA + 80 -> abyte_kept W1 memc W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
assert (KAb : forall b a, In b Ab -> fst b <= a < fst b + snd b -> abyte_kept W1 memc W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  assert (Hb1 : In (p, n) (ablocks B ly1 S1)) by (apply Hinc; apply in_or_app; left; exact Hb).
  assert (Hb2 : In (p, n) (ablocks B ly2 S2))
    by (apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (Hn1 : ~ In (p, n) HL1) by exact (nls_nodup_disj _ Ab HL1 (p, n) HNDl Hb).
  destruct (cnl_blk ly1 S1 W1 memc mdc p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr & _).
  replace a with (p + (a - p)) by lia.
  split; [apply (Kblk p n); [exact Hb1 | exact Hb2 | exact Hn1 | lia] | intros _; apply (Pblk p n); [exact Hb2 | lia]]. }
assert (HOB2 : ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly1 S1) /\ In (OUT, CO) (ablocks B ly2 S2) /\
  ~ In (OUT, CO) (list_blks E1 ++ HL1) /\ ~ In (OUT, CO) HL2)).
{ destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
  assert (HOr : In (OUT, CO) (Ab ++ rest0)).
  { pose proof (Permutation_in _ Hp1 HOin) as Hx. apply in_app_or in Hx as [Hx | Hx]; [|exact Hx].
    exfalso. apply HOn. apply in_or_app. right. exact Hx. }
  split; [exact HCO|]. split; [exact HOin|].
  split; [apply (Permutation_in _ (Permutation_sym Hp2)); apply in_or_app; right; exact HOr|].
  split; [exact HOn|]. intros Hx. exact (nls_nodup_disj _ HL2 (Ab ++ rest0) (OUT, CO) HNDp2 Hx HOr). }
clear HOB.
assert (HnT2 : Z.of_nat (length (texts H2)) = hl_n H2) by (unfold texts, hl_n; rewrite length_map; reflexivity).
assert (HCS : hl_cap H2 = capstep (texts H1) (bzs (snd r)) (hl_cap H1)).
{ unfold capstep. rewrite <- HT2, HC2, <- HnT1, <- HnT2.
  destruct (Nat.ltb_spec (length (texts H1)) (length (texts H2)));
  destruct (Z.ltb_spec (Z.of_nat (length (texts H1))) (Z.of_nat (length (texts H2)))); try reflexivity; lia. }
pose proof (upd_len (texts H1) (bzs (snd r))) as (U1 & U2). rewrite <- HT2 in U1, U2.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 80 <= x < HA + 96) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) memc x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). exact (Kimg x Hi Ho He Hn). }
(* the state at 0x85f9c *)
exists regs2, mem2, md2. split; [rewrite R1; reflexivity|].
exists ly2, S2, (kk + kk2), H2, jk.
split; [exact HEQ|].
split.
{ pose proof (ajournal_gx_G_mono0R G' G 0 [] GM_STK (spZ regsc) (blk_FP HL1) ly1 S1 W1 memc mdc [] ly2 S2 W2 mem2 md2 kk2
    HG'G HJg) as HJg'. rewrite Usp in HJg'.
  pose proof (ajournal_gx_sub0R Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 memc mdc kk
    GM_STK (sp0 - 112) 0 [] (blk_FP HL1) [] ly2 S2 W2 mem2 md2 kk2 HJ HJg' ltac:(rewrite WS, WG; lia) ltac:(lia) ltac:(lia)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP) as HJ2.
  cbn [app] in HJ2. exact HJ2. }
split; [exact (nls_apk_trans _ _ _ _ _ _ HPK HPKg)|].
split.
{ refine (nls_src_swap ly1 S1 W1 memc ly2 S2 W2 mem2 HA (set_exp_held h E1 H1) H2 HSRC KHd _ _ HLH2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_expected] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Ab; apply in_or_app; right; apply in_or_app; left; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HE1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Ab; apply in_or_app; right; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_expected] in Hb. rewrite !nls_alist_blks in Hb.
    apply (Permutation_in _ (Permutation_sym Hp2)). apply in_or_app. right. apply in_or_app. left. unfold Ab.
    destruct Hb as [<- | Hb]; [apply in_or_app; right; apply in_or_app; left; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; exact Hb | apply in_or_app; right; apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup.
    replace (hs_blocks (set_exp_held (set_exp_held h E1 H1) (hs_expected (set_exp_held h E1 H1)) H2)) with (map fst (Ab ++ HL2)).
    + pose proof (nls_nodup_blocks_fst _ _ _ _ _ HAR2) as Hf.
      pose proof (Permutation_NoDup (Permutation_map fst (Permutation_trans Hp2 (Permutation_sym (nls_perm_swap _ Ab HL2 rest0)))) Hf) as Hf2.
      rewrite map_app in Hf2. exact (NoDup_app_remove_r _ _ Hf2).
    + unfold hs_blocks, Ab, HL2. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
      rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
split; [exact HND2|].
split; [rewrite upds_snoc, <- HTX; exact HT2|].
split; [rewrite cnl_cap_snoc, <- HTX, <- HCAP; exact HCS|].
split.
{ rewrite txs_app, nls_cb_app. change (txs [r]) with [bzs (snd r)]. rewrite nls_cb_one.
  destruct (is_begin (bzs (snd r))) eqn:Eb; [lia|].
  destruct (Nat.lt_ge_cases (length (texts H1)) (length (texts H2))) as [Hlt | Hge]; [destruct (U2 Hlt) as [Hb _]; congruence | lia]. }
split.
{ rewrite HC2. destruct (Z.ltb_spec (hl_n H1) (hl_n H2)) as [Hlt | Hge]; [|exact HCB].
  destruct (U2 ltac:(lia)) as (Hbeg & _).
  assert (Hcbe : (count_begin (txs pre) + 1 <= count_begin (texts EE))%nat).
  { change (texts EE) with (txs (hl_recs EE)). rewrite HEQ, txs_app, nls_cb_app.
    change (txs (r :: rs)) with ([bzs (snd r)] ++ txs rs). rewrite nls_cb_app, nls_cb_one, Hbeg. lia. }
  unfold capb, grow_cap in *. destruct (hl_n H1 =? hl_cap H1) eqn:Eq; [|lia]. apply Z.eqb_eq in Eq. destruct (hl_cap H1 =? 0); lia. }
split.
{ intros rest HQ0. pose proof (HPERM rest HQ0) as HP1x.
  assert (HP1y : Permutation (ablocks B ly1 S1) (HL1 ++ list_blks E1 ++ rest))
    by (eapply Permutation_trans; [exact HP1x|]; rewrite app_assoc; apply nls_perm_swap).
  eapply Permutation_trans; [exact (HPm _ HP1y)|]. rewrite app_assoc. apply nls_perm_swap. }
split; [rewrite HFR2; exact HFR|].
split.
{ eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLE2)|].
  rewrite nls_go_snoc, HGC, HTX, HCAP. lia. }
split.
{ replace (cnl_go MT (texts H2) (hl_cap H2) rs) with
    (cnl_go MT (RelayModel.upd (texts H1) (bzs (snd r))) (capstep (texts H1) (bzs (snd r)) (hl_cap H1)) rs)
    by (rewrite <- HT2, <- HCS; reflexivity).
  apply (mo_ok_step MT ML S1 S2 (gm_cost MT H1 (snd r))); [|exact HMLE2].
  rewrite HGC, Z.add_assoc. exact HMOK. }
split.
{ rewrite <- HT2, <- HCS in HRM3.
  assert (BB : blocks_bytes S2 = blocks_bytes S1 - hbytes (texts H1) (hl_cap H1) + hbytes (texts H2) (hl_cap H2)).
  { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ Hp1), (bsum_perm _ _ Hp2), !bsum_app.
    unfold HL1, HL2. rewrite !bsum_list_blks. lia. }
  rewrite BB. exact HRM3. }
split.
{ (* the room past gesture_model: its post's kr *)
  rewrite HT2, HCS. exact HRMg. }
split.
{ (* the live counts past gesture_model (W_cnl_cnt.v cnl_cnt_gm_post) *)
  apply (cnl_cnt_gm_post RP r rs H1 H2 (ablocks B ly1 S1) (ablocks B ly2 S2) (Ab ++ rest0));
  [first [exact HND | apply NoDup_ListNoDup; exact HND] | exact HT2 | exact HCS | exact Hp1 | exact Hp2 | exact HCNTr]. }
split.
{ apply (nls_vm_kept W1 W2 memc mem2 AT 8); [|exact HAT]. intros i Hi. apply Kstk; [|lia]. split; [lia|]. cbn in Hi. lia. }
split.
{ pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & Arom).
  cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale, Arom.
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C1]; intros i Hi;
    apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C2]; intros i Hi;
    apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split; [apply (nls_vm_kept W1 W2 memc mem2); [|exact C3]; intros i Hi;
    apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
  split.
  { apply (nls_ob_kept W1 W2 memc mem2); [|exact C4]. intros i Hi.
    destruct HOB2 as [-> | (HCO & HOin & HOin2 & HOn & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly1 S1 W1 memc mdc OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
    apply (Kblk OUT CO); [exact HOin | exact HOin2 | intros Hx; apply HOn; apply in_or_app; right; exact Hx | lia]. }
  split.
  { intros a Hr. destruct (ROMNS a Hr) as [He Hrp].
    assert (Hd : forall rr, {in_zr a rr} + {~ in_zr a rr}).
    { intros rr. unfold in_zr. destruct (Z_le_gt_dec (fst rr) a); destruct (Z_lt_ge_dec a (fst rr + snd rr));
      [left; lia | right; lia | right; lia | right; lia]. }
    destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Ho].
    - exact (rom_pinned_view0 ly2 S2 W2 mem2 md2 a HAR2 (Hrp Hown)).
    - rewrite (Kimg a (nls_rom_img a Hr) Ho He (fun Hn => Arom a ltac:(lia) Hr)). exact (C5 a Hr). }
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C6]; intros i Hi;
    apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
  split; [apply (nls_garr8_kept W1 W2 memc mem2); [|exact C7]; intros i Hi;
    apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
  apply (nls_garr8_kept W1 W2 memc mem2); [|exact C8]; intros i Hi.
  apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
split.
{ destruct HOB2 as [Hob0 | (HCO & _ & HOin2 & HOn & HOn2)]; [left; exact Hob0 | right].
  split; [exact HCO|]. split; [exact HOin2|].
  intros Hx. apply in_app_or in Hx as [Hx | Hx]; [apply HOn; apply in_or_app; left; exact Hx | exact (HOn2 Hx)]. }
split; [exact HSTR|].
split; [intros i Hi; rewrite (HERg i Hi); exact (HERR i Hi)|].
split.
{ intros a Ha. rewrite Kstk by lia. exact (HSRD a Ha). }
split; [apply (nls_frame_kept W1 W2 memc mem2 HFRM); intros a Ha; apply Kstk; lia|].
destruct HREGS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q22 & Q23 & Q24 & Q25 & Q27).
assert (P2 : getr regs2 2 = getr regsc 2) by (apply (HPg 2); unfold acallee_saved; lia).
assert (P3 : getr regs2 3 = getr regsc 3) by (apply (HPg 3); unfold acallee_saved; lia).
assert (P4 : getr regs2 4 = getr regsc 4) by (apply (HPg 4); unfold acallee_saved; lia).
assert (P8 : getr regs2 8 = getr regsc 8) by (apply (HPg 8); unfold acallee_saved; lia).
assert (P9 : getr regs2 9 = getr regsc 9) by (apply (HPg 9); unfold acallee_saved; lia).
assert (P18 : getr regs2 18 = getr regsc 18) by (apply (HPg 18); unfold acallee_saved; lia).
assert (P19 : getr regs2 19 = getr regsc 19) by (apply (HPg 19); unfold acallee_saved; lia).
assert (P22 : getr regs2 22 = getr regsc 22) by (apply (HPg 22); unfold acallee_saved; lia).
assert (P23 : getr regs2 23 = getr regsc 23) by (apply (HPg 23); unfold acallee_saved; lia).
assert (P24 : getr regs2 24 = getr regsc 24) by (apply (HPg 24); unfold acallee_saved; lia).
assert (P25 : getr regs2 25 = getr regsc 25) by (apply (HPg 25); unfold acallee_saved; lia).
assert (P27 : getr regs2 27 = getr regsc 27) by (apply (HPg 27); unfold acallee_saved; lia).
unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P27.
repeat split; assumption.
Qed.
(* cnl_step at R *)
Lemma cnl_step_xR : forall pre r rs W1 regs1 mem1 md1, cnl_inv_xR pre (r :: rs) W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) (cnl_midQ_xR pre r rs).
Proof.
intros pre r rs W1 regs1 mem1 md1 HI.
destruct HI as (ly1 & S1 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : AR0 ly1 S1 W1 mem1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE1 & _).
cbn [set_exp_held hs_expected] in HE1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields ly1 S1 W1 mem1 (HA + 64) (cnl_E (r :: rs) jk) true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v (cnl_E (r :: rs) jk) + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_loop W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 17)%nat -> ew Ev (32 + k) = nth k (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEv. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
assert (E32 : ew Ev 32 = Z_to_bv 64 gone) by exact (EX 0%nat ltac:(lia)).
assert (E35 : ew Ev 35 = Z_to_bv 64 (fst r)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew Ev 36 = Z_to_bv 64 (Z.of_nat (length (snd r)))) by exact (EX 4%nat ltac:(lia)).
assert (Usp : bv_unsigned (ew Ev 2) = sp0 - 112) by (rewrite E2; apply unsigned_lit_small; lia).
assert (Vb9 : base_val Ev (Some 9%nat) = HA) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (E33 : ew Ev 33 = Z_to_bv 64 (hl_v EE)) by exact (EX 1%nat ltac:(lia)).
assert (Vb33 : base_val Ev (Some 33%nat) = hl_v EE) by (cbn [base_val]; rewrite E33; apply unsigned_lit_small; lia).
pose proof (pa_obj_img 27 ltac:(lia)) as HgR. change (A_OBJ 27) with A_g_gone in HgR.
assert (Eg : ew Ev A_g_gone = Z_to_bv 64 (VAL A_g_gone)) by (rewrite HEv; apply Eimg_img; unfold A_g_gone, A_OBJ, A_TEXT, A_LIM; lia).
assert (Vbg : base_val Ev (Some 268%nat) = VAL A_g_gone)
  by (change (Some 268%nat) with (Some A_g_gone); cbn [base_val]; rewrite Eg; apply unsigned_lit_small; exact (pa_val_range _)).
assert (Vb2 : base_val Ev (Some 2%nat) = sp0 - 112) by (cbn [base_val]; exact Usp).
clear HEv EX.
(* the callee-saved registers at the loop head, as the state names them *)
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (27%bv : bv 5) O27.
assert (HOBx : ob = [] \/ In (OUT, CO) (ablocks B ly1 S1) /\ NO <= CO)
  by (destruct HOB as [H0 | (Hc1 & Hc2 & _)]; [left; exact H0 | right; split; assumption]).
assert (HinR1 : In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks (cnl_E (r :: rs) jk))).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HnH1 : ~ In (fst r, Z.of_nat (length (snd r)) + 1) (list_blks H1)).
{ pose proof (nls_exp_held_nodup _ _ _ _ _ HSRC) as Hnd. cbn [set_exp_held hs_expected hs_held] in Hnd.
  exact (nls_nodup_disj _ _ _ _ Hnd HinR1). }
assert (HgarR0 : garr8 SEGS (arm W1 mem1) (fst r) (bzs (snd r))).
{ unfold bzs in HgarR. rewrite map_app in HgarR. apply garr8_app in HgarR as [Hg _]. exact Hg. }
unfold A_cnl_loop.
(* ---- 0x85ec4: lbu a0, g_gone; beqz ---- *)
paj_run_tok_xR RUNg HS HJ SHOK Bspan. { nls_nowin_awr. }
psrr_branch_tok RUNg BRg HS SHOK Bspan.
- (* g_gone clear: next_line, the two compares, bcmp *)
  assert (Hg0 : gone = 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_eq in Hc; exact Hc).
  destruct (HSTR Hg0) as (rest0 & Hsk). rewrite nls_bsr_cons, <- app_assoc in Hsk. cbn [app] in Hsk.
  set (An := cpos gone A0 pre) in *.
  assert (HAn0 : 0 <= An) by (unfold An, cpos; rewrite Hg0; cbn; lia).
  assert (HAnO : An + Z.of_nat (length (snd r)) + 1 <= NO).
  { pose proof (f_equal (@length byte) Hsk) as Hl. rewrite length_skipn, length_app in Hl. cbn [length] in Hl. lia. }
  destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [rewrite Hob0 in AOBN; cbn [length] in AOBN; lia|].
  destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (HO16 & HO4096 & _ & HOle & HOreq1 & HOceil & _ & HOoff & HOapp & HOpres).
  (* ---- 0x85f18: to next_line(at, sp + 8, sp + 0) ---- *)
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan AF_fr_next_line. { nls_nowin_awr. }
  assert (MQ1 : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ1) as (AV1 & AP1).
  pmkst HS.
  prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
  prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11. prreg HS (12%bv : bv 5) N12.
  assert (UspN : spZ (ms_regs ms0) = sp0 - 112) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
  lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
  destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms0) mdN kk HJ)
    as (memS & HJi & _).
  pose proof HJi as (HARN & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRN & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
  (* s0 = at: the callee's frame-pointer chain from it *)
  assert (N2w : getr (ms_regs ms0) 2 = w64 (sp0 - 112)) by (rewrite N2, E2; reflexivity).
  assert (N8w : getr (ms_regs ms0) 8 = w64 AT) by (rewrite N8, (EEo 8%nat 8%bv eq_refl); exact R8).
  assert (SRD0 : cnl_stk_rd W1 (ms_mem ms0)) by (intros a Ha; rewrite AV1; exact (HSRD a Ha)).
  destruct (cnl_chain_at_xR ly1 S1 kk W1 (ms_mem ms0) mdN (ms_regs ms0) HJ SRD0
    (nls_frame_kept W1 W1 mem1 (ms_mem ms0) HFRM (fun a _ => AV1 a)) N2w N8w) as (chn & Hchn).
  assert (HPREn : AFP0 NL_STK ly1 S1 W1 (ms_regs ms0) (ms_mem ms0) mdN chn).
  { eapply (afn_pre_at0R (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms0) mdN kk (ms_regs ms0)
      NL_STK (- 112 - XO) chn HJi).
    - rewrite UspN. lia.
    - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
    - lia.
    - unfold NL_STK, NL_FRAME, ESTACK; lia.
    - rewrite WS. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
    - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact Hchn. }
  assert (HATn : val_mem SEGS (arm W1 (ms_mem ms0)) AT 8 An) by (apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact HAT]).
  eapply (SRrG_bind SEGS R R_trans).
  { (* next_line is a strict leaf: its SRr fact lifts to R *)
    apply (SRr_SRrG SEGS R WLE_R).
    eapply (NL W1 ly1 S1 [] (ms_regs ms0) (ms_mem ms0) mdN chn (112 + XO) AT (sp0 - 104) (sp0 - 112) An NO OUT ob HPREn).
    - lia.
    - rewrite Z.add_mod, AX16 by lia. reflexivity.
    - rewrite UspN, Etop. lia.
    - intros a Ha. apply HPRN. rewrite UspN in Ha. lia.
    - rewrite N10, (EEo 8%nat 8%bv eq_refl). exact R8.
    - rewrite N11, Usp. f_equal. lia.
    - rewrite N12. first [rewrite Usp; f_equal; lia | rewrite E2; reflexivity].
    - exact AAT8.
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 13; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [|exists 14; reflexivity].
      apply (Z.divide_trans _ 16); [exists 2; reflexivity | exact Hal16].
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - rewrite UspN. lia.
    - lia.
    - lia.
    - lia.
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (nls_ra_stack ly1 S1 W1 (ms_mem ms0) mdN); [exact HARN | rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - exact HATn.
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cno].
    - apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cout].
    - exact AOBN.
    - apply (nls_ob_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV1 | exact Cob].
    - lia.
    - intros _. split; [lia|]. split; [lia|]. split; [apply ANO32; lia|].
      intros a Ha. rewrite UspN. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - intros _. split; [rewrite Hsk; apply in_or_app; right; left; reflexivity|].
      split; [exact AMRO|].
      split; [apply (range_addressable_of_block0 ly1 S1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia]|].
      { exact HOin. }
      split; [apply (shadow_hull_vis_of_block0 ly1 S1 W1 (ms_mem ms0) mdN OUT CO); [exact HARN | | lia | lia | lia]|].
      { exact HOin. }
      intros a Hr. unfold rom_view in Crom. rewrite (AV1 a). exact (Crom a Hr). }
  cbv beta. intros W2 c2 Hwle2 (regs2 & mem2 & md2 & -> & HJn & HP2 & HWW & HPn & HFRn & Mno2 & Mout2 & Hob2 & HARM).
  subst W2.
  destruct HARM as [(HAO & _) | (ln & _ & Hfl & R10n & Vat2 & Vln2 & Vlen2)]; [lia|].
  assert (Hln : ln = snd r).
  { destruct Hfl as (rest & Hsk2 & Hnz'). rewrite Hsk in Hsk2. exact (nls_nul_split (snd r) ln (bsr rs ++ rest0) rest Hsk2 HnzR Hnz'). }
  subst ln.
  (* next_line's journal inside this one *)
  pose proof HJn as (_ & _ & _ & HXOn). rewrite UspN in HXOn, HFRn.
  pose proof (ajournal_gx_G_mono0 [] G (112 + XO) (nl_cells AT (sp0 - 104) (sp0 - 112)) NL_STK (spZ (ms_regs ms0)) []
    ly1 S1 W1 (ms_mem ms0) mdN [] ly1 S1 W1 mem2 md2 0 (fun a Ha => False_ind _ (inG_nil a Ha)) HJn) as HJn'.
  rewrite UspN in HJn'.
  pose proof (ajournal_gx_sub0R Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms0) mdN kk
    NL_STK (sp0 - 112) (112 + XO) (nl_cells AT (sp0 - 104) (sp0 - 112)) [] [] ly1 S1 W1 mem2 md2 0 HJ (cnl_gx_lift_xR HJn')
    ltac:(rewrite WS; unfold NL_STK, NL_FRAME, ESTACK; lia) ltac:(lia) ltac:(lia)) as HJ2.
  specialize (HJ2 ltac:(intros a (rr & Hrr & Ha); cbn [nl_cells In] in Hrr;
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha;
    [right; exists (AT, AT + 8); split; [left; reflexivity | cbn [fst snd]; lia] | left; rewrite WS; lia | left; rewrite WS; lia])
    HG ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))).
  cbn [app] in HJ2. rewrite Z.add_0_r in HJ2.
  assert (KEEPn : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - NL_STK <= a < sp0 - 112) ->
    ~ inFP (nl_cells AT (sp0 - 104) (sp0 - 112)) a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) (ms_mem ms0) a).
  { intros a Ha Hn Hcx. destruct (Z_lt_le_dec a (sp0 - 112)) as [Hlt | Hge]; [apply HFRn; [exact Ha | lia | exact Hcx]|].
    destruct (Z_lt_le_dec a (sp0 - 112 + (112 + XO))) as [Hlt2 | Hge2]; [apply HXOn; [lia | exact Hcx]|].
    apply HFRn; [exact Ha | lia | exact Hcx]. }
  assert (Hncell : forall a, ~ (sp0 - 112 <= a < sp0 - 96) -> a < AT \/ AT + 8 <= a ->
    ~ inFP (nl_cells AT (sp0 - 104) (sp0 - 112)) a).
  { intros a Hx1 Hx2 (rr & Hrr & Ha). cbn [nl_cells In] in Hrr.
    destruct Hrr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Ha; lia. }
  (* back at 0x85f28: keep the four regions, reseat the frame cells len (sp + 0) and line (sp + 8) *)
  jafter_call_keep_pi HS 50%nat regs2 (mrestrict (w_H W1) mem2) HP2 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); apply KEEPn.
    - rewrite Vb2 in Ha. lia.
    - rewrite Vb2 in Ha. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb2 in Ha; lia.
    - rewrite Vbg in Ha. lia.
    - rewrite Vbg in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vbg in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb9 in Ha. lia.
    - rewrite Vb9 in Ha. rewrite WS in Hslo. unfold NL_STK, NL_FRAME, ESTACK. lia.
    - apply Hncell; rewrite Vb9 in Ha; rewrite WS in Hslo; lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. unfold AREC in *. lia.
    - rewrite Vb33 in Ha. rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC, NL_STK, NL_FRAME, ESTACK in *. lia.
    - apply Hncell; rewrite Vb33 in Ha; rewrite HreqV in Hvceil; rewrite WS in Hslo; unfold AREC in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc Ev 50 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 50)%nat -> ew Ea m = ew Ev m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (F54 : ew Ea 54 = Z_to_bv 64 1) by (rewrite HEa; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; exact R10n).
  clear HEa.
  (* atom 66: the line's address, the value next_line left at sp + 16 *)
  apply (st_ok_pi_havoc_hi 66 Ea _ _ [Z_to_bv 64 (OUT + An)]) in HS; [|vm_compute; reflexivity].
  remember (havoc Ea 66 [Z_to_bv 64 (OUT + An)]) as Eb eqn:HEb in HS.
  assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
  assert (OLDb : forall m, (m < 66)%nat -> ew Eb m = ew Ea m) by (intros m Hm; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm).
  assert (F66 : ew Eb 66 = Z_to_bv 64 (OUT + An)) by (rewrite HEb; reflexivity).
  clear HEb.
  assert (OLD : forall m, (m < 50)%nat -> ew Eb m = ew Ev m) by (intros m Hm; rewrite OLDb by lia; exact (OLDa m Hm)).
  assert (E22 : ew Ev 22 = Z_to_bv 64 SB) by (rewrite (EEo 22%nat 22%bv eq_refl); exact R22).
  assert (Vb2b : base_val Eb (Some 2%nat) = sp0 - 112) by (cbn [base_val]; rewrite OLD by lia; exact Usp).
  assert (Vb9b : base_val Eb (Some 9%nat) = HA) by (rewrite <- Vb9; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vb33b : base_val Eb (Some 33%nat) = hl_v EE) by (rewrite <- Vb33; cbn [base_val]; rewrite OLD by lia; reflexivity).
  assert (Vbgb : base_val Eb (Some 268%nat) = VAL A_g_gone).
  { cbn [base_val]. assert (Hb : (A_TEXT <= 268 < A_LIM)%nat) by (cbv [A_TEXT A_LIM]; lia). exact (HEIb 268%nat Hb). }
  assert (HAR2 : AR0 ly1 S1 W1 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ2).
  apply (st_ok_pi_add_region Eb _ _ cnl_cells) in HS; [| reflexivity | | ].
  2: { unfold region_ok, cnl_cells. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem mkst restrict].
    rewrite Vb2b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 112) 0 8 (SOff 36 0) (Z.of_nat (length (snd r))));
      [cbn [sv_denot]; rewrite OLD by lia; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; unfold APARTIAL in HlenR; lia | cbn; lia |].
      replace (sp0 - 112 + 0) with (sp0 - 112) by lia. exact Vlen2.
    - apply (chunk_ok_val SEGS Eb _ (sp0 - 112) 8 8 (SOff 66 0) (OUT + An));
      [cbn [sv_denot]; rewrite F66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      replace (sp0 - 112 + 8) with (sp0 - 104) by lia. exact Vln2. }
  2: { apply all_disjoint_of_extents. unfold cnl_cells, extent_of_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi map ss_mem].
    rewrite Vb2b, Vbgb, Vb9b, Vb33b. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    rewrite HreqV in Hvceil. rewrite WS in Hslo. unfold AREC in *. repeat split; lia. }
  assert (SHOK2 : sh_ok SEGS BxL cnl_lSH Eb (mrestrict (w_H W1) mem2)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem2 md2 (HA + 64) 32 HAR2 AZS).
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 9 HA) by (first [rewrite OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block0 ly1 S1 W1 mem2 md2 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR2 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Eb 22 SB) by (first [rewrite OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Eb 33 (hl_v EE)) by (first [rewrite OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85f28: beqz a0 (abort); the traps on v (0x85f38, 0x85f3c-0x85f40); the length compare 0x85f60 (abort) ---- *)
  rewrite N1. paj_run_tok_xR RUNg HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUNg BRg HS SHOK2 Bspan.
  { (* next_line returned 0: impossible, it found r's line *)
    exfalso. rewrite branch_eq_U, (U_atom Eb 54 1), U_lit in Hc0 by (first [rewrite OLDb by lia; exact F54 | lia]).
    apply Z.eqb_eq in Hc0. lia. }
  clear Hc0. paj_run_tok_xR RUNg HS HJ2 SHOK2 Bspan. { nls_nowin_awr. }
  (* ---- bcmp(line, v[0].s, len) at 0x85f84, returning to 0x85f88 ---- *)
  assert (MQ2 : forall x, mrestrict (w_H W1) (ms_mem ms2) x = mrestrict (w_H W1) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr2 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr1 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem2 (ms_mem ms2) MQ2) as (AV2 & AP2).
  assert (AVc : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms2) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite AV2, KEEPn; [apply AV1 | lia | rewrite WS in Hslo; unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; rewrite WS in Hslo; lia. }
  pmkst HS.
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
  assert (UspB : spZ (ms_regs ms2) = sp0 - 112) by (unfold spZ at 1; rewrite T2, OLD by lia; rewrite E2; apply unsigned_lit_small; lia).
  assert (HARB : AR0 ly1 S1 W1 (ms_mem ms2) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md2) mat1 md2)) mat2
    (with_vm_backing (m_vm_lazy md2) mat1 md2))) by (eapply ajournal_gx_AR_xR; exact HJ2).
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (aj_bcmp_gx_at0R (SIGMA WS_bcmp) ABCMP G XO [(AT, AT + 8)] W1 (ms_regs ms2) (ms_mem ms2) CNL_STK sp0 FPc ly S W mem md []
      ly1 S1 _ kk (OUT + An) (fst r) (Z.of_nat (length (snd r))) (-112) (Z_to_bv 64 (BASE + 15428)) HG AX16 HJ2).
    - rewrite T10. exact F66.
    - rewrite T11, OLD by lia. exact E35.
    - rewrite T12, OLD by lia. exact E36.
    - unfold APARTIAL in HlenR. lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite UspB. lia.
    - reflexivity.
    - lia.
    - rewrite WS. unfold ESTACK. lia.
    - rewrite T3, OLD by lia. rewrite (EEo 3%nat 3%bv eq_refl). exact R3.
    - rewrite T4, OLD by lia. rewrite (EEo 4%nat 4%bv eq_refl). exact R4.
    - exact T1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AV2. replace a with (OUT + (a - OUT)) by lia. rewrite (Hob2 (a - OUT)) by lia. discriminate.
    - intros a Ha. split; [|rewrite UspB; unfold ESTACK; lia].
      rewrite AVc by lia. unfold aview, arm in *. replace a with (fst r + Z.of_nat (Z.to_nat (a - fst r))) by lia.
      rewrite (garr8_mbyte SEGS _ _ _ _ HgarR0) by (unfold bzs; rewrite length_map; lia). discriminate.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - intros a Ha. rewrite WS in Hslo. unfold ESTACK. lia.
    - unfold amem_range in *. lia.
    - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kLowMemEnd, kHighMemEnd in *. lia.
    - apply (range_addressable_of_block0 _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - intros Hp. apply (shadow_hull_vis_of_block0 _ _ _ _ _ OUT CO _ _ HARB HOin); lia.
    - apply (range_addressable_of_block0 _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia.
    - intros Hp. apply (shadow_hull_vis_of_block0 _ _ _ _ _ (fst r) (Z.of_nat (length (snd r)) + 1) _ _ HARB HinR); lia. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & vb & -> & HJ3 & HP3 & Hv & Hcmp & Hfr3 & Hpres3).
  (* r's line in the stream, as next_line left it *)
  assert (STR : forall i, (i < length (snd r))%nat ->
    aview SEGS (w_H W1) mem2 (OUT + An + Z.of_nat i) = Some (bv_unsigned (nth i (snd r) (Z_to_bv 8 0)))).
  { intros i Hi. replace (OUT + An + Z.of_nat i) with (OUT + (An + Z.of_nat i)) by lia.
    rewrite (Hob2 (An + Z.of_nat i)) by lia. do 2 f_equal.
    replace (Z.to_nat (An + Z.of_nat i)) with (Z.to_nat An + i)%nat by lia.
    rewrite <- nls_nth_skipn, Hsk. rewrite app_nth1 by exact Hi. reflexivity. }
  (* the line is v[0].s's text: bcmp returned 0 *)
  assert (Hv0 : vb = w64 0).
  { apply Hcmp. intros i Hi. rewrite AV2, AVc by lia.
    replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite STR by lia.
    rewrite (nls_view_of_garr8 W1 mem1 (fst r) (snd r) (Z.to_nat i) HgarR0) by lia. reflexivity. }
  assert (HAR3 : AR0 ly1 S1 W1 mem3 md3) by (eapply ajournal_gx_AR_xR; exact HJ3).
  jafter_call_keep_pi HS 67%nat regs3 (mrestrict (w_H W1) mem3) HP3 [0; 1; 2; 3; 4]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]];
    (split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; [|intros a Ha; exfalso; lia]);
    intros a Ha; apply (mbyte_of_aview SEGS); rewrite ?Vb2b, ?Vbgb, ?Vb9b, ?Vb33b in Ha; apply Hfr3;
    rewrite ?HreqV in Hvceil; rewrite ?WS in Hslo; unfold AREC, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Eb 67 (map (getr regs3) CLOB)) as Ec eqn:HEc in HS.
  assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEc; apply img_env_havoc; [exact HEIb | cbv; lia]).
  assert (OLDc : forall m, (m < 67)%nat -> ew Ec m = ew Eb m) by (intros m Hm; rewrite HEc; apply YN3v.ew_havoc_old; exact Hm).
  assert (F71 : ew Ec 71 = Z_to_bv 64 0) by (rewrite HEc; cbn [ew havoc map nth CLOB length Nat.sub Nat.ltb Nat.leb]; rewrite Hv, Hv0; reflexivity).
  clear HEc.
  assert (SHOK3 : sh_ok SEGS BxL cnl_lSH Ec (mrestrict (w_H W1) mem3)).
  { unfold sh_ok, cnl_lSH. constructor; [|constructor; [|constructor]].
    - eapply shent_ok_of_range.
      + apply (azs_range_addressable_x B ARx LAWS ly1 S1 [] W1 mem3 md3 (HA + 64) 32 HAR3 AZS).
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 9 HA) by (first [rewrite OLDc, OLD by lia; exact E9 | lia]). reflexivity.
      + lia.
      + lia.
      + intros x Hx. unfold SHADOW_OFF in *. lia.
    - eapply shent_ok_of_range.
      + apply (range_addressable_of_block0 ly1 S1 W1 mem3 md3 (hl_v EE) (AREC * hl_cap EE) (hl_v EE) 16 HAR3 HvinE); rewrite ?HreqV; unfold AREC in *; lia.
      + unfold BxL. rewrite (U_atom Ec 22 SB) by (first [rewrite OLDc, OLD by lia; exact E22 | unfold SB; lia]). reflexivity.
      + rewrite (U_atom Ec 33 (hl_v EE)) by (first [rewrite OLDc, OLD by lia; exact E33 | lia]). reflexivity.
      + lia.
      + rewrite HreqV in Hvceil. unfold AREC in *. lia.
      + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* ---- 0x85f88: bnez a0 (abort), then gesture_model(s, line, len) at 0x85f98 ---- *)
  paj_run_tok_xR RUNg HS HJ3 SHOK3 Bspan. { nls_nowin_awr. }
  psrr_branch_tok RUNg BRg HS SHOK3 Bspan.
  { exfalso. rewrite branch_ne_U, (U_atom Ec 71 0 F71), U_lit in Hc0 by lia. cbn in Hc0. discriminate. }
  clear Hc0. paj_run_to_tok_xR RUNTOg HS HJ3 SHOK3 Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ3 : forall x, mrestrict (w_H W1) (ms_mem ms4) x = mrestrict (w_H W1) mem3 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr4 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr3 ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem3 (ms_mem ms4) MQ3) as (AV3 & AP3).
  assert (KEEPb : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 112 - 2 * ESTACK <= a < sp0 - 112) ->
    aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) (ms_mem ms2) a).
  { intros a Ha Hn. rewrite AV3. apply Hfr3; [exact Ha | lia]. }
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  assert (LOW : forall a, 4096 <= a < alloc_ceiling -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). exact (AVc a Ha). }
  assert (FRM : forall a, sp0 - 96 <= a < sp0 -> aview SEGS (w_H W1) (ms_mem ms4) a = aview SEGS (w_H W1) mem1 a).
  { intros a Ha. rewrite KEEPb by (unfold ESTACK; lia). rewrite AV2, KEEPn; [apply AV1 | lia | unfold NL_STK, NL_FRAME, ESTACK; lia |].
    apply Hncell; lia. }
  assert (PRS : forall a, apresent (w_H W1) mem1 a -> apresent (w_H W1) (ms_mem ms4) a)
    by (intros a Hp; apply AP3, Hpres3, AP2, HPn, AP1, Hp).
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms4) md1 _ HAR1 LOW FRM PRS (or_intror (conj HOin HCO)) HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  assert (Ecp' : cpos gone A0 (pre ++ [r]) = An + Z.of_nat (length (snd r)) + 1).
  { unfold An, cpos. rewrite Hg0. cbn [Z.eqb]. rewrite nls_bsr_app, length_app, nls_bsr_cons, length_app. cbn [length].
    change (bsr []) with (@nil byte). cbn [length]. lia. }
  eapply (cnl_gm_xR pre r rs ly1 S1 kk H1 jk W1 (ms_regs ms4) (ms_mem ms4) _ (OUT + An) OUT CO
    HEQ HJ3 HPK' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite Ecp'. apply (nls_vm_kept W1 W1 mem2 (ms_mem ms4)); [|exact Vat2].
    intros i Hi. rewrite KEEPb by (cbn in Hi; unfold ESTACK; lia). exact (AV2 _).
  + exact HCONST'.
  + right. split; [exact HCO|]. split; [exact HOin | exact HOn].
  + intros _. exists rest0. rewrite Ecp'.
    replace (Z.to_nat (An + Z.of_nat (length (snd r)) + 1)) with ((length (snd r) + 1) + Z.to_nat An)%nat by lia.
    rewrite <- skipn_skipn, Hsk, skipn_app, skipn_all2 by lia.
    replace (length (snd r) + 1 - length (snd r))%nat with 1%nat by lia. reflexivity.
  + intros i Hi. rewrite LOW by exact (proj2 (cnl_errno_low i Hi)). exact (HERR i Hi).
  + intros a Ha. rewrite KEEPb by lia. rewrite AV2.
    destruct (Z_lt_le_dec a AT) as [Hl | Hg]; [|destruct (Z_lt_le_dec a (AT + 8)) as [Hl2 | Hg2]].
    * rewrite KEEPn by (try lia; apply Hncell; lia). rewrite AV1. exact (HSRD a Ha).
    * replace a with (AT + (a - AT)) by lia. exact (cnl_val_mem_view W1 mem2 AT 8 _ (a - AT) Vat2 ltac:(cbn; lia)).
    * rewrite KEEPn by (try lia; apply Hncell; lia). rewrite AV1. exact (HSRD a Ha).
  + exact HFRM'.
  + unfold cnl_regs_ok.
    assert (OLDx : forall m, (m < 50)%nat -> ew Ec m = ew Ev m) by (intros m Hm; rewrite OLDc, OLD by lia; reflexivity).
    assert (P24 : getr (ms_regs ms4) 24 = getr regs1 24).
    { rewrite Q24, O24. apply bv_eq. rewrite (HEIc 384%nat ltac:(cbv [A_TEXT A_LIM]; lia)), (HEI 384%nat ltac:(cbv [A_TEXT A_LIM]; lia)).
      reflexivity. }
    rewrite P24.
    assert (P2 : getr (ms_regs ms4) 2 = getr regs1 2) by (rewrite Q2, O2; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P3 : getr (ms_regs ms4) 3 = getr regs1 3) by (rewrite Q3, O3; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P4 : getr (ms_regs ms4) 4 = getr regs1 4) by (rewrite Q4, O4; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P8 : getr (ms_regs ms4) 8 = getr regs1 8) by (rewrite Q8, O8; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P9 : getr (ms_regs ms4) 9 = getr regs1 9) by (rewrite Q9, O9; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P18 : getr (ms_regs ms4) 18 = getr regs1 18) by (rewrite Q18, O18; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P19 : getr (ms_regs ms4) 19 = getr regs1 19) by (rewrite Q19, O19; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P22 : getr (ms_regs ms4) 22 = getr regs1 22) by (rewrite Q22, O22; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P23 : getr (ms_regs ms4) 23 = getr regs1 23) by (rewrite Q23, O23; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P25 : getr (ms_regs ms4) 25 = getr regs1 25) by (rewrite Q25, O25; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    assert (P27 : getr (ms_regs ms4) 27 = getr regs1 27) by (rewrite Q27, O27; first [reflexivity | repeat (rewrite OLDx by lia); reflexivity | cbn [sv_denot]; repeat (rewrite OLDx by lia); reflexivity]).
    rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P25, P27.
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10, OLDc, OLD by lia. exact E9.
  + rewrite Q11, OLDc by lia. exact F66.
  + rewrite Q12, OLDc, OLD by lia. exact E36.
  + apply nls_garr8_of_view. intros i Hi. rewrite KEEPb by (rewrite ?WS in Hslo; unfold ESTACK; lia). rewrite AV2. exact (STR i Hi).
  + exact HOin.
  + intros Hx. apply HOn. apply in_or_app. right. exact Hx.
  + lia.
  + lia.
- (* g_gone set: the text v[0] goes to gesture_model unread (the traps on v, 0x85ed8 / 0x85edc-0x85ee0, on the way) *)
  assert (Hg1 : gone <> 0) by (rewrite branch_eq_U, (U_atom Ev 32 gone E32), U_lit in Hc by lia; apply Z.eqb_neq in Hc; exact Hc).
  assert (Ecp : forall p, cpos gone A0 p = A0) by (intros p; unfold cpos; destruct (Z.eqb_spec gone 0); [contradiction | reflexivity]).
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan AF_fr_gesture_model. { nls_nowin_awr. }
  assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms0) x = mrestrict (w_H W1) mem1 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x).
    exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x). }
  destruct (nls_eqv_view W1 mem1 (ms_mem ms0) MQ) as (AV & AP).
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (27%bv : bv 5) Q27.
  destruct (nls_inv_kept ly1 S1 W1 mem1 (ms_mem ms0) md1 _ HAR1 (fun a _ => AV a) (fun a _ => AV a) AP HOBx HSRC HCONST HFRM HPK)
    as (HSRC' & HCONST' & HFRM' & HPK').
  eapply (cnl_gm_xR pre r rs ly1 S1 kk H1 jk W1 (ms_regs ms0) (ms_mem ms0) _ (fst r) (fst r) (Z.of_nat (length (snd r)) + 1)
    HEQ HJ HPK' HSRC' HND HTX HCAP HN HCB HPERM HFR HMLE HMOK HROOM HRMr HCNTr).
  + rewrite !Ecp in *. apply (nls_vm_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HAT].
  + exact HCONST'.
  + exact HOB.
  + intros Hg0. contradiction.
  + intros i Hi. rewrite AV. exact (HERR i Hi).
  + intros a Ha. rewrite AV. exact (HSRD a Ha).
  + exact HFRM'.
  + unfold cnl_regs_ok.
    rewrite (eq_trans Q2 (eq_sym O2)), (eq_trans Q3 (eq_sym O3)), (eq_trans Q4 (eq_sym O4)), (eq_trans Q8 (eq_sym O8)),
      (eq_trans Q9 (eq_sym O9)), (eq_trans Q18 (eq_sym O18)), (eq_trans Q19 (eq_sym O19)), (eq_trans Q22 (eq_sym O22)),
      (eq_trans Q23 (eq_sym O23)), (eq_trans Q24 (eq_sym O24)), (eq_trans Q25 (eq_sym O25)), (eq_trans Q27 (eq_sym O27)).
    exact HREGS.
  + rewrite Q1. reflexivity.
  + rewrite Q10. exact E9.
  + rewrite Q11. exact E35.
  + rewrite Q12. exact E36.
  + apply (nls_garr8_kept W1 W1 mem1 (ms_mem ms0)); [intros i _; apply AV | exact HgarR0].
  + exact HinR.
  + exact HnH1.
  + lia.
  + lia.
Qed.
(* cnl_test at R *)
Lemma cnl_test_xR : forall pre r rs W2 regs2 mem2 md2,
(rs <> [] -> forall W3 regs3 mem3 md3, cnl_inv_xR (pre ++ [r]) rs W3 regs3 mem3 md3 ->
  SRrG SEGS R W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + A_cnl_loop)) mem3 (seg_rom SEGS)) md3) Post_xR) ->
cnl_inv_xR (pre ++ [r]) rs W2 regs2 mem2 md2 ->
SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_drp)) mem2 (seg_rom SEGS)) md2) Post_xR.
Proof.
intros pre r rs W2 regs2 mem2 md2 IHL HI.
destruct HI as (ly2 & S2 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE2 & _).
cbn [set_exp_held hs_expected] in HE2.
pose proof HE2 as (MvE & MnE & _ & _ & (HnleC & HcapLt) & HvvE & _).
unfold cnl_E, hl_n in MvE, MnE, HnleC, HcapLt, HvvE. cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, HnleC, HcapLt, HvvE.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
assert (Hrs26 : Z.of_nat (length rs) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, !length_app in HnE. lia. }
assert (Rv : 0 <= hl_v EE < 2 ^ 64).
{ destruct HvvE as [(_ & ->) | (_ & Hvin & _)]; [lia|].
  destruct (cnl_blk ly2 S2 W2 mem2 md2 _ _ HAR2 Hvin) as (_ & H4096 & _ & _ & Hr1 & Hc & CC & _). lia. }
destruct (cnl_mkd A_cnl_drp W2 ly2 S2 mem2 md2 regs2 regs0 HA (hl_v EE) (Z.of_nat (length rs))
  HAR2 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 AZS HFRM MvE MnE Rv ltac:(lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs2 (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0)))) as Ed eqn:HEd.
assert (HEI : img_env VAL A_LIM Ed) by (rewrite HEd; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ed m = getr regs2 rr).
{ intros m rr Hm. rewrite HEd. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (EX : forall k, (k < 17)%nat -> ew Ed (32 + k) = nth k (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0)) (Z_to_bv 64 0)).
{ intros k Hk. rewrite HEd. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E2 : ew Ed 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E34 : ew Ed 34 = Z_to_bv 64 (Z.of_nat (length rs))) by exact (EX 2%nat ltac:(lia)).
assert (ES : forall k, (37 <= k < 49)%nat -> ew Ed k = Z_to_bv 64 (nth (k - 37) (cnl_svals regs0) 0)).
{ intros k Hk. assert (Ek : k = (32 + (5 + (k - 37)))%nat) by lia. rewrite Ek at 1.
  rewrite (EX (5 + (k - 37))%nat ltac:(lia)). unfold cnl_lx. rewrite map_app. cbn [map app nth Nat.add].
  apply map_nth. }
assert (HAE : env_agree 32 (Ereg regs2 (cnl_lx 0 (hl_v EE) (Z.of_nat (length rs)) 0 0 (cnl_svals regs0))) Ed)
  by (rewrite HEd; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HEd.
prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24.
prreg HS (25%bv : bv 5) O25.
unfold A_cnl_drp.
(* ---- 0x85fa8: lb a0,0(s7) (shadow of s + 72: zero); lw a0,0(s2); bgtz a0 -> the head 0x85ec4 ---- *)
paj_run_tok_xR RUNg HS HJ SHOK Bspan. { nls_nowin_awr. }
assert (MQ : forall x, mrestrict (w_H W2) (ms_mem ms) x = mrestrict (w_H W2) mem2 x)
  by (intros x; exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x)).
destruct (nls_eqv_view W2 mem2 (ms_mem ms) MQ) as (AV & AP).
psrr_branch_tok RUNg BRg HS SHOK Bspan.
- (* s->expected.n > 0: the next pass, from the head *)
  assert (Hne : rs <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ed (SOff 34 0)) = Z.of_nat (length rs)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length rs))) = Z.of_nat (length rs)) by (apply unsigned_lit_small; lia).
      rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
    rewrite Hs in Hc. intros E0. rewrite E0 in Hc. cbn in Hc. lia. }
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x88). { nls_nowin_awr. }
  assert (MQ0 : forall x, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x). apply MQ. }
  destruct (nls_eqv_view W2 mem2 (ms_mem ms0) MQ0) as (AV0 & AP0).
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ [2; 3; 4; 8; 9; 22; 27]%bv HS HAE ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19. prreg HS (23%bv : bv 5) F23. prreg HS (24%bv : bv 5) F24.
  prreg HS (25%bv : bv 5) F25.
  pmkst HS.
  unfold A_cnl_loop in IHL.
  apply (IHL Hne).
  exists ly2, S2, kk, H1, jk.
  split; [exact HEQ|].
  split; [exact HJ|].
  split; [exact (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W2 mem2 (ms_mem ms0) AP0))|].
  split; [exact (nls_src_kept_low ly2 S2 W2 mem2 (ms_mem ms0) md2 _ HAR2 HSRC (fun a _ => AV0 a) AP0)|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HN|]. split; [exact HCB|].
  split; [exact HPERM|]. split; [exact HFR|]. split; [exact HMLE|]. split; [exact HMOK|]. split; [exact HROOM|].
  split; [exact HRMr|]. split; [exact HCNTr|].
  split; [apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV0 | exact HAT]|].
  split; [exact (cnl_consts_meq W2 mem2 (ms_mem ms0) MQ0 HCONST)|].
  split; [exact HOB|]. split; [exact HSTR|].
  split; [intros i Hi; rewrite AV0; exact (HERR i Hi)|].
  split; [intros a Ha; rewrite AV0; exact (HSRD a Ha)|].
  split; [exact (nls_frame_kept W2 W2 mem2 (ms_mem ms0) HFRM (fun a _ => AV0 a))|].
  unfold cnl_regs_ok.
  rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)), (HK 8%bv ltac:(cbv; tauto)),
    (HK 9%bv ltac:(cbv; tauto)), (HK 22%bv ltac:(cbv; tauto)), (HK 27%bv ltac:(cbv; tauto)).
  rewrite (eq_trans F18 (eq_sym O18)), (eq_trans F19 (eq_sym O19)), (eq_trans F23 (eq_sym O23)), (eq_trans F24 (eq_sym O24)),
    (eq_trans F25 (eq_sym O25)).
  exact HREGS.
- (* s->expected.n = 0: the epilogue 0x85fc8 restores ra and s0..s10 and returns *)
  assert (Hrs0 : rs = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ed (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ed (SOff 34 0)) = Z.of_nat (length rs)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (Z.of_nat (length rs))) = Z.of_nat (length rs)) by (apply unsigned_lit_small; lia).
      rewrite bv_signed_small by (rewrite Hu; lia). exact Hu. }
    rewrite Hs in Hc. destruct rs; [reflexivity | cbn [length] in Hc; lia]. }
  subst rs.
  paj_run_tok_xR RUNg HS HJ SHOK Bspan. { nls_nowin_awr. }
  assert (MQ2 : forall x, mrestrict (w_H W2) (ms_mem ms0) x = mrestrict (w_H W2) mem2 x).
  { intros x. rewrite (nls_nowin _ _ _ _ HFr0 ltac:(vm_compute; reflexivity) x). apply MQ. }
  destruct (nls_eqv_view W2 mem2 (ms_mem ms0) MQ2) as (AV2 & AP2).
  prreg HS (1%bv : bv 5) F1. prreg HS (2%bv : bv 5) F2. prreg HS (3%bv : bv 5) F3. prreg HS (4%bv : bv 5) F4.
  prreg HS (8%bv : bv 5) F8. prreg HS (9%bv : bv 5) F9. prreg HS (18%bv : bv 5) F18. prreg HS (19%bv : bv 5) F19.
  prreg HS (20%bv : bv 5) F20. prreg HS (21%bv : bv 5) F21. prreg HS (22%bv : bv 5) F22. prreg HS (23%bv : bv 5) F23.
  prreg HS (24%bv : bv 5) F24. prreg HS (25%bv : bv 5) F25. prreg HS (26%bv : bv 5) F26. prreg HS (27%bv : bv 5) F27.
  assert (SV : forall k (rr : bv 5), (37 <= k < 49)%nat -> nth (k - 37) CNL_SAVED 0%bv = rr ->
    ew Ed k = getr regs0 rr).
  { intros k rr Hk Hn. rewrite (ES k Hk). unfold cnl_svals. rewrite (nth_indep _ 0 (bv_unsigned (getr regs0 0%bv)))
      by (cbn [length CNL_SAVED map]; lia).
    rewrite (map_nth (fun r0 => bv_unsigned (getr regs0 r0))). rewrite Hn. apply Z_to_bv_bv_unsigned. }
  (* the return moves no world: the strict return step lifts to R *)
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_xR.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?rr _ ?m _) ?d = _ /\ _ =>
    exists ly2, S2, [], rr, m, d, kk, (cnl_E [] jk), H1 end.
  split.
  { cbn [ms_regs]. rewrite F1, (SV 48%nat 1%bv ltac:(lia) eq_refl). rewrite Hra. reflexivity. }
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { intros rr Hr. unfold acallee_saved in Hr. cbn [ms_regs].
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
      rewrite F2, E2, (unsigned_lit_small (sp0 - 112)) by lia. replace (sp0 - 112 + 112) with sp0 by lia.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    - replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F3, (EEo 3%nat 3%bv eq_refl), R3. symmetry. exact Hgp.
    - replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F4, (EEo 4%nat 4%bv eq_refl), R4. symmetry. exact Htp.
    - replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F8. exact (SV 47%nat 8%bv ltac:(lia) eq_refl).
    - replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F9. exact (SV 46%nat 9%bv ltac:(lia) eq_refl).
    - assert (rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)
        as Hr' by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
      + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F18. exact (SV 45%nat 18%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F19. exact (SV 44%nat 19%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F20. exact (SV 43%nat 20%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F21. exact (SV 42%nat 21%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F22. exact (SV 41%nat 22%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F23. exact (SV 40%nat 23%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F24. exact (SV 39%nat 24%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F25. exact (SV 38%nat 25%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F26. exact (SV 37%nat 26%bv ltac:(lia) eq_refl).
      + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite F27, (EEo 27%nat 27%bv eq_refl). exact R27. }
  split; [exact (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W2 mem2 (ms_mem ms0) AP2))|].
  split; [cbn [ms_mem]; intros i Hi; rewrite AV2; exact (HERR i Hi)|].
  split; [cbn [ms_mem]; exact (nls_src_kept_low ly2 S2 W2 mem2 (ms_mem ms0) md2 _ HAR2 HSRC (fun a _ => AV2 a) AP2)|].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [rewrite HTX; f_equal; change (texts EE) with (txs (hl_recs EE)); rewrite HEQ, app_nil_r; reflexivity|].
  split; [unfold capb in HCB; exact HCB|].
  pose proof HCONST as (Cgone & Cno & Cout & Cob & _).
  split.
  { cbn [ms_mem]. apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2|].
    replace (if gone =? 0 then A0 + Z.of_nat (length (bstream EE)) else A0) with (cpos gone A0 (pre ++ [r])); [exact HAT|].
    unfold cpos, bstream, bsr. rewrite HEQ, app_nil_r. reflexivity. }
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cgone]|].
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cno]|].
  split; [cbn [ms_mem]; apply (nls_vm_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cout]|].
  split; [cbn [ms_mem]; apply (nls_ob_kept W2 W2 mem2 (ms_mem ms0)); [intros i _; apply AV2 | exact Cob]|].
  split; [exact HPERM|].
  split; [exact HFR|].
  split; [unfold cnl_cost; rewrite HEQ, app_nil_r; exact HMLE|].
  split; [exact HRMr|].
  (* the held list's capacity (cnl_post_x's last two conjuncts): H' = H1, whose capacity is cnl_cap over every
     record (cnl_inv's HCAP at pre ++ [r] = hl_recs EE, rs = []); it never shrinks (W_cnl_cnt.v cnl_cap_ge) *)
  assert (ECAP : hl_cap H1 = cnl_cap (texts HH) (hl_cap HH) (hl_recs EE)) by (rewrite HCAP, HEQ, app_nil_r; reflexivity).
  split; [rewrite ECAP; apply cnl_cap_ge | exact ECAP].
Qed.
(* cnl_drop at R: list_drop by LDROP_R *)
Lemma cnl_drop_xR : forall pre r rs W1 regs1 mem1 md1,
(rs <> [] -> forall W2 regs2 mem2 md2, cnl_inv_xR (pre ++ [r]) rs W2 regs2 mem2 md2 ->
  SRrG SEGS R W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + A_cnl_loop)) mem2 (seg_rom SEGS)) md2) Post_xR) ->
cnl_mid_xR pre r rs W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_back)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
intros pre r rs W1 regs1 mem1 md1 IHL HM.
destruct HM as (ly1 & S1 & kk & H1 & jk & HEQ & HJ & HPK & HSRC & HND & HTX & HCAP & HN & HCB & HPERM & HFR & HMLE & HMOK &
  HROOM & HRMr & HCNTr & HAT & HCONST & HOB & HSTR & HERR & HSRD & HFRM & HREGS).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof APRE as (_ & _ & _ & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (AC & _).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j AHAE AJLT AGA) as (HAlo & HAhi & HA8 & HA16 & Dgn & _ & _).
assert (HAR1 : AR0 ly1 S1 W1 mem1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
set (EL := cnl_E (r :: rs) jk) in *.
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpin & Hpj & _ & _ & HE1 & HH1 & HNDB).
cbn [set_exp_held hs_pending hs_partial hs_pjunk hs_expected hs_held] in Hpend, Hpin, Hpj, HE1, HH1.
pose proof HE1 as (MvE & MnE & _ & MwE & (HnleC & HcapLt) & HvvE & _ & _ & HFallE).
unfold EL, cnl_E, hl_n in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
cbn [hl_v hl_cap hl_recs hl_junk] in MvE, MnE, MwE, HnleC, HcapLt, HvvE, HFallE.
pose proof (Forall_inv HFallE) as (HinR & HgarR & HlinR & _).
destruct (HlinR eq_refl) as (HnzR & HlenR).
assert (HNN1 : 1 <= Z.of_nat (length (r :: rs))) by (cbn [length]; lia).
assert (HNNhi : Z.of_nat (length (r :: rs)) <= 2 ^ 26).
{ pose proof AEN as HnE. unfold hl_n in HnE. rewrite HEQ, length_app in HnE. lia. }
destruct HvvE as [(Hc0 & _) | (Hcpos & HvinE & Hjunk & HgarrE)]; [exfalso; lia|].
destruct (cnl_blk ly1 S1 W1 mem1 md1 (fst r) (Z.of_nat (length (snd r)) + 1) HAR1 HinR)
  as (Hr16 & Hr4096 & _ & Hrle & Hrreq1 & Hrceil & _ & Hroff & Hrapp & Hrpres).
destruct (cnl_blk ly1 S1 W1 mem1 md1 (hl_v EE) (AREC * hl_cap EE) HAR1 HvinE)
  as (Hv16 & Hv4096 & _ & _ & Hvreq1 & Hvceil & _ & Hvoff & Hvapp & Hvpres).
assert (HreqV : req_size (AREC * hl_cap EE) = AREC * hl_cap EE)
  by (unfold req_size; destruct (AREC * hl_cap EE =? 0) eqn:Eq; [apply Z.eqb_eq in Eq; unfold AREC in *; lia | reflexivity]).
destruct (cnl_rec_fields ly1 S1 W1 mem1 (HA + 64) EL true 0%nat HE1 ltac:(cbn; lia)) as (Mv0' & Mn0').
assert (Mv0 : val_mem SEGS (arm W1 mem1) (hl_v EE) 8 (fst r)).
{ rewrite <- (Z.mod_small (fst r) (2 ^ 64)) by lia.
  replace (hl_v EE) with (hl_v EL + 16 * Z.of_nat 0) by (cbn; lia). exact Mv0'. }
assert (Mn0 : val_mem SEGS (arm W1 mem1) (hl_v EE + 8) 8 (Z.of_nat (length (snd r)))).
{ rewrite <- (Z.mod_small (Z.of_nat (length (snd r))) (2 ^ 64)) by (unfold APARTIAL in HlenR; lia).
  replace (hl_v EE + 8) with (hl_v EL + 16 * Z.of_nat 0 + 8) by (cbn; lia). exact Mn0'. }
clear Mv0' Mn0'.
replace (HA + 64 + 8) with (HA + 72) in MnE by lia.
pose proof HCONST as (Cgone & Cno & Cout & Cob & Crom & Clg & Clb & Cle).
destruct (cnl_mk A_cnl_back W1 ly1 S1 mem1 md1 regs1 regs0 HA gone (hl_v EE) (Z.of_nat (length (r :: rs)))
  (fst r) (Z.of_nat (length (snd r))) (AREC * hl_cap EE)
  HAR1 HREGS Hal16 ltac:(lia) HAlo HAhi HA16 Dgn AZS HFRM Cgone AGN MvE MnE
  ltac:(lia) HvinE ltac:(rewrite HreqV; unfold AREC; lia) Mv0 Mn0 ltac:(lia) Hr16 ltac:(unfold APARTIAL in HlenR; lia)) as [HS SHOK].
pose proof HREGS as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R22 & R23 & R24 & R25 & R27).
remember (Eimg (Ereg regs1 (cnl_lx gone (hl_v EE) (Z.of_nat (length (r :: rs))) (fst r)
  (Z.of_nat (length (snd r))) (cnl_svals regs0)))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (rewrite HEv; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs1 rr).
{ intros m rr Hm. rewrite HEv. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E2 : ew Ev 2 = Z_to_bv 64 (sp0 - 112)) by (rewrite (EEo 2%nat 2%bv eq_refl); exact R2).
assert (E9 : ew Ev 9 = Z_to_bv 64 HA) by (rewrite (EEo 9%nat 9%bv eq_refl); exact R9).
clear HEv.
prreg HS (2%bv : bv 5) O2. prreg HS (3%bv : bv 5) O3. prreg HS (4%bv : bv 5) O4. prreg HS (8%bv : bv 5) O8.
prreg HS (9%bv : bv 5) O9. prreg HS (18%bv : bv 5) O18. prreg HS (19%bv : bv 5) O19. prreg HS (22%bv : bv 5) O22.
prreg HS (23%bv : bv 5) O23. prreg HS (24%bv : bv 5) O24. prreg HS (25%bv : bv 5) O25. prreg HS (27%bv : bv 5) O27.
unfold A_cnl_back.
(* ---- 0x85f9c: mv a0,s3; li a1,0; jal list_drop (0x85b50) ---- *)
paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan AF_fr_list_drop. { nls_nowin_awr. }
assert (MQ : forall x, mrestrict (w_H W1) (ms_mem ms) x = mrestrict (w_H W1) mem1 x)
  by (intros x; exact (nls_nowin _ _ _ _ HFr ltac:(vm_compute; reflexivity) x)).
destruct (nls_eqv_view W1 mem1 (ms_mem ms) MQ) as (AV & AP).
pmkst HS.
prreg HS (1%bv : bv 5) N1. prreg HS (2%bv : bv 5) N2. prreg HS (3%bv : bv 5) N3. prreg HS (4%bv : bv 5) N4.
prreg HS (8%bv : bv 5) N8. prreg HS (10%bv : bv 5) N10. prreg HS (11%bv : bv 5) N11.
prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (19%bv : bv 5) N19. prreg HS (22%bv : bv 5) N22.
prreg HS (23%bv : bv 5) N23. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25. prreg HS (27%bv : bv 5) N27.
lazymatch goal with |- SRrG _ _ _ {| cfg_ms := _; cfg_model := ?mdq |} _ => set (mdN := mdq) in * end.
assert (UspN : spZ (ms_regs ms) = sp0 - 112) by (unfold spZ at 1; rewrite N2, E2; apply unsigned_lit_small; lia).
(* the registers list_drop is called with are the loop's *)
assert (HREGSN : cnl_regs_ok (ms_regs ms) regs0 HA).
{ unfold cnl_regs_ok.
  rewrite (eq_trans N2 (eq_sym O2)), (eq_trans N3 (eq_sym O3)), (eq_trans N4 (eq_sym O4)), (eq_trans N8 (eq_sym O8)),
    (eq_trans N9 (eq_sym O9)), (eq_trans N18 (eq_sym O18)), (eq_trans N19 (eq_sym O19)), (eq_trans N22 (eq_sym O22)),
    (eq_trans N23 (eq_sym O23)), (eq_trans N24 (eq_sym O24)), (eq_trans N25 (eq_sym O25)), (eq_trans N27 (eq_sym O27)).
  exact HREGS. }
(* list_drop's globals: s->expected's head only *)
set (G2 := [(HA + 64, 16)]).
assert (HG2G : forall a, inG G2 a -> inG G a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; apply AGA; lia | exfalso; exact (inG_nil a Ha)]. }
assert (HnG2 : forall a, ~ (HA + 64 <= a < HA + 80) -> ~ inG G2 a).
{ intros a Hn Ha. apply inG_cons in Ha as [Ha | Ha]; [unfold in_zr in Ha; cbn [fst snd] in Ha; lia | exact (inG_nil a Ha)]. }
pose proof (gx_ok_sub SEGS B G2 G HG2G HG) as HG2.
assert (HG2R : forall a, inG G2 a -> inG cnl_ro a).
{ intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. unfold inG. apply Exists_exists. exists (VAL A_g_s, 384).
  split; [cbv [cnl_ro]; right; right; right; left; reflexivity|].
  unfold in_zr; cbn [fst snd]. rewrite AHAE in Ha. unfold ASRC in *. lia. }
assert (HGRT2 : gx_rt B G2) by (eapply gx_rt_sub; [exact HG2R | exact HGRR]).
assert (HRO2 : rom_out SEGS B G2).
{ apply cnl_rom_out_gs. intros a Ha. apply inG_cons in Ha as [Ha | Ha]; [|exfalso; exact (inG_nil a Ha)].
  unfold in_zr in Ha; cbn [fst snd] in Ha. rewrite AHAE in Ha. unfold ASRC in *. lia. }
(* list_drop's entry *)
destruct (ajournal_gx_inner0R G XO [(AT, AT + 8)] CNL_STK sp0 FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms) mdN kk HJ)
  as (memS & HJi & _).
assert (SRD0 : cnl_stk_rd W1 (ms_mem ms)) by (intros a Ha; rewrite AV; exact (HSRD a Ha)).
assert (HFRM0 : cnl_frame_ok W1 (ms_mem ms) sp0 regs0) by exact (nls_frame_kept W1 W1 mem1 (ms_mem ms) HFRM (fun a _ => AV a)).
destruct (cnl_chain_at_xR ly1 S1 kk W1 (ms_mem ms) mdN (ms_regs ms) HJ SRD0 HFRM0
  (proj1 HREGSN) (proj1 (proj2 (proj2 (proj2 HREGSN))))) as (chd & Hchd).
assert (HPREd : AFP0 LDROP_STK ly1 S1 W1 (ms_regs ms) (ms_mem ms) mdN chd).
{ eapply (afn_pre_at0R (CNL_STK + XO) (sp0 + XO) FPc ly S W memS md [] ly1 S1 W1 (ms_mem ms) mdN kk (ms_regs ms)
    LDROP_STK (- 112 - XO) chd HJi).
  - rewrite UspN. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_sub_r; [exists (-7); reflexivity | apply Z.mod_divide; [lia | exact AX16]].
  - lia.
  - unfold LDROP_STK, LDROP_FRAME, ASTACK; lia.
  - rewrite WS. unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - rewrite N1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite N1. destruct HBASE as (B1 & B2 & _). rewrite unsigned_lit_small by lia. lia.
  - rewrite N3, (EEo 3%nat 3%bv eq_refl). exact R3.
  - rewrite N4, (EEo 4%nat 4%bv eq_refl). exact R4.
  - exact Hchd. }
assert (HEL : alist_at B ly1 S1 W1 (ms_mem ms) (HA + 64) EL true).
{ apply (alist_at_kept B ly1 S1 W1 mem1 ly1 S1 W1 (ms_mem ms) (HA + 64) EL true HE1).
  - intros rr _ a _. apply abyte_kept_meq. apply MQ.
  - intros b Hb. exact (nls_blks_in _ _ _ _ _ _ _ HE1 b Hb). }
assert (HZ0 : 0 <= cnl_go MT (texts H1) (hl_cap H1) rs).
{ pose proof HH1 as (_ & _ & _ & _ & HcapH1 & _). apply nls_go_nonneg. unfold hl_n in HcapH1. lia. }
eapply (SRrG_bind SEGS R R_trans).
{ refine (LDROP_R G2 HG2 HGRT2 HRO2 W1 ly1 S1 [] (ms_regs ms) (ms_mem ms) mdN chd (HA + 64) EL true 0%nat HPREd _ _ HEL _ _ _ _ _ _ _ _
    (Z.to_nat (cnl_go MT_rk (texts H1) (hl_cap H1) rs) + kr)%nat _ _ _).
  - rewrite N10. first [rewrite <- O19; exact R19 | cbn [sv_denot]; rewrite E9, unsigned_lit_small by lia; reflexivity].
  - rewrite N11. reflexivity.
  - unfold EL, cnl_E. cbn [hl_recs length]. lia.
  - apply Z.mod_divide; [lia|]. apply Z.divide_add_r; [apply Z.mod_divide; [lia | exact HA8] | exists 8; reflexivity].
  - lia.
  - unfold EL, cnl_E, hl_n. cbn [hl_recs length]. pose proof AEN as Hn. unfold hl_n in Hn.
    rewrite HEQ, length_app in Hn. cbn [length] in Hn. unfold AREC. lia.
  - destruct AZS as (zr & Hzr & Hz8 & Hz1 & Hz2). exists zr. split; [exact Hzr|]. split; [exact Hz8|]. split; lia.
  - intros a Ha. split; [apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia | rewrite UspN; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia].
  - intros a Ha. unfold EL, cnl_E in Ha. cbn [hl_v hl_cap] in Ha. rewrite UspN. rewrite HreqV in Hvceil. unfold AREC, LDROP_STK, LDROP_FRAME, ASTACK in *. lia.
  - eapply (mo_ok_le MT ML); [exact HMOK|]. lia.
  - (* the room round: r's drop is the one free the budget owes before the rest *)
    exact HRMr.
  - (* list_drop's count premise (ldrop_pk = 0, cnt_ok) from the invariant (W_cnl_cnt.v cnl_cntm_free_pre) *)
    exact (cnl_cntm_free_pre RP r rs H1 _ HCNTr).
  - intros a Hr. rewrite AV. exact (Crom a Hr). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & hpD & regs2 & mem2 & md2 & -> & HJd & HPd & HPKd & HERd & HL2 & (b1 & b2 & Eb1 & Eb2) & HMLEd & HRMd).
hp0gR HJd.
unfold EL in HJd, Eb1, Eb2. cbn [cnl_E hl_recs hl_v hl_cap nth fst snd] in HJd, Eb1, Eb2.
assert (HAR2 : AR0 ly2 S2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJd).
(* what list_drop kept: its journal at G2 *)
pose proof HJd as HJd0. eapply ajournal_gx_inner_xR in HJd0. destruct HJd0 as (memS2 & HJdi & HgS2).
rewrite UspN in HJdi. destruct HJdi as (_ & HlyD & _ & _ & _ & HfrD & _ & _ & KF & KB & KI & _).
set (FPd := [(hl_v EE, hl_v EE + AREC * hl_cap EE);
  (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1))]) in *.
assert (Hcl : ~ YI16.sink_open_fp FPd).
{ apply sink_closed_pos. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia. }
assert (Kstk : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - 112 - LDROP_STK <= a < sp0 - 112) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Ha Hn. rewrite KF by (rewrite ?Z.add_0_r; lia). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. lia. }
assert (Kimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (HA + 64 <= a < HA + 80) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) (ms_mem ms) a).
{ intros a Hi Ho He Hn. pose proof (pa_img_range a Hi) as Hr.
  rewrite KI; [|exact Hi | exact Ho | exact He | exact (HPST a Hi) | exact (fp_spares_closed _ a Hcl)].
  apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. exact Hn. }
assert (Kblk : forall p n i, In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> ~ inFP FPd (p + i) ->
  0 <= i < req_size n -> aview SEGS (w_H W2) mem2 (p + i) = aview SEGS (w_H W1) (ms_mem ms) (p + i)).
{ intros p n i Hb1 Hb2 Hn Hi. destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hb1) as (_ & H4096 & _ & _ & _ & Hc2 & _ & Hoff & _).
  rewrite (KB p n i Hb1 Hb2 Hi Hn). apply HgS2. rewrite unsigned_lit_small by lia. apply HnG2. unfold off_img in Hoff. lia. }
assert (Pimg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  writable_at SEGS (arm W1 (ms_mem ms)) a -> writable_at SEGS (arm W2 mem2) a).
{ intros a Hi Ho He Hw. apply (nls_awr_kept W1 W2 (ms_mem ms) mem2 a); [|exact Hw]. intros Hp. exact (HPKd a Hi Ho He Hp). }
assert (Pblk : forall p n a, In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> writable_at SEGS (arm W2 mem2) a).
{ intros p n a Hb Ha. destruct (cnl_blk ly2 S2 W2 mem2 md2 p n HAR2 Hb) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpr).
  apply (apresent_writable SEGS). exact (proj1 (Hpr a Ha)). }
(* the blocks: list_drop took r's text out of the live ones *)
set (rb := (fst r, Z.of_nat (length (snd r)) + 1)) in *.
assert (HND1b : List.NoDup (ablocks B ly1 S1)) by exact (nls_nodup_blocks _ _ _ _ _ HAR1).
assert (Hlive : forall b, In b (ablocks B ly1 S1) -> b <> rb -> In b (ablocks B ly2 S2)).
{ intros b Hb Hne. rewrite Eb2. rewrite Eb1 in Hb. apply in_app_or in Hb as [Hb | [<- | Hb]];
  [apply in_or_app; left; exact Hb | exfalso; exact (Hne eq_refl) | apply in_or_app; right; exact Hb]. }
(* the expected list after the drop *)
set (jk' := HarnessRep.text_rec (last (r :: rs) (0, [])) ++ jk).
assert (EL2 : ldrop_list EL 0 = cnl_E rs jk') by reflexivity.
rewrite EL2 in HL2.
(* the source's blocks, as in cnl_gm *)
set (HL1 := list_blks H1) in *.
set (Ab := list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)] ++ list_blks EL).
assert (HNDl : List.NoDup (Ab ++ HL1)).
{ apply (nls_nodup_map _ _ fst). apply NoDup_ListNoDup in HNDB.
  replace (map fst (Ab ++ HL1)) with (hs_blocks (set_exp_held h EL H1)); [exact HNDB|].
  unfold hs_blocks, Ab, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
  rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
assert (HrbEL : In rb (list_blks EL)).
{ unfold list_blks. apply in_or_app. right. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))). left. reflexivity. }
assert (HvbEL : In (hl_v EE, AREC * hl_cap EE) (list_blks EL)).
{ unfold list_blks, EL, cnl_E. cbn [hl_cap hl_v]. destruct (hl_cap EE =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|].
  apply in_or_app. left. left. reflexivity. }
assert (Hs1 : VAL A_g_s <= HA /\ HA + 96 <= VAL A_g_s + 384) by (rewrite AHAE; unfold ASRC; lia).
assert (HNDl' : List.NoDup (((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL) ++ HL1)).
{ assert (Ex : ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL) ++ HL1 = Ab ++ HL1)
    by (unfold Ab; rewrite <- !app_assoc; reflexivity).
  rewrite Ex. exact HNDl. }
set (Oth := (list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ HL1).
assert (Hoth1 : forall b, In b Oth -> In b (ablocks B ly1 S1)).
{ intros b Hb. unfold Oth in Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (nls_blks_in _ _ _ _ _ _ _ HH1 _ Hb)].
  apply in_app_or in Hb as [Hb | Hb]; [exact (nls_blks_in _ _ _ _ _ _ _ Hpend _ Hb) | destruct Hb as [<- | []]; exact Hpin]. }
assert (Hoth2 : forall b, In b Oth -> In b (ablocks B ly2 S2)).
{ intros b Hb. apply (Hlive b (Hoth1 b Hb)). intros E'. subst b.
  exact (cnl_nodup_mid _ _ _ _ rb HNDl' Hb HrbEL). }
(* a byte of a block of the source other than r's text and the vector is outside list_drop's footprint *)
assert (KAb : forall b a, In b Oth -> fst b <= a < fst b + snd b -> abyte_kept W1 (ms_mem ms) W2 mem2 a).
{ intros (p & n) a Hb Ha. cbn [fst snd] in Ha.
  pose proof (Hoth1 _ Hb) as Hb1. pose proof (Hoth2 _ Hb) as Hb2.
  pose proof (cnl_nodup_mid _ _ _ _ (p, n) HNDl' Hb) as HnE.
  assert (Hnr : (p, n) <> rb) by (intros E'; rewrite E' in HnE; exact (HnE HrbEL)).
  assert (Hnv : (p, n) <> (hl_v EE, AREC * hl_cap EE)) by (intros E'; rewrite E' in HnE; exact (HnE HvbEL)).
  destruct (cnl_blk ly1 S1 W1 mem1 md1 p n HAR1 Hb1) as (_ & _ & Hn0 & Hnr' & _).
  replace a with (p + (a - p)) by lia.
  split; [|intros _; apply (Pblk p n); [exact Hb2 | lia]].
  apply (Kblk p n); [exact Hb1 | exact Hb2 | | lia].
  intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
  - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ p n HAR1 HvinE Hb1 ltac:(intros E'; apply Hnv; symmetry; exact E')) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
  - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ p n HAR1 HinR Hb1 ltac:(intros E'; apply Hnr; symmetry; exact E')) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the source's own bytes outside the expected head *)
assert (KHd : forall a, HA <= a < HA + 64 \/ HA + 80 <= a < HA + 96 -> abyte_kept W1 (ms_mem ms) W2 mem2 a).
{ intros a Ha. destruct (nls_ro (VAL A_g_s) 384 a ltac:(cbv [cnl_ro]; do 3 right; left; reflexivity) ltac:(lia)) as (Hi & Ho & He).
  split; [apply Kimg; [exact Hi | exact Ho | exact He | lia] | apply Pimg; assumption]. }
(* the expected list without r's record: its blocks and its source *)
assert (HPdrop : Permutation (list_blks EL) (rb :: list_blks (cnl_E rs jk'))) by exact (list_blks_drop0 (hl_v EE) (hl_cap EE) r rs jk jk').
pose proof (nls_src_kept_low ly1 S1 W1 mem1 (ms_mem ms) md1 _ HAR1 HSRC (fun a _ => AV a) AP) as HSRC0.
assert (HSRC2 : asrc_at B ly2 S2 W2 mem2 HA (set_exp_held h (cnl_E rs jk') H1)).
{ change (set_exp_held h (cnl_E rs jk') H1) with
    (set_exp_held (set_exp_held h EL H1) (cnl_E rs jk') (hs_held (set_exp_held h EL H1))).
  refine (nls_src_swap_e ly1 S1 W1 (ms_mem ms) ly2 S2 W2 mem2 HA (set_exp_held h EL H1) (cnl_E rs jk') HSRC0 KHd _ _ HL2 _).
  - intros rr Hrr a Ha. cbn [set_exp_held hs_partial hs_pjunk hs_pending hs_held] in Hrr.
    destruct Hrr as [<- | Hrr].
    + unfold gfp in Ha. cbn [fst snd] in Ha. unfold bzs in Ha. rewrite length_map, Hpj in Ha.
      apply (KAb (hs_partial h, APARTIAL)); [unfold Oth; apply in_or_app; left; apply in_or_app; right; left; reflexivity | cbn [fst snd]; exact Ha].
    + apply in_app_or in Hrr as [Hrr | Hrr].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ Hpend rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Oth; apply in_or_app; left; apply in_or_app; left; exact Hb | exact Hab].
      * destruct (nls_alist_fp_in _ _ _ _ _ _ _ HH1 rr Hrr a Ha) as [Hh | (b & Hb & Hab)]; [apply KHd; lia|].
        apply (KAb b); [unfold Oth; apply in_or_app; right; exact Hb | exact Hab].
  - intros b Hb. cbn [set_exp_held hs_partial hs_pending hs_held] in Hb. rewrite !nls_alist_blks in Hb.
    apply Hoth2. unfold Oth. destruct Hb as [<- | Hb]; [apply in_or_app; left; apply in_or_app; right; left; reflexivity|].
    apply in_app_or in Hb as [Hb | Hb]; [apply in_or_app; left; apply in_or_app; left; exact Hb | apply in_or_app; right; exact Hb].
  - apply NoDup_ListNoDup. apply NoDup_ListNoDup in HNDB.
    replace (hs_blocks (set_exp_held (set_exp_held h EL H1) (cnl_E rs jk') (hs_held (set_exp_held h EL H1))))
      with (map fst ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks (cnl_E rs jk') ++ HL1)).
    2: { unfold hs_blocks, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
         rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
    replace (hs_blocks (set_exp_held h EL H1))
      with (map fst ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL ++ HL1)) in HNDB.
    2: { unfold hs_blocks, HL1. cbn [set_exp_held hs_pending hs_partial hs_expected hs_held].
         rewrite !map_app, !nls_map_fst_blks. cbn [map fst]. rewrite <- !app_assoc. reflexivity. }
    assert (HP : Permutation ((list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks EL ++ HL1)
      (rb :: (list_blks (hs_pending h) ++ [(hs_partial h, APARTIAL)]) ++ list_blks (cnl_E rs jk') ++ HL1)).
    { rewrite HPdrop. apply Permutation_sym, Permutation_middle. }
    pose proof (Permutation_NoDup (Permutation_map fst HP) HNDB) as Hx. cbn [map] in Hx.
    apply List.NoDup_cons_iff in Hx as [_ Hx]. exact Hx. }
(* the journal: list_drop's inside this one *)
assert (HvbEE : In (hl_v EE, AREC * hl_cap EE) (list_blks EE)).
{ unfold list_blks. destruct (hl_cap EE =? 0) eqn:Ec; [apply Z.eqb_eq in Ec; lia|]. apply in_or_app. left. left. reflexivity. }
assert (HrbEE : In rb (list_blks EE)).
{ unfold list_blks. apply in_or_app. right. rewrite HEQ. apply (in_map (fun r0 => (fst r0, Z.of_nat (length (snd r0)) + 1))).
  apply in_or_app. right. left. reflexivity. }
assert (HFPd : forall a, inFP FPd a -> (inFP FPc a /\ exists b n, In (b, n) (ablocks B ly1 S1) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B ly1 S1) a).
{ intros a (rr & Hrr & Ha). left. cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Ha.
  - split; [|exists (hl_v EE), (AREC * hl_cap EE); split; [exact HvinE | rewrite HreqV; exact Ha]].
    exists (hl_v EE, hl_v EE + req_size (AREC * hl_cap EE)). split; [|cbn [fst snd]; rewrite HreqV; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (hl_v EE, AREC * hl_cap EE)).
    apply in_or_app. left. exact HvbEE.
  - split; [|exists (fst r), (Z.of_nat (length (snd r)) + 1); split; [exact HinR | exact Ha]].
    exists (fst r, fst r + req_size (Z.of_nat (length (snd r)) + 1)). split; [|cbn [fst snd]; exact Ha].
    unfold blk_FP. apply (in_map (fun b => (fst b, fst b + req_size (snd b))) _ rb). apply in_or_app. left. exact HrbEE. }
pose proof (ajournal_gx_G_mono0R G2 G 0 [] LDROP_STK (spZ (ms_regs ms)) FPd ly1 S1 W1 (ms_mem ms) mdN [] ly2 S2 W2 mem2 md2 1
  HG2G HJd) as HJd'. rewrite UspN in HJd'.
pose proof (ajournal_gx_sub0R Hsegs G CNL_STK sp0 XO [(AT, AT + 8)] FPc ly S W mem md [] ly1 S1 W1 (ms_mem ms) mdN kk
  LDROP_STK (sp0 - 112) 0 [] FPd [] ly2 S2 W2 mem2 md2 1 HJ HJd'
  ltac:(rewrite WS; unfold LDROP_STK, LDROP_FRAME, ASTACK; lia) ltac:(lia) ltac:(lia)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFPd) as HJ2.
cbn [app] in HJ2.
(* the loop's facts after the drop *)
pose proof CNLAP as (_ & Agn & _ & _ & _ & _ & Ano & Aou & Alg & Alb & Ale & _).
cbv zeta in Agn, Ano, Aou, Alg, Alb, Ale.
pose proof nls_lit_len as (L1 & L2 & L3).
assert (KR : forall b n x, In (b, n) cnl_ro -> b <= x < b + n -> ~ (HA + 64 <= x < HA + 80) ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W1) mem1 x).
{ intros b n x Hin Hx Hn. destruct (nls_ro b n x Hin Hx) as (Hi & Ho & He). rewrite (Kimg x Hi Ho He Hn). apply AV. }
assert (KS : forall a, sp0 - 96 <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W1) mem1 a).
{ intros a Ha. rewrite Kstk by (unfold LDROP_STK, LDROP_FRAME, ASTACK; lia). apply AV. }
assert (HREGS2 : cnl_regs_ok regs2 regs0 HA).
{ assert (P2 : getr regs2 2 = getr (ms_regs ms) 2) by (apply (HPd 2); unfold acallee_saved; lia).
  assert (P3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HPd 3); unfold acallee_saved; lia).
  assert (P4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HPd 4); unfold acallee_saved; lia).
  assert (P8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HPd 8); unfold acallee_saved; lia).
  assert (P9 : getr regs2 9 = getr (ms_regs ms) 9) by (apply (HPd 9); unfold acallee_saved; lia).
  assert (P18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HPd 18); unfold acallee_saved; lia).
  assert (P19 : getr regs2 19 = getr (ms_regs ms) 19) by (apply (HPd 19); unfold acallee_saved; lia).
  assert (P22 : getr regs2 22 = getr (ms_regs ms) 22) by (apply (HPd 22); unfold acallee_saved; lia).
  assert (P23 : getr regs2 23 = getr (ms_regs ms) 23) by (apply (HPd 23); unfold acallee_saved; lia).
  assert (P24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HPd 24); unfold acallee_saved; lia).
  assert (P25 : getr regs2 25 = getr (ms_regs ms) 25) by (apply (HPd 25); unfold acallee_saved; lia).
  assert (P27 : getr regs2 27 = getr (ms_regs ms) 27) by (apply (HPd 27); unfold acallee_saved; lia).
  unfold cnl_regs_ok. rewrite P2, P3, P4, P8, P9, P18, P19, P22, P23, P24, P25, P27. exact HREGSN. }
assert (HI2 : cnl_inv_xR (pre ++ [r]) rs W2 regs2 mem2 md2).
{ exists ly2, S2, (kk + 1), H1, jk'.
  split; [rewrite HEQ, <- app_assoc; reflexivity|].
  split; [exact HJ2|].
  split; [exact (nls_apk_trans _ _ _ _ _ _ (nls_apk_trans _ _ _ _ _ _ HPK (nls_apk_of_pres W1 mem1 (ms_mem ms) AP)) HPKd)|].
  split; [exact HSRC2|].
  split; [exact HND|]. split; [exact HTX|]. split; [exact HCAP|]. split; [exact HN|]. split; [exact HCB|].
  split.
  { intros rest HQ0. pose proof (HPERM rest HQ0) as HP1. rewrite Eb2. rewrite Eb1 in HP1.
    apply (cnl_perm_drop _ b1 b2 _ rb). eapply Permutation_trans; [exact HP1|].
    rewrite HPdrop. reflexivity. }
  split; [rewrite HfrD; exact HFR|].
  split; [eapply (mo_le_mono MT ML); [exact (mo_le_trans MT ML _ _ _ _ _ HMLE HMLEd)|]; lia|].
  split; [apply (mo_ok_step MT ML S1 S2 (mo_free MT)); [exact HMOK | exact HMLEd]|].
  split.
  { assert (BB : blocks_bytes S2 = blocks_bytes S1 - (Z.of_nat (length (snd r)) + 1)).
    { rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2), Eb1, Eb2, !bsum_app, bsum_cons. unfold rb. cbn [snd]. lia. }
    rewrite BB. exact HROOM. }
  (* the room round: list_drop's post room is the rest's budget; the counts fell by r's line (W_cnl_cnt.v
     cnl_cnt_free) *)
  split; [exact HRMd|].
  split; [rewrite Eb2; rewrite Eb1 in HCNTr; exact (cnl_cnt_free RP r rs H1 b1 b2 (fst r) HCNTr)|].
  split; [apply (nls_vm_kept W1 W2 mem1 mem2); [intros i Hi; apply KS; cbn in Hi; lia | exact HAT]|].
  split.
  { split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cgone]; intros i Hi;
      apply (KR (VAL A_g_gone) 1); [cbv [cnl_ro]; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cno]; intros i Hi;
      apply (KR (VAL A_g_nout) 8); [cbv [cnl_ro]; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split; [apply (nls_vm_kept W1 W2 mem1 mem2); [|exact Cout]; intros i Hi;
      apply (KR (VAL A_g_out) 8); [cbv [cnl_ro]; right; right; left; reflexivity | cbn in Hi; lia | cbn in Hi; lia]|].
    split.
    { apply (nls_ob_kept W1 W2 mem1 mem2); [|exact Cob]. intros i Hi.
      destruct HOB as [-> | (HCO & HOin & HOn)]; [cbn [length] in Hi; lia|].
      assert (HOr : (OUT, CO) <> rb) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HrbEL).
      assert (HOv : (OUT, CO) <> (hl_v EE, AREC * hl_cap EE)) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HvbEL).
      destruct (cnl_blk ly1 S1 W1 mem1 md1 OUT CO HAR1 HOin) as (_ & _ & _ & Hnr & _).
      rewrite (Kblk OUT CO i HOin (Hlive _ HOin HOr)); [apply AV | | lia].
      intros (rr & Hrr & Har). cbn [FPd In] in Hrr. destruct Hrr as [<- | [<- | []]]; cbn [fst snd] in Har.
      - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ OUT CO HAR1 HvinE HOin ltac:(intros E'; apply HOv; symmetry; exact E')) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HreqV in Hd. lia.
      - pose proof (sep_blocks0 ly1 S1 W1 mem1 md1 _ _ OUT CO HAR1 HinR HOin ltac:(intros E'; apply HOr; symmetry; exact E')) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    split; [eapply ajournal_gx_rom_view0R; [exact HJd | exact HRO2 | intros a Hr; rewrite AV; exact (Crom a Hr)]|].
    split; [apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Clg]; intros i Hi;
      apply (KR (VAL A_lit_gesture) 13); [cbv [cnl_ro]; do 4 right; left; reflexivity | rewrite L1 in Hi; lia | rewrite L1 in Hi; lia]|].
    split; [apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Clb]; intros i Hi;
      apply (KR (VAL A_lit_begin) 5); [cbv [cnl_ro]; do 5 right; left; reflexivity | rewrite L2 in Hi; lia | rewrite L2 in Hi; lia]|].
    apply (nls_garr8_kept W1 W2 mem1 mem2); [|exact Cle]; intros i Hi.
    apply (KR (VAL A_lit_end) 3); [cbv [cnl_ro]; do 6 right; left; reflexivity | rewrite L3 in Hi; lia | rewrite L3 in Hi; lia]. }
  split.
  { destruct HOB as [Hob0 | (HCO & HOin & HOn)]; [left; exact Hob0 | right].
    assert (HOr : (OUT, CO) <> rb) by (intros E'; apply HOn; apply in_or_app; left; rewrite E'; exact HrbEL).
    split; [exact HCO|]. split; [exact (Hlive _ HOin HOr)|].
    intros Hx. apply HOn. apply in_app_or in Hx as [Hx | Hx]; [|apply in_or_app; right; exact Hx].
    apply in_or_app. left. apply (Permutation_in _ (Permutation_sym HPdrop)). right. exact Hx. }
  split; [exact HSTR|].
  split; [intros i Hi; rewrite (HERd i Hi), AV; exact (HERR i Hi)|].
  split; [intros a Ha; rewrite KS by lia; exact (HSRD a Ha)|].
  split; [apply (nls_frame_kept W1 W2 mem1 mem2 HFRM); intros a Ha; apply KS; lia|].
  exact HREGS2. }
rewrite N1.
exact (cnl_test_xR pre r rs W2 regs2 mem2 md2 IHL HI2).
Qed.
(* cnl_loop / cnl_enter at R *)
Lemma cnl_loop_xR : forall k pre rs W1 regs1 mem1 md1, length rs = k -> rs <> [] ->
cnl_inv_xR pre rs W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
induction k as [|k IH]; intros pre rs W1 regs1 mem1 md1 Hk Hne HI; [destruct rs; [exfalso; exact (Hne eq_refl) | discriminate Hk]|].
destruct rs as [|r rs]; [exfalso; exact (Hne eq_refl)|]. cbn [length] in Hk. injection Hk as Hk.
eapply (SRrG_bind SEGS R R_trans); [exact (cnl_step_xR pre r rs W1 regs1 mem1 md1 HI)|].
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & HM).
apply (cnl_drop_xR pre r rs W2 regs2 mem2 md2); [|exact HM].
intros Hne2 W3 regs3 mem3 md3 HI3. exact (IH (pre ++ [r]) rs W3 regs3 mem3 md3 Hk Hne2 HI3).
Qed.
Lemma cnl_enter_xR : forall W1 regs1 mem1 md1, hl_recs EE <> [] -> cnl_inv_xR [] (hl_recs EE) W1 regs1 mem1 md1 ->
SRrG SEGS R W1 (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + A_cnl_loop)) mem1 (seg_rom SEGS)) md1) Post_xR.
Proof.
intros W1 regs1 mem1 md1 Hne HI.
exact (cnl_loop_xR (length (hl_recs EE)) [] (hl_recs EE) W1 regs1 mem1 md1 eq_refl Hne HI).
Qed.
End wR.
End loop.
Theorem pb_check_no_loss_at : forall W ly S regs mem md ch HA (j : nat) (h : hsrc) gone A0 NO OUT (ob : list byte),
AFP0 CNL_STK ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 AT ->
HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
asrc_at B ly S W mem HA h ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
NoDup (texts (hs_held h)) ->
hl_n (hs_expected h) < 2 ^ 26 ->
hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
val_mem SEGS (arm W mem) AT 8 A0 -> 0 <= A0 <= NO ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (VAL A_g_nout) 8 NO -> val_mem SEGS (arm W mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = NO -> NO <= 2 ^ 40 -> (0 < NO -> NO < 2 ^ 32) -> amem_range OUT (NO + 8) ->
(ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
(gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream (hs_expected h) ++ rest) ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
cnl_room MMAX (blocks_bytes S) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) ->
mo_ok MT S (cnl_cost MT (hs_expected h) (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cnl_cost MT_rk (hs_expected h) (hs_held h)) + kr) ->
cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S) ->
AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 ->
(forall a, spZ regs <= a < ly_top ly -> aview SEGS (w_H W) mem a <> None) ->
SRr SEGS W (cfg_at SEGS A_check_no_lossP regs mem md)
  (cnl_post_x B PST ARx MT RP G regs ly S [] W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
Proof.
intros W ly S regs mem md ch HA j h gone A0 NO OUT ob HPRE HXO HX16 HXtop HXp H10 H11 EHA Hj
HAT8 HATlo HAThi HSRC HGa Hzs HND HnE HnH MAT RA0 Mg Rg Mno Mout HOB Hlen HNO40 HNO32 HmrO HOBK HSKP Hrom
Hlg Hlb Hle HROOM HMOK kr HRM0 HCNT0 HCAPB HSTK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & HH0 & _).
destruct (cnl_entry W ly S regs mem md ch HA j (hs_expected h) HPRE H10 EHA Hj HGa Hzs HE HnE) as [HS SHOK].
pose proof (ajournal_gx_init0 G XO [(AT, AT + 8)] CNL_STK
  (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))) ly S W regs mem md ch HPRE HXO HX16 HXtop HXp) as HJ.
remember (Eimg (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E1 : ew Ev 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew Ev 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n (hs_expected h)))
  by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h)))) Ev)
  by (rewrite HEv; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HEv.
unfold cfg_at. change (w64 A_check_no_lossP) with (Z_to_bv 64 A_check_no_lossP).
unfold A_check_no_lossP, A_check_no_loss.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* s->expected.n <= 0: nothing to check, straight to the return *)
  assert (Hn0 : hl_recs (hs_expected h) = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc.
    destruct (hl_recs (hs_expected h)) as [|r rs]; [reflexivity|]. cbn [length] in Hc. lia. }
  paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
  assert (MEQ : forall x, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 112 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_x.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists ly, S, [], r, m, d, 0, (hs_expected h), (hs_held h) end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { lazymatch type of HS with st_ok_pi _ _ ?Eq _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Eq _ _ regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))) HS);
    [exact HAE | vm_compute; reflexivity] end. }
  split.
  { intros a Hi Hno Hne Hp. cbn [ms_mem]. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { cbn [ms_mem]. intros i Hi. apply aview_meq. apply MEQa. pose proof (cnl_errno_low i Hi) as (He1 & He2). lia. }
  split.
  { cbn [ms_mem]. rewrite set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 112) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact Hn0|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [unfold texts; rewrite Hn0; reflexivity|].
  split; [unfold capb in *; lia|].
  split.
  { cbn [ms_mem]. replace (if gone =? 0 then A0 + Z.of_nat (length (bstream (hs_expected h))) else A0) with A0.
    - apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
      intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia.
    - unfold bstream. rewrite Hn0. cbn [map concat length Z.of_nat]. destruct (gone =? 0); lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
    apply MEQa. destruct HOBK as [-> | (CO & HCO & HCOin & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly S W mem md OUT CO HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
  split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [unfold cnl_cost; rewrite Hn0; cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HRM0; rewrite Hn0 in HRM0; exact HRM0|].
  (* the held list's capacity: no record, H' = H *)
  split; [lia | rewrite Hn0; reflexivity].
- (* s->expected.n > 0: the rest of the prologue (0x85eac .. 0x85ec0) to the loop head 0x85ec4, then the loop *)
  assert (Hne : hl_recs (hs_expected h) <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc. intros He. rewrite He in Hc. cbn [length Z.of_nat] in Hc. lia. }
  (* the blocks of the two lists are a part of the live blocks (asrc_at: NoDup (hs_blocks h)) *)
  assert (APERM0 : exists rest, Permutation (ablocks B ly S) (list_blks (hs_expected h) ++ list_blks (hs_held h) ++ rest)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNDb).
    assert (LB : forall (l : hlist) LA, alist_at B ly S W mem LA l true -> incl (list_blks l) (ablocks B ly S)).
    { intros l LA HA2 b Hin. destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec).
      unfold list_blks in Hin. apply in_app_or in Hin as [Hin | Hin].
      - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
        destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin].
      - apply in_map_iff in Hin as (r & <- & Hr). rewrite Forall_forall in Hrec. exact (proj1 (Hrec r Hr)). }
    assert (ND : List.NoDup (list_blks (hs_expected h) ++ list_blks (hs_held h))).
    { apply (NoDup_map_inv fst). rewrite map_app, !cnl_list_blks_fst.
      unfold hs_blocks in HNDb. apply NoDup_ListNoDup in HNDb.
      apply cnl_nodup_app_r in HNDb. apply cnl_nodup_app_r in HNDb. exact HNDb. }
    destruct (perm_of_incl _ (ablocks B ly S) ND (incl_app (LB _ _ HE) (LB _ _ HH0))) as (rest & HP).
    exists rest. rewrite <- app_assoc in HP. exact HP. }
  paj_run_to_tok_x RUNTO HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x88).
  { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
  rewrite !wvb_collapse in HJ.
  assert (MEQ : forall x, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 112 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  (* the registers at the loop head *)
  assert (E3 : ew Ev 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
  assert (E4 : ew Ev 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
  assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew Ev 11 = Z_to_bv 64 AT) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (UHA : bv_unsigned (ew Ev 10) = HA) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E384 : bv_unsigned (ew Ev 384) = VAL (A_HI 104)) by exact (HEI 384%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?ms1) =>
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (23%bv : bv 5) HS) as Q23;
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (25%bv : bv 5) HS) as Q25;
    let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
    change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23;
    let e25 := eval vm_compute in (sr_get (ss_regs ss) (25%bv : bv 5)) in
    change (sr_get (ss_regs ss) (25%bv : bv 5)) with e25 in Q25 end.
  rewrite (U_shadow_reg Ev 10 32 72 HA E10 E32) in Q23 by lia.
  rewrite (U_shadow_reg Ev 10 32 64 HA E10 E32) in Q25 by lia.
  (* the frame cells: the prologue's 13 stores *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ss) 0%nat) in
    lazymatch r0 with Some ?r => pose proof (st_ok_pi_region_nth Ev ss _ 0%nat r HS eq_refl) as HR0 end end.
  cbn [ms_mem restrict] in HR0.
  assert (Hcp : cpos gone A0 [] = A0) by (unfold cpos, bsr; cbn [map concat length Z.of_nat]; destruct (gone =? 0); lia).
  assert (HCO : exists CO, ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\
    ~ In (OUT, CO) (list_blks (hs_expected h) ++ list_blks (hs_held h)))).
  { destruct HOBK as [-> | (CO & H1 & H2 & H3)]; [exists 0; left; reflexivity|].
    exists CO. right. split; [exact H1|]. split; [exact H2|].
    intros Hin. apply H3. apply (in_map fst) in Hin. cbn [fst] in Hin. rewrite map_app, !cnl_list_blks_fst in Hin.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  destruct HCO as (CO & HCO).
  pmkst HS.
  assert (Epc : 15232 = A_cnl_loop) by reflexivity. rewrite Epc.
  eapply (cnl_enter regs ly S W mem md ch HA j h gone A0 NO OUT CO ob kr).
  all: try eassumption.
  unfold cnl_inv.
  exists ly, S, 0, (hs_held h), (hl_junk (hs_expected h)).
  split; [reflexivity|].
  split; [exact HJ|].
  split.
  { intros a Hi Hno Hne' Hp. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { unfold cnl_E. rewrite cnl_E_id, set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 112) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact HND|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [unfold txs, count_begin; cbn [map filter length Z.of_nat]; lia|].
  split; [unfold capb; lia|].
  split; [intros rest Hp; unfold cnl_E; rewrite cnl_E_id; exact Hp|].
  split; [reflexivity|].
  split; [cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HMOK; exact HMOK|].
  split; [exact HROOM|].
  split; [exact HRM0|].
  split; [exact (cnl_cnt_entry RP (hs_expected h) (hs_held h) _ HCNT0)|].
  split.
  { rewrite Hcp. apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
    intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { unfold cnl_consts.
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
      apply MEQa. destruct HOBK as [-> | (CO' & HCO' & HCOin & _)]; [cbn [length] in Hi; lia|].
      destruct (cnl_blk ly S W mem md OUT CO' HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
    split.
    { intros a Hin. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (Hrom a Hin)|].
      apply MEQa. destruct Hin as (sg & Hsg & _ & Hsr).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hsr])) as HI. lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.K_GESTURE); [|exact Hlg].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.K_GESTURE) <= 13) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_gesture) 13 x
        ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_BEGIN); [|exact Hlb].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_BEGIN) <= 5) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_begin) 5 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_END); [|exact Hle].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_END) <= 3) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_end) 3 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. } }
  split; [exact HCO|].
  split.
  { intros Hg0. rewrite Hcp. destruct (HSKP Hg0) as (rest & Hr). exists rest. unfold bsr. unfold bstream in Hr. exact Hr. }
  split.
  { intros i Hi. apply aview_meq. apply MEQa. pose proof (cnl_errno_low i Hi) as (He1 & He2). lia. }
  split.
  { intros a Ha. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (HSTK a Ha)|].
    apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { apply (cnl_frame_of_region Ev W (ms_mem ms0) regs _ _ _ _ _ HR0 Usp EEo).
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd In]; repeat (first [left; reflexivity | right]). }
  unfold cnl_regs_ok.
  split; [rewrite Q2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite Q3, E3; exact Hgp|].
  split; [rewrite Q4, E4; exact Htp|].
  split; [rewrite Q8, E11; reflexivity|].
  split; [rewrite Q9, E10; reflexivity|].
  split; [rewrite Q18, UHA; reflexivity|].
  split; [rewrite Q19, UHA; reflexivity|].
  split; [rewrite Q22, E32; reflexivity|].
  split; [exact Q23|].
  split; [rewrite Q24; unfold w64; rewrite <- E384, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Q25|].
  rewrite Q27. exact (EEo 27%nat 27%bv eq_refl).
Qed.
(* ---- route R: pb_check_no_loss_at at a world relation R.  Its strict proof with the journal at R (from
   ajournal_gx_init_xR, R_refl), the prologue's runs concluding SRrG (RUNg / RUNTOg, BRg), the empty case's return lifted
   by SRr_SRrG (WLE_R), and the loop by cnl_enter_xR.  The strict pb_check_no_loss_at above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis LDROP_R : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_xR B PST ARx R MT RP G0 (BASE + AF_fr_list_drop).
Let RUNg := paj_run_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let RUNTOg := paj_run_to_x_xG B PST ARx LAWS R G HG XO [(AT, AT + 8)].
Let BRg := paj_branch_xR (PI := PI) (R := R).
Local Notation ajournal_gx_init0R Gq XOq OUTq STKq FPq lyq Sq Wq regsq memq mdq chq :=
  (ajournal_gx_init_xR SEGS B PST ARx R_refl Gq XOq OUTq STKq FPq lyq Sq [] Wq regsq memq mdq chq).
Theorem pb_check_no_loss_at_xR : forall W ly S regs mem md ch HA (j : nat) (h : hsrc) gone A0 NO OUT (ob : list byte),
AFP0 CNL_STK ly S W regs mem md ch ->
0 <= XO -> XO mod 16 = 0 -> spZ regs + XO <= ly_top ly ->
(forall a, spZ regs <= a < spZ regs + XO -> apresent (w_H W) mem a) ->
getr regs 10 = w64 HA -> getr regs 11 = w64 AT ->
HA = VAL A_g_s + ASRC * Z.of_nat j -> (j < 4)%nat ->
AT mod 8 = 0 -> spZ regs <= AT -> AT + 8 <= spZ regs + XO ->
asrc_at B ly S W mem HA h ->
(forall a, HA + 64 <= a < HA + 96 -> inG G a) -> azs B (HA + 64) 32 ->
NoDup (texts (hs_held h)) ->
hl_n (hs_expected h) < 2 ^ 26 ->
hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 ->
val_mem SEGS (arm W mem) AT 8 A0 -> 0 <= A0 <= NO ->
val_mem SEGS (arm W mem) (VAL A_g_gone) 1 gone -> 0 <= gone < 256 ->
val_mem SEGS (arm W mem) (VAL A_g_nout) 8 NO -> val_mem SEGS (arm W mem) (VAL A_g_out) 8 OUT ->
ob_at W mem OUT ob -> Z.of_nat (length ob) = NO -> NO <= 2 ^ 40 -> (0 < NO -> NO < 2 ^ 32) -> amem_range OUT (NO + 8) ->
(ob = [] \/ exists CO, NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\ ~ In OUT (hs_blocks h)) ->
(gone = 0 -> exists rest, skipn (Z.to_nat A0) ob = bstream (hs_expected h) ++ rest) ->
rom_view SEGS W mem ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
cnl_room MMAX (blocks_bytes S) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) ->
mo_ok MT S (cnl_cost MT (hs_expected h) (hs_held h)) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (cnl_cost MT_rk (hs_expected h) (hs_held h)) + kr) ->
cnt_ok_pk RP (cnl_pk (hs_expected h) (hs_held h)) (ablocks B ly S) ->
AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 ->
(forall a, spZ regs <= a < ly_top ly -> aview SEGS (w_H W) mem a <> None) ->
SRrG SEGS R W (cfg_at SEGS A_check_no_lossP regs mem md)
  (cnl_post_xR B PST ARx R MT RP G regs ly S [] W mem md XO HA AT h (hs_expected h) (hs_held h) gone A0 NO OUT ob kr).
Proof.
intros W ly S regs mem md ch HA j h gone A0 NO OUT ob HPRE HXO HX16 HXtop HXp H10 H11 EHA Hj
HAT8 HATlo HAThi HSRC HGa Hzs HND HnE HnH MAT RA0 Mg Rg Mno Mout HOB Hlen HNO40 HNO32 HmrO HOBK HSKP Hrom
Hlg Hlb Hle HROOM HMOK kr HRM0 HCNT0 HCAPB HSTK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : CNL_STK = 16640) by reflexivity.
destruct (cnl_ha HA j EHA Hj HGa) as (HAlo & HAhi & HA8 & HA16 & Dgn & Dgot & Dcell).
pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE & HH0 & _).
destruct (cnl_entry W ly S regs mem md ch HA j (hs_expected h) HPRE H10 EHA Hj HGa Hzs HE HnE) as [HS SHOK].
pose proof (ajournal_gx_init0R G XO [(AT, AT + 8)] CNL_STK
  (blk_FP (list_blks (hs_expected h) ++ list_blks (hs_held h))) ly S W regs mem md ch HPRE HXO HX16 HXtop HXp) as HJ.
remember (Eimg (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))))) as Ev eqn:HEv.
assert (HEI : img_env VAL A_LIM Ev) by (subst Ev; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew Ev m = getr regs rr).
{ intros m rr Hm. subst Ev. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (E1 : ew Ev 1 = getr regs 1) by exact (EEo 1%nat 1%bv eq_refl).
assert (E2 : ew Ev 2 = getr regs 2) by exact (EEo 2%nat 2%bv eq_refl).
assert (E34 : ew Ev 34 = Z_to_bv 64 (hl_n (hs_expected h)))
  by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h)))) Ev)
  by (rewrite HEv; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew Ev 32 = Z_to_bv 64 SB) by (subst Ev; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
clear HEv.
unfold cfg_at. change (w64 A_check_no_lossP) with (Z_to_bv 64 A_check_no_lossP).
unfold A_check_no_lossP, A_check_no_loss.
paj_run_tok_xR RUNg HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
psrr_branch_tok RUNg BRg HS SHOK Bspan.
- (* s->expected.n <= 0: nothing to check, straight to the return *)
  assert (Hn0 : hl_recs (hs_expected h) = []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_true_iff, Z.ltb_ge in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc.
    destruct (hl_recs (hs_expected h)) as [|r rs]; [reflexivity|]. cbn [length] in Hc. lia. }
  paj_run_tok_xR RUNg HS HJ SHOK Bspan. { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
  assert (MEQ : forall x, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 112 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  prreg HS (1%bv : bv 5) R1.
  (* the return moves no world: the strict return step lifts to R *)
  apply (SRr_SRrG SEGS R WLE_R).
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cnl_post_xR.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
    exists ly, S, [], r, m, d, 0, (hs_expected h), (hs_held h) end.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ|].
  split.
  { lazymatch type of HS with st_ok_pi _ _ ?Eq _ _ =>
    eapply (aregs_preserved_of_st_ok SEGS _ Eq _ _ regs (cnl_extra (hl_v (hs_expected h)) (hl_n (hs_expected h))) HS);
    [exact HAE | vm_compute; reflexivity] end. }
  split.
  { intros a Hi Hno Hne Hp. cbn [ms_mem]. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { cbn [ms_mem]. intros i Hi. apply aview_meq. apply MEQa. pose proof (cnl_errno_low i Hi) as (He1 & He2). lia. }
  split.
  { cbn [ms_mem]. rewrite set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 112) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact Hn0|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact HND|].
  split; [unfold texts; rewrite Hn0; reflexivity|].
  split; [unfold capb in *; lia|].
  split.
  { cbn [ms_mem]. replace (if gone =? 0 then A0 + Z.of_nat (length (bstream (hs_expected h))) else A0) with A0.
    - apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
      intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia.
    - unfold bstream. rewrite Hn0. cbn [map concat length Z.of_nat]. destruct (gone =? 0); lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
    intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
    pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
  split.
  { cbn [ms_mem]. intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
    apply MEQa. destruct HOBK as [-> | (CO & HCO & HCOin & _)]; [cbn [length] in Hi; lia|].
    destruct (cnl_blk ly S W mem md OUT CO HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
  split; [intros rest Hp; exact Hp|]. split; [reflexivity|].
  split; [unfold cnl_cost; rewrite Hn0; cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HRM0; rewrite Hn0 in HRM0; exact HRM0|].
  (* the held list's capacity: no record, H' = H *)
  split; [lia | rewrite Hn0; reflexivity].
- (* s->expected.n > 0: the rest of the prologue (0x85eac .. 0x85ec0) to the loop head 0x85ec4, then the loop *)
  assert (Hne : hl_recs (hs_expected h) <> []).
  { cbn [branch_taken] in Hc. rewrite bv_lts_signed in Hc. apply Bool.negb_false_iff, Z.ltb_lt in Hc.
    assert (Hz : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity. rewrite Hz in Hc.
    assert (Hs : bv_signed (sv_denot Ev (SOff 34 0)) = hl_n (hs_expected h)).
    { cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned.
      assert (Hu : bv_unsigned (Z_to_bv 64 (hl_n (hs_expected h))) = hl_n (hs_expected h))
        by (apply unsigned_lit_small; unfold hl_n in HnE |- *; lia).
      rewrite bv_signed_small by (rewrite Hu; unfold hl_n in HnE |- *; lia). exact Hu. }
    rewrite Hs in Hc. unfold hl_n in Hc. intros He. rewrite He in Hc. cbn [length Z.of_nat] in Hc. lia. }
  (* the blocks of the two lists are a part of the live blocks (asrc_at: NoDup (hs_blocks h)) *)
  assert (APERM0 : exists rest, Permutation (ablocks B ly S) (list_blks (hs_expected h) ++ list_blks (hs_held h) ++ rest)).
  { pose proof HSRC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HNDb).
    assert (LB : forall (l : hlist) LA, alist_at B ly S W mem LA l true -> incl (list_blks l) (ablocks B ly S)).
    { intros l LA HA2 b Hin. destruct HA2 as (_ & _ & _ & _ & Hcap & Hv & _ & _ & Hrec).
      unfold list_blks in Hin. apply in_app_or in Hin as [Hin | Hin].
      - destruct (hl_cap l =? 0) eqn:Ec; [destruct Hin|]. destruct Hin as [<- | []].
        destruct Hv as [(Hc0 & _) | (_ & Hvin & _)]; [apply Z.eqb_neq in Ec; lia | exact Hvin].
      - apply in_map_iff in Hin as (r & <- & Hr). rewrite Forall_forall in Hrec. exact (proj1 (Hrec r Hr)). }
    assert (ND : List.NoDup (list_blks (hs_expected h) ++ list_blks (hs_held h))).
    { apply (NoDup_map_inv fst). rewrite map_app, !cnl_list_blks_fst.
      unfold hs_blocks in HNDb. apply NoDup_ListNoDup in HNDb.
      apply cnl_nodup_app_r in HNDb. apply cnl_nodup_app_r in HNDb. exact HNDb. }
    destruct (perm_of_incl _ (ablocks B ly S) ND (incl_app (LB _ _ HE) (LB _ _ HH0))) as (rest & HP).
    exists rest. rewrite <- app_assoc in HP. exact HP. }
  paj_run_to_tok_xR RUNTOg HS HJ SHOK Bspan (AF_fr_check_no_loss + 0x88).
  { apply awr_ok_x_of; [awr_any; exact Usp | cnl_nowin Usp]. }
  rewrite !wvb_collapse in HJ.
  assert (MEQ : forall x, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) ->
    mrestrict (w_H W) (ms_mem ms0) x = mrestrict (w_H W) mem x).
  { intros x Hx. rewrite HFr0; [apply HFr|];
    (intros (r & Hin & Hr);
     lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change (In r l') in Hin end;
     cbn [In] in Hin;
     repeat (destruct Hin as [<- | Hin];
       [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp in Hr; unfold CNL_FRAME in Hr; lia|]);
     destruct Hin). }
  assert (MEQa : forall a, 4096 <= a < spZ regs - 112 ->
    mrestrict (w_H W) (ms_mem ms0) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
  by (intros a Ha; apply MEQ; rewrite unsigned_lit_small by lia; lia).
  (* the registers at the loop head *)
  assert (E3 : ew Ev 3 = getr regs 3) by exact (EEo 3%nat 3%bv eq_refl).
  assert (E4 : ew Ev 4 = getr regs 4) by exact (EEo 4%nat 4%bv eq_refl).
  assert (E10 : ew Ev 10 = Z_to_bv 64 HA) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
  assert (E11 : ew Ev 11 = Z_to_bv 64 AT) by (rewrite (EEo 11%nat 11%bv eq_refl); exact H11).
  assert (UHA : bv_unsigned (ew Ev 10) = HA) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (E384 : bv_unsigned (ew Ev 384) = VAL (A_HI 104)) by exact (HEI 384%nat ltac:(unfold A_TEXT, A_LIM; lia)).
  prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
  prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22.
  prreg HS (24%bv : bv 5) Q24. prreg HS (27%bv : bv 5) Q27.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict ?Hh ?ms1) =>
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (23%bv : bv 5) HS) as Q23;
    pose proof (st_ok_pi_restrict_reg Hh Ev ss ms1 (25%bv : bv 5) HS) as Q25;
    let e23 := eval vm_compute in (sr_get (ss_regs ss) (23%bv : bv 5)) in
    change (sr_get (ss_regs ss) (23%bv : bv 5)) with e23 in Q23;
    let e25 := eval vm_compute in (sr_get (ss_regs ss) (25%bv : bv 5)) in
    change (sr_get (ss_regs ss) (25%bv : bv 5)) with e25 in Q25 end.
  rewrite (U_shadow_reg Ev 10 32 72 HA E10 E32) in Q23 by lia.
  rewrite (U_shadow_reg Ev 10 32 64 HA E10 E32) in Q25 by lia.
  (* the frame cells: the prologue's 13 stores *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let r0 := eval vm_compute in (nth_error (ss_mem ss) 0%nat) in
    lazymatch r0 with Some ?r => pose proof (st_ok_pi_region_nth Ev ss _ 0%nat r HS eq_refl) as HR0 end end.
  cbn [ms_mem restrict] in HR0.
  assert (Hcp : cpos gone A0 [] = A0) by (unfold cpos, bsr; cbn [map concat length Z.of_nat]; destruct (gone =? 0); lia).
  assert (HCO : exists CO, ob = [] \/ (NO <= CO /\ In (OUT, CO) (ablocks B ly S) /\
    ~ In (OUT, CO) (list_blks (hs_expected h) ++ list_blks (hs_held h)))).
  { destruct HOBK as [-> | (CO & H1 & H2 & H3)]; [exists 0; left; reflexivity|].
    exists CO. right. split; [exact H1|]. split; [exact H2|].
    intros Hin. apply H3. apply (in_map fst) in Hin. cbn [fst] in Hin. rewrite map_app, !cnl_list_blks_fst in Hin.
    unfold hs_blocks. apply in_or_app. right. apply in_or_app. right. exact Hin. }
  destruct HCO as (CO & HCO).
  pmkst HS.
  assert (Epc : 15232 = A_cnl_loop) by reflexivity. rewrite Epc.
  eapply (cnl_enter_xR regs ly S W mem md ch HA j h gone A0 NO OUT CO ob kr).
  all: try eassumption.
  unfold cnl_inv_xR.
  exists ly, S, 0, (hs_held h), (hl_junk (hs_expected h)).
  split; [reflexivity|].
  split; [exact HJ|].
  split.
  { intros a Hi Hno Hne' Hp. pose proof (pa_img_range a Hi) as Hr.
    destruct Hp as [Hh [b Hb]]. split; [exact Hh|]. exists b. unfold mrestrict in MEQa.
    pose proof (MEQa a ltac:(lia)) as Hq. rewrite Hh in Hq. rewrite Hq. exact Hb. }
  split.
  { unfold cnl_E. rewrite cnl_E_id, set_exp_held_id.
    apply (cnl_src_kept ly S W mem md (ms_mem ms0) HA h (spZ regs - 112) HAR HSRC HAlo HAhi ltac:(lia)).
    intros a Ha. apply MEQa. lia. }
  split; [exact HND|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [unfold txs, count_begin; cbn [map filter length Z.of_nat]; lia|].
  split; [unfold capb; lia|].
  split; [intros rest Hp; unfold cnl_E; rewrite cnl_E_id; exact Hp|].
  split; [reflexivity|].
  split; [cbn [cnl_go]; apply (mo_le_refl MT ML)|].
  split; [unfold cnl_cost in HMOK; exact HMOK|].
  split; [exact HROOM|].
  split; [exact HRM0|].
  split; [exact (cnl_cnt_entry RP (hs_expected h) (hs_held h) _ HCNT0)|].
  split.
  { rewrite Hcp. apply (val_mem_meq W mem (ms_mem ms0) AT 8 A0); [|exact MAT].
    intros x Hx. apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { unfold cnl_consts.
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 1 gone); [|exact Mg].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_gone) 1 x ltac:(cbv [cnl_ro]; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 NO); [|exact Mno].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_nout) 8 x ltac:(cbv [cnl_ro]; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (val_mem_meq W mem (ms_mem ms0) _ 8 OUT); [|exact Mout].
      intros x Hx. cbn [Z.of_nat] in Hx. apply MEQa.
      pose proof (cnl_ro_keep (VAL A_g_out) 8 x ltac:(cbv [cnl_ro]; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { intros i Hi. rewrite (aview_meq W mem (ms_mem ms0) (OUT + i)); [exact (HOB i Hi)|].
      apply MEQa. destruct HOBK as [-> | (CO' & HCO' & HCOin & _)]; [cbn [length] in Hi; lia|].
      destruct (cnl_blk ly S W mem md OUT CO' HAR HCOin) as (_ & H4096 & _ & Hn1 & _ & Hc2 & _). lia. }
    split.
    { intros a Hin. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (Hrom a Hin)|].
      apply MEQa. destruct Hin as (sg & Hsg & _ & Hsr).
      pose proof (pa_img_range a ltac:(exists sg; split; [exact Hsg | exact Hsr])) as HI. lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.K_GESTURE); [|exact Hlg].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.K_GESTURE) <= 13) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_gesture) 13 x
        ltac:(cbv [cnl_ro]; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    split.
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_BEGIN); [|exact Hlb].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_BEGIN) <= 5) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_begin) 5 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. }
    { apply (garr8_meq W mem (ms_mem ms0) _ RelayModel.W_END); [|exact Hle].
      intros x Hx. apply MEQa.
      assert (Lg : Z.of_nat (length RelayModel.W_END) <= 3) by (vm_compute; discriminate).
      pose proof (cnl_ro_keep (VAL A_lit_end) 3 x
        ltac:(cbv [cnl_ro]; right; right; right; right; right; right; left; reflexivity) ltac:(lia)). lia. } }
  split; [exact HCO|].
  split.
  { intros Hg0. rewrite Hcp. destruct (HSKP Hg0) as (rest & Hr). exists rest. unfold bsr. unfold bstream in Hr. exact Hr. }
  split.
  { intros i Hi. apply aview_meq. apply MEQa. pose proof (cnl_errno_low i Hi) as (He1 & He2). lia. }
  split.
  { intros a Ha. rewrite (aview_meq W mem (ms_mem ms0) a); [exact (HSTK a Ha)|].
    apply MEQ. rewrite unsigned_lit_small by lia. lia. }
  split.
  { apply (cnl_frame_of_region Ev W (ms_mem ms0) regs _ _ _ _ _ HR0 Usp EEo).
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd In]; repeat (first [left; reflexivity | right]). }
  unfold cnl_regs_ok.
  split; [rewrite Q2, Usp; unfold w64; f_equal; lia|].
  split; [rewrite Q3, E3; exact Hgp|].
  split; [rewrite Q4, E4; exact Htp|].
  split; [rewrite Q8, E11; reflexivity|].
  split; [rewrite Q9, E10; reflexivity|].
  split; [rewrite Q18, UHA; reflexivity|].
  split; [rewrite Q19, UHA; reflexivity|].
  split; [rewrite Q22, E32; reflexivity|].
  split; [exact Q23|].
  split; [rewrite Q24; unfold w64; rewrite <- E384, Z_to_bv_bv_unsigned; reflexivity|].
  split; [exact Q25|].
  rewrite Q27. exact (EEo 27%nat 27%bv eq_refl).
Qed.
End wR.
End d.
(* image B's check_no_loss against the kit's generic contract (lib/B/W_contract_x.v Section w3n): HP0 on the pre's
   ARx makes the entry's ghost list [], and the walk above runs there *)
Theorem pb_check_no_loss_x : cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Proof.
intros W ly S Hp regs mem md ch XO1 HA j AT1 h gone A0 NO OUT ob HPRE.
hp0a (proj1 HPRE).
exact (pb_check_no_loss_at XO1 AT1 W ly S regs mem md ch HA j h gone A0 NO OUT ob HPRE).
Qed.
(* ---- route R: the arm lemma, cnl_spec_xR (W_contract_xR_g6.v) at a world relation R.  Beyond R and its laws it takes
   the R contracts GM_R (gesture_model, which calls realloc and free) and LDROP_R (list_drop, which calls free);
   next_line and bcmp stay at their strict contracts (NL, ABCMP).  The re-hiding instance is R := wle' SEGS RZ_cf.  The
   strict pb_check_no_loss_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis LDROP_R : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_xR B PST ARx R MT RP G0 (BASE + AF_fr_list_drop).
Theorem pb_check_no_loss_xR : cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Proof.
intros W ly S Hp regs mem md ch XO1 HA j AT1 h gone A0 NO OUT ob HPRE.
hp0a (proj1 HPRE).
intros.
eapply (pb_check_no_loss_at_xR XO1 AT1); eassumption.
Qed.
End wR.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.; A's Section cAR, lib/A/W_check_no_loss.v on
   a working branch e3e586a3b09): pb_check_no_loss's statement is the AR walk's, byte-identical, now a
   corollary of pb_check_no_loss_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].  Its Section
   keeps LAWS : AR_laws (a Theorem Labs lane's ruling 03:30Z: the plain names keep their B-old statements, Section hypotheses
   included); the proof derives LX0 (the laws at ARi0) from LAWS by lib/B/YLX0.v lx_AR_laws_x_ARi0_of, as
   lib/B/W_list_drop.v does.  The bridges are the kit's: W_contract_x cnl_spec_x_AR0 for the conclusion; nl_spec_x_of_AR0,
   gm_spec_g_x_of_AR0, ldrop_spec_x_of_AR0 (W_contract_x) and abcmp_realizes_x_of_AR0 (W_sites_x) for the callees;
   HP0 at ARi0 is W_journal_x.ARi0_hp0; IMGC / BLKN are W_kit_x.AR_imgc / AR_blkn; HPST holds at PST = []. ---- *)
Section cAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Variable MMAX : Z.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
(* No gx_rt of the caller's G: G_fr / G_SL hold errno, so it could never be discharged (W5, 2026-10-29). *)
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
(* An image read-only byte is not errno, and, if the runtime owns it, it is pinned to its image value (rom_pinned,
   W_journal.v; owned .rodata ranges lie inside image A's read-only LOAD, so `~ owned` was false). *)
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis NL : nl_spec B (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g B MT MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
(* B only: list_drop is a call (0x85fa4 jal list_drop 0x85b50), taken at the callee's own G (s->expected's head), in
   the form of W1's pb_list_drop_ro (lib/A/W_list_drop_top.v) and lib/A/W_gesture_model_g.v's LDROP_RO; B's
   list_drop walk (a Theorem Labs lane) discharges it. *)
Hypothesis LDROP : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec B MT G0 (BASE + AF_fr_list_drop).
(* B only: the two callees above take rom_out at their G, a part of g_s (W_journal.v rom_out: no ROM byte in G, the
   owned ROM bytes pinned, no ROM byte errno or the sink's overflow head); the instance, a vm_compute at PB_fr. *)
Hypothesis HRO : rom_out SEGS B [(VAL A_g_s, 384)].
Theorem pb_check_no_loss : cnl_spec B MT G MMAX (BASE + AF_fr_check_no_loss).
Proof.
pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
apply cnl_spec_x_AR0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
assert (IMGC : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly))
  by (intros ly S Hp W mem md H; destruct H as [HAR _]; exact (AR_imgc B ly S Hp W mem md HAR)).
assert (BLKN : forall ly S Hp W mem md p n, ARi0 SEGS B ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n)
  by (intros ly S Hp W mem md p n H Hin; destruct H as [HAR _]; exact (AR_blkn B ly S Hp W mem md p n HAR Hin)).
assert (HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) ([] : list (Z * Z))) by (intros a _ H; inversion H).
assert (NLx : nl_spec_x B [] (ARi0 SEGS B) (BASE + AF_fr_next_line)) by (apply nl_spec_x_of_AR0; exact NL).
assert (GMx : gm_spec_g_x B [] (ARi0 SEGS B) MT RP_AR MMAX (BASE + AF_fr_gesture_model)) by (apply gm_spec_g_x_of_AR0; exact GM).
assert (ABCx : abcmp_realizes_x SEGS B (ARi0 SEGS B) (SIGMA WS_bcmp)) by (apply abcmp_realizes_x_of_AR0; exact ABCMP).
assert (LDROPx : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_x B [] (ARi0 SEGS B) MT RP_AR G0 (BASE + AF_fr_list_drop))
  by (intros G0 H1 H2 H3; apply ldrop_spec_x_of_AR0; exact (LDROP G0 H1 H2 H3)).
eapply (pb_check_no_loss_x B [] (ARi0 SEGS B) MT RP_AR G MMAX); eassumption.
Qed.
End cAR.
(* ---- CNL_rm_x (the B top's row 34, lib/B/W_LLVMFuzzerTestOneInput_top_x.v:483 on a working branch
   e43cf0c7bef): cnl_spec_x at every gx_ok G, with no gx_rt / rom_out premise at G.  Section c's hypotheses name G only
   in HG : gx_ok SEGS B G (the walk reads neither gx_rt nor rom_out at the caller's G: the callees' G are parts of g_s,
   whose rom_out is HRO), so the statement is pb_check_no_loss_x with G quantified. ---- *)
Section rm.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
  fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis HPST : forall a, in_img SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis TL : PALib B.
Hypothesis CNLAP : cnl_objs_apart.
Hypothesis ML : ameter_laws MT.
Hypothesis HGR : gx_ok SEGS B cnl_ro.
Hypothesis HGRR : gx_rt B cnl_ro.
Hypothesis ROMNS : forall a, in_rom SEGS a -> ~ (as_errno B <= a < as_errno B + 4) /\
  (Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a).
Hypothesis NL : nl_spec_x B PST ARx (BASE + AF_fr_next_line).
Hypothesis GM : gm_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LDROP : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_x B PST ARx MT RP G0 (BASE + AF_fr_list_drop).
Hypothesis HRO : rom_out SEGS B [(VAL A_g_s, 384)].
Corollary pb_check_no_loss_rm_x : forall G, gx_ok SEGS B G -> cnl_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_check_no_loss).
Proof. intros G HG. eapply (pb_check_no_loss_x B PST ARx MT RP G MMAX); eassumption. Qed.
(* ---- route R: CNL_rm_x at a world relation R, pb_check_no_loss_xR with G quantified ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis GM_R : gm_spec_g_xR B PST ARx R MT RP MMAX (BASE + AF_fr_gesture_model).
Hypothesis LDROP_R : forall G0, gx_ok SEGS B G0 -> gx_rt B G0 -> rom_out SEGS B G0 ->
  ldrop_spec_xR B PST ARx R MT RP G0 (BASE + AF_fr_list_drop).
Corollary pb_check_no_loss_rm_xR : forall G, gx_ok SEGS B G ->
  cnl_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_check_no_loss).
Proof. intros G HG. eapply (pb_check_no_loss_xR B PST ARx MT RP G MMAX); eassumption. Qed.
End wR.
End rm.
End b.
End a.
(* the image objects the walk reads are apart, and g_s holds no read-only byte, at the pinned placement PB_fr
   (lib/B/W_img.v): the image's read-only bytes are [0x10000, 0x9d000) (segments 000 r-- and 001 r-x) *)
Section fr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cnl_rom_range_fr : forall a, in_rom (@pa_segs _ fr_prog_listing PB_fr) a -> 0x10000 <= a < 0x9d000.
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) frsegs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) frsegs sg Hin). }
rewrite Hw in H. remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez.
clear Eb Ez Hin Hw. vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; inversion H; subst; lia.
Qed.
Lemma cnl_objs_apart_fr : cnl_objs_apart (PI := PB_fr).
Proof.
unfold cnl_objs_apart, A_g_s, A_g_gone, A_g_nout, A_g_out, A_lit_gesture, A_lit_begin, A_lit_end. cbv zeta.
assert (E0 : pa_val (PAImg := PB_fr) (A_OBJ 0) = 0x9df50) by (vm_compute; reflexivity).
assert (E30 : pa_val (PAImg := PB_fr) (A_OBJ 30) = 0xa6638) by (vm_compute; reflexivity).
assert (E27 : pa_val (PAImg := PB_fr) (A_OBJ 27) = 0x5d8de0) by (vm_compute; reflexivity).
assert (E19 : pa_val (PAImg := PB_fr) (A_OBJ 19) = 0x5d8e60) by (vm_compute; reflexivity).
assert (E12 : pa_val (PAImg := PB_fr) (A_OBJ 12) = 0x5d8e40) by (vm_compute; reflexivity).
assert (E29 : pa_val (PAImg := PB_fr) (A_OBJ 29) = 0x5d90c0) by (vm_compute; reflexivity).
assert (E18 : pa_val (PAImg := PB_fr) (A_OBJ 18) = 0x20f20) by (vm_compute; reflexivity).
assert (E20 : pa_val (PAImg := PB_fr) (A_OBJ 20) = 0x20f40) by (vm_compute; reflexivity).
assert (E21 : pa_val (PAImg := PB_fr) (A_OBJ 21) = 0x20f60) by (vm_compute; reflexivity).
rewrite E0, E30, E27, E19, E12, E29, E18, E20, E21.
split; [reflexivity|].
repeat match goal with |- _ /\ _ => split; [lia|] end.
intros a Ha Hr. apply cnl_rom_range_fr in Hr. lia.
Qed.
End fr.
