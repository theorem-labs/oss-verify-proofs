(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgKcLib.v at 723a83a0833b; the same library for
   image B's key piece: image B's cuts (lib/AU/HPgSegM.v, prefix hqu_), B's write ranges (res and x at F + 0x2a0 .. F + 0x348,
   their shadow granules 0x54 .. 0x69, the real-frame cells [R, R+0x160)), B's frame shadow length 116, B's register
   list of hku_L, B's strings, and B's read-only segments (lib/AU/Img0U.v); strncmp against the prefix is not
   restated (lib/Prog/HeadCheck/PairFacts.v strncmp_prefix). *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the facts the four parts of the piece "the key and the channel" (lib/AU/HPgKcuCut.v)
   share. Proves no function (kind: segment lemma).
   - hku_base3_kept: a cut's hqu_base3 survives a run that changes only the callees' stack window
     [R - T_SEG_STK, R), the real-frame cells [R, R+0x120) and x->keys (x+0x80 .. x+0x84, x = F + 0x2c0), keeps
     sp / gp / tp, the allocator state and the I/O state; hku_inv_regs is the register-only case for hku_inv.
   - hku_cstr_now: the image's strings (HPgImgB.hi_strs: the harness's "reac.headamp." 0x20f40 and its three param
     names 0x21380 / 0x213a0 / 0x213c0 among them) as the string wrappers' contracts read them, at any cut of M03.
   - hku_arodata_now: the read-only segments' bytes in the form of the wrapper contracts' read-only premise, with the
     empty extra range (0, 0): what a string wrapper's contract reads of it is the in-segment half.
   - hku_keymem: the key of entry m (Accessors.key_of) in the pp block at a cut: its bytes and its NUL, its length,
     the tail of the NUL's word, the block it lies in and the shadow bytes of the entry's 112-byte granule span.
   - the model: the pairs from at0, one step of the fold, x->keys++ on x's bytes.
   How the memory facts are carried: a cut's hsu_core says every byte outside the callees' stack window and outside
   M03's write set hqu_E3 (res, x, their shadow granules, [R, R+0x160), out, errno) reads as at M03's start; the
   read-only segments read as the image's at both states (rom_view); the frame for locals, the live blocks and the
   image are apart from each other and from the stack (YG0d's AR laws, through HPgSiteA.hd_cctx_facts, whose
   statement names no image but the frame class 4, image B's class too).
   Section hypothesis: errno_low (lib/Reusable/YCbq.v api_env: errno lies in the image), as lib/A/HPgCalls.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors Spa.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCalls HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgImgA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSteps HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgKcuCut.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ======================================== the model ======================================== *)
(* the tail of a list from an index inside it *)
Lemma hku_skipn_nth : forall {A : Type} (l : list A) (i : nat) (d : A),
(i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof.
intros A l. induction l as [|x l IH]; intros [|i] d H; cbn [length] in H; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.

(* the pairs pod_next_pair finds from at0, when entry m is the first key from at0 and m + 1 exists *)
Lemma hku_pairs_at : forall (es : list Model.ent) (at0 m : nat) k,
(at0 <= m)%nat -> (S m < length es)%nat ->
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q es (Model.Ent 0 0 [])) = None) ->
Accessors.key_of (nth m es (Model.Ent 0 0 [])) = Some k ->
Accessors.pairs_by Accessors.key_of (skipn at0 es) None =
(k, nth (S m) es (Model.Ent 0 0 [])) :: Accessors.pairs_by Accessors.key_of (skipn (S (S m)) es) None.
Proof.
intros es at0 m k Hle Hlt Hnone Hk.
remember (m - at0)%nat as t eqn:Ht. revert at0 Hle Hnone Ht.
induction t as [|t IH]; intros at0 Hle Hnone Ht.
- assert (E : at0 = m) by lia. subst at0.
  rewrite (hku_skipn_nth es m (Model.Ent 0 0 [])) by lia. cbn [Accessors.pairs_by]. rewrite Hk.
  rewrite (hku_skipn_nth es (S m) (Model.Ent 0 0 [])) by lia. cbn [Accessors.pairs_by]. reflexivity.
- rewrite (hku_skipn_nth es at0 (Model.Ent 0 0 [])) by lia. cbn [Accessors.pairs_by].
  rewrite (Hnone at0) by lia.
  apply (IH (S at0)); [lia | intros q Hq; apply Hnone; lia | lia].
Qed.

(* x->keys++ on x's bytes: the 4 bytes at 0x80 are keys *)
Lemma hku_x_open_keys : forall cs keys rf, (length cs <= X_CELLS)%nat -> 0 <= keys < 2 ^ 31 - 1 ->
Model.overwrite (hqu_x_open cs keys rf) 128 (Z_to_le_bytes 4 (keys + 1)) = hqu_x_open cs (keys + 1) rf.
Proof.
intros cs keys rf Hc Hk.
set (A := repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs ++ repeat (Z_to_bv 8 0) (12 * (X_CELLS - length cs)) ++
  Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs)))).
assert (EA : forall kk, hqu_x_open cs kk rf = A ++ Mem.le4 (Z_to_bv 64 kk) ++ Mem.le4 (Z_to_bv 64 rf)).
{ intros kk. unfold hqu_x_open, ha_res_bytes, A. rewrite <- !app_assoc. reflexivity. }
assert (LA : length A = 128%nat).
{ unfold A. rewrite !length_app, !repeat_length, length_x_cells_bytes, Mem.length_le4.
  unfold X_CELLS in *. lia. }
rewrite (EA keys), (EA (keys + 1)). rewrite <- LA.
rewrite Layout.overwrite_mid by (rewrite Mem.length_le4, length_Z_to_le_bytes; reflexivity).
f_equal. f_equal. unfold Mem.le4. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ======================================== the key's text ======================================== *)
Lemma hku_nul_idx_le : forall (l : list byte) j, (j < length l)%nat -> bv_unsigned (nth j l Cursor.NUL) = 0 ->
(Cursor.nul_idx l <= j)%nat.
Proof.
induction l as [|x l IH]; intros j Hj Hz; cbn [length] in Hj; [lia|].
cbn [Cursor.nul_idx]. destruct (Z.eqb_spec (bv_unsigned x) 0) as [E|E]; [lia|].
destruct j as [|j]; [cbn [nth] in Hz; exfalso; exact (E Hz)|].
cbn [nth] in Hz. specialize (IH j ltac:(lia) Hz). lia.
Qed.

Lemma hku_cstr_nonzero : forall (l : list byte) x, In x (firstn (Cursor.nul_idx l) l) -> bv_unsigned x <> 0.
Proof.
induction l as [|y l IH]; intros x H; [destruct H|].
cbn [Cursor.nul_idx] in H. destruct (Z.eqb_spec (bv_unsigned y) 0) as [E|E]; cbn [firstn In] in H; [destruct H|].
destruct H as [<-|H]; [exact E | exact (IH x H)].
Qed.

Lemma hku_cstr_nth : forall (l : list byte) i, (i <= Cursor.nul_idx l)%nat -> (Cursor.nul_idx l < length l)%nat ->
bv_unsigned (nth i (firstn (Cursor.nul_idx l) l ++ [Cursor.NUL]) Cursor.NUL) = bv_unsigned (nth i l Cursor.NUL).
Proof.
induction l as [|y l IH]; intros i Hi Hl; cbn [length] in Hl; [lia|].
cbn [Cursor.nul_idx] in *. destruct (Z.eqb_spec (bv_unsigned y) 0) as [E|E].
- assert (i = 0%nat) as -> by lia. cbn [firstn app nth]. rewrite E. reflexivity.
- destruct i as [|i]; [reflexivity|]. cbn [firstn app nth]. apply IH; lia.
Qed.

(* a key: at most 44 bytes, no NUL, shorter than the body, and its bytes and NUL are the body's *)
Lemma hku_key_facts : forall e k, Model.ent_wf e -> Accessors.key_of e = Some k ->
(length k <= 44)%nat /\ ~ In Cursor.NUL k /\ (length k < length (Model.e_body e))%nat /\
(forall i, (i <= length k)%nat ->
 bv_unsigned (nth i (k ++ [Cursor.NUL]) Cursor.NUL) = bv_unsigned (nth i (Model.e_body e) Cursor.NUL)).
Proof.
intros e k (_ & Hbl & Hsz) Hk. unfold Accessors.key_of in Hk.
match type of Hk with context [if ?c then _ else _] => destruct c eqn:E; [|discriminate Hk] end.
injection Hk as <-. apply andb_prop in E as [E E3]. apply andb_prop in E as [_ E2].
apply Z.leb_le in E2. apply Z.eqb_eq in E3. unfold Accessors.last_body_byte in E3.
assert (Hj : (Z.to_nat (Model.e_size e - 1) < length (Model.e_body e))%nat) by lia.
pose proof (hku_nul_idx_le (Model.e_body e) _ Hj E3) as Hn.
unfold Cursor.cstr. rewrite length_firstn.
assert (HL : Nat.min (Cursor.nul_idx (Model.e_body e)) (length (Model.e_body e)) = Cursor.nul_idx (Model.e_body e))
  by lia.
rewrite HL.
split; [lia|]. split; [|split; [lia|]].
- intros H. apply (hku_cstr_nonzero _ _ H). reflexivity.
- intros i Hi. apply hku_cstr_nth; lia.
Qed.

(* the fold at a key: KEY's fold equation, with the pair (k, ent[m + 1]) skipped (no prefix) or in front *)
Lemma hku_fold_skip : forall cx r (at0 m : nat) k cs keys rf,
(at0 <= m)%nat -> (S m < length (Model.ents r))%nat ->
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k ->
hqu_fold_inv rsegs cx r at0 cs keys rf -> ha_prefix k = false ->
hqu_fold_inv rsegs cx r (S (S m)) cs keys rf.
Proof.
intros cx r at0 m k cs keys rf H1 H2 H3 H4 Hf Hp. unfold hqu_fold_inv in *.
rewrite (hku_pairs_at (Model.ents r) at0 m k H1 H2 H3 H4) in Hf. cbn [ha_fold] in Hf.
rewrite Hp in Hf. cbn [negb] in Hf. exact Hf.
Qed.

Lemma hku_pair_of_fold : forall cx r (at0 m : nat) k cs keys rf,
(at0 <= m)%nat -> (S m < length (Model.ents r))%nat ->
(forall q, (at0 <= q < m)%nat -> Accessors.key_of (nth q (Model.ents r) (Model.Ent 0 0 [])) = None) ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k ->
hqu_fold_inv rsegs cx r at0 cs keys rf -> ha_prefix k = true ->
hqu_pair_inv rsegs cx r m k (nth (S m) (Model.ents r) (Model.Ent 0 0 [])) cs keys rf.
Proof.
intros cx r at0 m k cs keys rf H1 H2 H3 H4 Hf Hp. unfold hqu_fold_inv, hqu_pair_inv in *.
rewrite (hku_pairs_at (Model.ents r) at0 m k H1 H2 H3 H4) in Hf.
split; [reflexivity|]. split; [exact Hp|]. split; [exact H2 | exact Hf].
Qed.

(* image B's third write range list, by its three ranges *)
Lemma hku_inw_w3 : forall e a, hd_inw e (hi_w3 headamp_himg_B) a ->
(e_F e + 0x2a0 <= a < e_F e + 0x348) \/ (shadow_addr (e_F e) + 0x54 <= a < shadow_addr (e_F e) + 0x69) \/
(e_R e <= a < e_R e + 0x160).
Proof.
intros e a H. unfold hd_inw in H. cbn [hi_w3 headamp_himg_B] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [fst snd hd_xv] in H. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis errno_low : api_env rsegs B.

(* ======================================== memory at a cut ======================================== *)
(* the cells M3c writes besides the callees' stack: the real-frame cells (R+0x90, R+0xd8 .. R+0x118) and
   x->keys *)
Definition hku_wr (cx : hsu_scx rsegs) (a : Z) : Prop :=
(e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x120) \/
(e_F (x_e rsegs cx) + HQU_XO + 0x80 <= a < e_F (x_e rsegs cx) + HQU_XO + 0x84).

(* M3c's own cells lie in M03's write set *)
Lemma hku_wr_E3 : forall cx a, hku_wr cx a -> hqu_E3 rsegs B cx a.
Proof.
intros cx a [H|H]; left; unfold hd_inw; cbn [hi_w3 headamp_himg_B].
- apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd. cbn [fst snd hd_xv]. lia.
- apply Exists_cons_hd. cbn [fst snd hd_xv]. unfold HQU_XO in H. lia.
Qed.

(* the one accessor of hqu_start_M03's conjuncts *)
Lemma hku_start : forall cx r ev, hqu_start_M03 rsegs B cx r ev ->
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) /\ Model.pod_rec_wf r /\
e_len (x_e rsegs cx) = Z.of_nat (length (Model.buf r)) /\
hd_fresh_block (ablocks B (x_ly rsegs cx) (x_S rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx))
  (e_pod (x_e rsegs cx)) (e_len (x_e rsegs cx)) /\
hd_fresh_block (ablocks B (x_ly rsegs cx) (x_S rsegs cx)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx))
  (e_out (x_e rsegs cx)) (3 * (e_cap (x_e rsegs cx) + 1)).
Proof.
intros cx r ev HS. destruct HS as (H1 & _ & H3 & H4 & _ & _ & H7 & _ & _ & _ & _ & H12 & _).
split; [exact H1|]. split; [exact H3|]. split; [exact H4|]. split; [exact H7 | exact H12].
Qed.

(* what a cut of M03 has: HPgSiteA's call context at the cut's state, sp at the segment's start = R, and the
   pp and pod blocks and the frame for locals live at the cut *)
Lemma hku_ctx : forall cx r ev E ly2 S2 W2 regs2 mem2 md2,
hqu_start_M03 rsegs B cx r ev -> hsu_core rsegs B MT cx E ly2 S2 W2 regs2 mem2 md2 ->
hd_cctx rsegs B ly2 S2 W2 mem2 md2 (x_e rsegs cx) (x_pos rsegs cx) /\
spZ (x_regs rsegs cx) = e_R (x_e rsegs cx) /\
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\
In (e_pod (x_e rsegs cx), e_len (x_e rsegs cx)) (ablocks B ly2 S2) /\
In (4, x_pos rsegs cx) (frames S2).
Proof.
intros cx r ev E ly2 S2 W2 regs2 mem2 md2 HS HC.
destruct (hku_start cx r ev HS) as (HP & _ & _ & Hfpod & Hfout).
unfold hsu_pre, hd_seg_pre in HP.
destruct HP as (HJ & _ & H2 & _ & _ & HSe & _ & Hrsz & Hwin & Hown & HF & _ & Hcap & _ & _ & _ & _ & _ & _ & _ & _
  & Hfpp).
unfold hsu_core, hsu_mid in HC. destruct HC as (HJ2 & _ & Hfr & Hperm & _).
pose proof HJ as (_ & _ & _ & _ & _ & Hfrc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
pose proof HJ2 as (HAR2 & _).
cbn [hi_rsz headamp_himg_B] in Hrsz.
assert (Ht : T_SEG_STK = 16384) by reflexivity.
pose proof YCbq.asan_consts as (HCv & _).
assert (Hfin : In (4, x_pos rsegs cx) (frames S2)).
{ rewrite Hfr, Hfrc. apply in_or_app. left. exact Hown. }
split.
- split; [exact HAR2|].
  split; [exact (Permutation_in _ (Permutation_sym Hperm) (proj1 (proj2 Hfout)))|].
  split; [exact Hfin|].
  split; [rewrite HF; change (hi_cid HPgImgA.headamp_himg_A) with 4; change (hi_cid headamp_himg_B) with 4; symmetry;
    eapply headamp_A_site_frame_at; [exact HJ | exact HJ2]|].
  split; [clear - Hc1 Hc2 Hwin; lia | exact Hcap].
- split; [unfold spZ; rewrite H2; apply hc_u64; clear - Hc1 Hc2 Hc3 Hc4 Hwin Hrsz HSe Ht HCv; lia|].
  split; [exact (Permutation_in _ (Permutation_sym Hperm) (proj1 (proj2 Hfpp)))|].
  split; [exact (Permutation_in _ (Permutation_sym Hperm) (proj1 (proj2 Hfpod))) | exact Hfin].
Qed.

(* a byte outside the callees' stack window and outside hqu_E3 reads at a cut as at M03's start *)
Lemma hku_kept2 : forall cx r ev ly2 S2 W2 regs2 mem2 md2 a,
hqu_start_M03 rsegs B cx r ev -> hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly2 S2 W2 regs2 mem2 md2 ->
0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
~ (e_F (x_e rsegs cx) + 0x2a0 <= a < e_F (x_e rsegs cx) + 0x348) ->
~ (shadow_addr (e_F (x_e rsegs cx)) + 0x54 <= a < shadow_addr (e_F (x_e rsegs cx)) + 0x69) ->
~ (e_R (x_e rsegs cx) <= a < e_R (x_e rsegs cx) + 0x160) ->
~ (e_out (x_e rsegs cx) <= a < e_out (x_e rsegs cx) + 3 * (e_cap (x_e rsegs cx) + 1)) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview rsegs (w_H W2) mem2 a = aview rsegs (w_H (x_W rsegs cx)) (x_memc rsegs cx) a.
Proof.
intros cx r ev ly2 S2 W2 regs2 mem2 md2 a HS HC Ha H1 H2 H3 H4 H5 H6.
destruct (hku_ctx cx r ev _ ly2 S2 W2 regs2 mem2 md2 HS HC) as (_ & Hsp & _).
unfold hsu_core, hsu_mid in HC. destruct HC as (_ & _ & _ & _ & _ & _ & Hmem).
apply Hmem; [exact Ha | rewrite Hsp; exact H1 |].
unfold hqu_E3. intros [Hw|[Ho|He]]; [|exact (H5 Ho) | exact (H6 He)].
apply hku_inw_w3 in Hw. destruct Hw as [Hw|[Hw|Hw]]; [exact (H2 Hw) | exact (H3 Hw) | exact (H4 Hw)].
Qed.

Lemma hku_apresent_some : forall H mem a, apresent H mem a -> aview rsegs H mem a <> None.
Proof. intros H mem a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

Lemma hku_rom_img : forall a, in_rom rsegs a -> in_img rsegs a.
Proof. intros a (sg & Hsg & _ & Hr). exists sg. split; [exact Hsg | exact Hr]. Qed.

Lemma hku_base3_kept : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
length sh = 116%nat ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem3 md3 (x_k rsegs cx) ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
same_io md2 md3 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) -> ~ hku_wr cx a ->
 aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs3 mem3 md3.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HS HB Hlen HJ3 Hr3 Hio3 Hk.
destruct HB as (HC & Hfx & Hfsh & Hrom & Hpp & Hpod & Hout & Hres & Herr).
destruct (hku_ctx cx r ev _ ly2 S2 W2 regs2 mem2 md2 HS HC) as (Hcc & Hsp & Hinpp & Hinpod & Hfin).
pose proof (hd_cctx_facts rsegs B ly2 S2 W2 mem2 md2 _ _ Hcc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
destruct (hku_start cx r ev HS) as (_ & Hwf & Hlbuf & _ & _).
pose proof Hcc as (HAR2 & Hinout & _ & HF2 & _). change (hi_cid HPgImgA.headamp_himg_A) with 4 in HF2.
assert (Ht : T_SEG_STK = 16384) by reflexivity.
pose proof alloc_ceiling_lt as Hlt.
(* a byte below the ceiling and outside the frame for locals *)
assert (Klow : forall a, 0 <= a < alloc_ceiling -> ~ (e_F (x_e rsegs cx) <= a < e_F (x_e rsegs cx) + 1024) ->
  aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hf. apply Hk.
  - clear - Ha Hlt. lia.
  - clear - Ha HRc. lia.
  - unfold hku_wr, HQU_XO. clear - Ha Hf HRc Ht. lia. }
(* a byte of a block live at the cut *)
assert (Kblk : forall p n j, In (p, n) (ablocks B ly2 S2) -> 0 <= j < req_size n ->
  aview rsegs (w_H W2) mem3 (p + j) = aview rsegs (w_H W2) mem2 (p + j)).
{ intros p n j Hin Hj.
  destruct (al_blocks _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hin) as (_ & P4 & Pce & _).
  pose proof (YCbq.sep_block_frame rsegs B (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hin Hfin)
    as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF2 in Hz.
  change (fs_frame_bytes 4) with 1024 in Hz.
  apply Klow; clear - Hj P4 Pce Hz; lia. }
assert (Hrq : forall n, 0 <= n -> n <= req_size n).
{ intros n Hn. unfold req_size. destruct (Z.eqb_spec n 0); lia. }
refine (conj _ (conj Hfx (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
- (* hsu_core *)
  unfold hsu_core, hsu_mid in *. destruct HC as (HJ2 & Hr2 & Hfr & Hperm & Hio & Hmo & Hmem).
  refine (conj HJ3 (conj _ (conj Hfr (conj Hperm (conj _ (conj Hmo _)))))).
  + intros q Hq. rewrite (Hr3 q Hq). exact (Hr2 q Hq).
  + revert Hio Hio3. unfold same_io. intros (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
    rewrite B1, B2, B3, B4. repeat split; assumption.
  + intros a Ha Hw HE. rewrite (Hk a Ha); [exact (Hmem a Ha Hw HE) | rewrite <- Hsp; exact Hw |].
    intros Hwr. apply HE. exact (hku_wr_E3 cx a Hwr).
- (* the frame's shadow bytes *)
  unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh). intros i Hi. rewrite Hlen in Hi.
  pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as DF.
  apply Hk; try unfold hku_wr, HQU_XO; unfold shadow_addr, SHADOW_OFF;
    clear - Hi F8 F4 Fce Fapp C1 HRc Ht DF; unfold kLowShadowBeg, kHighMemBeg in Fapp; lia.
- (* the read-only segments *)
  apply (hm_rom_kept rsegs W2 W2 mem2 mem3 Hrom). intros a Ha.
  pose proof (hku_rom_img a Ha) as Hi. pose proof (img_segs_low a Hi) as Hab.
  apply Klow; [unfold kLowMemEnd in Hab; clear - Hab C1; lia | intros Hf; exact (Fni a Hf Hi)].
- (* pp *)
  unfold hsu_pp_at in *. apply (hd_garr8_kept rsegs (w_H W2) _ mem2 _ _ _); [|exact Hpp]. intros j Hj.
  unfold hd_zbytes in Hj. rewrite length_map in Hj. pose proof (Layout.length_pp_bytes r Hwf) as HL.
  apply Kblk with (n := Layout.PP_SIZE); [exact Hinpp|]. change (req_size Layout.PP_SIZE) with Layout.PP_SIZE. lia.
- (* pod *)
  apply (hd_garr8_kept rsegs (w_H W2) _ mem2 _ _ _); [|exact Hpod]. intros j Hj.
  unfold hd_zbytes in Hj. rewrite length_map in Hj.
  apply Kblk with (n := e_len (x_e rsegs cx)); [exact Hinpod|].
  pose proof (Hrq (e_len (x_e rsegs cx)) ltac:(lia)). lia.
- (* out *)
  apply (hd_garr8_kept rsegs (w_H W2) _ mem2 _ _ _); [|exact Hout]. intros j Hj.
  unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
  assert (Hcl : Z.of_nat (length (ans_cells (hqu_ans rsegs cx r))) <= e_cap (x_e rsegs cx)).
  { unfold hqu_ans. pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r))
      (e_cap (x_e rsegs cx)) ltac:(lia)) as Hok.
    destruct (answer_ok_parts _ _ Hok) as [[(_ & Hc0 & _)|(Hr0 & Hrl & _)] _].
    - rewrite Hc0. cbn. lia.
    - lia. }
  apply Kblk with (n := 3 * (e_cap (x_e rsegs cx) + 1)); [exact Hinout|].
  pose proof (Hrq (3 * (e_cap (x_e rsegs cx) + 1)) ltac:(lia)). lia.
- (* res *)
  apply (hd_garr8_kept rsegs (w_H W2) _ mem2 _ _ _); [|exact Hres]. intros j Hj.
  unfold hd_zbytes in Hj. rewrite length_map in Hj. unfold ans_res_bytes in Hj. rewrite length_ha_res_bytes in Hj.
  unfold HQU_RES.
  apply Hk; try unfold hku_wr, HQU_XO; clear - Hj F4 Fce HRc Hlt Ht; lia.
- (* errno *)
  destruct Herr as (ev2 & Hev). exists ev2. intros kk Hkk.
  pose proof errno_low as ((E0 & E4) & Eimg & _).
  assert (Hi : in_img rsegs (as_errno B + Z.of_nat kk)) by (apply Eimg; lia).
  rewrite (Klow (as_errno B + Z.of_nat kk)); [exact (Hev kk Hkk) | unfold kLowMemEnd in E4; clear - E0 E4 Hkk C1; lia |].
  intros Hf. exact (Fni _ Hf Hi).
Qed.

(* the registers of hku_L: s0 s1 s3 s11 s4 s6 s9 s10 (hqu_L_seg), t5 t6 (hqu_L_t56), s2 s8 *)
Definition hku_keep : list Z := [8; 9; 19; 27; 20; 22; 25; 26; 30; 31; 18; 24].

Lemma hku_L_regs : forall cx m rr v, In (LReg rr, v) (hku_L rsegs cx m) -> In rr hku_keep.
Proof.
intros cx m rr v H. unfold hku_L, hqu_L_seg, hqu_L_frame, hqu_L_loopc, hqu_L_t56, hqu_L_body in H.
cbn [app In] in H.
repeat (destruct H as [H|H]; [first [discriminate H | injection H as E _; subst rr; unfold hku_keep; cbn [In];
  repeat (first [left; reflexivity | right])] |]).
destruct H.
Qed.

Lemma hku_inv_regs : forall cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hku_inv fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md3 (x_k rsegs cx) ->
same_io md2 md3 ->
(forall q : Z, q = 2 \/ q = 3 \/ q = 4 \/ In q hku_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
@hku_inv fx rc SK rsegs B MT cx fx2 r at0 m k cs keys rf ly2 S2 W2 regs3 mem2 md3.
Proof.
intros cx ev fx2 r at0 m k cs keys rf ly2 S2 W2 regs2 mem2 md2 regs3 md3 HS HI HJ3 Hio3 Hregs.
destruct HI as (HB & Hat & Hf1 & Hf2 & Hf3 & Hlive & Hm & Hk & Hp & Hx & Hcl).
refine (conj _ (conj _ (conj Hf1 (conj Hf2 (conj Hf3 (conj Hlive (conj Hm (conj Hk (conj Hp (conj Hx Hcl)))))))))).
- apply (hku_base3_kept cx ev fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 regs3 mem2 md3 HS HB hqu_shX_len HJ3).
  + intros q Hq. apply Hregs. destruct Hq as [Hq|[Hq|Hq]]; auto.
  + exact Hio3.
  + intros a _ _ _. reflexivity.
- unfold hsu_at_cx, hsu_at in *. rewrite Forall_forall in *. intros f Hf. specialize (Hat f Hf).
  destruct f as [l v]. destruct l as [rr|b o]; cbn [fst snd hd_at] in Hat |- *; [|exact Hat].
  rewrite Hregs; [exact Hat|]. right. right. right. exact (hku_L_regs cx m rr v Hf).
Qed.

(* the image's strings: every byte from the string's start to its NUL's word end is read-only image data *)
Definition hku_rom_b (a : Z) : bool :=
existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) && (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))
  rsegs.
Lemma hku_rom_b_ok : forall a, hku_rom_b a = true -> in_rom rsegs a.
Proof.
intros a H. unfold hku_rom_b in H. apply existsb_exists in H as (sg & Hin & Hb).
apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
exists sg. split; [exact Hin|]. split; [exact H0 | lia].
Qed.
Lemma hku_strs_rom_chk :
forallb (fun c => forallb (fun i => hku_rom_b (fst c + Z.of_nat i)) (seq 0 (length (snd c) + 8))) headamp_B_strs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma hku_strs_rom : forall a s, In (a, s) (hi_strs headamp_himg_B) ->
forall i, 0 <= i < Z.of_nat (length s) + 8 -> in_rom rsegs (a + i).
Proof.
intros a s Hin i Hi. pose proof hku_strs_rom_chk as H. rewrite forallb_forall in H.
specialize (H (a, s) Hin). cbn [fst snd] in H. rewrite forallb_forall in H.
specialize (H (Z.to_nat i) ltac:(apply in_seq; lia)). cbv beta in H. rewrite Z2Nat.id in H by lia.
exact (hku_rom_b_ok _ H).
Qed.

(* the hull of a low string's shadow lies just above kLowMemEnd *)
Lemma hku_hull_bounds : forall a n u, 0 <= a -> 0 <= n -> a + n < kLowMemEnd ->
shadow_addr a / 8 * 8 <= u < shadow_addr (a + n) / 8 * 8 + 8 -> kLowMemEnd <= u < kLowMemEnd + 0x10000008.
Proof.
intros a n u Ha Hn Hl Hu. unfold shadow_addr, SHADOW_OFF in Hu. unfold kLowMemEnd in *.
pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
pose proof (Z.div_mod (a + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (a + n) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + a / 8) 8 ltac:(lia)).
pose proof (Z.div_mod (0x7fff8000 + (a + n) / 8) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (0x7fff8000 + (a + n) / 8) 8 ltac:(lia)).
lia.
Qed.

(* the image's strings at a cut of M03 *)
Lemma hku_cstr_now : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
In (a, s) (hi_strs headamp_himg_B) ->
hd_cstr rsegs (w_H W2) mem2 a s.
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 a s HS HB Hin.
destruct HB as (HC & _ & _ & Hrom2 & _).
destruct (hku_start cx r ev HS) as (HP & _).
pose proof HP as HP'. unfold hsu_pre, hd_seg_pre in HP'.
destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstrs & _ & _ & Hromc & _).
pose proof (proj1 (Forall_forall _ _) Hstrs (a, s) Hin) as Hs0. cbn [fst snd] in Hs0.
destruct (hku_ctx cx r ev _ ly2 S2 W2 regs2 mem2 md2 HS HC) as (Hcc & _ & _ & _ & Hfin).
pose proof (hd_cctx_facts rsegs B ly2 S2 W2 mem2 md2 _ _ Hcc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hcc as (HAR2 & _ & _ & HF2 & _). change (hi_cid HPgImgA.headamp_himg_A) with 4 in HF2.
pose proof (hku_strs_rom a s Hin) as Hromi.
pose proof Hs0 as (_ & _ & _ & Ha0 & _ & Himg & _).
pose proof errno_low as ((E0 & E4) & _ & _).
assert (Ht : T_SEG_STK = 16384) by reflexivity.
pose proof alloc_ceiling_lt as Hlt.
pose proof (img_segs_low _ (Himg (Z.of_nat (length s)) ltac:(lia))) as Hhi.
apply (hd_cstr_kept rsegs _ _ _ _ a s Hs0).
- (* bytes and NUL: read-only image bytes *)
  intros i Hi. pose proof (Hromi i ltac:(lia)) as Hr. rewrite (Hrom2 _ Hr), (Hromc _ Hr). reflexivity.
- (* their shadow bytes *)
  intros x Hx. pose proof (Himg (x - a) ltac:(lia)) as Hxi. replace (a + (x - a)) with x in Hxi by lia.
  pose proof (img_segs_low x Hxi) as Hxb.
  pose proof (Z.div_mod (e_F (x_e rsegs cx)) 8 ltac:(lia)) as DF. pose proof (Z.div_mod x 8 ltac:(lia)) as Dx.
  pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *.
  apply (hku_kept2 cx r ev ly2 S2 W2 regs2 mem2 md2 _ HS HC);
    unfold shadow_of_addr, shadow_addr, SHADOW_OFF.
  + clear - Hxb Dx Mx. lia.
  + clear - Hxb Dx Mx HRc C1. lia.
  + clear - Hxb Dx Mx Fapp. lia.
  + intros Hs. apply (Fni x); [clear - Hs F8 DF Dx Mx; lia | exact Hxi].
  + clear - Hxb Dx Mx HRc C1 Ht. lia.
  + clear - Hxb Dx Mx Oapp. lia.
  + clear - Hxb Dx Mx E4. lia.
- (* the hull of their shadow *)
  intros u Hu Hn.
  replace (a + (Z.of_nat (length s) + 1) - 1) with (a + Z.of_nat (length s)) in Hu by lia.
  pose proof (hku_hull_bounds a (Z.of_nat (length s)) u ltac:(lia) ltac:(lia) ltac:(unfold kLowMemEnd in *; lia) Hu)
    as Hub.
  destruct (Z_le_gt_dec (shadow_addr (e_F (x_e rsegs cx)) + 0x54) u) as [H1|H1];
    [destruct (Z_lt_le_dec u (shadow_addr (e_F (x_e rsegs cx)) + 0x69)) as [H2|H2]|].
  + destruct (al_frames _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hfin) as (_ & _ & _ & Fsh).
    rewrite <- HF2 in Fsh. change (fs_frame_bytes 4 / 8) with 128 in Fsh.
    destruct (Fsh (u - shadow_addr (e_F (x_e rsegs cx))) ltac:(lia)) as (Hpr & _).
    replace (shadow_addr (e_F (x_e rsegs cx)) + (u - shadow_addr (e_F (x_e rsegs cx)))) with u in Hpr by lia.
    exact (hku_apresent_some _ _ _ Hpr).
  + rewrite (hku_kept2 cx r ev ly2 S2 W2 regs2 mem2 md2 _ HS HC); [exact Hn | idtac ..];
      unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *.
    * clear - Hub. lia.
    * clear - Hub HRc C1. lia.
    * clear - Hub Fapp. lia.
    * clear - H2. lia.
    * clear - Hub HRc C1 Ht. lia.
    * clear - Hub Oapp. lia.
    * clear - Hub E4. lia.
  + rewrite (hku_kept2 cx r ev ly2 S2 W2 regs2 mem2 md2 _ HS HC); [exact Hn | idtac ..];
      unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *.
    * clear - Hub. lia.
    * clear - Hub HRc C1. lia.
    * clear - Hub Fapp. lia.
    * clear - H1. lia.
    * clear - Hub HRc C1 Ht. lia.
    * clear - Hub Oapp. lia.
    * clear - Hub E4. lia.
- (* the tail of the NUL's word: read-only image bytes *)
  intros u Hu. pose proof (Z.mod_pos_bound (a + Z.of_nat (length s)) 8 ltac:(lia)) as M.
  pose proof (Hromi (u - a) ltac:(lia)) as Hr. replace (a + (u - a)) with u in Hr by lia.
  rewrite (Hrom2 _ Hr), (Hromc _ Hr). reflexivity.
Qed.

(* the read-only data as the string wrappers' contracts read it, at a cut of M03 *)
Lemma hku_arodata_now : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
arodata_okP rsegs 0 0 B (aview rsegs (w_H W2) mem2).
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 _ HB.
destruct HB as (_ & _ & _ & Hrom2 & _).
intros a Hro _ _. destruct Hro as [(sg & Hsg & Hw & Hr) | Hr]; [|lia].
exact (Hrom2 a (ex_intro _ sg (conj Hsg (conj Hw Hr)))).
Qed.

(* the n-th byte of an entry's memory past its two words is its body's *)
Lemma hku_ent_nth : forall e i d, (i < length (Model.e_body e))%nat ->
nth (8 + i) (Layout.ent_mem e) d = nth i (Model.e_body e) d.
Proof.
intros e i d Hi. unfold Layout.ent_mem.
replace (8 + i)%nat with (length (Cursor.le32 (Model.e_type e)) + (length (Cursor.le32 (Model.e_size e)) + i))%nat
  by (rewrite !Cursor.length_le32; lia).
rewrite !app_nth2_plus. apply app_nth1. exact Hi.
Qed.

(* the key of entry m at a cut of M03 *)
Lemma hku_keymem : forall cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 (m : nat) k,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
@hqu_base3 fx rc SK rsegs B MT cx fx2 r sh ly2 S2 W2 regs2 mem2 md2 ->
(m < length (Model.ents r))%nat ->
Accessors.key_of (nth m (Model.ents r) (Model.Ent 0 0 [])) = Some k ->
(length k <= 44)%nat /\ ~ In Cursor.NUL k /\
(forall i, (i <= length k)%nat ->
 val_mem rsegs (mrestrict (w_H W2) mem2) (hku_kaddr rsegs cx m + Z.of_nat i) 1
   (bv_unsigned (nth i (k ++ [Cursor.NUL]) Cursor.NUL))) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (hku_kaddr rsegs cx m) (hd_zbytes k ++ [0]) /\
hd_str_tail (aview rsegs (w_H W2) mem2) (hku_kaddr rsegs cx m + Z.of_nat (length k)) /\
In (e_pp (x_e rsegs cx), Layout.PP_SIZE) (ablocks B ly2 S2) /\
4096 <= e_pp (x_e rsegs cx) /\ e_pp (x_e rsegs cx) + Layout.PP_SIZE <= alloc_ceiling /\
e_pp (x_e rsegs cx) mod 16 = 0 /\
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF (hku_kaddr rsegs cx m - 12) 112 /\
(forall a, hku_kaddr rsegs cx m - 12 <= a < hku_kaddr rsegs cx m + 100 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)).
Proof.
intros cx ev fx2 r sh ly2 S2 W2 regs2 mem2 md2 m k HS HB Hm Hk.
destruct HB as (HC & _ & _ & _ & Hpp & _).
destruct (hku_start cx r ev HS) as (_ & Hwf & _).
destruct (hku_ctx cx r ev _ ly2 S2 W2 regs2 mem2 md2 HS HC) as (Hcc & _ & Hinpp & _).
pose proof Hcc as (HAR2 & _).
destruct (Model.ents_wf r Hwf) as (Hn32 & Hall).
destruct (Spa.buf_header r Hwf) as (_ & _ & _ & HB8).
assert (Hs96 : Forall (fun e => (length (Model.e_body e) <= 96)%nat) (Model.ents r)).
{ eapply Forall_impl; [|exact Hall]. intros x (_ & Hx & Hx2). lia. }
assert (HBl : Z.of_nat (length (Model.buf r)) <= Layout.POD_BUF_MAX) by (unfold Layout.POD_BUF_MAX; lia).
unfold hsu_pp_at in Hpp. apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)) in Hpp.
pose proof (hm_pp_ent rsegs (Model.buf r) (Model.is_props r) (Model.has_params r) (Model.params_struct r)
  (Model.ents r) (Model.corrupt r) HBl Hn32 Hs96 (w_H W2) mem2 (e_pp (x_e rsegs cx)) m Hpp Hm) as Hent.
set (e := nth m (Model.ents r) (Model.Ent 0 0 [])) in *.
assert (He : Model.ent_wf e) by (exact (proj1 (Forall_forall _ _) Hall e (nth_In _ (Model.Ent 0 0 []) Hm))).
destruct (hku_key_facts e k He Hk) as (Hl44 & Hnul & Hlt & Hnth).
pose proof He as (_ & Hbl & Hsz).
assert (Hlen104 : length (Layout.ent_mem e) = 104%nat) by (apply Layout.length_ent_mem; lia).
set (base := e_pp (x_e rsegs cx) + (Layout.OFF_ENT + Layout.ENT_SIZE * Z.of_nat m)) in *.
assert (Hka : hku_kaddr rsegs cx m = base + 8).
{ unfold hku_kaddr, base. lia. }
(* the bytes of the key and its NUL *)
assert (Hval : forall i, (i <= length k)%nat ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (hku_kaddr rsegs cx m + Z.of_nat i) 1
    (bv_unsigned (nth i (k ++ [Cursor.NUL]) Cursor.NUL))).
{ intros i Hi. pose proof (hm_bytes_byte rsegs _ _ _ _ (8 + i) Hent ltac:(rewrite Hlen104; lia)) as V.
  rewrite (hku_ent_nth e i _ ltac:(lia)) in V. change (Z_to_bv 8 0) with Cursor.NUL in V.
  rewrite (Hnth i Hi). rewrite Hka.
  replace (base + 8 + Z.of_nat i) with (base + Z.of_nat (8 + i)) by lia. exact V. }
destruct (al_blocks _ _ (YG0q.AR_laws_ok rsegs B) ly2 S2 W2 mem2 md2 _ _ HAR2 Hinpp) as (P16 & P4 & Pce & Papp & _).
change (req_size Layout.PP_SIZE) with Layout.PP_SIZE in Pce, Papp.
assert (Hm31 : (m <= 31)%nat) by lia.
split; [exact Hl44|]. split; [exact Hnul|]. split; [exact Hval|].
split.
- (* the key and its NUL as garr8 *)
  assert (EZ : hd_zbytes k ++ [0] = map (fun b : byte => bv_unsigned b) (k ++ [Cursor.NUL]))
    by (unfold hd_zbytes; rewrite map_app; reflexivity).
  rewrite EZ. intros j Hj. rewrite length_map, length_app in Hj. cbn [length] in Hj.
  rewrite hm_nth_map. change (Z_to_bv 8 0) with Cursor.NUL.
  split; [exact (Hval j ltac:(lia)) | apply hm_byte_range].
- split.
  + (* the tail of the NUL's word lies in the body *)
    intros a Ha. pose proof (Z.mod_pos_bound (hku_kaddr rsegs cx m + Z.of_nat (length k)) 8 ltac:(lia)) as M.
    rewrite Hka in Ha, M.
    pose proof (proj1 (hm_bytes_aview rsegs _ _ _ _) Hent (Z.to_nat (a - base)) ltac:(rewrite Hlen104; lia)) as A.
    rewrite Z2Nat.id in A by lia. replace (base + (a - base)) with a in A by lia. rewrite A. discriminate.
  + split; [exact Hinpp|]. split; [exact P4|]. split; [exact Pce|]. split; [exact P16|].
    split.
    * (* the shadow of the entry's granule span, inside the pp block *)
      rewrite Hka. eapply proj1.
      apply (hm_blk_ra rsegs B ly2 S2 W2 mem2 md2 (e_pp (x_e rsegs cx)) Layout.PP_SIZE (base + 8 - 12) 112 HAR2 Hinpp);
        try change (req_size Layout.PP_SIZE) with Layout.PP_SIZE;
        unfold base, Layout.OFF_ENT, Layout.ENT_SIZE, Layout.PP_SIZE; clear - Hm31; lia.
    * intros a Ha. rewrite Hka in Ha. unfold in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Papp.
      unfold base, Layout.OFF_ENT, Layout.ENT_SIZE, Layout.PP_SIZE in *. unfold SHADOW_OFF.
      clear - Ha Papp Hm31. lia.
Qed.

End d.
End b.

Print Assumptions hku_pairs_at.
Print Assumptions hku_x_open_keys.
Print Assumptions hku_fold_skip.
Print Assumptions hku_pair_of_fold.
Print Assumptions hku_base3_kept.
Print Assumptions hku_inv_regs.
Print Assumptions hku_cstr_now.
Print Assumptions hku_arodata_now.
Print Assumptions hku_keymem.
