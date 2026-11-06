(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the kit of segment F of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86974 .. 0x8699c: the three frees of the words blocks and the latch), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACbk.v (wcb_entry: the symbolic seed of a point of the function) and A/ACh2.v:122-290 (the step through a call and back, with the facts carried over it). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/LLVMFuzzerTestOneInput_s70.v, with its module paths changed; 855 of its 936 lines of code are new or changed and 347 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/LLVMFuzzerTestOneInput_s24k.v; 390 of its 805 lines of code are new or changed and 521 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): the kit of file group _s17, segment
   S07 of the test harness's entry function LLVMFuzzerTestOneInput (0x853bc .. 0x85410: reac_segconf_parse(c, text),
   check 18, free(text)). No function of the binary is proved here: these are the lemmas LLVMFuzzerTestOneInput_s17.v
   applies.

   - the model of the last turn (seg_spec.seg_after when f + 1 = nfiles): the reader's state and the model's after
     it, the answer of reac_segconf_parse equal to m->n, and conf_rel (SegModel.v's run_rel / file_rel / cross_rel
     applied to the turns of seg_run); the cursor after the turn (_s15's s5_cur_S, LLVMFuzzerTestOneInput_s15k.v
     at commit 1ff47048945a, copied);
   - the walk's facts at a cut, what a step keeps, the budget around a free and the free itself: _s24's kit
     (LLVMFuzzerTestOneInput_s24k.v, commit 17b6c3e39168 and its worktree's later
     s24_kept_of_journal / s24_blk_kept / s24_core_step_f), copied with s24_ renamed s17k_, its free at this
     segment's pc 0x8540c (mv a0, s7; jal free);
   - the call of reac_segconf_parse through PaFx.v's cl_callSF (the callee returns at some FP state fx1) and its
     contract, with what the call keeps (from the callee's inner journal) and reader_pre at the call. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YN01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaNoChain PaDenot PaSB PaFx PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
  refuse_c cross_check_c reac_segconf_parse_file_c reac_segconf_parse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_s10k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ======================================= the model of the last turn ======================================= *)
(* every turn's file record is well formed (SegModel.decode_ok); past the last, the default record is too *)
Lemma s17k_file_ok : forall inp k, SegModel.file_ok (seg_spec.seg_file inp k).
Proof.
intros inp k. unfold seg_spec.seg_file.
destruct (Nat.lt_ge_cases k (length (seg_spec.seg_files inp))) as [Hk | Hk].
- assert (HB : Forall SegModel.byte_ok (seg_spec.seg_in inp)).
  { unfold seg_spec.seg_in, seg_spec.zs. apply Forall_forall. intros z Hz.
    apply in_map_iff in Hz. destruct Hz as [b [Eb _]]. subst z.
    pose proof (bv_unsigned_in_range _ b) as R. change (bv_modulus 8) with 256 in R. unfold SegModel.byte_ok. lia. }
  pose proof (proj1 (SegModel.decode_ok (seg_spec.seg_in inp) HB)) as HF.
  rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hk.
- rewrite nth_overflow by exact Hk. unfold SegModel.file_ok, SegModel.nulfree. cbn. split; [intros []|]. lia.
Qed.
(* the reader's state and the model's state agree (conf_rel) after every run of drop-in turns *)
Lemma s17k_run_rel : forall inp k,
  SegModel.conf_rel (seg_spec.seg_rc (seg_spec.seg_run inp k)) (seg_spec.seg_mc (seg_spec.seg_run inp k)).
Proof.
intros inp k. induction k as [|k IH]; [exact SegModel.conf_rel0|].
cbn [seg_spec.seg_run]. unfold seg_spec.seg_turn_step.
pose proof (s17k_file_ok inp k) as (Hn & Hl & Hlb).
destruct (seg_spec.seg_run inp k) as [[c0 m0] r0].
cbn [seg_spec.seg_rc seg_spec.seg_mc fst snd] in IH |- *. cbv beta iota zeta.
pose proof (SegModel.file_rel c0 m0 (seg_spec.seg_txt inp k) (seg_spec.seg_label inp k) (seg_spec.seg_label inp k)
  IH Hn Hl eq_refl (SegModel.rd_label_ok _ Hlb)) as (H1 & _ & _).
revert H1. destruct (SegModel.r_parse_file c0 (seg_spec.seg_txt inp k) (seg_spec.seg_label inp k)) as [c1 n].
cbn [fst snd]. intros H1. exact H1.
Qed.
(* the last turn: the reader parses the text (reac_segconf_parse), the model files and crosses it; the answer is
   the model's segment count, so returned is unchanged; the two states agree *)
Lemma s17k_last : forall inp f, Z.of_nat (Datatypes.S f) = seg_spec.seg_nfiles inp ->
  seg_spec.seg_rc (seg_spec.seg_after inp f) =
    fst (SegModel.r_parse (seg_spec.seg_rc (seg_spec.seg_run inp f)) (seg_spec.seg_txt inp f)) /\
  seg_spec.seg_mc (seg_spec.seg_after inp f) =
    SegModel.m_cross (SegModel.m_file (seg_spec.seg_mc (seg_spec.seg_run inp f)) (seg_spec.seg_txt inp f) None) /\
  seg_spec.seg_ret (seg_spec.seg_after inp f) = seg_spec.seg_ret (seg_spec.seg_run inp f) /\
  snd (SegModel.r_parse (seg_spec.seg_rc (seg_spec.seg_run inp f)) (seg_spec.seg_txt inp f)) =
    Z.of_nat (length (SegModel.mc_seg (seg_spec.seg_mc (seg_spec.seg_after inp f)))) /\
  SegModel.conf_rel (seg_spec.seg_rc (seg_spec.seg_after inp f)) (seg_spec.seg_mc (seg_spec.seg_after inp f)).
Proof.
intros inp f Hl.
pose proof (s17k_run_rel inp f) as Hc.
pose proof (s17k_file_ok inp f) as (Hn & Hlen & _).
unfold seg_spec.seg_after. rewrite Hl, Z.eqb_refl. unfold seg_spec.seg_turn_step.
destruct (seg_spec.seg_run inp f) as [[c0 m0] r0].
cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd] in Hc |- *. cbv beta iota zeta.
pose proof (SegModel.file_rel c0 m0 (seg_spec.seg_txt inp f) (Some SegModel.S_base) None Hc Hn Hlen eq_refl
  ltac:(rewrite SegModel.rd_base; exact SegModel.rd_base_ok)) as (H1 & H2 & H3).
revert H1 H2. unfold SegModel.r_parse.
destruct (SegModel.r_parse_file c0 (seg_spec.seg_txt inp f) (Some SegModel.S_base)) as [c1 n].
cbn [fst snd]. intros H1 H2. subst n.
cbn [seg_spec.seg_rc seg_spec.seg_mc seg_spec.seg_ret fst snd].
rewrite SegModel.m_cross_len, Z.eqb_refl, andb_true_r.
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
apply SegModel.cross_rel; [exact H1 | rewrite H3; exact SegModel.rd_base].
Qed.
(* a text is at most 65535 bytes *)
Lemma s17k_txt_len : forall inp f, Z.of_nat (length (seg_spec.seg_txt inp f)) <= 65535.
Proof. intros inp f. exact (proj1 (proj2 (s17k_file_ok inp f))). Qed.
(* the counters of a reader's state that agrees with the model's are the model's *)
Lemma s17k_cnt : forall n rc0 rc1 mc, SegModel.conf_rel rc1 mc -> lt_cnt n rc0 mc -> lt_cnt n rc1 mc.
Proof.
intros n rc0 rc1 mc (_ & _ & _ & Hov & Hrf & _ & _ & Hgen) (C1 & C2 & C3 & C4 & C5 & C6).
unfold lt_cnt. rewrite Hov, Hrf, Hgen. repeat split; assumption.
Qed.

(* ---- the cursor after a turn (_s15's s5_next / s5_skip_S / s5_skip_S' / s5_cur_S, copied) ---- *)
Definition s17k_next (l : list Z) : list Z :=
  snd (SegModel.fuzz_take
    (snd (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))
    (fst (SegModel.fuzz_u16 (snd (SegModel.fuzz_u8 l))))).
Lemma s17k_take_fst : forall l n, fst (SegModel.fuzz_take l n) = firstn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s17k_take_snd : forall l n, snd (SegModel.fuzz_take l n) = skipn (Nat.min (Z.to_nat n) (length l)) l.
Proof. intros l n. reflexivity. Qed.
Lemma s17k_skip_S : forall k l, seg_spec.seg_skip (Datatypes.S k) l = seg_spec.seg_skip k (s17k_next l).
Proof.
intros k l. cbn [seg_spec.seg_skip]. unfold s17k_next.
destruct (SegModel.fuzz_u8 l) as [b i1]. cbn [fst snd].
destruct (SegModel.fuzz_u16 i1) as [len i2]. cbn [fst snd].
destruct (SegModel.fuzz_take i2 len) as [p i3]. cbn [fst snd]. reflexivity.
Qed.
Lemma s17k_skip_S' : forall f h, seg_spec.seg_skip (Datatypes.S f) h = s17k_next (seg_spec.seg_skip f h).
Proof.
induction f as [|f IH]; intros h.
- rewrite (s17k_skip_S 0 h). cbn [seg_spec.seg_skip]. reflexivity.
- rewrite (s17k_skip_S (Datatypes.S f) h), (IH (s17k_next h)), <- (s17k_skip_S f h). reflexivity.
Qed.
Lemma s17k_cur_S : forall pl f,
  seg_spec.seg_cur pl (Datatypes.S f) =
  skipn (Z.to_nat (seg_spec.seg_turn_np pl f)) (seg_spec.seg_turn_tail pl f).
Proof.
intros pl f.
unfold seg_spec.seg_turn_np, seg_spec.seg_turn_tail, seg_spec.seg_turn_len, seg_spec.seg_cur.
rewrite s17k_skip_S'. unfold s17k_next.
rewrite s17k_take_snd, s17k_take_fst, length_firstn, Nat2Z.id. f_equal. lia.
Qed.
(* the count and the address of the cursor after turn f, from the turn's tail and its take n' *)
Lemma s17k_cur_next : forall pl p f,
  seg_spec.seg_cur_n pl (Datatypes.S f) =
    Z.of_nat (length (seg_spec.seg_turn_tail pl f)) - seg_spec.seg_turn_np pl f /\
  seg_spec.seg_cur_at pl p (Datatypes.S f) = seg_spec.seg_turn_at pl p f + seg_spec.seg_turn_np pl f.
Proof.
intros pl p f.
assert (Hnp : seg_spec.seg_turn_np pl f =
  Z.of_nat (Nat.min (Z.to_nat (seg_spec.seg_turn_len pl f)) (length (seg_spec.seg_turn_tail pl f)))).
{ unfold seg_spec.seg_turn_np. rewrite s17k_take_fst, length_firstn. f_equal. lia. }
assert (Hl : length (seg_spec.seg_cur pl (Datatypes.S f)) =
  (length (seg_spec.seg_turn_tail pl f) -
   Nat.min (Z.to_nat (seg_spec.seg_turn_len pl f)) (length (seg_spec.seg_turn_tail pl f)))%nat).
{ rewrite s17k_cur_S, length_skipn, Hnp, Nat2Z.id. reflexivity. }
unfold seg_spec.seg_cur_n, seg_spec.seg_cur_at, seg_spec.seg_turn_at. rewrite Hl, Hnp. lia.
Qed.

(* ======================================= readers and lists ======================================= *)
Lemma s17k_bytes_ext : forall (rd rd' : reader) a l, (forall x, rd' x = rd x) -> sa_bytes rd a l -> sa_bytes rd' a l.
Proof. intros rd rd' a l HE H i Hi. rewrite HE. exact (H i Hi). Qed.
Lemma s17k_str_ext : forall (rd rd' : reader) p s, (forall x, rd' x = rd x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros rd rd' p s HE ((Hz & Hn) & Ht). split; [split; [intros i Hi; rewrite HE; exact (Hz i Hi) | exact Hn]|].
intros x Hx. rewrite HE. exact (Ht x Hx).
Qed.
Lemma s17k_rconf_ext : forall (rd rd' : reader) c rc0, (forall x, rd' x = rd x) -> sa_rconf rd c rc0 -> sa_rconf rd' c rc0.
Proof. intros rd rd' c rc0 HE (bs & Hb & He). exists bs. split; [eapply s17k_bytes_ext; eassumption | exact He]. Qed.
Lemma s17k_mconf_range : forall (rd rd' : reader) a mc,
  (forall i, 0 <= i < seg_spec.SEG_M_SIZE -> rd' (a + i) = rd (a + i)) -> sa_mconf rd a mc -> sa_mconf rd' a mc.
Proof.
intros rd rd' a mc K (bs & Hb & He). exists bs. split; [|exact He].
intros i Hi. destruct He as [Hl _]. rewrite K by lia. exact (Hb i Hi).
Qed.
Lemma s17k_pzd_nodup : forall l, (forall x, In x l -> 0 < snd x) -> pairwise zdisjoint l -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hp Hd; [constructor|]. destruct Hd as [Hx Hl]. constructor.
- intros Hin. rewrite Forall_forall in Hx. specialize (Hx x Hin). pose proof (Hp x (or_introl eq_refl)).
  unfold zdisjoint in Hx. lia.
- apply IH; [intros y Hy; exact (Hp y (or_intror Hy)) | exact Hl].
Qed.
(* free removes its block from the list at any place: what is left, against the cut's list *)
Lemma s17k_perm_free : forall (bl bl2 O R : list (Z * Z)) x,
  Permutation bl ((x :: O) ++ R) ->
  (exists l1 l2, bl = l1 ++ x :: l2 /\ bl2 = l1 ++ l2) ->
  Permutation bl2 (O ++ R).
Proof.
intros bl bl2 O R x HP (l1 & l2 & E1 & E2). subst bl bl2.
apply (Permutation_cons_inv (a := x)).
eapply Permutation_trans; [apply Permutation_middle | exact HP].
Qed.
Lemma s17k_req : forall n, 0 < n -> req_size n = n.
Proof. intros n Hn. unfold req_size. destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | reflexivity]. Qed.
(* the five registers the frame part of a cut reads (sp, gp, tp, s0, s1), kept from one state to a later one *)
Definition s17k_fregs (regs regs2 : bvmap 5 word) : Prop :=
  forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9) -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Lemma s17k_fregs_of_pres : forall regs regs2, aregs_preserved regs regs2 -> s17k_fregs regs regs2.
Proof. intros regs regs2 HP r Hr. apply HP. unfold acallee_saved. lia. Qed.
(* a rounded-up end below an 8-aligned address stays below it *)
Lemma s17k_up8 : forall x c, x <= c -> c mod 8 = 0 -> x + (- x) mod 8 <= c.
Proof.
intros x c H Hc. pose proof (Z.div_mod (- x) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (- x) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod c 8 ltac:(lia)) as D2. lia.
Qed.
(* m->n, a u32 field of the model's struct, read through the reader (_s16's s16_rd32_fld / s16_rd_n, copied) *)
Lemma s17k_nth_firstn : forall {A} (l : list A) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
intros A l. induction l as [|x l IH]; intros L i d Hi; destruct L as [|L]; try lia; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma s17k_nth_skipn : forall {A} (l : list A) o i d, nth i (skipn o l) d = nth (o + i) l d.
Proof.
intros A l o. revert l. induction o as [|o IH]; intros l i d; [reflexivity|].
destruct l as [|x l]; [destruct i; reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.
Lemma s17k_nth_fld : forall (bs : list byte) a n k d, (k < n)%nat -> nth k (seg_spec.fld a n bs) d = nth (a + k) bs d.
Proof. intros bs a n k d H. unfold seg_spec.fld. rewrite s17k_nth_firstn by exact H. apply s17k_nth_skipn. Qed.
Lemma s17k_rd32_fld : forall rd p (bs : list byte) o v, sa_bytes rd p bs -> (o + 4 <= length bs)%nat ->
  seg_spec.fld o 4 bs = Mem.le4 (Z_to_bv 64 v) -> 0 <= v < 2 ^ 32 -> rd32 rd (p + Z.of_nat o) v.
Proof.
intros rd p bs o v HB Hl Hf Hv k Hk.
replace (p + Z.of_nat o + Z.of_nat k) with (p + Z.of_nat (o + k)) by lia.
rewrite (HB (o + k)%nat) by lia. f_equal.
rewrite <- (s17k_nth_fld bs o 4 k ZB0 Hk), Hf. unfold Mem.le4.
rewrite (nth_error_nth _ _ _ (YN01.nth_error_Z_to_le_bytes 4 _ k Hk)).
rewrite Z_to_bv_unsigned, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite (Z.mod_small v (2 ^ 64)) by lia. unfold le_byte.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia). reflexivity.
Qed.
Lemma s17k_rd_n : forall rd p mc, sa_mconf rd p mc ->
  rd32 rd (p + seg_spec.MC_N) (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd p mc (bs & HB & L & LS & _ & (N0 & N) & _). unfold seg_spec.SEG_M_SIZE in L.
unfold seg_spec.fldz, seg_spec.MC_N in N. split; [|exact LS].
change (p + seg_spec.MC_N) with (p + 0x2000). change 0x2000 with (Z.of_nat (Z.to_nat 0x2000)).
apply (s17k_rd32_fld rd p bs _ _ HB); [cbn; lia | exact N | exact N0].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a reader at a machine address only depends on the address mod 2 ^ 64 *)
Lemma s17k_aview_wrap : forall H (m : word -> option byte) a, aview SEGS H m a = aview SEGS H m (a mod 2 ^ 64).
Proof.
intros H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod. reflexivity.
Qed.
Lemma s17k_keep_all : forall H (m m' : word -> option byte),
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a) -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros H m m' HK a. rewrite (s17k_aview_wrap H m' a), (s17k_aview_wrap H m a). apply HK.
apply Z.mod_pos_bound. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the journal from the entry every cut from K84eb8 on holds (lt_frame's first conjunct) *)
Definition s17k_J (cx : lcx) ly S (W : world SEGS) mem md (k : Z) : Prop :=
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k.

(* the entry's numbers: sp0 16-aligned, S1 = (sp0 - 320) & ~31 at most 351 below it, the stack window above the
   allocator's ceiling, below 2 ^ 47 *)
Lemma s17k_nums : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ x_s1 cx mod 16 = 0 /\ x_sp0 cx - 352 <= x_s1 cx <= x_sp0 cx - 320 /\
  alloc_ceiling + 32768 <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_sp0 cx <= ly_top (x_ly cx) /\ ly_top (x_ly cx) <= 2 ^ 47.
Proof.
intros cx HB. destruct HB as (HPRE & _).
destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold STK_LLVMFuzzerTestOneInput in *.
unfold x_s1, x_sp0, LT_FRAME.
set (sp := spZ (x_regs cx)) in *.
pose proof (Z.mod_pos_bound (sp - 320) 32 ltac:(lia)) as Hm.
assert (E : sp - 320 - (sp - 320) mod 32 = 32 * ((sp - 320) / 32))
  by (pose proof (Z.div_mod (sp - 320) 32 ltac:(lia)); lia).
rewrite E.
split; [exact Hal16|].
split; [replace (32 * ((sp - 320) / 32)) with (2 * ((sp - 320) / 32) * 16) by ring; apply Z.mod_mul; lia|].
split; [rewrite <- E; lia|]. lia.
Qed.

(* the live blocks of a state are distinct *)
Lemma s17k_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR.
destruct (ablocks B ly S) as [|[p0 n0] bl] eqn:Eb; [constructor|].
assert (Hin0 : In (p0, n0) (ablocks B ly S)) by (rewrite Eb; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p0 n0 HAR Hin0) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite <- Eb. apply (NoDup_map_inv (fun b : Z * Z => (fst b, req_size (snd b)))).
apply s17k_pzd_nodup; [|exact Hpw].
intros [a q] Hx. apply in_map_iff in Hx as ([pb nb] & Hq & Hpb). cbn in Hq. injection Hq as <- <-.
destruct (al_blocks _ _ LAWS ly S W mem md pb nb HAR Hpb) as (_ & _ & _ & _ & _ & _ & Hn).
cbn [snd]. pose proof (req_size_pos nb ltac:(lia)). lia.
Qed.
(* a block of the cut's list is live and is not one of the entry's blocks *)
Lemma s17k_blk_of : forall cx ly S (W : world SEGS) mem md b O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S O -> In b O ->
  In b (ablocks B ly S) /\ ~ In b (x_bl0 B cx).
Proof.
intros cx ly S W mem md b O HAR HP Hb.
assert (HND : List.NoDup (ablocks B ly S)) by exact (s17k_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2.
split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hb|].
intros Hb0. revert HND2 Hb Hb0. clear. induction O as [|x O IH]; intros HND2 Hb Hb0; [destruct Hb|].
cbn [app] in HND2. apply NoDup_cons_iff in HND2 as [Hni HND2].
destruct Hb as [<- | Hb]; [apply Hni; apply in_or_app; right; exact Hb0 | exact (IH HND2 Hb Hb0)].
Qed.
(* the head of the cut's block list is not in its tail *)
Lemma s17k_blk_head : forall cx ly S (W : world SEGS) mem md pa n O,
  AR SEGS B ly S W mem md -> lt_blocks B cx ly S ((pa, n) :: O) ->
  In (pa, n) (ablocks B ly S) /\ ~ In (pa, n) (x_bl0 B cx) /\ ~ In (pa, n) O.
Proof.
intros cx ly S W mem md pa n O HAR HP.
assert (HND : List.NoDup (ablocks B ly S)) by exact (s17k_nodup ly S W mem md HAR).
pose proof (Permutation_NoDup HP HND) as HND2. cbn [app] in HND2.
apply NoDup_cons_iff in HND2 as [Hni _].
split; [apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity|].
split; intros Hb; apply Hni; apply in_or_app; [right | left]; exact Hb.
Qed.

(* a live block of a positive size, from AR: nonzero, 16-aligned, every sub-range sa_addr, every byte mapped *)
Lemma s17k_blk : forall ly S (W : world SEGS) mem md p n,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < n ->
  4096 <= p /\ p mod 16 = 0 /\ p + n <= alloc_ceiling /\
  (forall a k, p <= a -> a + k <= p + n -> sa_addr (rdW W mem) a k) /\
  (forall a, p <= a < p + n -> rdW W mem a <> None).
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (Hm16 & H4096 & Hceil & _ & Hpres & _).
  pose proof (s17k_req n Hn) as Er. rewrite Er in Hceil, Hpres.
  pose proof asan_consts as (C1 & _).
  split; [exact H4096|]. split; [exact Hm16|]. split; [exact Hceil|]. split.
  - intros a k Ha Hk. unfold sa_addr. split; [lia|].
    split; [change (2 ^ 63) with 9223372036854775808; lia|].
    split; [apply (amem_range_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    split; [apply (range_addressable_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); rewrite Er; exact Hk|].
    intros Hk0. apply (shadow_hull_vis_of_block _ _ LAWS ly S W mem md p n a k HAR Hin Ha); [rewrite Er; exact Hk | exact Hk0].
  - intros a Ha. apply (aview_some_of_apresent SEGS). exact (proj1 (Hpres a Ha)).
Qed.
(* a harness block's facts at any state that holds it (lt_hblk), from AR *)
Lemma s17k_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> 0 < n -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin Hn.
destruct (s17k_blk ly S W mem md a n HAR Hin Hn) as (H4 & H16 & _ & HA & _).
split; [exact Hin|]. split; [exact H4|]. split; [exact H16|]. apply HA; lia.
Qed.

(* the frame chain at a call from sp = S1 with s0 = SP0: the frame record the prologue wrote (ra at SP0 - 8, the
   caller's s0 at SP0 - 16) pushed onto afn_pre's chain (chain_words_s2.v cw2_chain) *)
Lemma s17k_chain : forall cx ly S (W : world SEGS) mem md k,
  lt_base B MT cx -> s17k_J cx ly S W mem md k -> lt_saved cx (rdW W mem) ->
  exists ch, achain ly (rdW W mem) (x_s1 cx) (x_sp0 cx) ch.
Proof.
intros cx ly S W mem md k HB HJ HSV.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct HB as (HPRE & _).
destruct HPRE as (HAR0 & Hra0 & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & G1 & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
unfold STK_LLVMFuzzerTestOneInput in *.
destruct (Z_lt_le_dec (x_sp0 cx) (ly_top (x_ly cx) - 16)) as [Hlt | Hge].
- exists ((spZ (x_regs cx), raZ (x_regs cx), s0Z (x_regs cx)) :: x_ch cx).
  apply (achain_ly_top (x_ly cx) ly _ _ _ _ Etop).
  pose proof (HSV 0%nat _ eq_refl) as H0. pose proof (HSV 1%nat _ eq_refl) as H1.
  change (Z.of_nat (Datatypes.S 0)) with 1 in H0. change (Z.of_nat (Datatypes.S 1)) with 2 in H1.
  unfold x_sp0 in *.
  apply (achain_push (x_ly cx) (rdW (x_W cx) (x_mem cx)) (rdW W mem) (spZ (x_regs cx)) (s0Z (x_regs cx))
    (raZ (x_regs cx)) (x_ch cx) (x_s1 cx) Hch).
  + lia.
  + intros a Ha. apply G1.
    * lia.
    * lia.
    * intros (r & Hr & Ha'). cbn [ltoi_PG In] in Hr. destruct Hr as [<- | []]. cbn [fst snd] in Ha'.
      unfold longlA, A_LONGL, LONGL_N in Ha'. lia.
  + replace (spZ (x_regs cx) - 8) with (spZ (x_regs cx) - 8 * 1) by lia. exact H0.
  + replace (spZ (x_regs cx) - 16) with (spZ (x_regs cx) - 8 * 2) by lia. exact H1.
  + exact Hra4.
  + lia.
  + pose proof (Z.div_mod (spZ (x_regs cx)) 16 ltac:(lia)) as Hd. rewrite Hal16, Z.add_0_r in Hd.
    rewrite Hd. replace (16 * (spZ (x_regs cx) / 16)) with (2 * (spZ (x_regs cx) / 16) * 8) by ring.
    apply Z.mod_mul. lia.
  + lia.
  + lia.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* what a step keeps that a cut reads: the stack [S1, SP0) (saved registers, slots), the frame's header words and
   flag word, its 36 shadow bytes, and every image byte the runtime does not own *)
Definition s17k_kept (cx : lcx) (W : world SEGS) mem (W2 : world SEGS) mem2 : Prop :=
  (forall a, x_s1 cx <= a < x_sp0 cx -> rdW W2 mem2 a = rdW W mem a) /\
  (forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> rdW W2 mem2 a = rdW W mem a) /\
  (forall i, 0 <= i < 36 -> rdW W2 mem2 (x_sh cx + i) = rdW W mem (x_sh cx + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     rdW W2 mem2 a = rdW W mem a).
Lemma s17k_kept_all : forall cx (W W2 : world SEGS) mem mem2,
  (forall a, rdW W2 mem2 a = rdW W mem a) -> s17k_kept cx W mem W2 mem2.
Proof. intros cx W W2 mem mem2 H. repeat split; intros; apply H. Qed.
Lemma s17k_kept_trans : forall cx (W W1 W2 : world SEGS) mem mem1 mem2,
  s17k_kept cx W mem W1 mem1 -> s17k_kept cx W1 mem1 W2 mem2 -> s17k_kept cx W mem W2 mem2.
Proof.
intros cx W W1 W2 mem mem1 mem2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4).
split; [intros a Ha; rewrite (B1 a Ha); exact (A1 a Ha)|].
split; [intros a Ha; rewrite (B2 a Ha); exact (A2 a Ha)|].
split; [intros i Hi; rewrite (B3 i Hi); exact (A3 i Hi)|].
intros a H1 H2 H3. rewrite (B4 a H1 H2 H3). exact (A4 a H1 H2 H3).
Qed.

(* the frame part of a cut at a later state of the journal *)
Lemma s17k_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k2 o2,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  s17k_J cx ly2 S2 W2 mem2 md2 k2 -> s17k_fregs regs regs2 ->
  s17k_kept cx W mem W2 mem2 -> sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o2) ->
  lt_frame B cx ly2 S2 W2 regs2 mem2 md2 k2 o2.
Proof.
intros cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o2 HB HF HJ2 P (KS & KF & _ & _) HSH2.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & HSB & _).
split; [exact HJ2|].
split; [exact (eq_trans (P 2 ltac:(lia)) R2)|].
split; [exact (eq_trans (P 3 ltac:(lia)) R3)|].
split; [exact (eq_trans (P 4 ltac:(lia)) R4)|].
split; [exact (eq_trans (P 8 ltac:(lia)) R8)|].
split; [exact (eq_trans (P 9 ltac:(lia)) R9)|].
split.
{ intros i r Hi. rewrite <- (HSV i r Hi). apply rdword_ext. intros q Hq.
  assert (Hil : (i < 13)%nat) by (apply (proj1 (nth_error_Some LT_SAVED i)); rewrite Hi; discriminate).
  apply KS. lia. }
split; [rewrite <- HH0; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH8; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HH16; apply rdword_ext; intros q Hq; apply KF; lia|].
split; [rewrite <- HFL; apply rdword_ext; intros q Hq; apply KF; unfold LT_FLAGW; lia|].
split; [rewrite <- HSB; apply rdword_ext; intros q Hq; apply KS; lia|].
exact HSH2.
Qed.
Lemma s17k_fsh_kept : forall cx (W W2 : world SEGS) mem mem2 o,
  s17k_kept cx W mem W2 mem2 -> sa_zs (rdW W mem) (x_sh cx) (lt_fsh o) -> sa_zs (rdW W2 mem2) (x_sh cx) (lt_fsh o).
Proof.
intros cx W W2 mem mem2 o (_ & _ & KH & _) H i Hi. rewrite lt_fsh_len in Hi.
rewrite (KH (Z.of_nat i)) by lia. exact (H i ltac:(rewrite lt_fsh_len; exact Hi)).
Qed.
(* slots of S1 at a later state that keeps the stack *)
Lemma s17k_slots_kept : forall cx (W W2 : world SEGS) mem mem2 L,
  lt_base B MT cx -> lt_slots cx (rdW W mem) L -> (forall o v, In (o, v) L -> 0 <= o <= 312) ->
  s17k_kept cx W mem W2 mem2 -> lt_slots cx (rdW W2 mem2) L.
Proof.
intros cx W W2 mem mem2 L HB HS HL (KS & _) o v Hin.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof (HL o v Hin) as Ho.
rewrite <- (HS o v Hin). apply rdword_ext. intros q Hq. apply KS. lia.
Qed.

(* the budget around a free: an event is left, the meter allows a free, and the next cut's budget *)
Hypothesis MTL : ameter_laws MT.
Lemma s17k_bud_free : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx -> s17k_J cx ly S W mem md k -> lt_bud MT cx S k acc rem -> 1 <= rem ->
  st_nev S < EV_MAX /\ mo_ok MT S (mo_free MT) /\
  (forall S2, mo_le MT S S2 (mo_free MT) -> lt_bud MT cx S2 (k + 1) (acc + mo_free MT) (rem - 1)).
Proof.
intros cx ly S W mem md k acc rem HB HJ (Hk & Hrem & Hkr & Hle & Hacc & Hxm) Hr.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _ & HMO).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
pose proof (mo_free_nonneg MT MTL) as Hf0. pose proof (mo_malloc_nonneg MT MTL 65536 ltac:(lia)) as Hm0.
assert (HU : mo_free MT <= LT_U MT) by (unfold LT_U; lia).
assert (HU0 : 0 <= LT_U MT) by (unfold LT_U; lia).
split; [lia|].
split.
{ apply (mok_station MT (x_S cx) S (XM_LTOI MT (x_pl cx)) acc (mo_free MT) MTL HMO Hle Hf0). nia. }
intros S2 HM. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hle HM)|]. split; [lia|]. nia.
Qed.
(* across a call of no allocator event that changes only the frames (sa_noalloc): the same budget *)
Hypothesis MTFL : ameter_fs_laws MT.
Lemma s17k_bud_noalloc : forall cx S k acc rem f, lt_bud MT cx S k acc rem -> lt_bud MT cx (set_fs f S) k acc rem.
Proof.
intros cx S k acc rem f (Hk & Hrem & Hkr & Hle & Hacc & Hxm).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact (mo_le_set_fs_r MT MTFL _ _ f _ Hle)|]. split; lia.
Qed.
(* the events left at a cut: st_nev S <= EV_MAX *)
Lemma s17k_nev : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx -> s17k_J cx ly S W mem md k -> lt_bud MT cx S k acc rem -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W mem md k acc rem HB HJ (Hk & Hrem & Hkr & _).
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEV & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & Hnev & _). lia.
Qed.

(* ---- the cut after a step: frame, image, blocks and budget ---- *)
Hypothesis IMGS : s10_img.
Hypothesis BSYM : AF0m.SegBSyms B.
Lemma s17k_core_step : forall cx ly S (W : world SEGS) regs mem md k acc rem o O ly2 S2 (W2 : world SEGS) regs2 mem2 md2
  k2 acc2 rem2 O2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  s17k_J cx ly2 S2 W2 mem2 md2 k2 -> s17k_fregs regs regs2 -> s17k_kept cx W mem W2 mem2 ->
  Permutation (ablocks B ly2 S2) (O2 ++ x_bl0 B cx) -> lt_bud MT cx S2 k2 acc2 rem2 ->
  lt_core B MT cx ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 o O2.
Proof.
intros cx ly S W regs mem md k acc rem o O ly2 S2 W2 regs2 mem2 md2 k2 acc2 rem2 O2 HB (HF & HI & _ & _) HJ2 HP HK HP2 HBUD.
pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH).
split; [exact (s17k_frame_kept cx ly S W regs mem md k o ly2 S2 W2 regs2 mem2 md2 k2 o HB HF HJ2 HP HK
  (s17k_fsh_kept cx W W2 mem mem2 o HK HSH))|].
split; [|split; [exact HP2 | exact HBUD]].
destruct HK as (_ & _ & _ & KI).
exact (s10_lt_img_kept B IMGS BSYM cx W2 mem2 (rdW W mem) (proj1 HJ2) KI HI).
Qed.

(* the frame (3, x_fpos cx) at a state of the journal: live, at x_fr cx *)
Lemma s17k_frame_at : forall cx ly S (W : world SEGS) mem md k, s17k_J cx ly S W mem md k ->
  In (3, x_fpos cx) (frames S) /\ frame_addr ly 3 (x_fpos cx) = x_fr cx /\
  4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\ x_fr cx mod 32 = 0 /\
  (forall a, x_fr cx <= a < x_fr cx + 512 -> apresent (w_H W) mem a) /\
  (forall i, 0 <= i < 64 -> apresent (w_H W) mem (x_sh cx + i)).
Proof.
intros cx ly S W mem md k HJ.
destruct HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Hin : In (3, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly 3 (x_fpos cx) = x_fr cx) by (unfold x_fr, frame_addr, LT_FCLS; rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H4 & Hc & Ha).
destruct (al_frames _ _ LAWS ly S W mem md 3 (x_fpos cx) HAR Hin) as (H32 & _ & Hp & Hsp).
rewrite EFA in H4, Hc, Ha, H32, Hp, Hsp. change (fs_frame_bytes 3) with 512 in H4, Hc, Ha, Hp, Hsp.
change (512 / 8) with 64 in Hsp.
split; [exact Hin|]. split; [exact EFA|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Ha|].
split; [exact H32|]. split; [intros a Hr; exact (proj1 (Hp a Hr))|].
intros i Hi. exact (proj1 (Hsp i Hi)).
Qed.
(* at every cut the class-3 frame is the only live frame *)
Lemma s17k_frames : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx -> s17k_J cx ly S W mem md k ->
  frames S = [(LT_FCLS, x_fpos cx)].
Proof.
intros cx ly S W mem md k HB HJ.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HFR0 & _).
destruct HJ as (_ & _ & _ & _ & _ & Hfrs & _). rewrite Hfrs, HFR0. reflexivity.
Qed.

(* a call's acall_kept (the free wrapper's post) gives what a cut keeps, when the bytes the call may change (E)
   miss the frame and its shadow *)
Lemma s17k_kept_of_acall : forall cx ly S (W : world SEGS) mem md k (W2 : world SEGS) mem2 slo (Ex : Z -> Prop),
  lt_base B MT cx -> s17k_J cx ly S W mem md k ->
  acall_kept SEGS B ly S W mem W2 mem2 slo (x_s1 cx) Ex ->
  (forall a, x_fr cx <= a < x_fr cx + 512 -> ~ Ex a) -> (forall i, 0 <= i < 36 -> ~ Ex (x_sh cx + i)) ->
  s17k_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k W2 mem2 slo Ex HB HJ (K1 & _ & K3 & K4 & _) HEF HES.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s17k_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & _).
split; [intros a Ha; apply K1; lia|].
split.
{ intros a Ha. apply (K4 3 (x_fpos cx) a Hin); [left | apply HEF; lia].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia. }
split.
{ intros i Hi. apply (K4 3 (x_fpos cx) _ Hin); [right | apply HES; lia].
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh. lia. }
exact K3.
Qed.

(* a live block misses the frame and the frame's shadow *)
Lemma s17k_blk_apart : forall cx ly S (W : world SEGS) mem md k pa n,
  s17k_J cx ly S W mem md k -> In (pa, n) (ablocks B ly S) ->
  (forall a, x_fr cx <= a < x_fr cx + 512 -> ~ (pa <= a < pa + req_size n)) /\
  (forall i, 0 <= i < 36 -> ~ (pa <= x_sh cx + i < pa + req_size n)).
Proof.
intros cx ly S W mem md k pa n HJ Hb.
pose proof (proj1 HJ) as HAR.
destruct (s17k_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md pa n 3 (x_fpos cx) HAR Hb Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. change (fs_frame_bytes 3) with 512 in Hd.
destruct (al_blocks _ _ LAWS ly S W mem md pa n HAR Hb) as (_ & Hp4 & Hpc & Hpapp & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as Hrq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (shadow_addr_bounds (x_fr cx) ltac:(lia)) as Hsh.
split; [intros a Ha Hab; lia|].
intros i Hi Hab. unfold x_sh, shadow_addr, SHADOW_OFF in Hab. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
clear Hsh. lia.
Qed.

(* the frame and its shadow sit below the stack window of any call from S1 (all below the allocator's ceiling) *)
Lemma s17k_low : forall cx ly S (W : world SEGS) mem md k, lt_base B MT cx -> s17k_J cx ly S W mem md k ->
  x_fr cx + 512 + ASTACK + 352 <= x_s1 cx /\ x_sh cx + 64 + ASTACK + 352 <= x_s1 cx /\
  alloc_ceiling + 32768 - 352 <= x_s1 cx.
Proof.
intros cx ly S W mem md k HB HJ.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s17k_frame_at cx ly S W mem md k HJ) as (_ & _ & H4 & Hc & _).
pose proof asan_consts as (C1 & _).
unfold x_sh, shadow_addr, SHADOW_OFF, ASTACK. lia.
Qed.

(* a call's inner journal from S1 whose footprint lies in live blocks gives what a cut keeps (the image bytes by
   the journal's image clause: a block holds no image byte) (_s24's s24_kept_of_journal without its n cell) *)
Lemma s17k_kept_of_journal : forall cx ly S (W : world SEGS) mem md k STK1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1,
  lt_base B MT cx -> s17k_J cx ly S W mem md k ->
  ajournal SEGS B STK1 (x_s1 cx) FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 -> 0 <= STK1 <= ASTACK ->
  (forall a, inFP FP1 a -> exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n) ->
  s17k_kept cx W mem W2 mem2.
Proof.
intros cx ly S W mem md k STK1 FP1 ly2 S2 W2 mem2 md2 k1 HB HJ HJ1 HS1 HFP.
pose proof (s17k_nums cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
destruct (s17k_low cx ly S W mem md k HB HJ) as (L1 & L2 & L3).
pose proof (proj1 HJ) as HAR.
destruct (s17k_frame_at cx ly S W mem md k HJ) as (Hin & EFA & H4 & Hc & Happ & H32 & _).
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLOW : forall a, inFP FP1 a -> 4096 <= a < alloc_ceiling).
{ intros a Ha. destruct (HFP a Ha) as (b & n & Hb & Hr).
  destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hb) as (_ & Hb4 & Hbc & _). lia. }
assert (HNF : forall a, x_fr cx <= a < x_fr cx + 24 \/ x_fr cx + 504 <= a < x_fr cx + 512 -> ~ inFP FP1 a).
{ intros a Ha Hf. destruct (HFP a Hf) as (b & n & Hb & Hr).
  destruct (s17k_blk_apart cx ly S W mem md k b n HJ Hb) as (HA & _). exact (HA a ltac:(lia) Hr). }
assert (HNS : forall i, 0 <= i < 36 -> ~ inFP FP1 (x_sh cx + i)).
{ intros i Hi Hf. destruct (HFP _ Hf) as (b & n & Hb & Hr).
  destruct (s17k_blk_apart cx ly S W mem md k b n HJ Hb) as (_ & HA). exact (HA i Hi Hr). }
split.
{ intros a Ha. apply F1; [lia | lia | intros Hf; pose proof (HLOW a Hf); lia]. }
split.
{ intros a Ha. apply (F4 3 (x_fpos cx) a Hin); [left | exact (HNF a Ha)].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3) with 512. lia. }
split.
{ intros i Hi. apply (F4 3 (x_fpos cx) _ Hin); [right | exact (HNS i Hi)].
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes 3 / 8) with 64. unfold x_sh. lia. }
intros a Hi Ho He. apply F3; [exact Hi | exact Ho | exact He |].
apply fp_spares_closed.
- intros (r & Hr & Hr0). assert (Hf : inFP FP1 0) by (exists r; split; [exact Hr | exact Hr0]).
  pose proof (HLOW 0 Hf). lia.
- intros Hf. destruct (HFP a Hf) as (b & n & Hb & Hr).
  exact (blk_img SEGS B LAWS ly S W mem md b n a HAR Hb Hr Hi).
Qed.

(* a block the call's footprint misses keeps its bytes (the journal's block clause) *)
Lemma s17k_blk_kept : forall ly S (W : world SEGS) mem md STK1 sp1 FP1 ly2 S2 (W2 : world SEGS) mem2 md2 k1 p n,
  AR SEGS B ly S W mem md ->
  ajournal SEGS B STK1 sp1 FP1 ly S W mem md [] ly2 S2 W2 mem2 md2 k1 ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly2 S2) ->
  (forall a, inFP FP1 a -> exists b m, In (b, m) (ablocks B ly S) /\ (b, m) <> (p, n) /\ b <= a < b + req_size m) ->
  forall i, 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i).
Proof.
intros ly S W mem md STK1 sp1 FP1 ly2 S2 W2 mem2 md2 k1 p n HAR HJ1 Hp Hp2 HFP i Hi.
destruct HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 p n i Hp Hp2 Hi). intros Hf. destruct (HFP _ Hf) as (b & m & Hb & Hne & Hr).
pose proof (sep_blocks SEGS B LAWS ly S W mem md b m p n HAR Hb Hp Hne) as Hd. unfold zdisjoint in Hd.
cbn [fst snd] in Hd. lia.
Qed.
End e.

(* ================================== one free: 0x8540c (mv a0, s7; jal free) ================================== *)
(* the symbolic seed of the two instructions: every register its own atom, no region, no fact, no shadow entry
   (fuzz_command's LLVMFuzzerTestOneInput_Karity.v ka_seed_loc; _s24's s24_seed) *)
Definition S17_FREE : Z := 0x6d8.
Definition s17k_ss (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition S17x : sv := SOff 9 0.
Definition s17k_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Lemma s17k_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s17k_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))) /\
  sh_ok SEGS S17x [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (Eimg (Ereg regs [])) /\ env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])) /\
  (forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (Eimg (Ereg regs [])) n = getr regs rr).
Proof.
intros W regs mem pc.
split.
- unfold s17k_ss. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + exact I.
  + unfold facts_ok. cbn. tauto.
- split; [apply Forall_nil|].
  split; [apply Eimg_env|].
  split; [split; [intros i Hi; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]|].
  intros n rr Hn. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.

Section fr.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis TL : PALib B.
(* one free: the run from 0x8540c (mv a0, s7) to the free wrapper, the wrapper's rule, and back at 0x85414; the
   continuation gets the journal at k + 1, the registers kept, the block gone, the frames, what a cut keeps, the
   other blocks' bytes and the meter step (_s24's s24_free at this pc and register) *)
Lemma s17k_free : forall cx ly S (W : world SEGS) regs mem md k pa n Q,
  lt_base B MT cx -> s17k_J B cx ly S W mem md k ->
  getr regs 2 = w64 (x_s1 cx) -> getr regs 3 = getr (x_regs cx) 3 -> getr regs 4 = getr (x_regs cx) 4 ->
  getr regs 8 = w64 (x_sp0 cx) -> lt_saved cx (rdW W mem) -> getr regs 23 = w64 pa ->
  In (pa, n) (ablocks B ly S) -> ~ In (pa, n) (x_bl0 B cx) ->
  st_nev S < EV_MAX -> mo_ok MT S (mo_free MT) ->
  (forall ly2 S2 (W2 : world SEGS) regs2 mem2 md2,
     s17k_J B cx ly2 S2 W2 mem2 md2 (k + 1) -> aregs_preserved regs regs2 ->
     (exists l1 l2, ablocks B ly S = l1 ++ (pa, n) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) ->
     frames S2 = frames S -> s17k_kept B cx W mem W2 mem2 -> mo_le MT S S2 (mo_free MT) ->
     (forall p m i, In (p, m) (ablocks B ly S) -> (p, m) <> (pa, n) -> 0 <= i < req_size m ->
        rdW W2 mem2 (p + i) = rdW W mem (p + i)) ->
     SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + (S17_FREE + 8))) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + S17_FREE)) mem (seg_rom SEGS)) md) Q.
Proof.
intros cx ly S W regs mem md k pa n Q HBASE HJ R2 R3 R4 R8 HSV Hpa Hin Hnb0 Hnev MOK HC.
pose proof (paj_run B LAWS) as RUN.
pose proof (s17k_nums B MT cx HBASE) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct (s17k_chain B MT cx ly S W mem md k HBASE HJ HSV) as (ch & HCH).
destruct (s17k_blk_apart B cx ly S W mem md k pa n HJ Hin) as (HAF & HAS).
pose proof HJ as HJ'. unfold s17k_J in HJ'.
pose proof HJ' as (HAR & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBLO.
destruct (s17k_seed W regs mem S17_FREE) as (HS & SHOK & HEI & HAE & EEo).
set (E := Eimg (Ereg regs [])) in *.
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E23 : ew E 23 = getr regs 23) by (apply EEo; reflexivity).
clearbody E. clear EEo.
assert (Hcov : In (pa, n) (ablocks B (x_ly cx) (x_S cx)) -> forall i, 0 <= i < req_size n ->
  inFP (ltoi_PG longlA) (pa + i)) by (intros Hb; exfalso; exact (Hnb0 Hb)).
unfold s17k_ss, S17_FREE in HS.
paj_run_tok RUN HS HJ' SHOK s17k_span; try solve [apply awr_ok_nil].
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
pmkst HS.
rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (2%bv : bv 5) P2.
lazymatch goal with
| HFr : frame_of ?E0 _ (mrestrict _ _) (mrestrict _ ?m1) |- _ =>
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> rdW W m1 a = rdW W mem a)
    by (intros a Ha; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
        [ intros b wlo whi a' Hin' Hrr'; vm_compute in Hin'; destruct Hin' | exact Ha | intros Hff; destruct Hff ])
end.
lazymatch goal with
| |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) _) _ =>
  assert (HPT1 : aregs_preserved regs rT)
    by (eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]);
  assert (HspT : spZ rT = x_s1 cx)
    by (unfold spZ; transitivity (bv_unsigned (w64 (x_s1 cx)));
        [f_equal; exact (eq_trans P2 (eq_trans E2 R2)) | unfold w64; apply unsigned_lit_small; lia]);
  assert (Ha0 : getr rT 10 = w64 pa) by exact (eq_trans P10 (eq_trans E23 Hpa));
  assert (Hgp' : getr rT 3 = w64 (as_gp B))
    by exact (eq_trans (HPT1 3 ltac:(unfold acallee_saved; lia)) (eq_trans R3 Hgp0));
  assert (Htp' : getr rT 4 = w64 (as_tp B))
    by exact (eq_trans (HPT1 4 ltac:(unfold acallee_saved; lia)) (eq_trans R4 Htp0));
  assert (H8' : getr rT 8 = w64 (x_sp0 cx)) by exact (eq_trans (HPT1 8 ltac:(unfold acallee_saved; lia)) R8);
  assert (Hs0 : s0Z rT = x_sp0 cx)
    by (unfold s0Z; transitivity (bv_unsigned (w64 (x_sp0 cx))); [f_equal; exact H8' | unfold w64; apply unsigned_lit_small; lia]);
  assert (HraT : YK0s.ret_ok (getr rT 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]);
  assert (HraZ : 4096 <= raZ rT)
    by (unfold raZ; change (4096 <= bv_unsigned (getr rT (1%bv : bv 5))); rewrite P1; rewrite unsigned_lit_small by lia; lia);
  assert (Hch : chain_pre ly (rdW W mT) rT ch)
    by (eapply achain_chain_pre;
        [ eapply achain_kept with (lo := 0); [exact HCH | lia | rewrite Etop; lia | exact KEEP]
        | rewrite HspT; lia | exact Hs0 | exact HraZ ])
end.
eapply SRr_bind;
  [ lazymatch goal with
    | |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
      exact (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W rT mT STK_LLVMFuzzerTestOneInput (x_sp0 cx)
        (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S dT k pa n
        (x_s1 cx - x_sp0 cx) (getr rT 1) ch HJ' Hin Ha0 ltac:(rewrite HspT; lia)
        ltac:(rewrite Zminus_mod, Hs1al, Hal16; reflexivity) ltac:(lia)
        ltac:(unfold ASTACK, STK_LLVMFuzzerTestOneInput; lia)
        Hgp' Htp' eq_refl HraT Hnev Hch Hcov MOK)
    end
  | ].
cbv beta; intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfr2 & HK2 & MLE & HJin).
rewrite P1. apply (HC ly2 S2 W2 regs2 mem2 md2);
  [ exact HJ2 | exact (aregs_preserved_trans _ _ _ HPT1 HP2) | exact Hbl | exact Hfr2 | | exact MLE | ].
- lazymatch type of HK2 with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
  apply (s17k_kept_trans B cx W W W2 mem mT mem2);
  [ apply s17k_kept_all; exact (s17k_keep_all (w_H W) mem mT KEEP)
  | replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HK2 by lia;
    exact (s17k_kept_of_acall B MT cx ly S W mT mdv k W2 mem2 _ _ HBASE HJ' HK2 HAF HAS) ]
  end.
- intros p m i Hp Hne Hi.
  lazymatch type of HK2 with acall_kept _ _ _ _ _ ?mT _ _ _ _ _ =>
    destruct HK2 as (_ & KB & _);
    rewrite (KB p m i Hp Hi); [exact (s17k_keep_all (w_H W) mem mT KEEP (p + i))|]
  end.
  intros Hx. pose proof (sep_blocks SEGS B LAWS ly S W mem md p m pa n HAR Hp Hin Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.
End fr.

(* ================================== the call of reac_segconf_parse (0x853c4) ================================== *)
Section call.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis HPARSE : forall fx0 : YK11.FPState, reac_segconf_parse_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
(* its return address 0x853c8 *)
Definition S17_PRA : Z := 0x694.
(* the bytes reac_segconf_parse writes outside its window lie in c's block *)
Lemma s17k_fp_parse : forall c a, inFP (seg_spec.RC_PARSE_W c) a -> c <= a < c + seg_spec.SEG_C_SIZE.
Proof.
intros c a (r & Hin & H). unfold seg_spec.RC_PARSE_W in Hin. cbn [In] in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in H;
  unfold seg_spec.RC_N, seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.RC_READING, seg_spec.RC_GEN,
    seg_spec.SEG_C_SIZE in *; lia.
Qed.
Lemma s17k_stk_parse : 0 <= STK_reac_segconf_parse <= ASTACK.
Proof.
pose proof (proj1 (forallb_forall _ _) ltoi_callee_stks_b STK_reac_segconf_parse
  ltac:(unfold LTOI_CALLEE_STKS; cbn [In]; repeat (first [left; reflexivity | right]))) as H.
cbn beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* the call: cl_callSF with the callee's contract at the segment's FP state; the continuation runs at the FP state
   fx1 the callee returned (fxrel fx fx1) and gets the journal (EV 0), the registers kept, what a cut keeps, the
   bytes of every other block, the answer, c's new state and sa_noalloc *)
Lemma s17k_parse : forall cx ly S (W : world SEGS) regs mem md k c t rcs s,
  lt_base B MT cx -> s17k_J B cx ly S W mem md k ->
  getr regs 2 = w64 (x_s1 cx) -> getr regs 3 = getr (x_regs cx) 3 -> getr regs 4 = getr (x_regs cx) 4 ->
  getr regs 8 = w64 (x_sp0 cx) -> lt_saved cx (rdW W mem) -> getr regs 1 = w64 (BASE + S17_PRA) ->
  getr regs 10 = w64 c -> getr regs 11 = w64 t -> 0 <= c < 2 ^ 64 -> 0 <= t < 2 ^ 64 ->
  In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S) -> ~ In (c, seg_spec.SEG_C_SIZE) (x_bl0 B cx) ->
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) ->
  reader_pre SEGS B seg_litA_rc catA gotwA guardA ly S (rdW W mem) c t rcs s ->
  (forall x, In x CROSS_CHECK_LITS -> sa_lit SEGS B (rdW W mem) (seg_litA_rc x) x) ->
  st_nev S <= EV_MAX ->
  (forall (fx1 : YK11.FPState) ly2 S2 (W2 : world SEGS) regs2 mem2 md2, fxrel fx fx1 ->
     s17k_J B cx ly2 S2 W2 mem2 md2 k -> aregs_preserved regs regs2 ->
     s17k_kept B cx W mem W2 mem2 ->
     (forall p n i, In (p, n) (ablocks B ly S) -> (p, n) <> (c, seg_spec.SEG_C_SIZE) -> 0 <= i < req_size n ->
        rdW W2 mem2 (p + i) = rdW W mem (p + i)) ->
     getr regs2 10 = w64 (snd (SegModel.r_parse rcs s)) ->
     sa_rconf (rdW W2 mem2) c (fst (SegModel.r_parse rcs s)) -> sa_noalloc B ly S ly2 S2 ->
     SRr SEGS W2 (mkCfg (@mkst fx1 regs2 (w64 (BASE + S17_PRA)) mem2 (seg_rom SEGS)) md2)
       (lt_post (fx := fx1) B MT cx)) ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_segconf_parse)) mem (seg_rom SEGS)) md) (lt_post B MT cx).
Proof.
intros cx ly S W regs mem md k c t rcs s HB HJ R2 R3 R4 R8 HSV R1 R10 R11 Hc64 Ht64 HCin HCn HARO HRP HXL Hnev HK.
pose proof (s17k_nums B MT cx HB) as (Hal16 & Hs1al & Hs1 & Hceil & H47 & Htop & Htop2).
pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp0 & Htp0 & _).
destruct (s17k_chain B MT cx ly S W mem md k HB HJ HSV) as (ch & HCH).
pose proof (s17k_frames B MT cx ly S W mem md k HB HJ) as HFRS.
pose proof s17k_stk_parse as HSP.
pose proof asan_consts as (C1 & _).
assert (Hsp' : spZ regs = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (Hch' : achain ly (rdW W mem) (x_sp0 cx + (x_s1 cx - x_sp0 cx)) (s0Z regs) ch).
{ replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) by lia.
  unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH. }
pose proof pa_B_ok as (HB0 & HB1 & _). pose proof pa_base_lo as HBLO.
assert (Hraw : YK0s.ret_ok (getr regs 1)) by (rewrite R1; unfold w64; apply ret_ok_codeptr_v; [unfold S17_PRA; lia | reflexivity]).
assert (Hra4 : 4096 <= bv_unsigned (getr regs 1)).
{ rewrite R1. unfold w64, S17_PRA. rewrite unsigned_lit_small by lia. lia. }
assert (HROOM : sa_room_n 2 S) by (unfold sa_room_n; rewrite HFRS; cbn [length]; lia).
eapply SRr_bind.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_reac_segconf_parse)) STK_LLVMFuzzerTestOneInput
    (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S md k
    STK_reac_segconf_parse (seg_spec.RC_PARSE_W c) EV_reac_segconf_parse (x_s1 cx - x_sp0 cx) (getr regs 1) ch
    (fun ly' S' (W' : world SEGS) (regs' : bvmap 5 word) mem' md' =>
       getr regs' 10 = w64 (snd (SegModel.r_parse rcs s)) /\
       sa_rconf (rdW W' mem') c (fst (SegModel.r_parse rcs s)) /\ sa_noalloc B ly S ly' S')
    HJ Hsp' ltac:(rewrite Zminus_mod, Hs1al, Hal16; reflexivity) ltac:(lia) ltac:(lia)
    ltac:(unfold ASTACK, STK_LLVMFuzzerTestOneInput in *; lia)
    ltac:(rewrite R3; exact Hgp0) ltac:(rewrite R4; exact Htp0) eq_refl Hraw Hra4 Hch').
  - intros HPRE1. exact (HPARSE fx ly S W regs mem md ch c t rcs s HPRE1 HARO R10 Hc64 R11 Ht64 HRP HXL HROOM
      ltac:(unfold EV_reac_segconf_parse; lia)).
  - intros a Ha. right. exists c, seg_spec.SEG_C_SIZE. split; [exact HCin|]. split; [exact HCn|].
    pose proof (s17k_fp_parse c a Ha). rewrite (s17k_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)). lia. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & H01 & -> & HJ2 & HJ1 & HP & (Ha0 & Hrc & Hna)).
replace (k + EV_reac_segconf_parse) with k in HJ2 by (unfold EV_reac_segconf_parse; lia).
replace (x_sp0 cx + (x_s1 cx - x_sp0 cx)) with (x_s1 cx) in HJ1 by lia.
assert (HFP : forall a, inFP (seg_spec.RC_PARSE_W c) a ->
  exists b n, In (b, n) (ablocks B ly S) /\ b <= a < b + req_size n).
{ intros a Ha. exists c, seg_spec.SEG_C_SIZE. split; [exact HCin|].
  pose proof (s17k_fp_parse c a Ha). rewrite (s17k_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)). lia. }
pose proof (s17k_kept_of_journal B MT cx ly S W mem md k _ _ ly2 S2 W2 mem2 md2 _ HB HJ HJ1 HSP HFP) as HKP.
unfold lt_post. apply (srr_apost_baseF_lift SEGS fx1); [exact H01|].
rewrite R1. apply (HK fx1 ly2 S2 W2 regs2 mem2 md2 H01 HJ2 HP HKP); [| exact Ha0 | exact Hrc | exact Hna].
intros p n i Hp Hne Hi.
apply (s17k_blk_kept B ly S W mem md _ _ _ ly2 S2 W2 mem2 md2 _ p n (proj1 HJ) HJ1 Hp); [| | exact Hi].
- destruct Hna as (HPm & _). exact (Permutation_in _ (Permutation_sym HPm) Hp).
- intros a Ha. exists c, seg_spec.SEG_C_SIZE. split; [exact HCin|]. split; [intros E; apply Hne; rewrite E; reflexivity|].
  pose proof (s17k_fp_parse c a Ha). rewrite (s17k_req seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)). lia.
Qed.
End call.
End f.
End d.
