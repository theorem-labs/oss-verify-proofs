(* Segment L02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain): the memory facts the inner walk
   (Prog/Seg/L02W.v) carries from 0x13984 to 0x13ad8, how each callee's write set keeps them, and the callee
   premises they give.
   - l02_static: the address facts of L02_mem (the frame, the three blocks, the text's source) and the turn's text
     bounds of L02_model, none of which a write changes;
   - l02_env: the facts of the memory every later call needs (mem_inv, task_mem, the stack-protector cells, the two
     .data.rel.ro tables, the callee stack [S - 65472, S - 208), main's frame cells 0x20 and 0x30, the blocks'
     writability, the 4 bytes after the mconf block); env_tr keeps them across a write set inside A_all;
   - txt_at / lab_ok: the text at t and the label (exactly the bytes a word-at-a-time reader takes);
   - the premises of m_file, reac_segconf_parse_file, reac_segconf_parse and m_refuse at main's sp S - 208 with
     every callee's lo := S - 65472 (= S - 65536 + 64: every heap block ends at or below S - 65536, so a text read
     with its 8-byte slack stays below lo);
   - L02_J: the statement of the walk from the join 0x139f0 to L02_post.
   Every heap block is outside [0x10000, 0x54000) (blk_noimg: the image's reserved segments cover exactly that
   range), where the stack-protector cells, the tables and longl lie.
   Segment lemma of LLVMFuzzerTestOneInput's walk: L02's memory facts. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env m_file_c
  printf_facts_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require m_refuse_c reac_segconf_parse_file_c
  reac_segconf_parse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import L02M L02D.
Import ListNotations.
Open Scope Z_scope.

(** ** The image's reserved segments: [0x10000, 0x54000) exactly *)
Definition ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => cov L' (if a <=? cur then Z.max cur b else cur) end.

(* cov_in is Prog/snprintf.v's. *)
Lemma cov_in : forall L cur x, cur <= x < cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma resv_cov : cov (ivs (segments_reserved rsegs)) 0x10000 = 0x54000.
Proof. vm_compute. reflexivity. Qed.

Lemma resv_cover : forall x, 0x10000 <= x < 0x54000 -> exists s, In s (segments_reserved rsegs) /\
  bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s).
Proof.
  intros x Hx. rewrite <- resv_cov in Hx. destruct (cov_in _ _ _ Hx) as (a & b & Hin & Hab).
  unfold ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s & Es & Hs). injection Es as Ea Eb.
  exists s. split; [exact Hs | lia].
Qed.

Lemma resv_rng : forall s, In s (segments_reserved rsegs) ->
  0x10000 <= bv_unsigned (fst s) /\ bv_unsigned (fst s) + bv_unsigned (snd s) <= 0x54000.
Proof.
  assert (H : forallb (fun s : word * word => (0x10000 <=? bv_unsigned (fst s)) &&
                (bv_unsigned (fst s) + bv_unsigned (snd s) <=? 0x54000)) (segments_reserved rsegs) = true)
    by (vm_compute; reflexivity).
  intros s Hs. rewrite forallb_forall in H. specialize (H s Hs). apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** A block no reserved segment covers lies wholly below 0x10000 or at or above 0x54000. *)
Lemma noimg_bound : forall a n, blk_noimg rsegs a n -> 0 <= a -> 0 < n -> a + n <= 0x10000 \/ 0x54000 <= a.
Proof.
  intros a n F Ha Hn.
  destruct (Z.lt_ge_cases a 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (a + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (resv_cover 0x10000 ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F (0x10000 - a) ltac:(lia) s Hs). replace (a + (0x10000 - a)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases a 0x54000) as [H2|H2]; [|right; exact H2].
    destruct (resv_cover a ltac:(lia)) as (s & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(** Above the image no reserved segment reaches. *)
Lemma noimg_hi : forall D n, 0x54000 <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs Hr. pose proof (resv_rng s Hs). lia.
Qed.

Lemma blk_noimg_hi : forall D n, 0x54000 <= D -> blk_noimg rsegs D n.
Proof. exact noimg_hi. Qed.

(** ** Bytes *)
Lemma zs_zb : forall l, Forall (fun x => 0 <= x < 256) l -> zs (zb l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|]. inversion H; subst.
  unfold zs, zb in *. cbn [map]. f_equal; [|apply IH; assumption].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros l. apply length_map. Qed.

(** The u16 bound of the text and the label as a Z fact (the nat literal 65535 is abstract to lia). *)
Lemma nat_le_65535 : forall n, (n <= 65535)%nat -> Z.of_nat n <= 65535.
Proof. intros n H. apply Nat2Z.inj_le in H. exact H. Qed.
Lemma nat_le_of : forall n, Z.of_nat n <= 65535 -> (n <= 65535)%nat.
Proof. intros n H. apply Nat2Z.inj_le. exact H. Qed.

Lemma Forall_byte : forall l, Forall (fun x => 0 < x < 256) l -> Forall (fun x => 0 <= x < 256) l.
Proof. intros l H. rewrite Forall_forall in *. intros x Hx. specialize (H x Hx). lia. Qed.

Lemma Forall_nul : forall l, Forall (fun x => 0 < x < 256) l -> ~ In 0 l.
Proof. intros l H Hin. rewrite Forall_forall in H. specialize (H 0 Hin). lia. Qed.

Lemma bytes_at_out : forall W m m' a bs, bytes_at rsegs m a bs -> munch W m m' ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) -> bytes_at rsegs m' a bs.
Proof.
  intros W m m' a bs (Ha & Hl & H) Hm Ho. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite Hm; [apply H; exact Hi|]. rewrite wa_unsigned by lia. apply Ho. lia.
Qed.

Lemma mrd_out : forall W m m' a, munch W m m' -> 0 <= a < 2 ^ 64 -> outside W a ->
  mrd rsegs m' (wa a) = mrd rsegs m (wa a).
Proof. intros W m m' a Hm Ha Ho. unfold mrd. rewrite Hm; [reflexivity|]. rewrite wa_unsigned by lia. exact Ho. Qed.

Lemma bytes_at_sub : forall m a bs k l, bytes_at rsegs m a bs -> (k + l <= length bs)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
  intros m a bs k l H Hl.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn l (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** A store as a write set. *)
Lemma munch_store : forall m a bs, 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  munch [(a, a + Z.of_nat (length bs))] m (write_to_mem m (wa a) bs).
Proof.
  intros m a bs H1 H2. apply munch_write; [apply munch_refl | lia | lia |]. cbn [inside]. left. lia.
Qed.

(** task_mem after a write set below TASK_SIZE. *)
Lemma task_mem_out : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 2 ^ 64 -> x < TASK_SIZE \/ outside W x) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' TM MU H a b Ha.
  pose proof (bv_unsigned_in_range 64 a) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  destruct (H (bv_unsigned a) R) as [L|O]; [right; exact L|].
  rewrite (MU a O) in Ha. exact (TM a b Ha).
Qed.

Lemma TASK_SIZE_val : TASK_SIZE = 0x800000000000.
Proof. vm_compute. reflexivity. Qed.

(** stk gives a writable byte range. *)
Lemma stk_rw : forall m lo hi a n, stk rsegs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m lo hi a n H H1 H2.
  destruct (stk_split rsegs m lo (a + Z.of_nat n) hi H ltac:(destruct H as (? & ? & _); lia)) as [H3 _].
  destruct (stk_carve rsegs m lo (a + Z.of_nat n) n H3 ltac:(lia)) as [_ (junk & R)].
  replace (a + Z.of_nat n - Z.of_nat n) with a in R by lia. exists junk. exact R.
Qed.

(** ** The address facts *)
Definition l02_static (S c mm t nt src : Z) (s : list Z) : Prop :=
  S mod 16 = 0 /\ 2 ^ 40 <= S - 65536 /\ S <= 2 ^ 47 /\
  (forall a, S - 65536 <= a < S -> seg_rom rsegs (wa a) = None) /\
  0 < c /\ c mod 16 = 0 /\ blk_noimg rsegs c SEG_C_SIZE /\ c + SEG_C_SIZE <= S - 65536 /\
  0 < mm /\ mm mod 16 = 0 /\ blk_noimg rsegs mm SEG_M_SIZE /\ mm + SEG_M_SIZE <= S - 65536 /\
  0 < t /\ t mod 16 = 0 /\ blk_noimg rsegs t nt /\ t + nt <= S - 65536 /\
  nt = Z.of_nat (length s) + 1 /\
  apart t nt mm (mm + SEG_M_SIZE) /\ apart t nt c (c + SEG_C_SIZE) /\ apart mm SEG_M_SIZE c (c + SEG_C_SIZE) /\
  apart t nt 0x32ac0 (0x32ac0 + 128) /\ apart mm SEG_M_SIZE 0x32ac0 (0x32ac0 + 128) /\
  apart c SEG_C_SIZE 0x32ac0 (0x32ac0 + 128) /\
  0 <= src /\ apart src (Z.of_nat (length s)) t (t + nt) /\
  Forall (fun x => 0 < x < 256) s /\ (length s <= 65535)%nat.

Ltac st_dst H :=
  destruct H as (HS16 & HSlo & HShi & HROM & Hc0 & Hc16 & Hcn & Hcb & Hm0 & Hm16 & Hmn & Hmb & Ht0 & Ht16 & Htn &
                 Htb & Hnt & Atm & Atc & Amc & Atl & Aml & Acl & Hsrc & Ast & HsF & HsL).

(** The numeric core of the static facts: the three blocks as multiples of 16 outside the image, S a multiple of
    16 above 2^40 + 65536. *)
Definition l02_num (S c mm t nt : Z) : Prop :=
  (exists k, S = 16 * k) /\ 2 ^ 40 <= S - 65536 /\ S <= 2 ^ 47 /\
  0 < c /\ (exists k, c = 16 * k) /\ (c + SEG_C_SIZE <= 0x10000 \/ 0x54000 <= c) /\ c + SEG_C_SIZE <= S - 65536 /\
  0 < mm /\ (exists k, mm = 16 * k) /\ (mm + SEG_M_SIZE <= 0x10000 \/ 0x54000 <= mm) /\
  mm + SEG_M_SIZE <= S - 65536 /\
  0 < t /\ (exists k, t = 16 * k) /\ (t + nt <= 0x10000 \/ 0x54000 <= t) /\ t + nt <= S - 65536 /\ 1 <= nt /\
  apart t nt mm (mm + SEG_M_SIZE) /\ apart t nt c (c + SEG_C_SIZE) /\ apart mm SEG_M_SIZE c (c + SEG_C_SIZE) /\
  apart t nt 0x32ac0 (0x32ac0 + 128) /\ apart mm SEG_M_SIZE 0x32ac0 (0x32ac0 + 128) /\
  apart c SEG_C_SIZE 0x32ac0 (0x32ac0 + 128).

Lemma mod16_ex : forall x, x mod 16 = 0 -> exists k, x = 16 * k.
Proof. intros x H. exists (x / 16). pose proof (Z.div_mod x 16 ltac:(lia)). lia. Qed.

Lemma st_num : forall S c mm t nt src s, l02_static S c mm t nt src s -> l02_num S c mm t nt.
Proof.
  intros S c mm t nt src s HST. st_dst HST.
  unfold l02_num. refine (conj (mod16_ex _ HS16) (conj HSlo (conj HShi _))).
  refine (conj Hc0 (conj (mod16_ex _ Hc16) (conj (noimg_bound _ _ Hcn ltac:(lia) ltac:(unfold SEG_C_SIZE; lia))
    (conj Hcb _)))).
  refine (conj Hm0 (conj (mod16_ex _ Hm16) (conj (noimg_bound _ _ Hmn ltac:(lia) ltac:(unfold SEG_M_SIZE; lia))
    (conj Hmb _)))).
  refine (conj Ht0 (conj (mod16_ex _ Ht16) (conj (noimg_bound _ _ Htn ltac:(lia) ltac:(lia)) (conj Htb _)))).
  split; [lia|]. repeat (split; [assumption|]). assumption.
Qed.

Ltac num_dst H :=
  let kS := fresh "kS" in let kc := fresh "kc" in let km := fresh "km" in let kt := fresh "kt" in
  destruct H as ((kS & ES) & NSlo & NShi & Nc0 & (kc & Ec) & Ncimg & Ncb & Nm0 & (km & Em) & Nmimg & Nmb &
                 Nt0 & (kt & Et) & Ntimg & Ntb & Nnt & NAtm & NAtc & NAmc & NAtl & NAml & NAcl);
  unfold apart, SEG_C_SIZE, SEG_M_SIZE in *.

(** ** The write sets
    A_all: what any callee of the segment may write (the callee stack, the label buffer, longl's 120 bytes, the
    three blocks); A_back: what the calls after 0x139f0 write; A_m / A_c: before / at the reader's parse. *)
Definition A_all (S c mm t nt : Z) : list ivl :=
  [(S - 65472, S - 208); (S - 144, S - 104); (0x32ac0, 0x32ac0 + 120); (t, t + nt); (mm, mm + SEG_M_SIZE);
   (c, c + SEG_C_SIZE)].
Definition A_back (S c mm : Z) : list ivl := [(S - 65472, S - 208); (mm, mm + SEG_M_SIZE); (c, c + SEG_C_SIZE)].
Definition A_m (S mm : Z) : list ivl := [(S - 65472, S - 208); (mm, mm + SEG_M_SIZE)].
Definition A_c (S c : Z) : list ivl := [(S - 65472, S - 208); (c, c + SEG_C_SIZE)].

Ltac fp_tac := unfold sub_fp; intros ?x ?Hx; cbn [outside] in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; try exact I; lia.

Lemma sub_fp_trans : forall W1 W2 W3, sub_fp W1 W2 -> sub_fp W2 W3 -> sub_fp W1 W3.
Proof. intros W1 W2 W3 H1 H2 x Hx. apply H1, H2, Hx. Qed.

Lemma A_all_W : forall S c mm t nt, sub_fp (A_all S c mm t nt) (L02_W S c mm t nt).
Proof. intros. unfold A_all, L02_W, L02_FRAME, SA, SEG_PLAIN. cbn [sa_longl]. fp_tac. Qed.

Lemma A_back_all : forall S c mm t nt, sub_fp (A_back S c mm) (A_all S c mm t nt).
Proof. intros. unfold A_back, A_all. fp_tac. Qed.

Lemma A_m_back : forall S c mm, sub_fp (A_m S mm) (A_back S c mm).
Proof. intros. unfold A_m, A_back. fp_tac. Qed.

Lemma A_c_back : forall S c mm, sub_fp (A_c S c) (A_back S c mm).
Proof. intros. unfold A_c, A_back. fp_tac. Qed.

(** Accumulating a callee's write set into L02_W. *)
Lemma munch_acc : forall S c mm t nt m0 m m' W, munch (L02_W S c mm t nt) m0 m -> munch W m m' ->
  sub_fp W (A_all S c mm t nt) -> munch (L02_W S c mm t nt) m0 m'.
Proof.
  intros S c mm t nt m0 m m' W H1 H2 H3. eapply munch_trans; [exact H1|].
  eapply munch_weaken; [|exact H2]. eapply sub_fp_trans; [exact H3 | apply A_all_W].
Qed.

(** ** Outside the write sets *)
(* The image range [0x10000, 0x54000) but longl's bytes. *)
Lemma out_img : forall S c mm t nt x, l02_num S c mm t nt -> 0x10000 <= x < 0x54000 ->
  ~ (0x32ac0 <= x < 0x32ac0 + 120) -> outside (A_all S c mm t nt) x.
Proof. intros S c mm t nt x HN Hx Hl. num_dst HN. cbn [A_all outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.

(* Main's frame above the callee stack and below the label buffer: [S - 208, S - 144). *)
Lemma out_frame : forall S c mm t nt x, l02_num S c mm t nt -> S - 208 <= x < S - 144 ->
  outside (A_all S c mm t nt) x.
Proof. intros S c mm t nt x HN Hx. num_dst HN. cbn [A_all outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.

(* The 4 bytes after the mconf block. *)
Lemma out_mslack : forall S c mm t nt x, l02_num S c mm t nt -> mm + SEG_M_SIZE <= x < mm + SEG_M_SIZE + 4 ->
  outside (A_all S c mm t nt) x.
Proof. intros S c mm t nt x HN Hx. num_dst HN. cbn [A_all outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.

(* The text with its slack, up to the next 8-byte boundary after t + nt. *)
Lemma out_txt : forall S c mm t nt x, l02_num S c mm t nt -> t <= x < t + nt + (- (t + nt)) mod 8 ->
  outside (A_back S c mm) x.
Proof.
  intros S c mm t nt x HN Hx. num_dst HN. cbn [A_back outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *.
  assert (R : 0 <= (- (t + nt)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (R2 : exists q, t + nt + (- (t + nt)) mod 8 = 8 * q).
  { exists ((t + nt) / 8 + (if (t + nt) mod 8 =? 0 then 0 else 1)).
    pose proof (Z.div_mod (t + nt) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (t + nt) 8 ltac:(lia)).
    destruct (Z.eqb_spec ((t + nt) mod 8) 0) as [E|E].
    - replace (- (t + nt)) with (0 + (- ((t + nt) / 8)) * 8) by lia. rewrite Z.mod_add by lia. cbn. lia.
    - replace (- (t + nt)) with ((8 - (t + nt) mod 8) + (- ((t + nt) / 8) - 1) * 8) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
  destruct R2 as (q & Eq). repeat split; try exact I; lia.
Qed.

(* The c block before the reader's parse; the mconf block at the parse. *)
Lemma out_c_m : forall S c mm t nt x, l02_num S c mm t nt -> c <= x < c + SEG_C_SIZE -> outside (A_m S mm) x.
Proof. intros S c mm t nt x HN Hx. num_dst HN. cbn [A_m outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.
Lemma out_m_c : forall S c mm t nt x, l02_num S c mm t nt -> mm <= x < mm + SEG_M_SIZE -> outside (A_c S c) x.
Proof. intros S c mm t nt x HN Hx. num_dst HN. cbn [A_c outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.

(* longl's 128 bytes and the label buffer, after 0x139f0. *)
Lemma out_lab : forall S c mm t nt x, l02_num S c mm t nt ->
  (0x32ac0 <= x < 0x32ac0 + 128 \/ S - 144 <= x < S - 104) -> outside (A_back S c mm) x.
Proof. intros S c mm t nt x HN Hx. num_dst HN. cbn [A_back outside]. unfold SEG_C_SIZE, SEG_M_SIZE in *. repeat split; try exact I; lia. Qed.

(** ** The memory facts every call after the text copy needs *)
Definition l02_env (S c mm : Z) (m : word -> option byte) : Prop :=
  mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\ ssp_ok m /\ cat_img rsegs m (sa_catalogue SA) /\ words_img m /\
  stk rsegs m (S - 65472) (S - 208) /\
  bytes_at rsegs m (S - 208 + 0x20) (le8 (Z_to_bv 64 (mm + 0x10))) /\
  bytes_at rsegs m (S - 208 + 0x30) (le8 (Z_to_bv 64 c)) /\
  wr_at rsegs m c SEG_C_SIZE /\ wr_at rsegs m mm SEG_M_SIZE /\
  (exists sl, bytes_at rsegs m (mm + SEG_M_SIZE) sl /\ length sl = 4%nat).

Lemma env_tr : forall S c mm t nt m m' W,
  l02_num S c mm t nt -> l02_env S c mm m -> munch W m m' -> sub_fp W (A_all S c mm t nt) ->
  wmono rsegs m m' -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> stk rsegs m' (S - 65472) (S - 208) ->
  l02_env S c mm m'.
Proof.
  intros S c mm t nt m m' W HN (MI & TM & (G1 & g & G2) & CI & WI & ST & F20 & F30 & WC & WM & (sl & SL & SLn))
    MU SF WMo MI' TM' ST'.
  unfold l02_env. refine (conj MI' (conj TM' (conj _ (conj _ (conj _ (conj ST' (conj _ (conj _ _)))))))).
  - split.
    + eapply bytes_at_out; [exact G1 | exact MU|]. rewrite length_le8. intros x Hx. apply SF.
      apply out_img; [exact HN | unfold SA, SEG_PLAIN in Hx; cbn [sa_got_guard] in Hx; lia | unfold SA, SEG_PLAIN in Hx; cbn [sa_got_guard] in Hx; lia].
    + exists g. eapply bytes_at_out; [exact G2 | exact MU|]. rewrite length_le8. intros x Hx. apply SF.
      apply out_img; [exact HN | unfold SA, SEG_PLAIN in Hx; cbn [sa_guard] in Hx; lia | unfold SA, SEG_PLAIN in Hx; cbn [sa_guard] in Hx; lia].
  - intros a Ha. unfold SA, SEG_PLAIN, CAT_BYTES in Ha. cbn [sa_catalogue] in Ha.
    rewrite (mrd_out W m m' a MU ltac:(lia)); [apply CI; unfold SA, SEG_PLAIN, CAT_BYTES; cbn [sa_catalogue]; lia|].
    apply SF. apply out_img; [exact HN | lia | lia].
  - intros a Ha. unfold M_KEY_WORDS in Ha.
    rewrite (mrd_out W m m' a MU ltac:(lia)); [apply WI; unfold M_KEY_WORDS; lia|].
    apply SF. apply out_img; [exact HN | lia | lia].
  - eapply bytes_at_out; [exact F20 | exact MU|]. rewrite length_le8. intros x Hx. apply SF.
    apply out_frame; [exact HN | lia].
  - eapply bytes_at_out; [exact F30 | exact MU|].
    rewrite length_le8. intros x Hx. apply SF. apply out_frame; [exact HN | lia].
  - split; [exact (wr_at_transport rsegs m m' c SEG_C_SIZE WC WMo)|].
    split; [exact (wr_at_transport rsegs m m' mm SEG_M_SIZE WM WMo)|].
    exists sl. split; [|exact SLn]. eapply bytes_at_out; [exact SL | exact MU|]. rewrite SLn. intros x Hx.
    apply SF. apply out_mslack; [exact HN | unfold SEG_M_SIZE in *; lia].
Qed.

(** ** The text and the label *)
Definition txt_at (t : Z) (s : list Z) (m : word -> option byte) : Prop :=
  exists sl, bytes_at rsegs m t (zb s ++ ZERO :: sl) /\ Z.of_nat (length sl) = (- (t + Z.of_nat (length s) + 1)) mod 8.

Lemma txt_tr : forall S c mm t nt s m m' W, l02_num S c mm t nt -> nt = Z.of_nat (length s) + 1 ->
  txt_at t s m -> munch W m m' -> sub_fp W (A_back S c mm) -> txt_at t s m'.
Proof.
  intros S c mm t nt s m m' W HN Hnt (sl & B & L) MU SF. exists sl. split; [|exact L].
  eapply bytes_at_out; [exact B | exact MU|]. rewrite length_app, zb_length. cbn [length].
  intros x Hx. apply SF. apply (out_txt S c mm t nt x HN). lia.
Qed.

Lemma txt_cstr : forall t s m, Forall (fun x => 0 < x < 256) s -> txt_at t s m -> cstr_at rsegs m t s.
Proof.
  intros t s m HF (sl & B & L). exists (zb s), sl. split; [exact B|]. split; [apply zs_zb, Forall_byte, HF|].
  split; [apply Forall_nul, HF | lia].
Qed.

(** The label: NULL, or a C string in longl's 128 bytes or in the label buffer [S - 144, S - 104), with exactly
    the slack up to the next 8-byte boundary. *)
Definition lab_ok (S lp : Z) (lab : option (list Z)) (m : word -> option byte) : Prop :=
  match lab with
  | None => lp = 0
  | Some l =>
      0 < lp /\
      (exists sl, bytes_at rsegs m lp (zb l ++ ZERO :: sl) /\
                  Z.of_nat (length sl) = (- (lp + Z.of_nat (length l) + 1)) mod 8) /\
      Forall (fun x => 0 < x < 256) l /\
      ((0x32ac0 <= lp /\ lp + Z.of_nat (length l) + 8 <= 0x32ac0 + 128) \/
       (S - 144 <= lp /\ lp + Z.of_nat (length l) + 8 <= S - 104))
  end.

Lemma lab_tr : forall S c mm t nt lp lab m m' W, l02_num S c mm t nt ->
  lab_ok S lp lab m -> munch W m m' -> sub_fp W (A_back S c mm) -> lab_ok S lp lab m'.
Proof.
  intros S c mm t nt lp [l|] m m' W HN H MU SF; [|exact H].
  destruct H as (P & (sl & B & L) & HF & R). refine (conj P (conj _ (conj HF R))).
  exists sl. split; [|exact L]. eapply bytes_at_out; [exact B | exact MU|].
  rewrite length_app, zb_length. cbn [length]. intros x Hx. apply SF. apply (out_lab S c mm t nt x HN).
  assert (0 <= (- (lp + Z.of_nat (length l) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia). lia.
Qed.

Lemma lab_ocstr : forall S lp lab m, lab_ok S lp lab m -> ocstr_at rsegs m lp lab.
Proof.
  intros S lp [l|] m H; [|exact H]. destruct H as (P & (sl & B & L) & HF & R). split; [lia|].
  exists (zb l), sl. split; [exact B|]. split; [apply zs_zb, Forall_byte, HF|]. split; [apply Forall_nul, HF|lia].
Qed.

(** ** The blocks' contents *)
Lemma rc_tr : forall m m' W c rc, rconf_at rsegs m c rc -> munch W m m' ->
  (forall x, c <= x < c + SEG_C_SIZE -> outside W x) -> rconf_at rsegs m' c rc.
Proof.
  intros m m' W c rc (bs & B & E) MU H. exists bs. split; [|exact E].
  eapply bytes_at_out; [exact B | exact MU|]. destruct E as (L & _). rewrite L. exact H.
Qed.

Lemma mc_tr : forall m m' W mm mc, mconf_at rsegs m mm mc -> munch W m m' ->
  (forall x, mm <= x < mm + SEG_M_SIZE -> outside W x) -> mconf_at rsegs m' mm mc.
Proof.
  intros m m' W mm mc (bs & B & E) MU H. exists bs. split; [|exact E].
  eapply bytes_at_out; [exact B | exact MU|]. destruct E as (L & _). rewrite L. exact H.
Qed.

Lemma mconf_len : forall m mm mc, mconf_at rsegs m mm mc ->
  (length (mc_seg mc) <= 32)%nat /\ (length (mc_kept mc) <= 8)%nat.
Proof. intros m mm mc (bs & _ & (_ & L1 & _ & _ & _ & _ & L2 & _)). split; assumption. Qed.

Lemma rconf_len : forall m c rc, rconf_at rsegs m c rc -> (length (rc_seg rc) <= 32)%nat.
Proof. intros m c rc (bs & _ & (_ & L & _)). exact L. Qed.

(** ** The callee premises at main's sp S - 208 with lo := S - 65472 *)
Lemma mslack : forall S c mm m, l02_env S c mm m -> mm mod 16 = 0 -> blk_slack rsegs m mm SEG_M_SIZE.
Proof.
  intros S c mm m (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (sl & B & L)) H. exists sl. split; [exact B|].
  rewrite L. destruct (mod16_ex _ H) as (k & ->). unfold SEG_M_SIZE.
  replace (- (16 * k + 9236)) with (4 + (- 2 * k - 1155) * 8) by lia. rewrite Z.mod_add by lia. cbn. lia.
Qed.

(** x rounded up to the next multiple of 8. *)
Lemma rup8 : forall x, 0 <= (- x) mod 8 < 8 /\ exists q, x + (- x) mod 8 = 8 * q.
Proof.
  intros x. split; [apply Z.mod_pos_bound; lia|].
  exists (x / 8 + (if x mod 8 =? 0 then 0 else 1)).
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
  destruct (Z.eqb_spec (x mod 8) 0) as [E|E].
  - replace (- x) with (0 + (- (x / 8)) * 8) by lia. rewrite Z.mod_add by lia. cbn. lia.
  - replace (- x) with ((8 - x mod 8) + (- (x / 8) - 1) * 8) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

(** A text block apart from a 16-aligned block stays apart with its read span. *)
Lemma span_apart : forall t s b n, (exists k, t = 16 * k) -> (exists k, b = 16 * k) -> 0 < n ->
  apart t (Z.of_nat (length s) + 1) b (b + n) -> apart t (cstr_span t s) b (b + n).
Proof.
  intros t s b n (kt & Et) (kb & Eb) Hn H. unfold cstr_span, apart in *.
  destruct (rup8 (t + Z.of_nat (length s) + 1)) as (R & q & Eq). lia.
Qed.

Lemma printf_env_of : forall S c mm m fc, 2 ^ 40 <= S - 65536 -> S <= 2 ^ 47 -> l02_env S c mm m -> frm0 fc ->
  printf_env m fc (S - 65472) (S - 208).
Proof.
  intros S c mm m fc H1 H2 (MI & TM & SSP & _) FRM. unfold printf_env.
  refine (conj FRM (conj TM (conj SSP _))). unfold SA, SEG_PLAIN. cbn [sa_img_end]. lia.
Qed.

Lemma stack_ok_of : forall S c mm t nt src s m d, l02_static S c mm t nt src s -> l02_env S c mm m ->
  d <= 65264 -> stack_ok rsegs m (S - 65472) (S - 208) d.
Proof.
  intros S c mm t nt src s m d HST (_ & _ & _ & _ & _ & ST & _) Hd. st_dst HST.
  destruct (mod16_ex _ HS16) as (k & Ek).
  unfold stack_ok. split; [exact ST|]. split; [lia|]. split.
  - replace (S - 208) with ((k - 13) * 16) by lia. apply Z.mod_mul. lia.
  - intros a Ha. apply HROM. lia.
Qed.

Lemma mfile_pre_of : forall S c mm t nt src s m fc mc lp lab,
  l02_static S c mm t nt src s -> l02_env S c mm m -> txt_at t s m -> mconf_at rsegs m mm mc ->
  mc_gen mc + 1 < 2 ^ 31 -> mc_refused mc + 2 ^ 17 < 2 ^ 32 -> mc_overflow mc + 2 ^ 17 < 2 ^ 32 ->
  lab_ok S lp lab m -> frm0 fc ->
  m_file_pre m fc (S - 208) (S - 65472) mm t lp mc s lab.
Proof.
  intros S c mm t nt src s m fc mc lp lab HST ENV TXT MC G1 G2 G3 LAB FRM.
  pose proof ENV as (MI & TM & SSP & CI & WI & ST & _ & _ & WC & WM & _).
  pose proof (stack_ok_of S c mm t nt src s m M_FILE_STACK HST ENV ltac:(unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia))
    as SOK.
  pose proof (lab_ocstr S lp lab m LAB) as OC.
  pose proof HST as HST'. st_dst HST'.
  pose proof (mslack S c mm m ENV Hm16) as SLK.
  pose proof (printf_env_of S c mm m fc HSlo HShi ENV FRM) as PE.
  unfold m_file_pre.
  split; [lia|]. split; [exact Hm16|]. split; [exact Hmn|]. split; [exact MC|]. split; [exact WM|].
  split; [exact SLK|]. split; [unfold apart, SEG_M_SIZE in *; lia|].
  split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [lia|].
  split; [rewrite <- Hnt; exact Htn|]. split; [exact (txt_cstr t s m HsF TXT)|]. split; [exact HsL|].
  split; [unfold apart; lia|].
  split; [apply span_apart; [exact (mod16_ex _ Ht16) | exact (mod16_ex _ Hm16) | unfold SEG_M_SIZE; lia |
          rewrite <- Hnt; exact Atm]|].
  split; [exact OC|].
  split.
  { destruct lab as [l|]; [|exact I]. destruct LAB as (P & _ & _ & R).
    unfold apart, MC_READING, SEG_M_SIZE in *. lia. }
  split; [exact PE|]. split; [exact CI|]. split; [exact WI|]. split; [exact SOK|]. exact MI.
Qed.

Lemma reader_pre_of : forall S c mm t nt src s m fc rc d,
  l02_static S c mm t nt src s -> l02_env S c mm m -> txt_at t s m -> rconf_at rsegs m c rc ->
  rc_gen rc + 1 < 2 ^ 32 -> rc_refused rc + 2 ^ 17 < 2 ^ 32 -> rc_overflow rc + 2 ^ 17 < 2 ^ 32 ->
  frm0 fc -> d <= 65264 ->
  reac_segconf_parse_file_c.reader_pre d m fc (S - 208) (S - 65472) c t rc s.
Proof.
  intros S c mm t nt src s m fc rc d HST ENV TXT RC G1 G2 G3 FRM Hd.
  pose proof ENV as (MI & TM & SSP & CI & WI & ST & _ & _ & WC & WM & _).
  pose proof (stack_ok_of S c mm t nt src s m d HST ENV Hd) as SOK.
  pose proof HST as HST'. st_dst HST'.
  pose proof (printf_env_of S c mm m fc HSlo HShi ENV FRM) as PE.
  unfold reac_segconf_parse_file_c.reader_pre.
  split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [unfold apart, SEG_C_SIZE in *; lia|].
  split; [exact Hcn|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [lia|].
  split; [exact (txt_cstr t s m HsF TXT)|]. split; [exact HsL|]. split; [unfold apart; lia|].
  split; [apply span_apart; [exact (mod16_ex _ Ht16) | exact (mod16_ex _ Hc16) | unfold SEG_C_SIZE; lia |
          rewrite <- Hnt; exact Atc]|].
  split; [exact PE|]. split; [exact CI|]. split; [exact SOK|]. exact MI.
Qed.

Lemma pfile_lab_of : forall S c mm t nt src s m lp lab, l02_static S c mm t nt src s -> lab_ok S lp lab m ->
  ocstr_at rsegs m lp lab /\
  match lab with
  | Some l => (length l <= 65535)%nat /\ apart lp (Z.of_nat (length l) + 8) (S - 65472) (S - 208) /\
              apart lp (Z.of_nat (length l) + 8) (c + RC_READING) (c + RC_READING + 96)
  | None => True
  end.
Proof.
  intros S c mm t nt src s m lp lab HST LAB. split; [exact (lab_ocstr S lp lab m LAB)|].
  destruct lab as [l|]; [|exact I]. destruct LAB as (P & _ & _ & R). st_dst HST.
  cbv beta iota. unfold apart, RC_READING, SEG_C_SIZE in *.
  split; [apply nat_le_of; lia|]. split; lia.
Qed.

Lemma mrefuse_pre_of : forall S c mm t nt src s m fc mc, l02_static S c mm t nt src s -> l02_env S c mm m ->
  mconf_at rsegs m mm mc -> mc_refused mc + 1 < 2 ^ 32 -> frm0 fc ->
  m_refuse_c.m_refuse_pre m fc (S - 208) (S - 65472) mm 0 mc false.
Proof.
  intros S c mm t nt src s m fc mc HST ENV MC G FRM.
  pose proof ENV as (MI & TM & SSP & CI & WI & ST & _ & _ & WC & WM & _).
  pose proof (stack_ok_of S c mm t nt src s m m_refuse_c.M_REFUSE_STACK HST ENV
    ltac:(unfold m_refuse_c.M_REFUSE_STACK, PRINTF_K; lia)) as SOK.
  pose proof HST as HST'. st_dst HST'.
  pose proof (mslack S c mm m ENV Hm16) as SLK.
  pose proof (printf_env_of S c mm m fc HSlo HShi ENV FRM) as PE.
  unfold m_refuse_c.m_refuse_pre.
  split; [lia|]. split; [exact Hm16|]. split; [exact Hmn|]. split; [exact MC|]. split; [exact WM|].
  split; [exact SLK|]. split; [unfold apart, SEG_M_SIZE in *; lia|]. split; [lia|]. split; [exact G|].
  split; [exact PE|]. split; [exact SOK|]. exact MI.
Qed.

(** ** The callees' write sets *)
Lemma W_mfile : forall S mm k0 mc', (length (mc_seg mc') <= 32)%nat -> (length (mc_kept mc') <= 8)%nat ->
  sub_fp (M_FILE_W (S - 208) mm k0 mc') (A_m S mm).
Proof.
  intros S mm k0 mc' L1 L2.
  unfold M_FILE_W, A_m, mseg_addr, kept_addr, M_FILE_STACK, M_FILE_FRAME, PRINTF_K, MC_N, MC_REFUSED, MC_KEPT,
    MC_KEPT_LEN, MC_KNOCK, MC_NKEPT, MC_READING, MSEG_SIZE, SEG_M_SIZE.
  fp_tac.
Qed.

Lemma W_pfile : forall S c,
  sub_fp ((S - 208 - reac_segconf_parse_file_c.PARSE_FILE_STACK, S - 208) :: RC_PARSE_W c) (A_c S c).
Proof.
  intros S c. unfold reac_segconf_parse_file_c.PARSE_FILE_STACK, reac_segconf_parse_file_c.PARSE_FILE_FRAME,
    REFUSE_STACK, PRINTF_K, RC_PARSE_W, A_c, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE.
  fp_tac.
Qed.

Lemma W_parse : forall S c,
  sub_fp ((S - 208 - reac_segconf_parse_c.PARSE_STACK, S - 208) :: RC_PARSE_W c) (A_c S c).
Proof.
  intros S c. unfold reac_segconf_parse_c.PARSE_STACK, reac_segconf_parse_file_c.PARSE_FILE_STACK,
    reac_segconf_parse_file_c.PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, RC_PARSE_W, A_c, RC_N, RC_REFUSAL,
    RC_OVERFLOW, RC_READING, RC_GEN, SEG_C_SIZE.
  fp_tac.
Qed.

Lemma W_mrefuse : forall S mm mc', (length (mc_kept mc') <= 8)%nat ->
  sub_fp (m_refuse_c.m_refuse_W (S - 208) mm mc') (A_m S mm).
Proof.
  intros S mm mc' L. unfold m_refuse_c.m_refuse_W.
  destruct (Z.of_nat (length (mc_kept mc')) <? 8) eqn:E; cbn [app].
  - apply Z.ltb_lt in E.
    unfold A_m, kept_addr, m_refuse_c.M_REFUSE_STACK, PRINTF_K, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED,
      SEG_M_SIZE.
    fp_tac.
  - unfold A_m, m_refuse_c.M_REFUSE_STACK, PRINTF_K, MC_REFUSED, SEG_M_SIZE. fp_tac.
Qed.

(** One 4-byte store into m->seg[i] (i < 32). *)
Lemma W_seg4 : forall S mm i off, (i < 32)%nat -> 0 <= off -> off + 4 <= 256 ->
  sub_fp [(mm + 256 * Z.of_nat i + off, mm + 256 * Z.of_nat i + off + 4)] (A_m S mm).
Proof. intros S mm i off H1 H2 H3. unfold A_m, SEG_M_SIZE. fp_tac. Qed.

(** ** From L02_mem *)
Lemma l02_static_of : forall S c mm t nt src s rc mc m lb,
  L02_mem S c mm t nt src s rc mc m -> L02_model s lb rc mc -> l02_static S c mm t nt src s.
Proof.
  intros S c mm t nt src s rc mc m lb HM (HF & HL & _).
  destruct HM as (MI & TM & SSP & CI & WI & HS16 & HSlo & HShi & ST & HROM & F20 & F28 & F30 & Hc0 & Hc16 & Hcn & Hcb &
    Hm0 & Hm16 & Hmn & Hmb & Ht0 & Ht16 & Htn & Htb & Hnt & Atm & Atc & Amc & Atl & Aml & Acl & (bc & BC & _) & _ &
    (bm & BM & _) & _ & _ & (jt & RT) & _ & BS & Ast & _).
  pose proof (bytes_at_bound _ _ _ _ BC) as Bc. pose proof (bytes_at_bound _ _ _ _ BM) as Bm.
  pose proof (rw_cells_bound _ _ _ _ RT) as Bt. pose proof (bytes_at_bound _ _ _ _ BS) as Bs.
  unfold SA, SEG_PLAIN in Atl, Aml, Acl. cbn [sa_longl] in Atl, Aml, Acl.
  unfold l02_static. repeat (split; [first [assumption | lia]|]). first [assumption | lia].
Qed.

(** ** The join 0x139f0 (after the text copy, its NUL and the label) and what the walk from it proves *)
Definition L02_J (S c mm t nt src x5 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
    (sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 : word) (m0 : word -> option byte) : Prop :=
  forall (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : word -> option byte) (lp : Z),
    frm0 fc -> munch (L02_W S c mm t nt) m0 m -> wmono rsegs m0 m ->
    l02_env S c mm m -> txt_at t s m -> rconf_at rsegs m c rc -> mconf_at rsegs m mm mc ->
    lab_ok S lp (label_of lb) m ->
    evt rsegs (L02_post S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s6 s10 m0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 t) s8
               (Z_to_bv 64 lp) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x139f0) fc None m (seg_rom rsegs)).

(** The walk from 0x139f0 (Prog/Seg/L02W_back.v proves it from K_L02): for the cut's registers and the turn's data,
    L02_J. The walk to 0x139f0 (Prog/Seg/L02W_front.v) uses it to give L02_inner. *)
Definition L02_back_stmt : Prop :=
  forall (S c mm t nt src x5 x6 f nf lb : Z) (s : list Z) (rc : rconf) (mc : mconf) (ret : bool)
         (sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 : word) (m0 : word -> option byte),
    l02_static S c mm t nt src s -> L02_model s lb rc mc ->
    sp = Z_to_bv 64 (S - L02_FRAME) -> s0 = Z_to_bv 64 mm -> s10 = Z_to_bv 64 (mm + MC_N) ->
    s2 = Z_to_bv 64 nf -> s11 = Z_to_bv 64 f -> 0 <= f < nf -> nf <= 4 -> s4 = Z_to_bv 64 (b2z ret) ->
    s3 = Z_to_bv 64 src -> s5 = Z_to_bv 64 x5 -> s6 = Z_to_bv 64 x6 ->
    L02_J S c mm t nt src x5 x6 f nf lb s rc mc ret sp gp tp s0 s2 s3 s4 s5 s6 s10 s11 m0.
