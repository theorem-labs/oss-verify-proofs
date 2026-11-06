(** The inlined pod_write_ent of the pod loop and the record copy, 0x1350c -> 0x13618 of the plain image: the two
    32-bit puts (the pod's size word, then its type word), the copy of the pod's body, the pad to a multiple of
    eight, and, inside the first SPA_PROP_params Struct, the copy of the 104-byte object into pp->ent[pp->n_ent++].

    Proved against [Cut.S_write] with the contracts of memset and memcpy as premises. The memory the walk carries
    is [MW]: the block image of RoleBuild/Facts.v, the frame cells the block reads back (the constants of the
    preheader and the property's variables), the pod object on the stack, and the eight bytes of pp->len. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memset_c memcpy_c.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog.RoleBuild Require Import Facts Cut.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_even := rewrite ret_pc_even by (first [lia | reflexivity]).

Tactic Notation "gen_mem" ident(H) ident(mn) :=
  revert H;
  lazymatch goal with
  | |- _ -> evt _ _ (MS _ _ _ _ _ ?mm _) => generalize mm
  end;
  intros mn H.

(** ** The arithmetic of the block's lengths *)

(** The pad pod.h:187 writes, as a modulus. *)
Lemma pad8_alt : forall z, pad8 z = (- z) mod 8.
Proof.
  intros z. unfold pad8.
  pose proof (Z.div_mod z 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as B.
  rewrite <- (Z.mod_add (- z) (z / 8 + 1) 8) by lia.
  f_equal. lia.
Qed.

(** The pad of a length is the pad of its part past the last multiple of eight. *)
Lemma pad8_shift : forall a b, (8 | a) -> pad8 (a + b) = pad8 b.
Proof.
  intros a b [c ->]. rewrite !pad8_alt.
  rewrite <- (Z.mod_add (- b) (- c) 8) by lia. f_equal. lia.
Qed.

(** `sext.w` of a small nonnegative word. *)
Lemma sext32_id : forall z, 0 <= z < 2^31 -> bv_swrap 32 (bv_unsigned (Z_to_bv 64 z) + 0) = z.
Proof.
  intros z Hz. rewrite unsigned_lit by lia. rewrite Z.add_0_r.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** A 32-bit load of a small nonnegative word. *)
Lemma sx32_id : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). lia.
Qed.

(** `negw a1,a0; andi s3,a1,7` is the pad of the length in a0 (pod.h:187). *)
Lemma neg_and7 : forall z, 0 < z < 2^31 ->
  Z.land (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 z))))) 7 = pad8 z.
Proof.
  intros z Hz. rewrite (unsigned_lit z) by lia.
  rewrite (bv_swrap_small 32 (0 - z)) by (change (bv_half_modulus 32) with (2^31); lia).
  rewrite unsigned_lit_wrap, (umod_neg (0 - z)) by lia.
  replace 7 with (Z.ones 3) by reflexivity. rewrite Z.land_ones by lia.
  rewrite pad8_alt. change (2 ^ 3) with 8.
  replace (0 - z + 2 ^ 64) with (- z + 2305843009213693952 * 8)
    by (change (2 ^ 64) with 18446744073709551616; lia).
  apply Z.mod_add. lia.
Qed.

(** A four-byte store of a literal word writes the field [le32] holds. *)
Lemma le4_le32 : forall t, le4 (Z_to_bv 64 t) = le32 t.
Proof.
  intros t. unfold le4, le32. rewrite unsigned_lit_wrap. apply Z_to_le_bytes_mod. cbn. lia.
Qed.

(** ** Lists: the four byte stores of a put, and two writes that do not meet *)

Lemma ow32 : forall (I : list byte) (o v : Z), 0 <= o -> (Z.to_nat o + 4 <= length I)%nat ->
  overwrite (overwrite (overwrite (overwrite I (Z.to_nat o) (le1 (Z_to_bv 64 v)))
      (Z.to_nat (o + 1)) (le1 (Z_to_bv 64 (Z.shiftr v 8))))
      (Z.to_nat (o + 2)) (le1 (Z_to_bv 64 (Z.shiftr v 16))))
      (Z.to_nat (o + 3)) (le1 (Z_to_bv 64 (Z.shiftr v 24)))
  = overwrite I (Z.to_nat o) (le32 v).
Proof.
  intros I o v Ho HI. rewrite <- le32_of_stores.
  replace (Z.to_nat (o + 1)) with (Z.to_nat o + length (le1 (Z_to_bv 64 v)))%nat
    by (rewrite length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_le1; lia).
  replace (Z.to_nat (o + 2))
    with (Z.to_nat o + length (le1 (Z_to_bv 64 v) ++ le1 (Z_to_bv 64 (Z.shiftr v 8))))%nat
    by (rewrite length_app, !length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_app, !length_le1; lia).
  replace (Z.to_nat (o + 3))
    with (Z.to_nat o + length ((le1 (Z_to_bv 64 v) ++ le1 (Z_to_bv 64 (Z.shiftr v 8)))
                               ++ le1 (Z_to_bv 64 (Z.shiftr v 16))))%nat
    by (rewrite !length_app, !length_le1; lia).
  rewrite overwrite_adj by (rewrite !length_app, !length_le1; lia).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma ow_comm : forall (I x y : list byte) (p q : nat),
  (p + length x <= q)%nat -> (q + length y <= length I)%nat ->
  overwrite (overwrite I p x) q y = overwrite (overwrite I q y) p x.
Proof.
  intros I x y p q H1 H2.
  set (A := firstn p I). set (X := firstn (length x) (skipn p I)).
  set (M := firstn (q - p - length x)%nat (skipn (p + length x)%nat I)).
  set (Y := firstn (length y) (skipn q I)).
  set (C := skipn (q + length y)%nat I).
  assert (LA : length A = p) by (subst A; rewrite length_firstn; lia).
  assert (LX : length X = length x) by (subst X; rewrite length_firstn, length_skipn; lia).
  assert (LM : length M = (q - p - length x)%nat) by (subst M; rewrite length_firstn, length_skipn; lia).
  assert (LY : length Y = length y) by (subst Y; rewrite length_firstn, length_skipn; lia).
  assert (EI : I = A ++ X ++ M ++ Y ++ C).
  { subst A X M Y C.
    transitivity (firstn p I ++ skipn p I); [symmetry; apply firstn_skipn|]. f_equal.
    transitivity (firstn (length x) (skipn p I) ++ skipn (length x) (skipn p I));
      [symmetry; apply firstn_skipn|]. f_equal.
    rewrite skipn_skipn. replace (length x + p)%nat with (p + length x)%nat by lia.
    transitivity (firstn (q - p - length x)%nat (skipn (p + length x)%nat I)
                  ++ skipn (q - p - length x)%nat (skipn (p + length x)%nat I));
      [symmetry; apply firstn_skipn|]. f_equal.
    rewrite skipn_skipn. replace (q - p - length x + (p + length x))%nat with q by lia.
    transitivity (firstn (length y) (skipn q I) ++ skipn (length y) (skipn q I));
      [symmetry; apply firstn_skipn|]. f_equal.
    rewrite skipn_skipn. f_equal. lia. }
  clearbody A X M Y C.
  assert (E1 : overwrite I p x = A ++ x ++ M ++ Y ++ C).
  { rewrite EI. replace p with (length A) by lia. apply overwrite_mid. lia. }
  assert (E2 : overwrite I q y = (A ++ X ++ M) ++ y ++ C).
  { rewrite EI.
    replace (A ++ X ++ M ++ Y ++ C) with ((A ++ X ++ M) ++ Y ++ C) by (rewrite <- !app_assoc; reflexivity).
    replace q with (length (A ++ X ++ M)) by (rewrite !length_app; lia).
    apply overwrite_mid. lia. }
  rewrite E1, E2.
  replace (A ++ x ++ M ++ Y ++ C) with ((A ++ x ++ M) ++ Y ++ C) by (rewrite <- !app_assoc; reflexivity).
  replace ((A ++ X ++ M) ++ y ++ C) with (A ++ X ++ (M ++ y ++ C)) by (rewrite <- !app_assoc; reflexivity).
  replace q with (length (A ++ x ++ M)) by (rewrite !length_app; lia).
  rewrite (overwrite_mid (A ++ x ++ M) Y C y ltac:(lia)).
  replace p with (length A) by lia.
  rewrite (overwrite_mid A X (M ++ y ++ C) x ltac:(lia)).
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** The block image at the offsets the code reads and writes *)

(** One pod_put: the bytes appended to buf, then pp->len (pod.h:179-180). *)
Lemma img_app : forall (b x : list byte) isp hasp pst esx corr,
  Z.of_nat (length b + length x) <= 16384 ->
  overwrite (overwrite (pp_image b isp hasp pst esx corr) (length b) x)
    (Z.to_nat 16384) (le64 (Z.of_nat (length b) + Z.of_nat (length x)))
  = pp_image (b ++ x) isp hasp pst esx corr.
Proof.
  intros b x isp hasp pst esx corr H.
  rewrite (pp_image_put b x isp hasp pst esx corr H).
  replace (Z.of_nat (length b) + Z.of_nat (length x)) with (Z.of_nat (length b + length x)) by lia.
  reflexivity.
Qed.

(** The record copy pp->ent[pp->n_ent++] = e: n_ent first, then the entry (pod.h:432). *)
Lemma img_ent : forall b isp hasp pst (esx : list ent) corr (ee : ent),
  Z.of_nat (length b) <= 16384 -> (length esx < 32)%nat ->
  Forall (fun z => (length (e_body z) <= 96)%nat) (esx ++ [ee]) ->
  overwrite (overwrite (pp_image b isp hasp pst esx corr) (Z.to_nat 19732)
               (le32 (Z.of_nat (length esx) + 1)))
            (Z.to_nat (16404 + Z.of_nat (length esx) * 104)) (ent_mem ee)
  = pp_image b isp hasp pst (esx ++ [ee]) corr.
Proof.
  intros b isp hasp pst esx corr ee Hb Hl Hs.
  pose proof Hs as Hs'. apply Forall_app in Hs' as [Hes Hee]. apply Forall_inv in Hee.
  assert (LP : Z.of_nat (length (pp_image b isp hasp pst esx corr)) = PP_SIZE)
    by (apply length_pp_image; [exact Hb | lia | exact Hes]).
  unfold PP_SIZE in LP.
  rewrite (pp_image_ent b isp hasp pst esx ee corr Hb Hl Hs).
  replace (16404 + Z.of_nat (length esx) * 104) with (OFF_ENT + ENT_SIZE * Z.of_nat (length esx))
    by (unfold OFF_ENT, ENT_SIZE; lia).
  symmetry. apply ow_comm.
  - rewrite (length_ent_mem ee Hee). unfold OFF_ENT, ENT_SIZE, OFF_N_ENT. lia.
  - rewrite length_le32. unfold OFF_N_ENT. lia.
Qed.

(** pp->len and pp->n_ent as the code reads them. *)
Lemma len_slice : forall b isp hasp pst esx corr, Z.of_nat (length b) <= 16384 ->
  firstn 8 (skipn (Z.to_nat 16384) (pp_image b isp hasp pst esx corr)) = le64 (Z.of_nat (length b)).
Proof. intros. apply pp_image_slice_len. exact H. Qed.

Lemma nent_slice : forall b isp hasp pst esx corr, Z.of_nat (length b) <= 16384 ->
  (length esx <= 32)%nat -> Forall (fun z => (length (e_body z) <= 96)%nat) esx ->
  firstn 4 (skipn (Z.to_nat 19732) (pp_image b isp hasp pst esx corr)) = le32 (Z.of_nat (length esx)).
Proof. intros. apply pp_image_slice_nent; assumption. Qed.

(** ** Reads of whole cells *)
Lemma rd_all : forall m1 A bs, bytes_at rsegs m1 A bs ->
  ov_read_bytes rsegs m1 (wa A) (length bs) = Some bs.
Proof.
  intros m1 A bs H.
  pose proof (bytes_at_ov_read rsegs m1 A bs 0 (length bs) H ltac:(cbn; lia)) as X.
  cbn [Z.of_nat skipn] in X. rewrite Z.add_0_r, firstn_all in X. exact X.
Qed.

Lemma rd8 : forall m1 A bs, bytes_at rsegs m1 A bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m1 (wa A) 8 = Some bs.
Proof. intros m1 A bs H L. rewrite <- L. apply rd_all. exact H. Qed.

Lemma rd4 : forall m1 A bs, bytes_at rsegs m1 A bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m1 (wa A) 4 = Some bs.
Proof. intros m1 A bs H L. rewrite <- L. apply rd_all. exact H. Qed.

Lemma bodies96 : forall esx, Forall ent_wf esx -> Forall (fun z => (length (e_body z) <= 96)%nat) esx.
Proof.
  intros esx H. induction H as [|x l Hx Hl IH]; constructor; [|exact IH].
  destruct Hx as (_ & Hb & Hs). lia.
Qed.

(** pp->len is the eight bytes at 0x4000 of the block image. *)
Lemma len_bytes_of : forall sp m rest src pp lo b isp hasp pst esx corr m1,
  MBr sp m rest src pp lo (pp_image b isp hasp pst esx corr) m1 ->
  Z.of_nat (length b) <= 16384 ->
  bytes_at rsegs m1 (pp + 16384) (le64 (Z.of_nat (length b))).
Proof.
  intros sp m rest src pp lo b isp hasp pst esx corr m1 MB Hb.
  assert (BL : Z.of_nat (length (pp_image b isp hasp pst esx corr)) = 19744)
    by (destruct MB as (_ & HL & _); unfold POD_PROPS in HL; exact HL).
  pose proof (MBr_pp_bytes sp m rest src pp lo (pp_image b isp hasp pst esx corr) m1 16384 8 MB
                ltac:(lia) ltac:(lia)) as X.
  rewrite (len_slice b isp hasp pst esx corr Hb) in X. exact X.
Qed.

Section Walk.
Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
Variables (rest : list byte) (fl src pp lo : Z).
Hypothesis HOK : BOK sp rest src pp lo.
Hypothesis MSET : memset_contract.
Hypothesis MCPY : memcpy_contract.
Variables (sh np : Z) (ps : list (Z * pval)) (i : nat) (cnt : Z).
Variables (es : list ent) (k : nat) (e : ent) (r : list byte).
Hypothesis HWF : pc_wf sh ps.
Hypothesis HSH : sh <> 7.
Hypothesis HES : Forall ent_wf es.
Hypothesis HK : (length es = k)%nat.
Hypothesis HK32 : (k < 32)%nat.
Hypothesis HEW : ent_wf e.
Hypothesis HPS2 : (length ps <= 2)%nat.
Hypothesis HSUF : suffix rest r.
Hypothesis HCNT : 0 <= cnt <= 32.
Hypothesis HKC : Z.of_nat k < cnt.

(** The parts of the record at this cut. *)
Definition isp0 : bool := is_props (PodRec sh ps None).
Definition hasp0 : bool := has_params (PodRec sh ps None).
Definition pst0 : bool := params_struct (PodRec sh ps None).
Definition ES0 : list ent := pc_ents (PbCut sh ps (Some es)).
Definition ES1 : list ent := pc_ents (PbCut sh ps (Some (es ++ [e]))).
Definition b0 : list byte := pc_buf (PbCut sh ps (Some es)).
Definition L0 : Z := Z.of_nat (length b0).
Definition sz : Z := e_size e.
Definition ty : Z := e_type e.
Definition pd : Z := pad8 sz.
Definition IMG (b : list byte) (esx : list ent) : list byte := pp_image b isp0 hasp0 pst0 esx false.

Lemma img_cut0 : pc_image (PbCut sh ps (Some es)) = IMG b0 ES0.
Proof. reflexivity. Qed.

Lemma img_cut1 : pc_image (PbCut sh ps (Some (es ++ [e]))) = IMG (b0 ++ enc_pod e) ES1.
Proof.
  unfold IMG, ES1, isp0, hasp0, pst0, b0, pc_image. cbn [pc_shape pc_props].
  rewrite <- pc_buf_pod. reflexivity.
Qed.

(** ** The lengths this piece needs *)
Lemma wf_pval : Forall (fun kv => pval_wf (snd kv)) ps.
Proof. destruct HWF as (_ & H & _). apply (Forall_impl _ (fun kv Hk => proj2 Hk) H). Qed.

Lemma wf_ents : Forall ent_wf (all_ents ps).
Proof. destruct HWF as (_ & _ & H & _). exact H. Qed.

Lemma L0_hi : L0 <= 5384.
Proof.
  unfold L0, b0.
  destruct (pc_buf_len_open sh ps es wf_pval wf_ents HES) as [H _]. lia.
Qed.

Lemma L0_div : (8 | L0).
Proof.
  unfold L0, b0.
  destruct (pc_buf_len_open sh ps es wf_pval wf_ents HES) as [_ H]. exact H.
Qed.

Lemma L0_lo : 16 <= L0.
Proof.
  unfold L0, b0, pc_buf, body_bytes, open_bytes. cbn [pc_shape pc_props pc_open].
  rewrite !zlen_app, !zlen_le32. lia.
Qed.

Lemma sz_rng : 0 <= sz <= 45.
Proof. destruct HEW as (_ & _ & H). exact H. Qed.

Lemma body_len : length (e_body e) = Z.to_nat sz.
Proof. destruct HEW as (_ & H & _). exact H. Qed.

Lemma ty_rng : 0 <= ty < 2^32.
Proof. destruct HEW as (H & _ & _). exact H. Qed.

Lemma pd_rng : 0 <= pd < 8.
Proof. apply pad8_bound. Qed.

Lemma enc_len : Z.of_nat (length (enc_pod e)) = 8 + sz + pd.
Proof. unfold pd, sz. apply zlen_enc_pod. exact HEW. Qed.

(** The addresses of the frame, the block and the input. *)
Lemma rng : 0 < pp /\ pp + 19744 <= lo /\ lo + 96 <= bv_unsigned sp /\ 0 <= lo
            /\ bv_unsigned sp + 392 <= 2^64.
Proof.
  destruct HOK as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _).
  unfold POD_PROPS, MID_STACK, FRAME_LOCALS in *. lia.
Qed.

(** ** The memory the walk carries *)
Definition FR (m1 : word -> option byte) : Prop :=
  CFIX sp pp m1 /\ CVAR sp fl np sh ps i cnt m1 /\
  cell8 m1 (bv_unsigned sp + 0x78) (Z.of_nat (length r)) /\
  bytes_at rsegs m1 (bv_unsigned sp + 0x88) (ent_mem e).

Definition MW (Ib : list byte) (len : Z) (m1 : word -> option byte) : Prop :=
  MBr sp m rest src pp lo Ib m1 /\ FR m1 /\ bytes_at rsegs m1 (pp + 16384) (le64 len).

Lemma keep8 : forall m1 m2 (a n A v : Z), cell8 m1 A v -> munch [(a, a + n)] m1 m2 ->
  a + n <= bv_unsigned sp -> bv_unsigned sp <= A -> cell8 m2 A v.
Proof.
  intros m1 m2 a n A v H MU H1 H2. unfold cell8 in *.
  apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU).
  cbn [disjoint_from]. rewrite length_le8. split; [lia | exact I].
Qed.

Lemma keepb : forall m1 m2 (a n A : Z) bs, bytes_at rsegs m1 A bs -> munch [(a, a + n)] m1 m2 ->
  a + n <= bv_unsigned sp -> bv_unsigned sp <= A -> bytes_at rsegs m2 A bs.
Proof.
  intros m1 m2 a n A bs H MU H1 H2.
  apply (bytes_at_transport rsegs _ m1 m2 _ _ H MU).
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

Lemma FR_munch : forall m1 m2 (a n : Z), FR m1 -> munch [(a, a + n)] m1 m2 ->
  pp <= a -> a + n <= pp + 19744 -> FR m2.
Proof.
  intros m1 m2 a n (CF & CV & C78 & CE) MU Ha Hb. pose proof rng as R.
  destruct CF as (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80).
  destruct CV as (V00 & V08 & V18 & V30 & V48 & V58 & V70).
  split; [|split; [|split]].
  - repeat split; (eapply keep8; [eassumption | exact MU | lia | lia]).
  - repeat split; (eapply keep8; [eassumption | exact MU | lia | lia]).
  - eapply keep8; [exact C78 | exact MU | lia | lia].
  - eapply keepb; [exact CE | exact MU | lia | lia].
Qed.

Lemma FR_write : forall m1 (a : Z) bs, FR m1 -> pp <= a -> a + Z.of_nat (length bs) <= pp + 19744 ->
  FR (write_to_mem m1 (Z_to_bv 64 a) bs).
Proof.
  intros m1 a bs H Ha Hb. pose proof rng as R.
  apply (FR_munch m1 _ a (Z.of_nat (length bs)) H); [|lia|lia].
  apply munch_of_write; lia.
Qed.

Lemma mw_mb : forall Ib len m1, MW Ib len m1 -> MBr sp m rest src pp lo Ib m1.
Proof. intros Ib len m1 (H & _). exact H. Qed.

Lemma mw_ilen : forall Ib len m1, MW Ib len m1 -> Z.of_nat (length Ib) = 19744.
Proof.
  intros Ib len m1 (H & _). destruct H as (_ & HL & _). unfold POD_PROPS in HL. exact HL.
Qed.

Lemma mw_ok : forall Ib len m1 (o a : Z) (j : nat), MW Ib len m1 -> a = pp + o -> 0 <= o ->
  o + Z.of_nat j <= 19744 -> store_ok rsegs m1 (wa a) j = true.
Proof.
  intros Ib len m1 o a j MWm -> Ho Hj.
  apply (MBr_pp_ok sp m rest src pp lo Ib m1 o j (mw_mb _ _ _ MWm) Ho).
  unfold POD_PROPS. lia.
Qed.

Lemma mw_rd_len : forall Ib len m1, MW Ib len m1 ->
  ov_read_bytes rsegs m1 (wa (pp + 16384)) 8 = Some (le8 (Z_to_bv 64 len)).
Proof.
  intros Ib len m1 (_ & _ & HL). rewrite le8_lit64. apply rd8; [exact HL | apply length_le64].
Qed.

Lemma mw_store : forall Ib len m1 (o a : Z) bs, MW Ib len m1 -> a = pp + o -> 0 <= o ->
  o + Z.of_nat (length bs) <= 19744 -> (o + Z.of_nat (length bs) <= 16384 \/ 16392 <= o) ->
  MW (overwrite Ib (Z.to_nat o) bs) len (write_to_mem m1 (Z_to_bv 64 a) bs).
Proof.
  intros Ib len m1 o a bs MWm -> Ho Hn Hd. pose proof rng as R.
  pose proof (mw_ilen _ _ _ MWm) as BL. pose proof MWm as (MB & FRm & HL).
  split; [|split].
  - apply (MBr_pp_store sp m rest src pp lo HOK Ib m1 o bs MB Ho). lia.
  - apply FR_write; [exact FRm | lia | lia].
  - apply (bytes_at_write_other rsegs m1 (pp + o) bs (pp + 16384) (le64 len) HL);
      [lia | lia | rewrite length_le64; lia].
Qed.

Lemma mw_setlen : forall Ib len len' m1, MW Ib len m1 -> 0 <= len' ->
  MW (overwrite Ib (Z.to_nat 16384) (le64 len')) len'
     (write_to_mem m1 (Z_to_bv 64 (pp + 16384)) (le64 len')).
Proof.
  intros Ib len len' m1 MWm Hl. pose proof rng as R.
  pose proof (mw_ilen _ _ _ MWm) as BL. pose proof MWm as (MB & FRm & HL).
  split; [|split].
  - replace (pp + 16384) with (pp + 16384) by reflexivity.
    apply (MBr_pp_store sp m rest src pp lo HOK Ib m1 16384 (le64 len') MB ltac:(lia)).
    rewrite length_le64. lia.
  - apply FR_write; [exact FRm | lia | rewrite length_le64; lia].
  - apply bytes_at_write_same; [lia | rewrite length_le64; lia].
Qed.

Lemma mw_call : forall Ib len m1 m2 (o n a : Z) bs, MW Ib len m1 -> a = pp + o ->
  munch [(a, a + n)] m1 m2 -> wmono rsegs m1 m2 -> mem_inv rsegs m2 ->
  bytes_at rsegs m2 a bs -> Z.of_nat (length bs) = n -> 0 <= o -> o + n <= 19744 ->
  (o + n <= 16384 \/ 16392 <= o) ->
  MW (overwrite Ib (Z.to_nat o) bs) len m2.
Proof.
  intros Ib len m1 m2 o n a bs MWm -> MU WM MI HB Hbs Ho Hn Hd. pose proof rng as R.
  pose proof (mw_ilen _ _ _ MWm) as BL. pose proof MWm as (MB & FRm & HL).
  split; [|split].
  - apply (MBr_call_pp sp m rest src pp lo HOK Ib m1 m2 o n bs MB MU WM MI HB Hbs Ho).
    unfold POD_PROPS. lia.
  - apply (FR_munch m1 m2 (pp + o) n FRm MU); lia.
  - apply (bytes_at_transport rsegs _ m1 m2 _ _ HL MU).
    cbn [disjoint_from]. rewrite length_le64. split; [lia | exact I].
Qed.

(** The pod's body inside the 104-byte object on the stack (pod.h:72-74). *)
Lemma body_at : forall m1, bytes_at rsegs m1 (bv_unsigned sp + 0x88) (ent_mem e) ->
  bytes_at rsegs m1 (bv_unsigned sp + 0x90) (e_body e).
Proof.
  intros m1 H. unfold ent_mem in H.
  apply bytes_at_app in H as [_ H]. rewrite length_le32 in H.
  apply bytes_at_app in H as [_ H]. rewrite length_le32 in H.
  apply bytes_at_app in H as [H _].
  replace (bv_unsigned sp + 0x90) with (bv_unsigned sp + 0x88 + Z.of_nat 4 + Z.of_nat 4) by (cbn; lia).
  exact H.
Qed.

(** ** The recorded pods at this cut *)
Lemma fp_none : seen_of ps = false -> first_params ps = None.
Proof.
  intros H. unfold seen_of in H. unfold first_params.
  destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:E; [|reflexivity].
  apply find_some in E as [Hin Hk]. exfalso.
  assert (HX : existsb (fun kv => fst kv =? POD_PROP_PARAMS) ps = true)
    by (apply existsb_exists; exists kv; split; assumption).
  congruence.
Qed.

Lemma first_true : first_of ps = true -> ES0 = es /\ ES1 = es ++ [e].
Proof.
  intros H. unfold first_of in H. apply negb_true_iff in H.
  pose proof (fp_none H) as HN.
  assert (HPF : pc_first (PbCut sh ps (Some es)) = true)
    by (unfold pc_first; cbn [pc_props]; apply negb_true_iff; exact H).
  assert (E0 : ES0 = es).
  { unfold ES0, pc_ents. cbn [pc_props pc_open]. rewrite HN. reflexivity. }
  split; [exact E0|].
  unfold ES1. rewrite (pc_ents_pod sh ps es e HPF). unfold ES0 in E0. rewrite E0. reflexivity.
Qed.

Lemma first_false : first_of ps = false -> ES1 = ES0.
Proof.
  intros H. unfold ES1, ES0. apply (pc_ents_pod_other sh ps es e).
  unfold pc_first. cbn [pc_props]. unfold first_of in H. exact H.
Qed.

Lemma ES0_wf : Forall ent_wf ES0 /\ (length ES0 <= 32)%nat.
Proof.
  destruct (first_of ps) eqn:EF.
  - destruct (first_true EF) as [E0 _]. rewrite E0. split; [exact HES | lia].
  - unfold ES0, pc_ents. cbn [pc_props pc_open].
    destruct (first_params ps) as [[v|esx]|] eqn:E.
    + split; [constructor | cbn; lia].
    + unfold first_params in E.
      destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:EF2; [|discriminate].
      cbn in E. apply find_some in EF2 as [Hin _].
      pose proof wf_pval as WP. rewrite Forall_forall in WP.
      pose proof wf_ents as WE. apply all_ents_Forall in WE. rewrite Forall_forall in WE.
      specialize (WP kv Hin). specialize (WE kv Hin).
      injection E as E. rewrite E in WP, WE. cbn [ents_of] in WE. split; [exact WE | exact WP].
    + exfalso. unfold first_of in EF. apply negb_false_iff in EF. unfold seen_of in EF.
      unfold first_params in E.
      destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:EF2; [discriminate|].
      apply existsb_exists in EF as [kv [Hin Hk]].
      pose proof (find_none _ _ EF2 kv Hin) as Hn. cbn in Hn. congruence.
Qed.

Lemma ES1_wf : Forall ent_wf ES1 /\ (length ES1 <= 32)%nat.
Proof.
  destruct (first_of ps) eqn:EF.
  - destruct (first_true EF) as [_ E1]. rewrite E1. rewrite length_app. cbn [length].
    split; [apply Forall_app; split; [exact HES | constructor; [exact HEW | constructor]] | lia].
  - rewrite (first_false EF). exact ES0_wf.
Qed.

(** ** The latch 0x13618 *)
Lemma latch_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s5 t3 t4 t5 t6 : word) m1,
  MW (IMG (b0 ++ enc_pod e) ES1) (L0 + 8 + sz + pd) m1 ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r)
    (MS (mkR ra sp gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
             a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384)) a7 (Z_to_bv 64 MULT10)
             s3 (Z_to_bv 64 (Z.of_nat (length r))) s5 (Z_to_bv 64 (cur rest src r))
             (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k))
             (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
         F (Z_to_bv 64 0x13618) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s5 t3 t4 t5 t6 m1 MWm.
  pose proof MWm as (MB & (CF & CV & _ & _) & _).
  apply evt_done. unfold CNTL. cbv beta.
  exists ra, t0, t1, t2, a0, a1, a2, a3, a4, a5, a7, s3, s5, t3, t4, t5, t6, m1.
  split; [reflexivity|].
  split; [rewrite img_cut1; exact MB|].
  split; [exact CF|]. split; [exact CV|].
  split; [exact HSUF|]. split; [exact HWF|]. split; [exact HSH|].
  split; [apply Forall_app; split; [exact HES | constructor; [exact HEW | constructor]]|].
  split; [exact HK|]. split; [exact HK32|]. split; [exact HPS2|].
  split; [exact HCNT | exact HKC].
Qed.

(** ** 0x135e0 -> 0x13618: the record copy pp->ent[pp->n_ent++] = e (pod.h:431-432) *)
Lemma rec_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s5 t3 t4 t5 t6 : word) m1,
  MW (IMG (b0 ++ enc_pod e) ES0) (L0 + 8 + sz + pd) m1 ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r)
    (MS (mkR ra sp gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
             a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384)) a7 (Z_to_bv 64 MULT10)
             s3 (Z_to_bv 64 (Z.of_nat (length r))) s5 (Z_to_bv 64 (cur rest src r))
             (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k))
             (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
         F (Z_to_bv 64 0x135e0) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a7 s3 s5 t3 t4 t5 t6 m1 MWm.
  pose proof rng as R. pose proof L0_hi. pose proof L0_lo. pose proof sz_rng. pose proof pd_rng.
  pose proof enc_len as EL.
  destruct ES0_wf as [W0f W0l]. destruct ES1_wf as [W1f W1l].
  assert (LB : Z.of_nat (length (b0 ++ enc_pod e)) = L0 + 8 + sz + pd)
    by (rewrite length_app; unfold L0 in *; lia).
  pose proof MWm as (MB & FRm & HL).
  destruct FRm as (CF & CV & C78 & CE).
  pose proof CF as (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80).
  pose proof CV as (V00 & V08 & V18 & V30 & V48 & V58 & V70).
  destruct (first_of ps) eqn:EF.
  - (* the first SPA_PROP_params Struct: the pod is recorded *)
    destruct (first_true EF) as [E0 E1].
    try rewrite EF in V70. cbn [Z.b2z] in V70.
    assert (HR70 : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 0x70)) 8
                   = Some (le8 (Z_to_bv 64 1)))
      by (apply rd8; [exact V70 | apply length_le8]).
    step. clear HR70. step. if_false.
    (* 0x135e8 ld a2,0x40(sp) *)
    assert (HR40 : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 0x40)) 8
                   = Some (le8 (Z_to_bv 64 (pp + 19732))))
      by (apply rd8; [exact F40 | apply length_le8]).
    step. clear HR40.
    (* 0x135ec lw a0,0(a2) *)
    assert (HRN : ov_read_bytes rsegs m1 (wa (pp + 19732)) 4
                  = Some (le4 (Z_to_bv 64 (Z.of_nat k)))).
    { rewrite le4_le32.
      pose proof (MBr_read sp m rest src pp lo (IMG (b0 ++ enc_pod e) ES0) m1 19732 4 MB
                    ltac:(lia) ltac:(pose proof (mw_ilen _ _ _ MWm); lia)) as X.
      unfold IMG in X.
      rewrite (nent_slice (b0 ++ enc_pod e) isp0 hasp0 pst0 ES0 false ltac:(lia) W0l
                 (bodies96 ES0 W0f)) in X.
      rewrite E0, HK in X. exact X. }
    step. clear HRN.
    rewrite (sx32_id (Z.of_nat k)) by lia.
    (* 0x135f0 addi a1,a0,1; 0x135f4 addi a3,zero,0x68; 0x135f8 mul a0,a0,a3 *)
    step. step. step.
    rewrite (unsigned_lit (Z.of_nat k)) by lia.
    (* 0x135fc sw a1,0(a2) *)
    assert (HS : store_ok rsegs m1 (wa (pp + 19732)) 4 = true)
      by (apply (mw_ok _ _ _ 19732 _ 4%nat MWm); lia).
    step. clear HS.
    assert (MW2 : MW (overwrite (IMG (b0 ++ enc_pod e) ES0) (Z.to_nat 19732)
                        (le4 (Z_to_bv 64 (Z.of_nat k + 1)))) (L0 + 8 + sz + pd)
                     (write_to_mem m1 (Z_to_bv 64 (pp + 19732)) (le4 (Z_to_bv 64 (Z.of_nat k + 1))))).
    { apply (mw_store _ _ _ 19732 _ _ MWm); [reflexivity | lia | rewrite length_le4; lia
                                            | rewrite length_le4; lia]. }
    clear MB HL CF CV C78 CE F10 F20 F38 F40 F50 F60 F68 F80 V00 V08 V18 V30 V48 V58 V70 MWm.
    gen_mem MW2 m2.
    pose proof MW2 as (MB2 & FR2 & HL2).
    pose proof FR2 as (CF2 & CV2 & C782 & CE2).
    pose proof CF2 as (G10 & G20 & G38 & G40 & G50 & G60 & G68 & G80).
    (* 0x13600 ld a1,0x38(sp) *)
    assert (HR38 : ov_read_bytes rsegs m2 (wa (bv_unsigned sp + 0x38)) 8
                   = Some (le8 (Z_to_bv 64 (pp + 16404))))
      by (apply rd8; [exact G38 | apply length_le8]).
    step. clear HR38.
    (* 0x13604 add a0,a1,a0 *)
    step.
    try rewrite (unsigned_lit (pp + 16404)) by lia.
    try rewrite (unsigned_lit (Z.of_nat k * 104)) by lia.
    (* 0x13608 addi a1,sp,0x88; 0x1360c addi a2,zero,0x68; 0x13610 jal memcpy *)
    step. step. step.
    eapply evt_cut.
    { eapply MCPY with (src := ent_mem e).
      - rewrite (unsigned_lit (bv_unsigned sp + 0x88)) by lia. exact CE2.
      - rewrite (unsigned_lit 104) by lia. rewrite (length_ent_mem e) by (rewrite body_len; lia).
        reflexivity.
      - rewrite (unsigned_lit (pp + 16404 + Z.of_nat k * 104)) by lia.
        rewrite (unsigned_lit 104) by lia.
        replace (pp + 16404 + Z.of_nat k * 104) with (pp + (16404 + Z.of_nat k * 104)) by lia.
        apply (MBr_pp_cells sp m rest src pp lo _ m2 (16404 + Z.of_nat k * 104) 104%nat MB2);
          [lia | pose proof (mw_ilen _ _ _ MW2); lia].
      - rewrite (unsigned_lit (bv_unsigned sp + 0x88)) by lia.
        rewrite (unsigned_lit (pp + 16404 + Z.of_nat k * 104)) by lia.
        rewrite (unsigned_lit 104) by lia. lia.
      - destruct MB2 as (_ & _ & _ & _ & _ & _ & MI2 & _). exact MI2. }
    intros ms' Hpost. unfold memcpy_post in Hpost.
    destruct Hpost as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m3 &
                       Ems & MU3 & WM3 & MI3 & CB3 & _).
    subst ms'. ret_even.
    rewrite (unsigned_lit (pp + 16404 + Z.of_nat k * 104)) in MU3, CB3 by lia.
    rewrite (unsigned_lit 104) in MU3, CB3 by lia.
    assert (MW3 : MW (overwrite (overwrite (IMG (b0 ++ enc_pod e) ES0) (Z.to_nat 19732)
                        (le4 (Z_to_bv 64 (Z.of_nat k + 1))))
                        (Z.to_nat (16404 + Z.of_nat k * 104)) (ent_mem e)) (L0 + 8 + sz + pd) m3).
    { apply (mw_call _ _ m2 m3 (16404 + Z.of_nat k * 104) 104
               (pp + 16404 + Z.of_nat k * 104) (ent_mem e) MW2);
        [lia | | exact WM3 | exact MI3 | | | lia | lia | lia].
      - replace (pp + 16404 + Z.of_nat k * 104 + 104)
          with (pp + 16404 + Z.of_nat k * 104 + 104) by reflexivity. exact MU3.
      - exact (rw_cells_CB_bytes m3 _ 104%nat _ CB3).
      - rewrite (length_ent_mem e) by (rewrite body_len; lia). reflexivity. }
    clear MB2 HL2 CF2 CV2 C782 CE2 G10 G20 G38 G40 G50 G60 G68 G80 MW2 CB3 MU3 WM3 MI3.
    gen_mem MW3 m4.
    (* 0x13614 ld a6,0x80(sp) *)
    pose proof MW3 as (MB4 & FR4 & HL4). pose proof FR4 as (CF4 & _).
    pose proof CF4 as (H10 & H20 & H38 & H40 & H50 & H60 & H68 & H80).
    assert (HR80 : ov_read_bytes rsegs m4 (wa (bv_unsigned sp + 0x80)) 8
                   = Some (le8 (Z_to_bv 64 (pp + 16384))))
      by (apply rd8; [exact H80 | apply length_le8]).
    step. clear HR80.
    apply latch_ok.
    replace (IMG (b0 ++ enc_pod e) ES1) with
      (overwrite (overwrite (IMG (b0 ++ enc_pod e) ES0) (Z.to_nat 19732)
          (le4 (Z_to_bv 64 (Z.of_nat k + 1)))) (Z.to_nat (16404 + Z.of_nat k * 104)) (ent_mem e));
      [exact MW3|].
    rewrite le4_le32. unfold IMG. rewrite E1.
    assert (HL0 : (length ES0 < 32)%nat) by (rewrite E0; lia).
    assert (HF0 : Forall (fun z => (length (e_body z) <= 96)%nat) (ES0 ++ [e])).
    { apply bodies96. rewrite E0. apply Forall_app.
      split; [exact HES | constructor; [exact HEW | constructor]]. }
    replace (Z.of_nat k) with (Z.of_nat (length ES0)) by (rewrite E0, HK; reflexivity).
    rewrite <- E0.
    apply img_ent; [lia | exact HL0 | exact HF0].
  - (* a later params Struct: nothing is recorded *)
    try rewrite EF in V70. cbn [Z.b2z] in V70.
    assert (HR70 : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 0x70)) 8
                   = Some (le8 (Z_to_bv 64 0)))
      by (apply rd8; [exact V70 | apply length_le8]).
    step. clear HR70. step. if_true.
    apply latch_ok. rewrite (first_false EF). exact MWm.
Qed.

(** ** 0x135ac -> 0x135e0: the pad to a multiple of eight (pod.h:187) *)
Lemma pad_ok : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a7 s3 s4 t3 t4 t5 t6 : word) m1,
  MW (IMG (b0 ++ le32 sz ++ le32 ty ++ e_body e) ES0) (L0 + 8 + sz) m1 ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r)
    (MS (mkR ra sp gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
             (Z_to_bv 64 (L0 + 8 + sz)) a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384)) a7
             (Z_to_bv 64 MULT10) s3 s4 (Z_to_bv 64 16384) (Z_to_bv 64 (cur rest src r))
             (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S8V) (Z_to_bv 64 (Z.of_nat k))
             (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
         F (Z_to_bv 64 0x135ac) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a7 s3 s4 t3 t4 t5 t6 m1 MWm.
  pose proof rng as R. pose proof L0_hi. pose proof L0_lo. pose proof sz_rng. pose proof pd_rng.
  pose proof L0_div as DV.
  assert (EPD : pad8 (L0 + 8 + sz) = pd).
  { unfold pd. replace (L0 + 8 + sz) with ((L0 + 8) + sz) by lia.
    apply pad8_shift. destruct DV as [c ->]. exists (c + 1). lia. }
  assert (LBC : Z.of_nat (length (b0 ++ le32 sz ++ le32 ty ++ e_body e)) = L0 + 8 + sz).
  { rewrite !length_app, !length_le32, body_len. unfold L0 in *. lia. }
  pose proof MWm as (MB & FRm & HL). pose proof FRm as (CF & CV & C78 & CE).
  pose proof CF as (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80).
  (* 0x135ac ld s4,0x78(sp) *)
  assert (HR78 : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 0x78)) 8
                 = Some (le8 (Z_to_bv 64 (Z.of_nat (length r)))))
    by (apply rd8; [exact C78 | apply length_le8]).
  step. clear HR78.
  (* 0x135b0 negw a1,a0; 0x135b4 andi s3,a1,7 *)
  step. step.
  rewrite (neg_and7 (L0 + 8 + sz)) by lia. rewrite EPD.
  (* 0x135b8 add a1,s3,a0; 0x135bc bltu s5,a1 *)
  step.
  assert (BND : bv_ltu (Z_to_bv 64 16384) (Z_to_bv 64 (pd + (L0 + 8 + sz))) = false)
    by (apply put_cap_dead'; lia).
  step. rewrite BND; cbv iota. clear BND.
  (* 0x135c0 add a0,s11,a0; 0x135c4 mv a1,zero; 0x135c8 mv a2,s3; 0x135cc jal memset *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MSET.
    - rewrite (unsigned_lit (pp + (L0 + 8 + sz))) by lia.
      rewrite (unsigned_lit pd) by lia.
      apply (MBr_pp_cells sp m rest src pp lo _ m1 (L0 + 8 + sz) (Z.to_nat pd) MB);
        [lia | pose proof (mw_ilen _ _ _ MWm); lia].
    - destruct MB as (_ & _ & _ & _ & _ & _ & MI & _). exact MI. }
  intros ms' Hpost. unfold memset_post in Hpost.
  destruct Hpost as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 &
                     Ems & MU2 & WM2 & MI2 & CB2).
  subst ms'. ret_even.
  rewrite (unsigned_lit (pp + (L0 + 8 + sz))) in MU2, CB2 by lia.
  rewrite (unsigned_lit pd) in MU2, CB2 by lia.
  rewrite (unsigned_lit 0) in CB2 by lia.
  change (0 mod 256) with 0 in CB2.
  assert (MW2 : MW (overwrite (IMG (b0 ++ le32 sz ++ le32 ty ++ e_body e) ES0)
                      (Z.to_nat (L0 + 8 + sz)) (zeros (Z.to_nat pd))) (L0 + 8 + sz) m2).
  { apply (mw_call _ _ m1 m2 (L0 + 8 + sz) pd (pp + (L0 + 8 + sz)) (zeros (Z.to_nat pd)) MWm);
      [lia | exact MU2 | exact WM2 | exact MI2 | | rewrite length_zeros; lia | lia | lia | lia].
    exact (rw_cells_CB_bytes m2 _ (Z.to_nat pd) _ CB2). }
  clear MB HL CF CV C78 CE F10 F20 F38 F40 F50 F60 F68 F80 MWm CB2 MU2 WM2 MI2.
  gen_mem MW2 m3.
  pose proof MW2 as (MB2 & FR2 & HL2). pose proof FR2 as (CF2 & CV2 & C782 & CE2).
  pose proof CF2 as (G10 & G20 & G38 & G40 & G50 & G60 & G68 & G80).
  (* 0x135d0 ld a6,0x80(sp) *)
  assert (HR80 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + 0x80)) 8
                 = Some (le8 (Z_to_bv 64 (pp + 16384))))
    by (apply rd8; [exact G80 | apply length_le8]).
  step. clear HR80.
  (* 0x135d4 ld a0,0(a6) *)
  pose proof (mw_rd_len _ _ _ MW2) as HRL. step. clear HRL.
  (* 0x135d8 add a0,a0,s3; 0x135dc sd a0,0(a6) *)
  step.
  assert (HS : store_ok rsegs m3 (wa (pp + 16384)) 8 = true)
    by (apply (mw_ok _ _ _ 16384 _ 8%nat MW2); lia).
  step. clear HS.
  rewrite le8_lit64.
  assert (MW3 : MW (IMG (b0 ++ enc_pod e) ES0) (L0 + 8 + sz + pd)
                   (write_to_mem m3 (Z_to_bv 64 (pp + 16384)) (le64 (L0 + 8 + sz + pd)))).
  { replace (IMG (b0 ++ enc_pod e) ES0)
      with (overwrite (overwrite (IMG (b0 ++ le32 sz ++ le32 ty ++ e_body e) ES0)
              (Z.to_nat (L0 + 8 + sz)) (zeros (Z.to_nat pd)))
              (Z.to_nat 16384) (le64 (L0 + 8 + sz + pd))).
    - apply (mw_setlen _ (L0 + 8 + sz) _ _ MW2). lia.
    - assert (LZ : length (zeros (Z.to_nat pd)) = Z.to_nat pd) by apply length_zeros.
      replace (Z.to_nat (L0 + 8 + sz)) with (length (b0 ++ le32 sz ++ le32 ty ++ e_body e)) by lia.
      replace (L0 + 8 + sz + pd)
        with (Z.of_nat (length (b0 ++ le32 sz ++ le32 ty ++ e_body e))
              + Z.of_nat (length (zeros (Z.to_nat pd)))) by lia.
      unfold IMG. rewrite img_app by lia.
      f_equal. unfold enc_pod, sz, ty, pd. rewrite <- !app_assoc. reflexivity. }
  replace (L0 + 8 + sz + pd) with (L0 + 8 + sz + pd) in MW3 by reflexivity.
  clear MB2 HL2 CF2 CV2 C782 CE2 G10 G20 G38 G40 G50 G60 G68 G80 MW2.
  gen_mem MW3 m4.
  apply rec_ok. exact MW3.
Qed.

(** ** 0x13580 -> 0x135ac: memcpy of the pod's body (pod.h:204, :179) *)
Lemma body_ok : forall (ra t0 t1 t2 a1 a2 a3 a4 a5 a7 s3 t3 t4 t5 t6 : word) m1,
  MW (IMG (b0 ++ le32 sz ++ le32 ty) ES0) (L0 + 8) m1 ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r)
    (MS (mkR ra sp gp tp t0 t1 t2
             (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
             (Z_to_bv 64 (L0 + 8)) a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384)) a7
             (Z_to_bv 64 MULT10) s3 (Z_to_bv 64 sz) (Z_to_bv 64 16384)
             (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S8V)
             (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
         F (Z_to_bv 64 0x13580) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a1 a2 a3 a4 a5 a7 s3 t3 t4 t5 t6 m1 MWm.
  pose proof rng as R. pose proof L0_hi. pose proof L0_lo. pose proof sz_rng. pose proof pd_rng.
  assert (LBB : Z.of_nat (length (b0 ++ le32 sz ++ le32 ty)) = L0 + 8)
    by (rewrite !length_app, !length_le32; unfold L0 in *; lia).
  pose proof MWm as (MB & FRm & HL). pose proof FRm as (CF & CV & C78 & CE).
  pose proof CF as (F10 & F20 & F38 & F40 & F50 & F60 & F68 & F80).
  (* 0x13580 sext.w s4,s4 *)
  step. rewrite (sext32_id sz) by lia.
  (* 0x13584 add a1,a0,s4; 0x13588 bltu s5,a1 *)
  step.
  assert (BND : bv_ltu (Z_to_bv 64 16384) (Z_to_bv 64 (L0 + 8 + sz)) = false)
    by (apply put_cap_dead'; lia).
  step. rewrite BND; cbv iota. clear BND.
  (* 0x1358c add a0,s11,a0; 0x13590 addi a1,sp,0x90; 0x13594 mv a2,s4; 0x13598 jal memcpy *)
  step. step. step. step.
  eapply evt_cut.
  { eapply MCPY with (src := e_body e).
    - rewrite (unsigned_lit (bv_unsigned sp + 0x90)) by lia. apply body_at. exact CE.
    - rewrite (unsigned_lit sz) by lia. exact body_len.
    - rewrite (unsigned_lit (pp + (L0 + 8))) by lia. rewrite (unsigned_lit sz) by lia.
      apply (MBr_pp_cells sp m rest src pp lo _ m1 (L0 + 8) (Z.to_nat sz) MB);
        [lia | pose proof (mw_ilen _ _ _ MWm); lia].
    - rewrite (unsigned_lit (bv_unsigned sp + 0x90)) by lia.
      rewrite (unsigned_lit (pp + (L0 + 8))) by lia. rewrite (unsigned_lit sz) by lia. lia.
    - destruct MB as (_ & _ & _ & _ & _ & _ & MI & _). exact MI. }
  intros ms' Hpost. unfold memcpy_post in Hpost.
  destruct Hpost as (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 &
                     Ems & MU2 & WM2 & MI2 & CB2 & _).
  subst ms'. ret_even.
  rewrite (unsigned_lit (pp + (L0 + 8))) in MU2, CB2 by lia.
  rewrite (unsigned_lit sz) in MU2, CB2 by lia.
  assert (MW2 : MW (overwrite (IMG (b0 ++ le32 sz ++ le32 ty) ES0) (Z.to_nat (L0 + 8)) (e_body e))
                   (L0 + 8) m2).
  { apply (mw_call _ _ m1 m2 (L0 + 8) sz (pp + (L0 + 8)) (e_body e) MWm);
      [lia | exact MU2 | exact WM2 | exact MI2 | | rewrite body_len; lia | lia | lia | lia].
    exact (rw_cells_CB_bytes m2 _ (Z.to_nat sz) _ CB2). }
  clear MB HL CF CV C78 CE F10 F20 F38 F40 F50 F60 F68 F80 MWm CB2 MU2 WM2 MI2.
  gen_mem MW2 m3.
  pose proof MW2 as (MB2 & FR2 & HL2). pose proof FR2 as (CF2 & CV2 & C782 & CE2).
  pose proof CF2 as (G10 & G20 & G38 & G40 & G50 & G60 & G68 & G80).
  (* 0x1359c ld a6,0x80(sp) *)
  assert (HR80 : ov_read_bytes rsegs m3 (wa (bv_unsigned sp + 0x80)) 8
                 = Some (le8 (Z_to_bv 64 (pp + 16384))))
    by (apply rd8; [exact G80 | apply length_le8]).
  step. clear HR80.
  (* 0x135a0 ld a0,0(a6) *)
  pose proof (mw_rd_len _ _ _ MW2) as HRL. step. clear HRL.
  (* 0x135a4 add a0,a0,s4; 0x135a8 sd a0,0(a6) *)
  step.
  assert (HS : store_ok rsegs m3 (wa (pp + 16384)) 8 = true)
    by (apply (mw_ok _ _ _ 16384 _ 8%nat MW2); lia).
  step. clear HS.
  rewrite le8_lit64.
  assert (MW3 : MW (IMG (b0 ++ le32 sz ++ le32 ty ++ e_body e) ES0) (L0 + 8 + sz)
                   (write_to_mem m3 (Z_to_bv 64 (pp + 16384)) (le64 (L0 + 8 + sz)))).
  { replace (IMG (b0 ++ le32 sz ++ le32 ty ++ e_body e) ES0)
      with (overwrite (overwrite (IMG (b0 ++ le32 sz ++ le32 ty) ES0)
              (Z.to_nat (L0 + 8)) (e_body e)) (Z.to_nat 16384) (le64 (L0 + 8 + sz))).
    - apply (mw_setlen _ (L0 + 8) _ _ MW2). lia.
    - pose proof body_len as BLN.
      replace (Z.to_nat (L0 + 8)) with (length (b0 ++ le32 sz ++ le32 ty)) by lia.
      replace (L0 + 8 + sz) with (Z.of_nat (length (b0 ++ le32 sz ++ le32 ty))
                                  + Z.of_nat (length (e_body e))) by lia.
      unfold IMG. rewrite img_app by lia.
      f_equal. rewrite <- !app_assoc. reflexivity. }
  clear MB2 HL2 CF2 CV2 C782 CE2 G10 G20 G38 G40 G50 G60 G68 G80 MW2.
  gen_mem MW3 m4.
  apply pad_ok. exact MW3.
Qed.

(** ** 0x1350c -> 0x13580: the size word and the type word (pod.h:202-203, :179-180) *)
Lemma puts_ok : forall (ra t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 : word) m1,
  MW (IMG b0 ES0) L0 m1 ->
  evt rsegs (CNTL sp gp tp F fc m rest fl src pp lo sh np ps i cnt es k e r)
    (MS (mkR ra sp gp tp (Z_to_bv 64 (-0x4001)) t1 t2
             (Z_to_bv 64 (bv_unsigned sp + 0x128)) (Z_to_bv 64 (bv_unsigned sp + 0xf0))
             a0 a1 a2 a3 a4 a5 (Z_to_bv 64 (pp + 16384)) (Z_to_bv 64 (-0x3ffd))
             (Z_to_bv 64 MULT10) (Z_to_bv 64 ty) (Z_to_bv 64 sz) (Z_to_bv 64 16384)
             (Z_to_bv 64 (cur rest src r)) (Z_to_bv 64 (at_of sh ps)) (Z_to_bv 64 S8V)
             (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 S10V) (Z_to_bv 64 pp) t3 t4 t5 t6)
         F (Z_to_bv 64 0x1350c) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t1 t2 a0 a1 a2 a3 a4 a5 t3 t4 t5 t6 m1 MWm.
  pose proof rng as R. pose proof L0_hi. pose proof L0_lo. pose proof sz_rng. pose proof pd_rng.
  pose proof ty_rng as TY.
  assert (LB0 : Z.of_nat (length b0) = L0) by reflexivity.
  pose proof (mw_ilen _ _ _ MWm) as LIM.
  (* 0x1350c ld a0,0(a6) *)
  pose proof (mw_rd_len _ _ _ MWm) as HRL. step. clear HRL.
  (* 0x13510 addi a1,a0,0x70; 0x13514 bltu s5,a1 *)
  step.
  assert (B1 : bv_ltu (Z_to_bv 64 16384) (Z_to_bv 64 (L0 + 112)) = false)
    by (apply put_cap_dead'; lia).
  step. rewrite B1; cbv iota. clear B1.
  (* 0x13518 add a1,a0,a7; 0x1351c bltu a1,t0 *)
  step.
  assert (B2 : bv_ltu (Z_to_bv 64 (L0 + -16381)) (Z_to_bv 64 (-16385)) = false)
    by (apply put_cap_dead; lia).
  step. rewrite B2; cbv iota. clear B2.
  (* 0x13520 add a0,s11,a0; the three shifts of s4 *)
  step. step. step. step.
  rewrite (unsigned_lit sz) by lia.
  (* 0x13530 .. 0x1353c: the four byte stores of the size word *)
  assert (HS0 : store_ok rsegs m1 (wa (pp + L0)) 1 = true)
    by (apply (mw_ok _ _ _ L0 _ 1%nat MWm); lia).
  step. clear HS0.
  assert (MW1 : MW (overwrite (IMG b0 ES0) (Z.to_nat L0) (le1 (Z_to_bv 64 sz))) L0
                   (write_to_mem m1 (Z_to_bv 64 (pp + L0)) (le1 (Z_to_bv 64 sz)))).
  { apply (mw_store _ _ _ L0 _ _ MWm); [reflexivity | lia | rewrite length_le1; lia
                                        | rewrite length_le1; lia]. }
  clear MWm. gen_mem MW1 m2.
  assert (HS1 : store_ok rsegs m2 (wa (pp + L0 + 1)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 1) _ 1%nat MW1); lia).
  step. clear HS1.
  assert (MW2 : MW (overwrite (overwrite (IMG b0 ES0) (Z.to_nat L0) (le1 (Z_to_bv 64 sz)))
                     (Z.to_nat (L0 + 1)) (le1 (Z_to_bv 64 (Z.shiftr sz 8)))) L0
                   (write_to_mem m2 (Z_to_bv 64 (pp + L0 + 1)) (le1 (Z_to_bv 64 (Z.shiftr sz 8))))).
  { apply (mw_store _ _ _ (L0 + 1) _ _ MW1); [lia | lia | rewrite length_le1; lia
                                              | rewrite length_le1; lia]. }
  clear MW1. gen_mem MW2 m3.
  assert (HS2 : store_ok rsegs m3 (wa (pp + L0 + 2)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 2) _ 1%nat MW2); lia).
  step. clear HS2.
  assert (MW3 : MW (overwrite (overwrite (overwrite (IMG b0 ES0) (Z.to_nat L0) (le1 (Z_to_bv 64 sz)))
                     (Z.to_nat (L0 + 1)) (le1 (Z_to_bv 64 (Z.shiftr sz 8))))
                     (Z.to_nat (L0 + 2)) (le1 (Z_to_bv 64 (Z.shiftr sz 16)))) L0
                   (write_to_mem m3 (Z_to_bv 64 (pp + L0 + 2)) (le1 (Z_to_bv 64 (Z.shiftr sz 16))))).
  { apply (mw_store _ _ _ (L0 + 2) _ _ MW2); [lia | lia | rewrite length_le1; lia
                                              | rewrite length_le1; lia]. }
  clear MW2. gen_mem MW3 m4.
  assert (HS3 : store_ok rsegs m4 (wa (pp + L0 + 3)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 3) _ 1%nat MW3); lia).
  step. clear HS3.
  assert (MW4 : MW (overwrite (IMG b0 ES0) (Z.to_nat L0) (le32 sz)) L0
                   (write_to_mem m4 (Z_to_bv 64 (pp + L0 + 3)) (le1 (Z_to_bv 64 (Z.shiftr sz 24))))).
  { rewrite <- (ow32 (IMG b0 ES0) L0 sz ltac:(lia) ltac:(lia)).
    apply (mw_store _ _ _ (L0 + 3) _ _ MW3); [lia | lia | rewrite length_le1; lia
                                              | rewrite length_le1; lia]. }
  clear MW3. gen_mem MW4 m5.
  (* 0x13540 ld a0,0(a6); 0x13544 addi a0,a0,4; 0x13548 add a1,a0,a7; 0x1354c sd a0,0(a6) *)
  pose proof (mw_rd_len _ _ _ MW4) as HRL. step. clear HRL.
  step. step.
  assert (HS4 : store_ok rsegs m5 (wa (pp + 16384)) 8 = true)
    by (apply (mw_ok _ _ _ 16384 _ 8%nat MW4); lia).
  step. clear HS4.
  rewrite le8_lit64.
  assert (MW5 : MW (IMG (b0 ++ le32 sz) ES0) (L0 + 4)
                   (write_to_mem m5 (Z_to_bv 64 (pp + 16384)) (le64 (L0 + 4)))).
  { replace (IMG (b0 ++ le32 sz) ES0)
      with (overwrite (overwrite (IMG b0 ES0) (Z.to_nat L0) (le32 sz))
              (Z.to_nat 16384) (le64 (L0 + 4))).
    - apply (mw_setlen _ L0 _ _ MW4). lia.
    - replace (Z.to_nat L0) with (length b0) by lia.
      replace (L0 + 4) with (Z.of_nat (length b0) + Z.of_nat (length (le32 sz)))
        by (rewrite length_le32; lia).
      unfold IMG. apply img_app. rewrite length_le32. lia. }
  pose proof (mw_ilen _ _ _ MW5) as LIM1.
  clear MW4 LIM. gen_mem MW5 m6.
  (* 0x13550 bltu a1,t0 *)
  assert (B3 : bv_ltu (Z_to_bv 64 (L0 + -16377)) (Z_to_bv 64 (-16385)) = false).
  { replace (L0 + -16377) with (L0 + 4 + -16381) by lia. apply put_cap_dead. lia. }
  step. rewrite B3; cbv iota. clear B3.
  (* 0x13554 add a0,s11,a0; the three shifts of s3 *)
  step. step. step. step.
  rewrite (unsigned_lit ty) by lia.
  assert (LB1 : Z.of_nat (length (b0 ++ le32 sz)) = L0 + 4)
    by (rewrite length_app, length_le32; lia).
  (* 0x13564 .. 0x13570: the four byte stores of the type word *)
  assert (HT0 : store_ok rsegs m6 (wa (pp + (L0 + 4))) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 4) _ 1%nat MW5); lia).
  step. clear HT0.
  assert (MT1 : MW (overwrite (IMG (b0 ++ le32 sz) ES0) (Z.to_nat (L0 + 4)) (le1 (Z_to_bv 64 ty)))
                   (L0 + 4)
                   (write_to_mem m6 (Z_to_bv 64 (pp + (L0 + 4))) (le1 (Z_to_bv 64 ty)))).
  { apply (mw_store _ _ _ (L0 + 4) _ _ MW5); [reflexivity | lia | rewrite length_le1; lia
                                              | rewrite length_le1; lia]. }
  clear MW5. gen_mem MT1 m7.
  assert (HT1 : store_ok rsegs m7 (wa (pp + (L0 + 4) + 1)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 4 + 1) _ 1%nat MT1); lia).
  step. clear HT1.
  assert (MT2 : MW (overwrite (overwrite (IMG (b0 ++ le32 sz) ES0) (Z.to_nat (L0 + 4))
                       (le1 (Z_to_bv 64 ty)))
                     (Z.to_nat (L0 + 4 + 1)) (le1 (Z_to_bv 64 (Z.shiftr ty 8)))) (L0 + 4)
                   (write_to_mem m7 (Z_to_bv 64 (pp + (L0 + 4) + 1))
                      (le1 (Z_to_bv 64 (Z.shiftr ty 8))))).
  { apply (mw_store _ _ _ (L0 + 4 + 1) _ _ MT1); [lia | lia | rewrite length_le1; lia
                                                  | rewrite length_le1; lia]. }
  clear MT1. gen_mem MT2 m8.
  assert (HT2 : store_ok rsegs m8 (wa (pp + (L0 + 4) + 2)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 4 + 2) _ 1%nat MT2); lia).
  step. clear HT2.
  assert (MT3 : MW (overwrite (overwrite (overwrite (IMG (b0 ++ le32 sz) ES0) (Z.to_nat (L0 + 4))
                       (le1 (Z_to_bv 64 ty)))
                     (Z.to_nat (L0 + 4 + 1)) (le1 (Z_to_bv 64 (Z.shiftr ty 8))))
                     (Z.to_nat (L0 + 4 + 2)) (le1 (Z_to_bv 64 (Z.shiftr ty 16)))) (L0 + 4)
                   (write_to_mem m8 (Z_to_bv 64 (pp + (L0 + 4) + 2))
                      (le1 (Z_to_bv 64 (Z.shiftr ty 16))))).
  { apply (mw_store _ _ _ (L0 + 4 + 2) _ _ MT2); [lia | lia | rewrite length_le1; lia
                                                  | rewrite length_le1; lia]. }
  clear MT2. gen_mem MT3 m9.
  assert (HT3 : store_ok rsegs m9 (wa (pp + (L0 + 4) + 3)) 1 = true)
    by (apply (mw_ok _ _ _ (L0 + 4 + 3) _ 1%nat MT3); lia).
  step. clear HT3.
  assert (MT4 : MW (overwrite (IMG (b0 ++ le32 sz) ES0) (Z.to_nat (L0 + 4)) (le32 ty)) (L0 + 4)
                   (write_to_mem m9 (Z_to_bv 64 (pp + (L0 + 4) + 3))
                      (le1 (Z_to_bv 64 (Z.shiftr ty 24))))).
  { rewrite <- (ow32 (IMG (b0 ++ le32 sz) ES0) (L0 + 4) ty ltac:(lia) ltac:(lia)).
    apply (mw_store _ _ _ (L0 + 4 + 3) _ _ MT3); [lia | lia | rewrite length_le1; lia
                                                  | rewrite length_le1; lia]. }
  clear MT3. gen_mem MT4 m10.
  (* 0x13574 ld a0,0(a6); 0x13578 addi a0,a0,4; 0x1357c sd a0,0(a6) *)
  pose proof (mw_rd_len _ _ _ MT4) as HRL. step. clear HRL.
  step. try replace (L0 + 4 + 4) with (L0 + 8) by lia.
  assert (HT4 : store_ok rsegs m10 (wa (pp + 16384)) 8 = true)
    by (apply (mw_ok _ _ _ 16384 _ 8%nat MT4); lia).
  step. clear HT4.
  rewrite le8_lit64.
  assert (MT5 : MW (IMG (b0 ++ le32 sz ++ le32 ty) ES0) (L0 + 8)
                   (write_to_mem m10 (Z_to_bv 64 (pp + 16384)) (le64 (L0 + 8)))).
  {
    replace (IMG (b0 ++ le32 sz ++ le32 ty) ES0)
      with (overwrite (overwrite (IMG (b0 ++ le32 sz) ES0) (Z.to_nat (L0 + 4)) (le32 ty))
              (Z.to_nat 16384) (le64 (L0 + 8))).
    - apply (mw_setlen _ (L0 + 4) _ _ MT4). lia.
    - replace (Z.to_nat (L0 + 4)) with (length (b0 ++ le32 sz)) by lia.
      replace (L0 + 8) with (Z.of_nat (length (b0 ++ le32 sz)) + Z.of_nat (length (le32 ty)))
        by (rewrite length_le32; lia).
      unfold IMG. rewrite img_app by (rewrite !length_le32; lia).
      f_equal. rewrite <- app_assoc. reflexivity. }
  clear MT4. gen_mem MT5 m11.
  try replace (L0 + 4 + 4) with (L0 + 8) by lia.
  apply body_ok. exact MT5.
Qed.

End Walk.

(** 0x1350c -> 0x13618: the inlined pod_write_ent and the record copy. *)
Theorem write_holds : forall (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (rest : list byte) (fl src pp lo : Z),
  memset_c.memset_contract -> memcpy_c.memcpy_contract ->
  Cut.S_write sp gp tp F fc m rest fl src pp lo.
Proof.
  intros sp gp tp F fc m rest fl src pp lo MSET MCPY HOK sh np ps i cnt es k e r ms HJ.
  destruct HJ as (ra & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & t3 & t4 & t5 & t6 & m1 &
                  Ems & MB & CF & CV & C78 & CE & HSUF & HWF & HSH & HES & HK & HK32 & HEW &
                  HPS2 & HCNT & HKC).
  subst ms.
  eapply puts_ok; try eassumption.
  split; [|split].
  - exact MB.
  - split; [exact CF | split; [exact CV | split; [exact C78 | exact CE]]].
  - apply (len_bytes_of sp m rest src pp lo (pc_buf (PbCut sh ps (Some es)))
             (is_props (PodRec sh ps None)) (has_params (PodRec sh ps None))
             (params_struct (PodRec sh ps None)) (pc_ents (PbCut sh ps (Some es))) false m1).
    + exact MB.
    + destruct (pc_buf_len_open sh ps es
                  (Forall_impl _ (fun kv Hk => proj2 Hk) (proj1 (proj2 HWF)))
                  (proj1 (proj2 (proj2 HWF))) HES) as [HH _].
      lia.
Qed.
