(** reac-pw/fuzz_segconf: the build-independent part of the kit for the satisfiability lemmas of the premises of
    contract family F1 (lib/Prog/*_c.v and lib/U/Prog/*_c.v; written against seg_spec.v of c7b9518dac31: role_enc,
    mconf_encp).
    The per-build parts are Prog/SegSat.v (plain, over Img0.rsegs) and U/Prog/SegSat.v (UBSan, over U/Img0.rsegs);
    the lemmas are in Prog/sat/F1Sat.v and U/Prog/sat/F1Sat.v.

    proves no function (kind: statement text; closed satisfiability lemmas of contract premises). Nothing here is an
    Axiom, a Parameter, an admit or an Admitted.

    What it gives.
    - Canonical images (lists of byte values in Z) of the spine's states, laid out as seg_spec.v's encodings say:
      rconf_img (struct reac_segconf, 16616 bytes), mconf_img (struct mconf, 9236), rseg_img / mseg_img, rtab_img /
      mtab_img (the VLAN tables). Every field the encoding fixes holds the state's value, every other byte is 0.
    - Boolean checkers of seg_spec's encodings (rconf_encb, mconf_encb, mseg_encb, rtab_encb, mtab_encb) with their
      soundness lemmas, so that `rconf_enc rc bs` for a concrete rc and bs is `apply rconf_encb_ok; vm_compute;
      reflexivity` (a closed goal, no targeted vm_compute).
    - A concrete memory RMEM rs built from a list of regions (address, byte values); the first region that holds an
      address gives its byte, an address in no region reads the image (mrd's None branch). The lemmas give bytes_at,
      cstr_at, cstrz_at, stk, wr_at, stack_ok, cat_img and mem_inv of RMEM rs from closed side conditions.
    - The real values (T0, the input D0 whose decode is the payload P0 with one file T0, RC0 / MC0 the states after
      it, the addresses of the blocks and the stack) and the tactics zside / sat_goal that discharge a premise
      conjunct by conjunct. *)
From Stdlib Require Import String.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
Import ListNotations.
Open Scope Z_scope.

(** ** 1. Canonical images *)

Definition le4z (v : Z) : list Z := [v mod 256; (v / 256) mod 256; (v / 65536) mod 256; (v / 16777216) mod 256].
Definition le2z (v : Z) : list Z := [v mod 256; (v / 256) mod 256].
Definition zrep (n : nat) : list Z := repeat 0 n.
Definition padz (s : list Z) (cap : nat) : list Z := s ++ zrep (cap - length s).

(** struct reac_segconf_seg, 356 bytes (seg_spec.v lines 13-15); said_ignored (0x20) is 0. *)
Definition rseg_img (s : rseg) : list Z :=
  padz (rs_name s) 16 ++ le4z (rs_role s) ++ le4z (b2z (rs_role_set s)) ++ le4z (b2z (rs_ignore s)) ++
  le4z (b2z (rs_ignore_set s)) ++ zrep 4 ++ padz (rs_model s) 24 ++ le4z (b2z (rs_model_set s)) ++
  padz (rs_model_file s) 96 ++ padz (rs_role_file s) 96 ++ padz (rs_ignore_file s) 96 ++ le4z (rs_seen_gen s).

(** struct reac_segconf, 16616 bytes: seg[32] (0), n (0x2c80), present + path (0x2c84, 516 bytes, 0), refusal[8][200]
    (0x2e88), n_refusals (0x34c8), refused (0x34cc), overflow (0x34d0), file .. base (0x34d4, 2988 bytes, 0),
    reading[96] (0x4080), gen (0x40e0), padding (0x40e4, 4). *)
Definition rconf_img (rc : rconf) : list Z :=
  concat (map rseg_img (rc_seg rc)) ++ zrep (356 * (32 - length (rc_seg rc))) ++
  le4z (Z.of_nat (length (rc_seg rc))) ++ zrep 516 ++
  concat (map (fun s => padz s 200) (rc_refusal rc)) ++ zrep (200 * (8 - length (rc_refusal rc))) ++
  le4z (Z.of_nat (length (rc_refusal rc))) ++ le4z (rc_refused rc) ++ le4z (rc_overflow rc) ++ zrep 2988 ++
  padz (rc_reading rc) 96 ++ le4z (rc_gen rc) ++ zrep 4.

(** struct mseg, 256 bytes (seg_spec.v lines 18-19). *)
Definition mseg_img (g : mseg) : list Z :=
  padz (ms_name g) 16 ++ le4z (ms_role g) ++ le4z (b2z (ms_role_set g)) ++ le4z (b2z (ms_ignore g)) ++
  le4z (b2z (ms_ignore_set g)) ++ le4z (b2z (ms_model_set g)) ++ padz (ms_model g) 24 ++
  padz (ms_role_file g) 96 ++ padz (ms_ignore_file g) 96 ++ le4z (ms_gen g).

(** struct mconf, 9236 bytes: seg[32] (0), n (0x2000), overflow (0x2004), refused (0x2008), kept[8][112] (0x200c),
    kept_knock[8] (0x238c), n_kept (0x23ac), gen (0x23b0), reading[96] (0x23b4). [pend] is seg_spec.mconf_encp's
    pending knock flag: kept_knock[n_kept] = 1 when pend and n_kept < 8 (m_key's store just before the m_refuse that
    keeps it); mconf_img is the form with no pending flag. *)
Definition mconf_imgp (pend : bool) (mc : mconf) : list Z :=
  concat (map mseg_img (mc_seg mc)) ++ zrep (256 * (32 - length (mc_seg mc))) ++
  le4z (Z.of_nat (length (mc_seg mc))) ++ le4z (mc_overflow mc) ++ le4z (mc_refused mc) ++
  concat (map (fun k => padz (fst k) 112) (mc_kept mc)) ++ zrep (112 * (8 - length (mc_kept mc))) ++
  concat (map (fun k => le4z (b2z (snd k))) (mc_kept mc)) ++
  (if pend && (length (mc_kept mc) <? 8)%nat then le4z 1 ++ zrep (4 * (7 - length (mc_kept mc)))
   else zrep (4 * (8 - length (mc_kept mc)))) ++
  le4z (Z.of_nat (length (mc_kept mc))) ++ le4z (mc_gen mc) ++ padz (mc_reading mc) 96.
Definition mconf_img (mc : mconf) : list Z := mconf_imgp false mc.

(** The VLAN tables: struct reac_declared_vlan (18 bytes) and struct mvlan (20 bytes) per entry. *)
Definition rtab_img (t : list (list Z * Z)) : list Z := concat (map (fun e => padz (fst e) 16 ++ le2z (snd e)) t).
Definition mtab_img (t : list (list Z * Z)) : list Z := concat (map (fun e => padz (fst e) 16 ++ le4z (snd e)) t).
(** The harness's tab block (calloc(cap + 1, 18)): the reader's entries, zeros up to cap, then the guard entry
    tab[cap] of 0x5a (fuzz_segconf.c:649-654); the mt block (calloc(cap + 1, 20)): the model's entries, then zeros. *)
Definition tab_img (t : list (list Z * Z)) (cap : Z) : list Z :=
  rtab_img t ++ zrep (18 * (Z.to_nat cap - length t)) ++ repeat 0x5a 18.
Definition mt_img (t : list (list Z * Z)) (cap : Z) : list Z :=
  mtab_img t ++ zrep (20 * (Z.to_nat cap + 1 - length t)).

(** ** 2. Boolean checkers of seg_spec's encodings *)

Definition nulfreeb (s : list Z) : bool := negb (existsb (Z.eqb 0) s).
Definition byte_okb (z : Z) : bool := (0 <=? z) && (z <? 256).

Lemma nulfreeb_ok : forall s, nulfreeb s = true -> ~ In 0 s.
Proof.
  intros s H Hin. unfold nulfreeb in H. apply negb_true_iff in H.
  assert (E : existsb (Z.eqb 0) s = true) by (apply existsb_exists; exists 0; split; [exact Hin | apply Z.eqb_refl]).
  congruence.
Qed.

Lemma zs_inj : forall f g : list byte, zs f = zs g -> f = g.
Proof.
  induction f as [|x f IH]; intros [|y g] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma bu8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hz.
Qed.

Lemma zs_zb : forall s, forallb byte_okb s = true -> zs (zb s) = s.
Proof.
  induction s as [|z s IH]; intros H; [reflexivity|]. cbn in H. apply andb_true_iff in H as [H1 H2].
  unfold byte_okb in H1. apply andb_true_iff in H1 as [H1 H3]. apply Z.leb_le in H1. apply Z.ltb_lt in H3.
  cbn. rewrite bu8 by lia. f_equal. apply IH. exact H2.
Qed.

Lemma zb_zs : forall bs : list byte, zb (zs bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Definition bytes_eqz (f g : list byte) : bool := leqb (zs f) (zs g).
Lemma bytes_eqz_ok : forall f g, bytes_eqz f g = true -> f = g.
Proof. intros f g H. apply zs_inj. apply leqb_eq. exact H. Qed.

Definition cstr_encb (cap : nat) (s : list Z) (f : list byte) : bool :=
  (length f =? cap)%nat && (length s <? cap)%nat && nulfreeb s && leqb (firstn (S (length s)) (zs f)) (s ++ [0]).
Lemma cstr_encb_ok : forall cap s f, cstr_encb cap s f = true -> cstr_enc cap s f.
Proof.
  intros cap s f H. unfold cstr_encb in H. repeat rewrite andb_true_iff in H. destruct H as [[[H1 H2] H3] H4].
  split; [apply Nat.eqb_eq; exact H1|]. split; [apply Nat.ltb_lt; exact H2|].
  split; [apply nulfreeb_ok; exact H3|]. apply leqb_eq. exact H4.
Qed.

Definition u32_encb (v : Z) (f : list byte) : bool := (0 <=? v) && (v <? 2 ^ 32) && bytes_eqz f (le4 (Z_to_bv 64 v)).
Lemma u32_encb_ok : forall v f, u32_encb v f = true -> u32_enc v f.
Proof.
  intros v f H. unfold u32_encb in H. repeat rewrite andb_true_iff in H. destruct H as [[H1 H2] H3].
  split; [split; [apply Z.leb_le | apply Z.ltb_lt]; assumption | apply bytes_eqz_ok; exact H3].
Qed.

Definition flag_encb (b : bool) (f : list byte) : bool := bytes_eqz f (le4 (Z_to_bv 64 (if b then 1 else 0))).
Lemma flag_encb_ok : forall b f, flag_encb b f = true -> flag_enc b f.
Proof. intros b f H. apply bytes_eqz_ok. exact H. Qed.

Definition role_encb (v : Z) (f : list byte) : bool := u32_encb v f && (v <? 2 ^ 31).
Lemma role_encb_ok : forall v f, role_encb v f = true -> role_enc v f.
Proof.
  intros v f H. unfold role_encb in H. apply andb_true_iff in H as [H1 H2].
  split; [apply u32_encb_ok; exact H1 | apply Z.ltb_lt; exact H2].
Qed.

Definition allidx (n : nat) (P : nat -> bool) : bool := forallb P (seq 0 n).
Lemma allidx_ok : forall n P, allidx n P = true -> forall i, (i < n)%nat -> P i = true.
Proof. intros n P H i Hi. unfold allidx in H. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

(** Split a conjunction that is syntactically one (not inside a definition), destruct an [&&] hypothesis. *)
Ltac csplit := repeat match goal with |- _ /\ _ => split end.
Ltac bdestr H := repeat rewrite andb_true_iff in H; decompose [and] H.
(** [allidx_ok] on the hypothesis [allidx _ _ = true] whose instance closes the goal (backtracking over them). *)
Ltac allidx_use i Hi := match goal with HA : allidx _ _ = true |- _ => exact (allidx_ok _ _ HA i Hi) end.
Ltac enc_fin :=
  lazymatch goal with
  | |- cstr_enc _ _ _ => apply cstr_encb_ok; assumption
  | |- u32_enc _ _ => apply u32_encb_ok; assumption
  | |- role_enc _ _ => apply role_encb_ok; assumption
  | |- flag_enc _ _ => apply flag_encb_ok; assumption
  | |- @eq nat _ _ => apply Nat.eqb_eq; assumption
  | |- @eq Z _ _ => apply Z.eqb_eq; assumption
  | |- @eq (list _) _ _ => apply bytes_eqz_ok; assumption
  | |- (_ <= _)%nat => apply Nat.leb_le; assumption
  | |- (_ < _)%nat => apply Nat.ltb_lt; assumption
  | |- (_ <= _)%Z => apply Z.leb_le; assumption
  | |- (_ < _)%Z => apply Z.ltb_lt; assumption
  end.

Definition rseg_encb (s : rseg) (f : list byte) : bool :=
  (length f =? 356)%nat &&
  cstr_encb 16 (rs_name s) (fld 0 16 f) &&
  role_encb (rs_role s) (fldz RS_ROLE 4 f) &&
  flag_encb (rs_role_set s) (fldz RS_ROLE_SET 4 f) &&
  flag_encb (rs_ignore s) (fldz RS_IGNORE 4 f) &&
  flag_encb (rs_ignore_set s) (fldz RS_IGNORE_SET 4 f) &&
  cstr_encb 24 (rs_model s) (fldz RS_MODEL 24 f) &&
  flag_encb (rs_model_set s) (fldz RS_MODEL_SET 4 f) &&
  cstr_encb 96 (rs_model_file s) (fldz RS_MODEL_FILE 96 f) &&
  cstr_encb 96 (rs_role_file s) (fldz RS_ROLE_FILE 96 f) &&
  cstr_encb 96 (rs_ignore_file s) (fldz RS_IGNORE_FILE 96 f) &&
  u32_encb (rs_seen_gen s) (fldz RS_SEEN_GEN 4 f).
Lemma rseg_encb_ok : forall s f, rseg_encb s f = true -> rseg_enc s f.
Proof. intros s f H. unfold rseg_encb in H. bdestr H. unfold rseg_enc. csplit; enc_fin. Qed.

Definition rconf_encb (rc : rconf) (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? SEG_C_SIZE) && (length (rc_seg rc) <=? 32)%nat &&
  allidx (length (rc_seg rc)) (fun i => rseg_encb (nth i (rc_seg rc) rseg_d) (fld (356 * i) 356 bs)) &&
  u32_encb (Z.of_nat (length (rc_seg rc))) (fldz RC_N 4 bs) &&
  (length (rc_refusal rc) <=? 8)%nat &&
  allidx (length (rc_refusal rc))
    (fun i => cstr_encb 200 (nth i (rc_refusal rc) []) (fld (Z.to_nat RC_REFUSAL + 200 * i) 200 bs)) &&
  u32_encb (Z.of_nat (length (rc_refusal rc))) (fldz RC_NREF 4 bs) &&
  u32_encb (rc_refused rc) (fldz RC_REFUSED 4 bs) &&
  u32_encb (rc_overflow rc) (fldz RC_OVERFLOW 4 bs) &&
  cstr_encb 96 (rc_reading rc) (fldz RC_READING 96 bs) &&
  u32_encb (rc_gen rc) (fldz RC_GEN 4 bs).
Lemma rconf_encb_ok : forall rc bs, rconf_encb rc bs = true -> rconf_enc rc bs.
Proof.
  intros rc bs H. unfold rconf_encb in H. bdestr H. unfold rconf_enc. csplit;
    first [ enc_fin | intros i Hi; lazymatch goal with
      | |- rseg_enc _ _ => apply rseg_encb_ok;
          match goal with HA : allidx (length (rc_seg _)) _ = true |- _ => exact (allidx_ok _ _ HA i Hi) end
      | |- cstr_enc _ _ _ => apply cstr_encb_ok;
          match goal with HA : allidx (length (rc_refusal _)) _ = true |- _ => exact (allidx_ok _ _ HA i Hi) end
      end ].
Qed.

Definition mseg_encb (g : mseg) (f : list byte) : bool :=
  (length f =? 256)%nat &&
  cstr_encb 16 (ms_name g) (fld 0 16 f) &&
  role_encb (ms_role g) (fldz MS_ROLE 4 f) &&
  flag_encb (ms_role_set g) (fldz MS_ROLE_SET 4 f) &&
  flag_encb (ms_ignore g) (fldz MS_IGNORE 4 f) &&
  flag_encb (ms_ignore_set g) (fldz MS_IGNORE_SET 4 f) &&
  flag_encb (ms_model_set g) (fldz MS_MODEL_SET 4 f) &&
  cstr_encb 24 (ms_model g) (fldz MS_MODEL 24 f) &&
  cstr_encb 96 (ms_role_file g) (fldz MS_ROLE_FILE 96 f) &&
  cstr_encb 96 (ms_ignore_file g) (fldz MS_IGNORE_FILE 96 f) &&
  u32_encb (ms_gen g) (fldz MS_GEN 4 f).
Lemma mseg_encb_ok : forall g f, mseg_encb g f = true -> mseg_enc g f.
Proof. intros g f H. unfold mseg_encb in H. bdestr H. unfold mseg_enc. csplit; enc_fin. Qed.

Definition mconf_encpb (pend : bool) (mc : mconf) (bs : list byte) : bool :=
  (Z.of_nat (length bs) =? SEG_M_SIZE) && (length (mc_seg mc) <=? 32)%nat &&
  allidx (length (mc_seg mc)) (fun i => mseg_encb (nth i (mc_seg mc) mseg_d) (fld (256 * i) 256 bs)) &&
  u32_encb (Z.of_nat (length (mc_seg mc))) (fldz MC_N 4 bs) &&
  u32_encb (mc_overflow mc) (fldz MC_OVERFLOW 4 bs) &&
  u32_encb (mc_refused mc) (fldz MC_REFUSED 4 bs) &&
  (length (mc_kept mc) <=? 8)%nat &&
  allidx (length (mc_kept mc))
    (fun i => cstr_encb 112 (fst (nth i (mc_kept mc) ([], false))) (fld (Z.to_nat MC_KEPT + 112 * i) 112 bs) &&
              flag_encb (snd (nth i (mc_kept mc) ([], false))) (fld (Z.to_nat MC_KNOCK + 4 * i) 4 bs)) &&
  allidx 8 (fun i => (i <? length (mc_kept mc))%nat ||
                     flag_encb (pend && (i =? length (mc_kept mc))%nat) (fld (Z.to_nat MC_KNOCK + 4 * i) 4 bs)) &&
  u32_encb (Z.of_nat (length (mc_kept mc))) (fldz MC_NKEPT 4 bs) &&
  u32_encb (mc_gen mc) (fldz MC_GEN 4 bs) &&
  cstr_encb 96 (mc_reading mc) (fldz MC_READING 96 bs).
Lemma mconf_encpb_ok : forall pend mc bs, mconf_encpb pend mc bs = true -> mconf_encp pend mc bs.
Proof.
  intros pend mc bs H. unfold mconf_encpb in H. bdestr H. unfold mconf_encp. csplit;
    first [ enc_fin | intros i Hi; lazymatch goal with
      | |- mseg_enc _ _ => apply mseg_encb_ok;
          match goal with HA : allidx (length (mc_seg _)) _ = true |- _ => exact (allidx_ok _ _ HA i Hi) end
      | |- _ /\ _ =>
          match goal with HA : allidx (length (mc_kept _)) _ = true |- _ =>
            pose proof (allidx_ok _ _ HA i Hi) as Hk; cbv beta in Hk;
            apply andb_true_iff in Hk as [Hk1 Hk2]; split; [apply cstr_encb_ok | apply flag_encb_ok]; assumption end
      | |- flag_enc _ _ =>
          assert (Hi8 : (i < 8)%nat) by lia;
          match goal with HA : allidx 8 _ = true |- _ =>
            pose proof (allidx_ok _ _ HA i Hi8) as Hk; cbv beta in Hk;
            apply orb_true_iff in Hk as [Hk|Hk]; [apply Nat.ltb_lt in Hk; lia | apply flag_encb_ok; exact Hk] end
      end ].
Qed.
Definition mconf_encb (mc : mconf) (bs : list byte) : bool := mconf_encpb false mc bs.
Lemma mconf_encb_ok : forall mc bs, mconf_encb mc bs = true -> mconf_enc mc bs.
Proof. intros mc bs H. exact (mconf_encpb_ok false mc bs H). Qed.

Definition rvlan_encb (e : list Z * Z) (f : list byte) : bool :=
  (length f =? 18)%nat && cstr_encb 16 (fst e) (fld 0 16 f) && (0 <=? snd e) && (snd e <? 65536) &&
  bytes_eqz (fld 16 2 f) (le2 (Z_to_bv 64 (snd e))).
Lemma rvlan_encb_ok : forall e f, rvlan_encb e f = true -> rvlan_enc e f.
Proof.
  intros e f H. unfold rvlan_encb in H. bdestr H. unfold rvlan_enc. csplit; enc_fin.
Qed.

Definition mvlan_encb (e : list Z * Z) (f : list byte) : bool :=
  (length f =? 20)%nat && cstr_encb 16 (fst e) (fld 0 16 f) && u32_encb (snd e) (fld 16 4 f).
Lemma mvlan_encb_ok : forall e f, mvlan_encb e f = true -> mvlan_enc e f.
Proof. intros e f H. unfold mvlan_encb in H. bdestr H. unfold mvlan_enc. csplit; enc_fin. Qed.

Definition rtab_encb (t : list (list Z * Z)) (bs : list byte) : bool :=
  (length bs =? 18 * length t)%nat && allidx (length t) (fun i => rvlan_encb (nth i t ([], 0)) (fld (18 * i) 18 bs)).
Lemma rtab_encb_ok : forall t bs, rtab_encb t bs = true -> rtab_enc t bs.
Proof.
  intros t bs H. unfold rtab_encb in H. bdestr H. split; [enc_fin|].
  intros i Hi. apply rvlan_encb_ok. allidx_use i Hi.
Qed.

Definition mtab_encb (t : list (list Z * Z)) (bs : list byte) : bool :=
  (length bs =? 20 * length t)%nat && allidx (length t) (fun i => mvlan_encb (nth i t ([], 0)) (fld (20 * i) 20 bs)).
Lemma mtab_encb_ok : forall t bs, mtab_encb t bs = true -> mtab_enc t bs.
Proof.
  intros t bs H. unfold mtab_encb in H. bdestr H. split; [enc_fin|].
  intros i Hi. apply mvlan_encb_ok. allidx_use i Hi.
Qed.

(** ** 3. The region memory *)

Definition region : Type := (Z * list Z)%type.
Fixpoint rmem (rs : list region) (x : Z) : option Z :=
  match rs with
  | [] => None
  | (a, zl) :: r =>
      if (a <=? x) && (x <? a + Z.of_nat (length zl)) then nth_error zl (Z.to_nat (x - a)) else rmem r x
  end.
Definition RMEM (rs : list region) : word -> option byte :=
  fun w => option_map (Z_to_bv 8) (rmem rs (bv_unsigned w)).
(** No region of rs meets [lo, hi). *)
Definition rclear (rs : list region) (lo hi : Z) : bool :=
  forallb (fun r => (fst r + Z.of_nat (length (snd r)) <=? lo) || (hi <=? fst r)) rs.
(** Every loaded segment ends at or below E. *)
Definition segs_below (segs : list Segment) (E : Z) : bool :=
  forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? E) segs.
(** The bytes zl read from the image at p (each a byte value). *)
Definition img_zb (segs : list Segment) (p : Z) (zl : list Z) : bool :=
  forallb byte_okb zl &&
  forallb (fun i => match seg_rom segs (wa (p + Z.of_nat i)) with
                    | Some b => bv_unsigned b =? nth i zl 0 | None => false end) (seq 0 (length zl)).

Lemma rclear_sub : forall l lo hi lo' hi', rclear l lo hi = true -> lo <= lo' -> hi' <= hi -> rclear l lo' hi' = true.
Proof.
  intros l lo hi lo' hi' H H1 H2. unfold rclear in *. rewrite forallb_forall in *. intros r Hr.
  specialize (H r Hr). apply orb_true_iff in H as [H|H]; apply Z.leb_le in H; apply orb_true_iff;
    [left | right]; apply Z.leb_le; lia.
Qed.

Lemma rmem_clear : forall rs lo hi x, rclear rs lo hi = true -> lo <= x < hi -> rmem rs x = None.
Proof.
  induction rs as [|[a zl] r IH]; intros lo hi x H Hx; [reflexivity|].
  unfold rclear in H. cbn [forallb fst snd] in H. apply andb_true_iff in H as [H1 H2].
  cbn [rmem]. destruct ((a <=? x) && (x <? a + Z.of_nat (length zl))) eqn:E.
  - exfalso. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    apply orb_true_iff in H1 as [H|H]; apply Z.leb_le in H; lia.
  - apply (IH lo hi); assumption.
Qed.

Lemma rmem_lookup : forall rs k a zl x,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) x (x + 1) = true -> a <= x < a + Z.of_nat (length zl) ->
  rmem rs x = nth_error zl (Z.to_nat (x - a)).
Proof.
  induction rs as [|[a0 zl0] r IH]; intros k a zl x Hk Hc Hx; destruct k as [|k]; cbn [nth_error] in Hk;
    try discriminate.
  - injection Hk as <- <-. cbn [rmem].
    destruct (Z.leb_spec a0 x); [|lia]. destruct (Z.ltb_spec x (a0 + Z.of_nat (length zl0))); [|lia]. reflexivity.
  - cbn [firstn] in Hc. unfold rclear in Hc. cbn [forallb fst snd] in Hc. apply andb_true_iff in Hc as [Hc1 Hc2].
    cbn [rmem]. destruct ((a0 <=? x) && (x <? a0 + Z.of_nat (length zl0))) eqn:E.
    + exfalso. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
      apply orb_true_iff in Hc1 as [H|H]; apply Z.leb_le in H; lia.
    + apply (IH k); [exact Hk | exact Hc2 | exact Hx].
Qed.

Lemma rmem_cover : forall rs a zl x, In (a, zl) rs -> a <= x < a + Z.of_nat (length zl) -> exists z, rmem rs x = Some z.
Proof.
  induction rs as [|[a0 zl0] r IH]; intros a zl x Hin Hx; [destruct Hin|].
  cbn [rmem]. destruct ((a0 <=? x) && (x <? a0 + Z.of_nat (length zl0))) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    destruct (nth_error zl0 (Z.to_nat (x - a0))) eqn:N; [eexists; reflexivity|]. apply nth_error_None in N. lia.
  - destruct Hin as [Heq|Hin].
    + injection Heq as <- <-. exfalso. apply andb_false_iff in E as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia.
    + apply (IH a zl); assumption.
Qed.

Lemma rmem_some_in : forall rs x z, rmem rs x = Some z ->
  exists a zl, In (a, zl) rs /\ a <= x < a + Z.of_nat (length zl).
Proof.
  induction rs as [|[a0 zl0] r IH]; intros x z H; [discriminate|]. cbn [rmem] in H.
  destruct ((a0 <=? x) && (x <? a0 + Z.of_nat (length zl0))) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
    exists a0, zl0. split; [left; reflexivity | lia].
  - destruct (IH x z H) as (a & zl & Hin & Hx). exists a, zl. split; [right; exact Hin | exact Hx].
Qed.

Lemma RMEM_at : forall rs x, 0 <= x < 2 ^ 64 -> RMEM rs (wa x) = option_map (Z_to_bv 8) (rmem rs x).
Proof. intros rs x Hx. unfold RMEM. rewrite wa_unsigned by lia. reflexivity. Qed.

Lemma fs_spec : forall segs x n s, find_segment segs x n = Some s ->
  In s segs /\ Z.of_N (seg_base s) <= x /\ x + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s).
Proof.
  induction segs as [|sg r IH]; intros x n s H; cbn [find_segment] in H; [discriminate|].
  destruct (Z.leb_spec (Z.of_N (seg_base sg)) x) as [Hb1|Hb1];
    destruct (Z.leb_spec (x + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) as [Hb2|Hb2];
    cbn [andb] in H.
  - injection H as <-. split; [left; reflexivity | lia].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
  - destruct (IH x n s H) as (Hi1 & Hi2). split; [right; exact Hi1 | exact Hi2].
Qed.

Lemma find_segment_hi : forall segs E x n, segs_below segs E = true -> E <= x -> 0 < n -> find_segment segs x n = None.
Proof.
  intros segs E x n HB Hx Hn. destruct (find_segment segs x n) as [s|] eqn:F; [|reflexivity].
  destruct (fs_spec _ _ _ _ F) as (Hin & H1 & H2). unfold segs_below in HB. rewrite forallb_forall in HB.
  specialize (HB s Hin). apply Z.leb_le in HB. lia.
Qed.

Lemma seg_rom_hi : forall segs E x, segs_below segs E = true -> E <= x -> 0 <= x < 2 ^ 64 -> seg_rom segs (wa x) = None.
Proof.
  intros segs E x HB Hx Hr. unfold seg_rom, memory_read. cbv beta. rewrite wa_unsigned by lia.
  rewrite (find_segment_hi segs E x (Z.of_N 1)); [reflexivity | exact HB | lia | lia].
Qed.

Section Regions.
Variable segs : list Segment.

Lemma mrd_RMEM_some : forall rs x z, rmem rs x = Some z -> 0 <= x < 2 ^ 64 ->
  mrd segs (RMEM rs) (wa x) = Some (Z_to_bv 8 z).
Proof. intros rs x z H Hx. unfold mrd. rewrite RMEM_at, H by exact Hx. reflexivity. Qed.

Lemma wview_RMEM : forall rs x z, rmem rs x = Some z -> 0 <= x < 2 ^ 64 -> wview segs (RMEM rs) (wa x) <> None.
Proof. intros rs x z H Hx. unfold wview. rewrite RMEM_at, H by exact Hx. discriminate. Qed.

Lemma mrd_RMEM_none : forall rs x, rmem rs x = None -> 0 <= x < 2 ^ 64 -> mrd segs (RMEM rs) (wa x) = seg_rom segs (wa x).
Proof. intros rs x H Hx. unfold mrd. rewrite RMEM_at, H by exact Hx. reflexivity. Qed.

(** The bytes [p, p + n) of the region k, read through RMEM rs. *)
Lemma region_bytes : forall rs k a zl p n,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) p (p + n) = true ->
  0 <= a -> a + Z.of_nat (length zl) <= 2 ^ 64 -> a <= p -> 0 <= n -> p + n <= a + Z.of_nat (length zl) ->
  bytes_at segs (RMEM rs) p (zb (firstn (Z.to_nat n) (skipn (Z.to_nat (p - a)) zl))).
Proof.
  intros rs k a zl p n Hk Hc Ha Hz Hp Hn Hpn.
  assert (Hlen : length (zb (firstn (Z.to_nat n) (skipn (Z.to_nat (p - a)) zl))) = Z.to_nat n).
  { unfold zb. rewrite length_map, length_firstn, length_skipn. lia. }
  split; [lia|]. split; [rewrite Hlen; lia|].
  intros i Hi. rewrite Hlen in Hi.
  unfold mrd. rewrite RMEM_at by lia.
  rewrite (rmem_lookup rs k a zl (p + Z.of_nat i) Hk);
    [| apply (rclear_sub _ p (p + n)); [exact Hc | lia | lia] | lia].
  unfold zb. rewrite nth_error_map, nth_error_firstn, nth_error_skipn.
  destruct (Nat.ltb_spec i (Z.to_nat n)) as [_|]; [|lia].
  replace (Z.to_nat (p + Z.of_nat i - a)) with (Z.to_nat (p - a) + i)%nat by lia.
  destruct (nth_error zl (Z.to_nat (p - a) + i)) eqn:E; [reflexivity|]. apply nth_error_None in E. lia.
Qed.

Lemma region_sat : forall (P : list byte -> Prop) rs k a zl p n,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) p (p + n) = true ->
  0 <= a -> a + Z.of_nat (length zl) <= 2 ^ 64 -> a <= p -> 0 <= n -> p + n <= a + Z.of_nat (length zl) ->
  P (zb (firstn (Z.to_nat n) (skipn (Z.to_nat (p - a)) zl))) ->
  exists bs, bytes_at segs (RMEM rs) p bs /\ P bs.
Proof.
  intros P rs k a zl p n Hk Hc Ha Hz Hp Hn Hpn HP. eexists. split; [|exact HP].
  apply (region_bytes rs k); assumption.
Qed.

Lemma bytes_region : forall rs k a zl p bs,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) p (p + Z.of_nat (length bs)) = true ->
  0 <= a -> a + Z.of_nat (length zl) <= 2 ^ 64 -> a <= p -> p + Z.of_nat (length bs) <= a + Z.of_nat (length zl) ->
  leqb (firstn (length bs) (skipn (Z.to_nat (p - a)) zl)) (zs bs) = true ->
  bytes_at segs (RMEM rs) p bs.
Proof.
  intros rs k a zl p bs Hk Hc Ha Hz Hp Hpn Heq.
  pose proof (region_bytes rs k a zl p (Z.of_nat (length bs)) Hk Hc Ha Hz Hp ltac:(lia) Hpn) as B.
  rewrite Nat2Z.id in B. apply leqb_eq in Heq. rewrite Heq, zb_zs in B. exact B.
Qed.

Lemma cstrz_region : forall rs k a zl p s,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) p (p + Z.of_nat (length s) + 1) = true ->
  0 <= a -> a + Z.of_nat (length zl) <= 2 ^ 64 -> a <= p -> p + Z.of_nat (length s) + 1 <= a + Z.of_nat (length zl) ->
  leqb (firstn (S (length s)) (skipn (Z.to_nat (p - a)) zl)) (s ++ [0]) = true ->
  forallb byte_okb s = true -> nulfreeb s = true ->
  cstrz_at segs (RMEM rs) p s.
Proof.
  intros rs k a zl p s Hk Hc Ha Hz Hp Hpn Heq Hr Hn. exists (zb s). split; [|split].
  - pose proof (region_bytes rs k a zl p (Z.of_nat (length s) + 1) Hk ltac:(rewrite Z.add_assoc; exact Hc) Ha Hz Hp
      ltac:(lia) ltac:(lia)) as B.
    replace (Z.to_nat (Z.of_nat (length s) + 1)) with (S (length s)) in B by lia.
    apply leqb_eq in Heq. rewrite Heq in B. unfold zb in B. rewrite map_app in B. exact B.
  - apply zs_zb. exact Hr.
  - apply nulfreeb_ok. exact Hn.
Qed.

Lemma cstr_region : forall rs k a zl p s,
  nth_error rs k = Some (a, zl) -> rclear (firstn k rs) p (p + Z.of_nat (length s) + 8) = true ->
  0 <= a -> a + Z.of_nat (length zl) <= 2 ^ 64 -> a <= p -> p + Z.of_nat (length s) + 8 <= a + Z.of_nat (length zl) ->
  leqb (firstn (S (length s)) (skipn (Z.to_nat (p - a)) zl)) (s ++ [0]) = true ->
  forallb byte_okb s = true -> nulfreeb s = true ->
  cstr_at segs (RMEM rs) p s.
Proof.
  intros rs k a zl p s Hk Hc Ha Hz Hp Hpn Heq Hr Hn.
  set (L := skipn (Z.to_nat (p - a)) zl).
  set (sl := skipn (S (length s)) (firstn (length s + 8) L)).
  assert (HL : (length s + 8 <= length L)%nat) by (unfold L; rewrite length_skipn; lia).
  assert (E8 : firstn (length s + 8) L = s ++ 0 :: sl).
  { rewrite <- (firstn_skipn (S (length s)) (firstn (length s + 8) L)). fold sl.
    rewrite firstn_firstn. replace (Nat.min (S (length s)) (length s + 8)) with (S (length s)) by lia.
    apply leqb_eq in Heq. fold L in Heq. rewrite Heq, <- app_assoc. reflexivity. }
  assert (Hsl : length sl = 7%nat) by (unfold sl; rewrite length_skipn, length_firstn; lia).
  exists (zb s), (zb sl). split; [|split; [|split]].
  - pose proof (region_bytes rs k a zl p (Z.of_nat (length s) + 8) Hk ltac:(rewrite Z.add_assoc; exact Hc) Ha Hz Hp
      ltac:(lia) ltac:(lia)) as B.
    replace (Z.to_nat (Z.of_nat (length s) + 8)) with (length s + 8)%nat in B by lia.
    fold L in B. rewrite E8 in B. unfold zb in B. rewrite map_app in B. exact B.
  - apply zs_zb. exact Hr.
  - apply nulfreeb_ok. exact Hn.
  - unfold zb. rewrite length_map, Hsl. pose proof (Z.mod_pos_bound (- (p + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
    lia.
Qed.

Lemma bytes_img : forall rs p bs,
  rclear rs p (p + Z.of_nat (length bs)) = true -> img_zb segs p (zs bs) = true ->
  0 <= p -> p + Z.of_nat (length bs) <= 2 ^ 64 -> bytes_at segs (RMEM rs) p bs.
Proof.
  intros rs p bs Hc Hi Hp Hpn. unfold img_zb in Hi. apply andb_true_iff in Hi as [Hr Hi].
  rewrite forallb_forall in Hi. split; [lia|]. split; [lia|]. intros i Hlt.
  rewrite mrd_RMEM_none; [| apply (rmem_clear rs p (p + Z.of_nat (length bs))); [exact Hc | lia] | lia].
  assert (Hzl : length (zs bs) = length bs) by (unfold zs; apply length_map).
  specialize (Hi i ltac:(apply in_seq; lia)).
  destruct (seg_rom segs (wa (p + Z.of_nat i))) as [b|] eqn:E; [|discriminate].
  apply Z.eqb_eq in Hi. rewrite <- (zb_zs bs). unfold zb. rewrite nth_error_map.
  rewrite (nth_error_nth' (zs bs) 0) by lia. cbn [option_map]. f_equal. apply bv_eq.
  rewrite Hi. rewrite forallb_forall in Hr. specialize (Hr (nth i (zs bs) 0) ltac:(apply nth_In; lia)).
  unfold byte_okb in Hr. apply andb_true_iff in Hr as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  rewrite bu8 by lia. reflexivity.
Qed.

Lemma cstrz_img : forall rs p s,
  rclear rs p (p + Z.of_nat (length s) + 1) = true -> img_zb segs p (s ++ [0]) = true -> nulfreeb s = true ->
  0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 -> cstrz_at segs (RMEM rs) p s.
Proof.
  intros rs p s Hc Hi Hn Hp Hpn.
  assert (Hr : forallb byte_okb s = true).
  { unfold img_zb in Hi. apply andb_true_iff in Hi as [Hi _]. rewrite forallb_app in Hi.
    apply andb_true_iff in Hi as [Hi _]. exact Hi. }
  exists (zb s). split; [|split; [apply zs_zb; exact Hr | apply nulfreeb_ok; exact Hn]].
  replace (zb s ++ [ZERO]) with (zb (s ++ [0])) by (unfold zb; rewrite map_app; reflexivity).
  apply bytes_img.
  - replace (p + Z.of_nat (length (zb (s ++ [0])))) with (p + Z.of_nat (length s) + 1)
      by (unfold zb; rewrite length_map, length_app; cbn [length]; lia).
    exact Hc.
  - rewrite zs_zb; [exact Hi|]. rewrite forallb_app, Hr. reflexivity.
  - exact Hp.
  - unfold zb. rewrite length_map, length_app. cbn [length]. lia.
Qed.

Lemma stk_region : forall rs a zl lo hi, In (a, zl) rs -> a <= lo -> hi <= a + Z.of_nat (length zl) ->
  0 <= lo -> hi <= 2 ^ 64 -> stk segs (RMEM rs) lo hi.
Proof.
  intros rs a zl lo hi Hin H1 H2 H3 H4. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (rmem_cover rs a zl x Hin ltac:(lia)) as [z Hz]. split.
  - apply (wview_RMEM rs x z Hz). lia.
  - exists (Z_to_bv 8 z). apply mrd_RMEM_some; [exact Hz | lia].
Qed.

Lemma wr_at_region : forall rs k a zl p n, nth_error rs k = Some (a, zl) -> a <= p ->
  p + n <= a + Z.of_nat (length zl) -> 0 <= p -> p + n <= 2 ^ 64 -> wr_at segs (RMEM rs) p n.
Proof.
  intros rs k a zl p n Hk H1 H2 H3 H4. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (rmem_cover rs a zl (p + i) (nth_error_In rs k Hk) ltac:(lia)) as [z Hz].
  apply (wview_RMEM rs (p + i) z Hz). lia.
Qed.

Lemma stack_ok_region : forall E rs k a zl lo sp depth,
  segs_below segs E = true -> nth_error rs k = Some (a, zl) ->
  a <= lo -> sp <= a + Z.of_nat (length zl) -> E <= lo -> 0 <= lo -> sp <= 2 ^ 64 ->
  lo + depth <= sp -> sp mod 16 = 0 -> stack_ok segs (RMEM rs) lo sp depth.
Proof.
  intros E rs k a zl lo sp depth HB Hk H1 H2 H3 H4 H5 H6 H7. split; [|split; [exact H6|split; [exact H7|]]].
  - apply (stk_region rs a zl); try assumption. apply (nth_error_In rs k Hk).
  - intros x Hx. apply (seg_rom_hi segs E); [exact HB | lia | lia].
Qed.

Lemma mem_inv_hi : forall E rs, segs_below segs E = true -> forallb (fun r => E <=? fst r) rs = true ->
  mem_inv segs (RMEM rs).
Proof.
  intros E rs HB HR a b Hm. unfold RMEM in Hm. destruct (rmem rs (bv_unsigned a)) as [z|] eqn:E1; [|discriminate].
  destruct (rmem_some_in rs (bv_unsigned a) z E1) as (a0 & zl & Hin & Hx).
  rewrite forallb_forall in HR. specialize (HR _ Hin). cbn [fst] in HR. apply Z.leb_le in HR.
  unfold ro_addr. rewrite (find_segment_hi segs E); [reflexivity | exact HB | lia | lia].
Qed.

Lemma cat_img_clear : forall rs cat, rclear rs cat (cat + CAT_BYTES) = true -> 0 <= cat -> cat + CAT_BYTES <= 2 ^ 64 ->
  cat_img segs (RMEM rs) cat.
Proof.
  intros rs cat Hc H1 H2 a Ha. apply mrd_RMEM_none; [|lia]. apply (rmem_clear rs cat (cat + CAT_BYTES)); [exact Hc|lia].
Qed.

Lemma rw_cells_CB : forall m A bs, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs Hb Hw. split; [split|].
  - cbn. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact Hw.
Qed.

Lemma ocstrz_at_some : forall m a s, a <> 0 -> cstrz_at segs m a s -> ocstrz_at segs m a (Some s).
Proof. intros m a s H1 H2. exact (conj H1 H2). Qed.

End Regions.

(** ** 4. The real values *)

(** The text of the one file (the hand-written reac-pw.conf, read by reac_segconf_parse and m_file(m, text, NULL)):
    five lines, one segment eth0.5 (a VLAN name, so the declared-VLAN tables get an entry), role box, model s1608,
    ignore no, and a knock line, which both parsers refuse (the reader's refusal holds "takes no plan"; the model
    keeps the address with kept_knock = 1). *)
Definition T0 : list Z := sb "[segment eth0.5]
role = box
model = s1608
ignore = no
knock = 1
"%string.
(** The fuzz input: cap byte 4 (cap = 4 % 40), flags 1 (the "enp1s0" VLAN seed), nfiles byte 0 (one file), the
    file's label byte 0 and its 16-bit length, then T0 (fuzz_segconf.c:583-600, SegModel.decode). *)
Definition D0 : list Z := [4; 1; 0; 0; Z.of_nat (length T0); 0] ++ T0.
Definition P0 : payload := decode D0.
(** The states after the file loop: the reader's (reac_segconf_parse on rconf0) and the model's (m_file, m_cross). *)
Definition RC0 : rconf := fst (r_parse rconf0 T0).
Definition MC0 : mconf := m_cross (m_file mconf0 T0 None).
Definition RET0 : bool := true && (snd (r_parse rconf0 T0) =? Z.of_nat (length (mc_seg MC0))).
(** m->seg[0], its name, and the probe "<name>x" (fuzz_segconf.c:641). *)
Definition G0 : mseg := nth 0 (mc_seg MC0) mseg_d.
Definition NM0 : list Z := ms_name G0.
Definition PROBE0 : list Z := snprintf_s 18 F_probe [AS NM0].
(** The VLAN tables at check_declared: vlan_init of the payload, then each side's walk (fuzz_segconf.c:649-664). *)
Definition CAP0 : Z := p_cap P0.
Definition VL0 : list (list Z * Z) := vlan_init P0.
Definition GOT0 : Z * list (list Z * Z) := r_declared RC0 VL0 CAP0.
Definition WANT0 : Z * list (list Z * Z) := m_declared MC0 VL0 CAP0.
(** main's cell r after reac_segconf_role(c, g->name, &r): the role when it returns 1, else the 0x5a main stored
    (fuzz_segconf.c:625-626). *)
Definition R_CELL0 : Z := match r_role RC0 NM0 with Some r => r | None => 0x5a end.
(** The model value of T0's line 3 ("model = s1608"), as reac_segconf_parse_file folds it into low[24] before
    reac_box_catalogue_by_token (R:254-257). *)
Definition VAL0 : list Z := sb "s1608"%string.
Definition LOW0 : list Z := r_low VAL0 0 24.

Lemma P0_eq : P0 = Payload 4 1 [File 0 T0].
Proof. vm_compute. reflexivity. Qed.
(** The payload's run gives these states and returned = 1, and no check of the harness aborts on it. *)
Lemma run_P0 : run P0 = (RC0, MC0, RET0).
Proof. vm_compute. reflexivity. Qed.
Lemma harness_ok_P0 : harness_ok P0 = true.
Proof. vm_compute. reflexivity. Qed.

(** Addresses. S_TOP: LLVMFuzzerTestOneInput's entry sp (16-aligned; reac-pw/fuzz_role's W_S, one page below the
    process entry sp 0x7fffffff0000); the stack region the frame gives is [LO, S_TOP), LO = S_TOP - 65536. The heap
    blocks (c = malloc(16616), m = calloc(1, 9236), tab = calloc(cap + 1, 18), mt = calloc(cap + 1, 20)) are
    16-aligned and lie below LO, near 0x7fff_f000_0000 - 2^20. *)
Definition S_TOP : Z := 0x7ffffffef000.
Definition LO : Z := S_TOP - 65536.
Definition C0 : Z := 0x7fffeff00000.
Definition M0 : Z := 0x7fffeff10000.
Definition TAB0 : Z := 0x7fffeff20000.
Definition MT0 : Z := 0x7fffeff30000.
(** Every region sits at or above IMG_END; both images end below it (plain 0x54000, UBSan 0x55000). *)
Definition IMG_END : Z := 0x100000.

(** The stack region, zeros (the premises fix none of its bytes but the ones a region before it in the list
    places). *)
Definition R_STACK : region := (LO, zrep 65536).

(** ** 5. Tactics *)

(** The vm-checked equation: replace t by its value. *)
Ltac vmeq t := let v := eval vm_compute in t in replace t with v by (vm_compute; reflexivity).

(** A closed side condition. *)
Ltac zside :=
  lazymatch goal with
  | |- nth_error _ _ = Some _ => reflexivity
  | |- True => exact I
  | |- rconf_enc _ _ => apply rconf_encb_ok; vm_compute; reflexivity
  | |- mconf_enc _ _ => apply mconf_encb_ok; vm_compute; reflexivity
  | |- mconf_encp _ _ _ => apply mconf_encpb_ok; vm_compute; reflexivity
  | |- mseg_enc _ _ => apply mseg_encb_ok; vm_compute; reflexivity
  | |- rtab_enc _ _ => apply rtab_encb_ok; vm_compute; reflexivity
  | |- mtab_enc _ _ => apply mtab_encb_ok; vm_compute; reflexivity
  | |- (_ <= _ < _)%Z => split; zside
  | |- (_ <= _)%Z => apply Z.leb_le; vm_compute; reflexivity
  | |- (_ < _)%Z => apply Z.ltb_lt; vm_compute; reflexivity
  | |- (_ <> _)%Z => apply Z.eqb_neq; vm_compute; reflexivity
  | |- @eq Z _ _ => apply Z.eqb_eq; vm_compute; reflexivity
  | |- @eq nat _ _ => apply Nat.eqb_eq; vm_compute; reflexivity
  | |- _ => vm_compute; reflexivity
  end.

(** Try a region index k = 0 .. 7. *)
Ltac kfind tac := first [ tac 0%nat | tac 1%nat | tac 2%nat | tac 3%nat | tac 4%nat | tac 5%nat | tac 6%nat
                        | tac 7%nat ].

(** One conjunct of a premise over RMEM rs; HB : segs_below segs IMG_END = true for the build's segs. *)
Ltac sat_goal HB :=
  lazymatch goal with
  | |- stack_ok _ (RMEM _) _ _ _ =>
      kfind ltac:(fun k => solve [eapply (stack_ok_region _ IMG_END _ k _ _ _ _ _ HB); zside])
  | |- mem_inv _ (RMEM _) => apply (mem_inv_hi _ IMG_END _ HB); vm_compute; reflexivity
  | |- apart _ _ _ _ => unfold apart; first [left; zside | right; zside]
  | |- rconf_at _ (RMEM _) _ _ =>
      unfold rconf_at; kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ SEG_C_SIZE); zside])
  | |- mconf_at _ (RMEM _) _ _ =>
      unfold mconf_at; kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ SEG_M_SIZE); zside])
  | |- mconf_atp _ _ (RMEM _) _ _ =>
      unfold mconf_atp; kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ SEG_M_SIZE); zside])
  | |- mseg_at _ (RMEM _) _ _ =>
      unfold mseg_at; kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ MSEG_SIZE); zside])
  | |- rtab_at _ (RMEM _) _ ?t =>
      unfold rtab_at;
      kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ (RVLAN_SIZE * Z.of_nat (length t))); zside])
  | |- mtab_at _ (RMEM _) _ ?t =>
      unfold mtab_at;
      kfind ltac:(fun k => solve [eapply (region_sat _ _ _ k _ _ _ (MVLAN_SIZE * Z.of_nat (length t))); zside])
  | |- guard_at _ (RMEM _) _ _ =>
      unfold guard_at; kfind ltac:(fun k => solve [eapply (bytes_region _ _ k); zside])
  | |- cstrz_at _ (RMEM _) _ _ =>
      first [ kfind ltac:(fun k => solve [eapply (cstrz_region _ _ k); zside]) | solve [eapply cstrz_img; zside] ]
  | |- cstr_at _ (RMEM _) _ _ => kfind ltac:(fun k => solve [eapply (cstr_region _ _ k); zside])
  | |- ocstrz_at _ _ _ (Some _) => apply ocstrz_at_some; [zside | sat_goal HB]
  | |- ocstrz_at _ _ _ None => reflexivity
  | |- wr_at _ (RMEM _) _ _ => kfind ltac:(fun k => solve [eapply (wr_at_region _ _ k); zside])
  | |- cat_img _ (RMEM _) _ => apply cat_img_clear; zside
  | |- bytes_at _ (RMEM _) _ _ =>
      first [ kfind ltac:(fun k => solve [eapply (bytes_region _ _ k); zside]) | solve [eapply bytes_img; zside] ]
  | |- _ \/ _ => first [ left; solve [csplit; sat_goal HB] | right; csplit; sat_goal HB ]
  | |- _ => zside
  end.
Ltac sat_all HB := csplit; sat_goal HB.
