(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput: the build-independent bridges from the cut
   predicates' encodings (seg_spec.rconf_at / mconf_at) and the spine's checks (MainBPure.mb_checks) to the premises
   of the callees of M02's evt body (the reader's queries, the check_* of the segment, refusal and probe loops,
   m_find, check_absent). Both builds' walks of M02 use them (lib/Prog/Seg/M02*.v, lib/U/Prog/Seg/M02*.v); every
   lemma is over a segment list [segs] and no image.
   - fields: mb_fld_fld, mb_fld_at, mb_cstrz, mb_cstr (a char[cap] field of a block: its C string, NUL and the
     slack a word-at-a-time reader takes);
   - the model's block: mb_mseg_at (m->seg[i]), mb_mname (its name), mb_kept (m->kept[i] and kept_knock[i]),
     mb_mconf_n / mb_mconf_nkept (the counts the code loads), mb_mfind_lt (m_find's index is an entry);
   - the reader's block: mb_rfind_lt, mb_model / mb_role_file / mb_ignore_file (the accessors' pointer answers,
     seg_spec.model_ptr etc., as the C strings check_model / check_provenance read), mb_ptr_rng (those pointers lie
     in [0, c + 16616]), mb_role_rng, mb_refusal (c->refusal[i]), mb_rconf_nref;
   - the checks: mb_check_seg_nth (check_seg of the i-th segment, split), mb_kept_all_nth, mb_check_refusals_len,
     mb_probe_s (the probe text "<name>x");
   - piece C's probe text (first written in lib/Prog/Seg/M02_C.v): c_T (the name and 'x'), c_pf_zs, c_T_nz, c_name_rng,
     c_T_rng (its bytes are 1 .. 255), c_pad16 (a name's read slack in its 16-byte field).
   Part of the proof of LLVMFuzzerTestOneInput: helper lemmas of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
Import OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.check_segments.CsPure.
Import ListNotations.
Open Scope Z_scope.

Module M02Bridge.

(* ---- Lists ---- *)
Lemma mb_fld_fld : forall (bs : list byte) k len off n, (off + n <= len)%nat ->
  fld off n (fld k len bs) = fld (k + off) n bs.
Proof.
  intros bs k len off n H. unfold fld.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Nat.min n (len - off)) with n by lia. f_equal. f_equal. lia.
Qed.

Lemma mb_fld_len : forall (bs : list byte) k n, (k + n <= length bs)%nat -> length (fld k n bs) = n.
Proof. intros bs k n H. unfold fld. rewrite length_firstn, length_skipn. lia. Qed.

Lemma mb_zs_len : forall l, length (zs l) = length l.
Proof. intros l. unfold zs. apply length_map. Qed.

Lemma mb_check_seg_nth : forall rc l i, forallb (check_seg rc) l = true -> (i < length l)%nat ->
  check_seg rc (nth i l mseg_d) = true.
Proof.
  intros rc l i H Hi. rewrite forallb_forall in H. apply H. apply nth_In. exact Hi.
Qed.

Lemma mb_kept_all_nth : forall gs ws i, check_kept_all gs ws = true -> (i < length gs)%nat ->
  (i < length ws)%nat -> check_kept (nth i gs []) (nth i ws ([], false)) = true.
Proof.
  induction gs as [|g gs IH]; intros [|w ws] i H Hg Hw; cbn in Hg, Hw; try lia.
  cbn [check_kept_all] in H. apply andb_true_iff in H as [H1 H2].
  destruct i as [|i]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia | lia].
Qed.

Lemma mb_check_refusals_len : forall rc mc, check_refusals rc mc = true ->
  length (rc_refusal rc) = length (mc_kept mc) /\ rc_refused rc = mc_refused mc.
Proof.
  intros rc mc H. unfold check_refusals in H. apply andb_true_iff in H as [H1 H2].
  apply Z.eqb_eq in H1. apply Nat.eqb_eq in H2. split; assumption.
Qed.

Lemma mb_cut_nul_id : forall s, nulfree s -> cut_nul s = s.
Proof.
  induction s as [|x s IH]; intros H; [reflexivity|]. cbn [cut_nul].
  destruct (Z.eqb_spec x 0) as [E|E]; [exfalso; apply H; left; exact E|].
  f_equal. apply IH. intros Hin. apply H. right. exact Hin.
Qed.

(** The probe text of m->seg[i] (fuzz_segconf.c:641, snprintf(probe, 18, "%sx", name)): the name and 'x'. *)
Lemma mb_probe_s : forall s, nulfree s -> (length s < 17)%nat -> snprintf_s 18 F_probe [AS s] = s ++ [120].
Proof.
  intros s Hn Hl. unfold snprintf_s.
  replace (fmt F_probe [AS s]) with (cut_nul s ++ [120]) by reflexivity.
  rewrite (mb_cut_nul_id s Hn). apply firstn_all2. rewrite length_app. cbn [length]. lia.
Qed.

Lemma mb_rfind_go : forall l nm k i, r_find_go l nm k = Some i -> (k <= i < k + length l)%nat.
Proof.
  induction l as [|s l IH]; intros nm k i H; cbn [r_find_go] in H; [discriminate|].
  destruct (strcmp (rs_name s) nm =? 0); [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.

Lemma mb_rfind_lt : forall rc nm i, r_find rc nm = Some i -> (i < length (rc_seg rc))%nat.
Proof. intros rc nm i H. unfold r_find in H. apply mb_rfind_go in H. lia. Qed.

Lemma mb_mfind_go : forall l nm k i, m_find_go l nm k = Some i -> (k <= i < k + length l)%nat.
Proof.
  induction l as [|g l IH]; intros nm k i H; cbn [m_find_go] in H; [discriminate|].
  destruct ((strlen (ms_name g) =? length nm)%nat && leqb (firstn (length nm) (ms_name g)) nm);
    [injection H as <-; cbn [length]; lia|].
  apply IH in H. cbn [length]. lia.
Qed.

Lemma mb_mfind_lt : forall mc nm i, m_find mc nm = Some i -> (i < length (mc_seg mc))%nat.
Proof. intros mc nm i H. unfold m_find in H. apply mb_mfind_go in H. lia. Qed.

(* ---- The probe text of piece C (both builds; first written in lib/Prog/Seg/M02_C.v as M02CPure) ---- *)
(** The probe text of m->seg[i]: its name and 'x'. *)
Definition c_T (mc : mconf) (i : nat) : list Z := ms_name (nth i (mc_seg mc) mseg_d) ++ [120].

Lemma c_pf_zs : forall bs : list byte, map (Z_to_bv 8) (zs bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. unfold zs in *. cbn [map]. f_equal; [|exact IH].
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma c_T_nz : forall l, Forall (fun x => 0 < x < 256) l -> ~ In 0 l.
Proof. intros l H Hin. rewrite Forall_forall in H. specialize (H _ Hin). cbv beta in H. lia. Qed.

Lemma c_name_rng : forall (sx : list byte) s, zs sx = s -> nulfree s -> Forall (fun x => 0 < x < 256) s.
Proof.
  intros sx s E N. apply Forall_forall. intros x Hx.
  assert (X0 : x <> 0) by (intros ->; exact (N Hx)).
  rewrite <- E in Hx. unfold zs in Hx. apply in_map_iff in Hx as (b & <- & _).
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia.
Qed.

Lemma c_T_rng : forall mc i sx, zs sx = ms_name (nth i (mc_seg mc) mseg_d) ->
  nulfree (ms_name (nth i (mc_seg mc) mseg_d)) -> Forall (fun x => 0 < x < 256) (c_T mc i).
Proof.
  intros mc i sx Zx N. unfold c_T. apply Forall_app. split; [exact (c_name_rng sx _ Zx N)|].
  apply Forall_cons; [cbv beta; lia | apply Forall_nil].
Qed.

(* The read slack of a name in the 16-byte field of a 16-aligned entry. *)
Lemma c_pad16 : forall mm j L K, mm mod 16 = 0 -> 0 <= j -> 0 <= L -> 0 <= K -> L + 1 + K = 16 ->
  (- (mm + 256 * j + L + 1)) mod 8 <= K.
Proof. intros. Z.div_mod_to_equations. lia. Qed.

(* ---- In memory ---- *)
Section At.
Variable segs : list Segment.

Lemma mb_fld_at : forall m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (fld k n bs).
Proof. intros m a bs k n H Hk. unfold fld. apply bytes_at_sub; assumption. Qed.

(** A char[cap] field [k, k + cap) of the bytes bs at b holding the C string s: its bytes and NUL. *)
Lemma mb_cstrz_raw : forall m b bs k cap s, bytes_at segs m b bs -> (k + cap <= length bs)%nat ->
  cstr_enc cap s (fld k cap bs) ->
  exists sx, bytes_at segs m (b + Z.of_nat k) (sx ++ [ZERO]) /\ ~ In ZERO sx /\ zs sx = s.
Proof.
  intros m b bs k cap s H Hk E.
  pose proof (mb_fld_at m b bs k cap H Hk) as Hf.
  assert (Lf : length (fld k cap bs) = cap) by (apply mb_fld_len; exact Hk).
  apply (cstr_bytes segs m _ (fld k cap bs) cap s Hf); [lia|].
  rewrite firstn_all2 by lia. exact E.
Qed.

Lemma mb_cstrz : forall m b bs k cap s, bytes_at segs m b bs -> (k + cap <= length bs)%nat ->
  cstr_enc cap s (fld k cap bs) -> cstrz_at segs m (b + Z.of_nat k) s.
Proof.
  intros m b bs k cap s H Hk E.
  destruct (mb_cstrz_raw m b bs k cap s H Hk E) as (sx & Bx & Nx & Zx).
  exists sx. split; [exact Bx|]. split; [exact Zx|]. exact (proj1 (proj2 (proj2 E))).
Qed.

(** The same with the n bytes after the NUL present: the slack a word-at-a-time reader takes (seg_spec.cstr_at). *)
Lemma mb_cstr : forall m b bs k cap s n, bytes_at segs m b bs -> (k + cap <= length bs)%nat ->
  cstr_enc cap s (fld k cap bs) -> (k + length s + 1 + n <= length bs)%nat ->
  (- (b + Z.of_nat k + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat n ->
  cstr_at segs m (b + Z.of_nat k) s.
Proof.
  intros m b bs k cap s n H Hk E Hn Hs.
  destruct (mb_cstrz_raw m b bs k cap s H Hk E) as (sx & Bx & Nx & Zx).
  assert (Lx : length sx = length s) by (rewrite <- Zx; symmetry; apply mb_zs_len).
  pose proof (mb_fld_at m b bs (k + length s + 1) n H Hn) as R.
  exists sx, (fld (k + length s + 1) n bs).
  split.
  - replace (sx ++ ZERO :: fld (k + length s + 1) n bs) with ((sx ++ [ZERO]) ++ fld (k + length s + 1) n bs)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact Bx|]. rewrite length_app, Lx. cbn [length].
    replace (b + Z.of_nat k + Z.of_nat (length s + 1)) with (b + Z.of_nat (k + length s + 1)) by lia. exact R.
  - split; [exact Zx|]. split; [exact (proj1 (proj2 (proj2 E)))|].
    rewrite mb_fld_len by exact Hn. exact Hs.
Qed.

(* ---- The model's block, struct mconf ---- *)
Lemma mb_mseg_at : forall m a mc i, mconf_at segs m a mc -> (i < length (mc_seg mc))%nat ->
  mseg_at segs m (a + 256 * Z.of_nat i) (nth i (mc_seg mc) mseg_d).
Proof.
  intros m a mc i (bs & B & L & L32 & HS & _) Hi.
  exists (fld (256 * i) 256 bs). split; [|exact (HS i Hi)].
  unfold SEG_M_SIZE in L.
  replace (a + 256 * Z.of_nat i) with (a + Z.of_nat (256 * i)) by lia.
  apply mb_fld_at; [exact B | lia].
Qed.

(** The name of m->seg[i]: a C string of at most 15 bytes in the 16-byte field, with its slack inside the field
    (the entry is 16-aligned when the block is). *)
Lemma mb_mname : forall m a mc i, mconf_at segs m a mc -> a mod 16 = 0 -> (i < length (mc_seg mc))%nat ->
  cstrz_at segs m (a + 256 * Z.of_nat i) (ms_name (nth i (mc_seg mc) mseg_d)) /\
  cstr_at segs m (a + 256 * Z.of_nat i) (ms_name (nth i (mc_seg mc) mseg_d)) /\
  (exists sx slack, bytes_at segs m (a + 256 * Z.of_nat i) (sx ++ ZERO :: slack) /\
     zs sx = ms_name (nth i (mc_seg mc) mseg_d) /\ ~ In ZERO sx /\ length (sx ++ ZERO :: slack) = 16%nat) /\
  nulfree (ms_name (nth i (mc_seg mc) mseg_d)) /\ (length (ms_name (nth i (mc_seg mc) mseg_d)) < 16)%nat.
Proof.
  intros m a mc i (bs & B & L & L32 & HS & _) A16 Hi.
  destruct (HS i Hi) as (Lf & En & _).
  unfold SEG_M_SIZE in L.
  set (g := nth i (mc_seg mc) mseg_d) in *. clearbody g.
  assert (Ef : fld 0 16 (fld (256 * i) 256 bs) = fld (256 * i) 16 bs).
  { rewrite mb_fld_fld by lia. f_equal. lia. }
  rewrite Ef in En.
  assert (Hk : (256 * i + 16 <= length bs)%nat) by lia.
  replace (a + 256 * Z.of_nat i) with (a + Z.of_nat (256 * i)) by lia.
  pose proof En as (_ & Ls & Nn & _).
  destruct (mb_cstrz_raw m a bs (256 * i) 16 _ B Hk En) as (sx & Bx & Nx & Zx).
  assert (Lx : length sx = length (ms_name g)) by (rewrite <- Zx; symmetry; apply mb_zs_len).
  split; [exact (mb_cstrz m a bs (256 * i) 16 _ B Hk En)|].
  split.
  { apply (mb_cstr m a bs (256 * i) 16 _ (16 - length (ms_name g) - 1) B Hk En); [lia|].
    replace (a + Z.of_nat (256 * i) + Z.of_nat (length (ms_name g)) + 1)
      with (16 * (a / 16 + 16 * Z.of_nat i) + (Z.of_nat (length (ms_name g)) + 1))
      by (rewrite Nat2Z.inj_mul; Z.div_mod_to_equations; lia).
    assert (E8 : forall q r, 0 < r <= 16 -> (- (16 * q + r)) mod 8 <= 16 - r).
    { intros q r Hr. Z.div_mod_to_equations. lia. }
    rewrite Nat2Z.inj_sub by lia. rewrite Nat2Z.inj_sub by lia. specialize (E8 (a / 16 + 16 * Z.of_nat i)
      (Z.of_nat (length (ms_name g)) + 1) ltac:(lia)). lia. }
  split.
  { pose proof (mb_fld_at m a bs (256 * i + length (ms_name g) + 1) (16 - length (ms_name g) - 1) B
                  ltac:(lia)) as R.
    exists sx, (fld (256 * i + length (ms_name g) + 1) (16 - length (ms_name g) - 1) bs).
    split.
    - replace (sx ++ ZERO :: fld (256 * i + length (ms_name g) + 1) (16 - length (ms_name g) - 1) bs)
        with ((sx ++ [ZERO]) ++ fld (256 * i + length (ms_name g) + 1) (16 - length (ms_name g) - 1) bs)
        by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact Bx|]. rewrite length_app, Lx. cbn [length].
      replace (a + Z.of_nat (256 * i) + Z.of_nat (length (ms_name g) + 1))
        with (a + Z.of_nat (256 * i + length (ms_name g) + 1)) by lia. exact R.
    - split; [exact Zx|]. split; [exact Nx|].
      rewrite length_app, Lx. cbn [length]. rewrite mb_fld_len by lia. lia. }
  split; [exact Nn | exact Ls].
Qed.

(** m->kept[i] (a C string of at most 111 bytes, its read slack inside the block: the field is 4 mod 8, and the
    4 bytes after kept[7] are kept_knock[0]) and kept_knock[i] (0 or 1). *)
Lemma mb_kept : forall m a mc i, mconf_at segs m a mc -> a mod 16 = 0 -> (i < length (mc_kept mc))%nat ->
  cstr_at segs m (kept_addr a i) (fst (nth i (mc_kept mc) ([], false))) /\
  cstrz_at segs m (kept_addr a i) (fst (nth i (mc_kept mc) ([], false))) /\
  kept_addr a i + Z.of_nat (length (fst (nth i (mc_kept mc) ([], false)))) + 1 <= a + SEG_M_SIZE /\
  bytes_at segs m (a + MC_KNOCK + 4 * Z.of_nat i)
    (le4 (Z_to_bv 64 (b2z (snd (nth i (mc_kept mc) ([], false)))))) /\
  (i < 8)%nat.
Proof.
  intros m a mc i (bs & B & L & L32 & HS & UN & UO & UR & HL8 & HK & _) A16 Hi.
  destruct (HK i Hi) as (Ek & Fk).
  unfold SEG_M_SIZE in L.
  set (w := nth i (mc_kept mc) ([], false)) in *. clearbody w.
  set (kk := Z.to_nat MC_KEPT) in *. assert (Ekk : Z.of_nat kk = 8204) by reflexivity. clearbody kk.
  set (kn := Z.to_nat MC_KNOCK) in *. assert (Ekn : Z.of_nat kn = 9100) by reflexivity. clearbody kn.
  pose proof Ek as (Lk & Ls & Nn & _).
  assert (Hk : (kk + 112 * i + 112 <= length bs)%nat) by lia.
  unfold kept_addr, MC_KEPT, MC_KEPT_LEN, MC_KNOCK, SEG_M_SIZE.
  replace (a + 8204 + 112 * Z.of_nat i) with (a + Z.of_nat (kk + 112 * i)) by lia.
  split.
  { apply (mb_cstr m a bs (kk + 112 * i) 112 _ (Z.to_nat ((- (a + Z.of_nat (kk + 112 * i) +
             Z.of_nat (length (fst w)) + 1)) mod 8)) B Hk Ek).
    - assert (R8 : 0 <= (- (a + Z.of_nat (kk + 112 * i) + Z.of_nat (length (fst w)) + 1)) mod 8 < 8)
        by (apply Z.mod_pos_bound; lia).
      lia.
    - rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia). lia. }
  split; [exact (mb_cstrz m a bs (kk + 112 * i) 112 _ B Hk Ek)|].
  split; [lia|].
  split.
  { unfold flag_enc in Fk. unfold b2z. rewrite <- Fk.
    replace (a + 9100 + 4 * Z.of_nat i) with (a + Z.of_nat (kn + 4 * i)) by lia.
    apply mb_fld_at; [exact B | lia]. }
  lia.
Qed.

(** The counts the code loads: m->n (m + 0x2000), m->n_kept (m + 0x23ac), c->n_refusals (c + 0x34c8). *)
Lemma mb_mconf_n : forall m a mc, mconf_at segs m a mc ->
  ov_read_bytes segs m (wa (a + MC_N)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_seg mc))))) /\
  (length (mc_seg mc) <= 32)%nat.
Proof.
  intros m a mc (bs & B & L & L32 & _ & UN & _). unfold SEG_M_SIZE in L.
  split; [|exact L32]. apply (cs_rd4 segs m a bs MC_N _ B); unfold MC_N; [lia | lia | exact UN].
Qed.

Lemma mb_mconf_nkept : forall m a mc, mconf_at segs m a mc ->
  ov_read_bytes segs m (wa (a + MC_NKEPT)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (mc_kept mc))))) /\
  (length (mc_kept mc) <= 8)%nat.
Proof.
  intros m a mc (bs & B & L & L32 & _ & _ & _ & _ & L8 & _ & _ & UK & _). unfold SEG_M_SIZE in L.
  split; [|exact L8]. apply (cs_rd4 segs m a bs MC_NKEPT _ B); unfold MC_NKEPT; [lia | lia | exact UK].
Qed.

(* ---- The reader's block, struct reac_segconf ---- *)
Lemma mb_rconf_nref : forall m c rc, rconf_at segs m c rc ->
  ov_read_bytes segs m (wa (c + RC_NREF)) 4 = Some (le4 (Z_to_bv 64 (Z.of_nat (length (rc_refusal rc))))) /\
  (length (rc_refusal rc) <= 8)%nat.
Proof.
  intros m c rc (bs & B & L & _ & _ & _ & L8 & _ & UR & _). unfold SEG_C_SIZE in L.
  split; [|exact L8]. apply (cs_rd4 segs m c bs RC_NREF _ B); unfold RC_NREF; [lia | lia | exact UR].
Qed.

(** A field [off, off + cap) of the entry c->seg[i] holding the C string s, as a C string at c + 356 i + off. *)
Lemma mb_rseg_cstrz : forall m c bs i off cap s, bytes_at segs m c bs -> Z.of_nat (length bs) = SEG_C_SIZE ->
  (i < 32)%nat -> (off + cap <= 356)%nat ->
  cstr_enc cap s (fld off cap (fld (356 * i) 356 bs)) ->
  cstrz_at segs m (c + 356 * Z.of_nat i + Z.of_nat off) s /\
  c + 356 * Z.of_nat i + Z.of_nat off + Z.of_nat (length s) + 1 <= c + SEG_C_SIZE.
Proof.
  intros m c bs i off cap s B L Hi Ho E.
  rewrite mb_fld_fld in E by lia. unfold SEG_C_SIZE in L.
  pose proof E as (Lf & Ls & _).
  replace (c + 356 * Z.of_nat i + Z.of_nat off) with (c + Z.of_nat (356 * i + off)) by lia.
  split; [apply (mb_cstrz m c bs (356 * i + off) cap s B); [lia | exact E]|].
  unfold SEG_C_SIZE. lia.
Qed.

Lemma mb_role_rng : forall m c rc nm v, rconf_at segs m c rc -> r_role rc nm = Some v -> 0 <= v < 2 ^ 31.
Proof.
  intros m c rc nm v (bs & B & L & L32 & HS & _) H. unfold r_role in H.
  destruct (r_find rc nm) as [i|] eqn:EF; [|discriminate].
  destruct (rs_role_set (r_seg rc i)); [|discriminate]. injection H as <-.
  pose proof (mb_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & ((R1 & _) & R2) & _). unfold r_seg. lia.
Qed.

(** The pointer answers lie in [0, c + 16616]: NULL, or a field of an entry of c's 32. *)
Lemma mb_ptr_rng : forall m c rc nm, rconf_at segs m c rc -> 0 <= c ->
  0 <= model_ptr c rc nm <= c + SEG_C_SIZE /\ 0 <= role_file_ptr c rc nm <= c + SEG_C_SIZE /\
  0 <= ignore_file_ptr c rc nm <= c + SEG_C_SIZE /\ 0 <= find_ptr c rc nm <= c + SEG_C_SIZE.
Proof.
  intros m c rc nm (bs & B & L & L32 & _) Hc.
  unfold model_ptr, role_file_ptr, ignore_file_ptr, find_ptr, rseg_addr, RSEG_SIZE, RS_MODEL, RS_ROLE_FILE,
    RS_IGNORE_FILE, SEG_C_SIZE.
  destruct (r_find rc nm) as [i|] eqn:EF; [|repeat split; lia].
  pose proof (mb_rfind_lt rc nm i EF) as Hi.
  destruct (r_model rc nm), (r_role_file rc nm), (r_ignore_file rc nm); repeat split; lia.
Qed.

Lemma mb_model : forall m c rc nm, rconf_at segs m c rc -> 0 < c ->
  ocstrz_at segs m (model_ptr c rc nm) (r_model rc nm) /\
  (forall s, r_model rc nm = Some s -> model_ptr c rc nm + Z.of_nat (length s) + 1 <= c + SEG_C_SIZE).
Proof.
  intros m c rc nm (bs & B & L & L32 & HS & _) Hc. unfold model_ptr, r_model.
  destruct (r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (mb_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & Em & _).
  unfold r_seg. destruct (rs_model_set (nth i (rc_seg rc) rseg_d)); [|split; [reflexivity | discriminate]].
  unfold fldz, RS_MODEL in Em. change (Z.to_nat 36) with 36%nat in Em. change (Z.to_nat 24) with 24%nat in Em.
  destruct (mb_rseg_cstrz m c bs i 36 24 _ B L ltac:(lia) ltac:(lia) Em) as [Hz Hb].
  unfold rseg_addr, RSEG_SIZE, RS_MODEL. change (Z.of_nat 36) with 36 in Hz, Hb.
  split; [split; [lia | exact Hz]|]. intros s Es. injection Es as <-. exact Hb.
Qed.

Lemma mb_role_file : forall m c rc nm, rconf_at segs m c rc -> 0 < c ->
  ocstrz_at segs m (role_file_ptr c rc nm) (r_role_file rc nm) /\
  (forall s, r_role_file rc nm = Some s -> role_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + SEG_C_SIZE).
Proof.
  intros m c rc nm (bs & B & L & L32 & HS & _) Hc. unfold role_file_ptr, r_role_file.
  destruct (r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (mb_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ef & _).
  unfold r_seg.
  destruct (rs_role_set (nth i (rc_seg rc) rseg_d) && negb (hd0 (rs_role_file (nth i (rc_seg rc) rseg_d)) =? 0));
    [|split; [reflexivity | discriminate]].
  unfold fldz, RS_ROLE_FILE in Ef. change (Z.to_nat 160) with 160%nat in Ef. change (Z.to_nat 96) with 96%nat in Ef.
  destruct (mb_rseg_cstrz m c bs i 160 96 _ B L ltac:(lia) ltac:(lia) Ef) as [Hz Hb].
  unfold rseg_addr, RSEG_SIZE, RS_ROLE_FILE. change (Z.of_nat 160) with 160 in Hz, Hb.
  split; [split; [lia | exact Hz]|]. intros s Es. injection Es as <-. exact Hb.
Qed.

Lemma mb_ignore_file : forall m c rc nm, rconf_at segs m c rc -> 0 < c ->
  ocstrz_at segs m (ignore_file_ptr c rc nm) (r_ignore_file rc nm) /\
  (forall s, r_ignore_file rc nm = Some s -> ignore_file_ptr c rc nm + Z.of_nat (length s) + 1 <= c + SEG_C_SIZE).
Proof.
  intros m c rc nm (bs & B & L & L32 & HS & _) Hc. unfold ignore_file_ptr, r_ignore_file.
  destruct (r_find rc nm) as [i|] eqn:EF; [|split; [reflexivity | discriminate]].
  pose proof (mb_rfind_lt rc nm i EF) as Hi.
  destruct (HS i Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ei & _).
  unfold r_seg.
  destruct (rs_ignore_set (nth i (rc_seg rc) rseg_d) &&
            negb (hd0 (rs_ignore_file (nth i (rc_seg rc) rseg_d)) =? 0)); [|split; [reflexivity | discriminate]].
  unfold fldz, RS_IGNORE_FILE in Ei. change (Z.to_nat 256) with 256%nat in Ei. change (Z.to_nat 96) with 96%nat in Ei.
  destruct (mb_rseg_cstrz m c bs i 256 96 _ B L ltac:(lia) ltac:(lia) Ei) as [Hz Hb].
  unfold rseg_addr, RSEG_SIZE, RS_IGNORE_FILE. change (Z.of_nat 256) with 256 in Hz, Hb.
  split; [split; [lia | exact Hz]|]. intros s Es. injection Es as <-. exact Hb.
Qed.

(** c->refusal[i]: a C string of at most 199 bytes in its 200-byte field (8-aligned when c is), its slack inside
    the field. *)
Lemma mb_refusal : forall m c rc i, rconf_at segs m c rc -> c mod 16 = 0 -> (i < length (rc_refusal rc))%nat ->
  cstr_at segs m (refusal_addr c i) (nth i (rc_refusal rc) []) /\
  cstrz_at segs m (refusal_addr c i) (nth i (rc_refusal rc) []) /\
  refusal_addr c i + Z.of_nat (length (nth i (rc_refusal rc) [])) + 1 <= c + SEG_C_SIZE.
Proof.
  intros m c rc i (bs & B & L & L32 & HS & UN & L8 & HR & _) C16 Hi.
  pose proof (HR i Hi) as Er. unfold SEG_C_SIZE in L.
  set (kr := Z.to_nat RC_REFUSAL) in *. assert (Ekr : Z.of_nat kr = 11912) by reflexivity. clearbody kr.
  set (t := nth i (rc_refusal rc) []) in *. clearbody t.
  pose proof Er as (Lf & Ls & _).
  assert (Hk : (kr + 200 * i + 200 <= length bs)%nat) by lia.
  unfold refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, SEG_C_SIZE.
  replace (c + 11912 + 200 * Z.of_nat i) with (c + Z.of_nat (kr + 200 * i)) by lia.
  split.
  { apply (mb_cstr m c bs (kr + 200 * i) 200 t (200 - length t - 1) B Hk Er); [lia|].
    replace (c + Z.of_nat (kr + 200 * i) + Z.of_nat (length t) + 1)
      with (8 * (c / 8 + 1489 + 25 * Z.of_nat i) + (Z.of_nat (length t) + 1))
      by (rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Ekr; Z.div_mod_to_equations; lia).
    assert (E8 : forall q r, 0 < r <= 200 -> (- (8 * q + r)) mod 8 <= 200 - r).
    { intros q r Hr. Z.div_mod_to_equations. lia. }
    rewrite !Nat2Z.inj_sub by lia.
    specialize (E8 (c / 8 + 1489 + 25 * Z.of_nat i) (Z.of_nat (length t) + 1) ltac:(lia)). lia. }
  split; [exact (mb_cstrz m c bs (kr + 200 * i) 200 t B Hk Er)|].
  lia.
Qed.

End At.

End M02Bridge.
