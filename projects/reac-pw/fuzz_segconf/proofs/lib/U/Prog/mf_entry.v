(** m_file (UBSan build, image 1696d6c34ffd): the piece S_MF_ENTRY of U/Prog/m_file_c.v (family F3).

    The entry 0x14268-0x14348: the prologue (frame 0x110, 13 `sd`), the c & 3 trap, snprintf(c->reading, 96, "%s",
    label ? label : "reac-pw.conf"), c->gen++ (with its signed overflow trap), `lbu *text` (empty text goes to the
    epilogue 0x14980), and the set-up 0x142fc-0x14344 that establishes the line loop's registers and frame cells
    before the head 0x14348. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac ZBridge FP Image.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Memory facts *)

(** MemNorm's task_mem after writes whose bytes were all present or in a writable segment before. *)
Lemma mfe_task_mem : forall W m m', MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, ~ outside W (bv_unsigned x) -> wview rsegs m x <> None) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' T MU H x b E.
  destruct (m x) as [b'|] eqn:E0; [exact (T x b' E0)|].
  assert (Hx : ~ outside W (bv_unsigned x)) by (intros Ho; rewrite (MU x Ho), E0 in E; discriminate E).
  pose proof (H x Hx) as Hw. unfold wview in Hw. rewrite E0 in Hw.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|]; [left; discriminate | contradiction].
Qed.

Lemma mfe_disjoint_le : forall W a n n', disjoint_from W a n -> 0 <= n' <= n -> disjoint_from W a n'.
Proof.
  induction W as [|[x y] W IH]; intros a n n' H Hn; cbn in *; [exact I|].
  destruct H as [H1 H2]. split; [lia | exact (IH a n n' H2 Hn)].
Qed.

(** The reserved segments cover [0x10000, 0x55000) without a gap, so a block with no byte in them lies below or
    above (the argument of U/Prog/snprintf.v's img_free_bound). *)
Definition mfe_ivs (l : list (word * word)) : list (Z * Z) :=
  map (fun s => (bv_unsigned (fst s), bv_unsigned (fst s) + bv_unsigned (snd s))) l.

Fixpoint mfe_cov (L : list (Z * Z)) (cur : Z) : Z :=
  match L with [] => cur | (a, b) :: L' => mfe_cov L' (if a <=? cur then Z.max cur b else cur) end.

Lemma mfe_cov_in : forall L cur x, cur <= x < mfe_cov L cur -> exists a b, In (a, b) L /\ a <= x < b.
Proof.
  induction L as [|[a b] L IH]; intros cur x Hx; cbn [mfe_cov] in Hx; [lia|].
  revert Hx. destruct (a <=? cur) eqn:E; intros Hx.
  - apply Z.leb_le in E. destruct (Z.lt_ge_cases x (Z.max cur b)) as [H|H].
    + exists a, b. split; [left; reflexivity | lia].
    + destruct (IH (Z.max cur b) x ltac:(lia)) as (a' & b' & Hin & Hab). exists a', b'.
      split; [right; exact Hin | exact Hab].
  - destruct (IH cur x Hx) as (a' & b' & Hin & Hab). exists a', b'. split; [right; exact Hin | exact Hab].
Qed.

Lemma mfe_rsegs_cov : mfe_cov (mfe_ivs (segments_reserved rsegs)) 0x10000 = 0x55000.
Proof. vm_compute. reflexivity. Qed.

Lemma mfe_noimg : forall a n, 0 <= a -> 0 < n -> blk_noimg rsegs a n -> a + n <= 0x10000 \/ 0x55000 <= a.
Proof.
  intros a n Ha Hn F.
  assert (Cv : forall x, 0x10000 <= x < 0x55000 -> exists s, In s (segments_reserved rsegs)
                 /\ bv_unsigned (fst s) <= x < bv_unsigned (fst s) + bv_unsigned (snd s)).
  { intros x Hx. rewrite <- mfe_rsegs_cov in Hx. destruct (mfe_cov_in _ _ _ Hx) as (a0 & b0 & Hin & Hab).
    unfold mfe_ivs in Hin. apply in_map_iff in Hin. destruct Hin as (s0 & Es & Hs). injection Es as Ea Eb.
    exists s0. split; [exact Hs | lia]. }
  destruct (Z.lt_ge_cases a 0x10000) as [H1|H1].
  - destruct (Z.le_gt_cases (a + n) 0x10000) as [H2|H2]; [left; exact H2|].
    destruct (Cv 0x10000 ltac:(lia)) as (s0 & Hs & Hx). exfalso.
    apply (F (0x10000 - a) ltac:(lia) s0 Hs). replace (a + (0x10000 - a)) with 0x10000 by lia. exact Hx.
  - destruct (Z.lt_ge_cases a 0x55000) as [H2|H2]; [|right; exact H2].
    destruct (Cv a ltac:(lia)) as (s0 & Hs & Hx). exfalso.
    apply (F 0 ltac:(lia) s0 Hs). rewrite Z.add_0_r. exact Hx.
Qed.

(** A C string whose bytes up to the next 8-byte boundary are not written stays. *)
Lemma mfe_cstr_transport : forall W m m' a s, cstr_at rsegs m a s -> munch W m m' ->
  disjoint_from W a (cstr_span a s) -> cstr_at rsegs m' a s.
Proof.
  intros W m m' a s HC MU HD.
  destruct (cstr_cut rsegs m a s HC) as (bs & sl & HB & Hz & Hn & _ & Hl & Hsl & _).
  assert (Hk0 : 0 <= (- (a + Z.of_nat (length bs) + 1)) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  unfold cstr_span in HD. rewrite <- Hl in HD.
  remember ((- (a + Z.of_nat (length bs) + 1)) mod 8) as k eqn:Ek.
  assert (Hk : (Z.to_nat k <= length sl)%nat) by lia.
  rewrite <- (firstn_skipn (Z.to_nat k) sl) in HB.
  replace (bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) sl ++ skipn (Z.to_nat k) sl)
    with ((bs ++ Z_to_bv 8 0 :: firstn (Z.to_nat k) sl) ++ skipn (Z.to_nat k) sl) in HB
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in HB as [HB _].
  exists bs, (firstn (Z.to_nat k) sl). split; [|split; [exact Hz | split; [exact Hn|]]].
  - eapply bytes_at_transport; [exact HB | exact MU |].
    rewrite app_length. cbn [length]. rewrite firstn_length_le by exact Hk.
    replace (Z.of_nat (length bs + S (Z.to_nat k))) with (Z.of_nat (length bs) + 1 + k) by lia. exact HD.
  - rewrite firstn_length_le by exact Hk. rewrite <- Hl, <- Ek. lia.
Qed.

(** The values of a C string are bytes. *)
Lemma mfe_cstr_range : forall m a l, cstr_at rsegs m a l -> Forall (fun x => 0 <= x < 256) l.
Proof.
  intros m a l (bs & sl & _ & Hz & _ & _). rewrite <- Hz. unfold zs. apply Forall_map. apply Forall_forall.
  intros b _. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(** A range that reads as the image stays so when no byte of it is written. *)
Lemma mfe_mrd_transport : forall W m m' b n, munch W m m' -> disjoint_from W b n -> 0 <= b -> b + n <= 2 ^ 64 ->
  (forall a, b <= a < b + n -> mrd rsegs m (wa a) = seg_rom rsegs (wa a)) ->
  forall a, b <= a < b + n -> mrd rsegs m' (wa a) = seg_rom rsegs (wa a).
Proof.
  intros W m m' b n MU HD H0 H1 H a Ha. rewrite <- (H a Ha). unfold mrd. rewrite MU; [reflexivity|].
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact HD | lia].
Qed.

(** The trailing bytes of a block (blk_slack) stay when the eight bytes after it are not written. *)
Lemma mfe_slack_transport : forall W m m' a n, blk_slack rsegs m a n -> munch W m m' ->
  disjoint_from W (a + n) 8 -> blk_slack rsegs m' a n.
Proof.
  intros W m m' a n (sl & HB & Hl) MU HD.
  pose proof (Z.mod_pos_bound (- (a + n)) 8 ltac:(lia)) as Hk0.
  remember ((- (a + n)) mod 8) as k eqn:Ek.
  rewrite <- (firstn_skipn (Z.to_nat k) sl) in HB. apply bytes_at_app in HB as [HB _].
  exists (firstn (Z.to_nat k) sl). split.
  - eapply bytes_at_transport; [exact HB | exact MU |].
    eapply mfe_disjoint_le; [exact HD|]. rewrite firstn_length_le by lia. lia.
  - rewrite firstn_length_le by lia. lia.
Qed.

(** The first byte of a C string: its first character, or its NUL (as in U/Prog/mf_tail.v). *)
Lemma mfe_cstr_first : forall m p s, cstr_at rsegs m p s ->
  exists b : byte, ov_read_bytes rsegs m (wa (p + Z.of_nat 0)) 1 = Some [b] /\
    (s = [] -> bv_unsigned b = 0) /\ (s <> [] -> bv_unsigned b <> 0).
Proof.
  intros m p s HC.
  destruct (cstr_cut rsegs m p s HC) as (bs & sl & HB & Hz & Hnz & Hn & Hlen & _ & _).
  destruct bs as [|b0 bs].
  - exists ZERO. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros _; reflexivity|]. intros Hs. exfalso. apply Hs. rewrite <- Hz. reflexivity.
  - exists b0. rewrite (bytes_at_ov_read rsegs m p _ 0 1 HB) by (cbn; lia). cbn.
    split; [reflexivity|]. split; [intros Hs; rewrite <- Hz in Hs; discriminate Hs|].
    intros _ E. apply Hnz. rewrite <- Hz. cbn. left. exact E.
Qed.

(** The bytes of the cells after the first ones, and of one 8-byte cell. *)
Lemma mfe_cells_suffix : forall m A pre post, rw_cells rsegs m A (pre ++ post) ->
  bytes_at rsegs m (A + Z.of_nat (cells_size pre)) (cells_bytes post).
Proof.
  intros m A pre post [[Hwf Hb] _]. apply cells_wf_app in Hwf as [Hw1 _].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [_ Hb].
  rewrite cells_bytes_length in Hb by exact Hw1. exact Hb.
Qed.

Lemma mfe_cell8_at : forall m A cs k v a w, rw_cells rsegs m A cs -> cell_at cs k = Some (C8 v) ->
  a = A + Z.of_nat k -> v = w -> bytes_at rsegs m a (le8 w).
Proof.
  intros m A cs k v a w H Hc -> <-.
  destruct (cell_at_split cs k (C8 v) (C8 v) Hc) as (pre & post & -> & Hsz & _).
  pose proof (mfe_cells_suffix m A pre (C8 v :: post) H) as B. rewrite Hsz in B.
  cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

(** ~x as a 64-bit word. *)
Lemma mfe_not : forall x, 0 <= x < 2 ^ 64 -> Z_to_bv 64 (18446744073709551615 - x) = Z_to_bv 64 (- 1 - x).
Proof.
  intros x Hx. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with 18446744073709551616.
  replace (-1 - x) with ((18446744073709551615 - x) + (-1) * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(** The 96-byte field at c + off of a block with no byte in the image is an snprintf destination. *)
Lemma mfe_img_free : forall c n off k, blk_noimg rsegs c n -> 0 <= off -> off + k <= n -> pf_img_free (c + off) k.
Proof.
  intros c n off k H H0 H1 i Hi s0 Hs. replace (c + off + i) with (c + (off + i)) by lia. apply H; [lia | exact Hs].
Qed.

Lemma mfe_byte_self : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(** The %s argument: a C string apart from the stack region [lo, S) and from the destination [D, D + n). *)
Lemma mfe_arg_str : forall m S lo D n a l, cstr_at rsegs m a l -> a <> 0 -> 0 <= a ->
  (a + Z.of_nat (length l) + 8 <= lo \/ S <= a) -> (a + Z.of_nat (length l) + 8 <= D \/ D + n <= a) ->
  pf_arg_ok m S lo D n (Z_to_bv 64 a) (APtr l).
Proof.
  intros m S lo D n a l HC Ha0 Ha1 H1 H2.
  destruct (cstr_cut rsegs m a l HC) as (bs & sl & HB & Hz & Hn & _ & Hl & Hsl & Hsl8).
  pose proof (bytes_at_bound _ _ _ _ HB) as HBB. rewrite app_length in HBB. cbn [length] in HBB.
  cbn [pf_arg_ok]. rewrite unsigned_lit by lia.
  split.
  - rewrite <- Hz. unfold zs. apply Forall_map. apply Forall_forall. intros b Hb.
    pose proof (bv_unsigned_in_range 8 b) as Rb. change (bv_modulus 8) with 256 in Rb.
    split; [|lia]. destruct (Z.eq_dec (bv_unsigned b) 0) as [E|E]; [|lia].
    exfalso. apply Hn. rewrite <- Hz. unfold zs. rewrite <- E. apply in_map. exact Hb.
  - exists sl. rewrite <- Hl. split; [|split; [exact Hsl | split; [lia | split; lia]]].
    replace (pf_bytes (l ++ [0]) ++ sl) with (bs ++ Z_to_bv 8 0 :: sl); [exact HB|].
    unfold pf_bytes. rewrite map_app. rewrite <- Hz. unfold zs. rewrite map_map.
    rewrite (map_ext (fun x => Z_to_bv 8 (bv_unsigned x)) (fun x => x)) by (intros b; apply mfe_byte_self).
    rewrite map_id. rewrite <- app_assoc. reflexivity.
Qed.

Lemma mfe_nulfree_of : forall l, forallb (fun c => negb (c =? 0)) l = true -> ~ In 0 l.
Proof. intros l H Hin. rewrite forallb_forall in H. specialize (H 0 Hin). cbn in H. discriminate H. Qed.

(** The literal "reac-pw.conf" (.rodata 0x10463, its NUL at 0x1046f; 0x10470 is 8-aligned, so no slack). *)
Lemma mfe_base_cstr : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. unfold STR_BASE.
  assert (HLn : Z.of_nat (length (zb S_base ++ [ZERO])) = 13) by (vm_compute; reflexivity).
  assert (HMd : (- (0x10463 + Z.of_nat (length S_base) + 1)) mod 8 = 0) by (vm_compute; reflexivity).
  assert (HLs : Z.of_nat (length ([] : list byte)) = 0) by reflexivity.
  pose proof (ro_cells_image rsegs m 0x10463 (zb S_base ++ [ZERO]) MI ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(rewrite HLn; lia)) as R.
  pose proof (proj2 R) as R2. cbn [cells_bytes cbytes] in R2. rewrite app_nil_r in R2.
  exists (zb S_base), []. split; [exact R2|].
  split; [vm_compute; reflexivity|].
  split; [apply mfe_nulfree_of; vm_compute; reflexivity|].
  rewrite HMd, HLs. lia.
Qed.

(** The format "%s" (.rodata 0x104e0). *)
Lemma mfe_fmt_s : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104e0 (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m MI.
  assert (HLn : Z.of_nat (length (pf_bytes ([37; 115] ++ [0]))) = 3) by reflexivity.
  pose proof (ro_cells_image rsegs m 0x104e0 (pf_bytes ([37; 115] ++ [0])) MI ltac:(vm_compute; reflexivity)
                ltac:(lia) ltac:(rewrite HLn; lia)) as R.
  pose proof (proj2 R) as R2. cbn [cells_bytes cbytes] in R2. rewrite app_nil_r in R2. exact R2.
Qed.

Lemma mfe_sx32 : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2^31); lia). reflexivity.
Qed.

Lemma mfe_addiw1 : forall v, 0 <= v -> v + 1 < 2 ^ 31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 1)) = Z_to_bv 64 (v + 1).
Proof.
  intros v H1 H2. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); lia). reflexivity.
Qed.

Lemma mfe_slts_false : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> b <= a ->
  bv_lts (Z_to_bv 64 a) (Z_to_bv 64 b) = false.
Proof.
  intros a b Ha Hb Hle. rewrite bv_lts_lxor, !unsigned_lit by lia.
  rewrite !zb_lxor_sign by lia. rewrite !Z.mod_small by lia. apply Z.ltb_ge. lia.
Qed.

Lemma mfe_zxb_eq0 : forall b : byte, bv_eqb (zxb b) (Z_to_bv 64 0) = (bv_unsigned b =? 0).
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R.
  unfold bv_eqb, zxb. rewrite !unsigned_lit by lia. reflexivity.
Qed.

(** The state the entry hands to the head: gen + 1, reading = the 95-byte prefix of the label or of the base name. *)
Definition mfe_fin (mc : mconf) (s L : list Z) : mconf :=
  fst (m_lines (mc_set_gen (mc_gen mc + 1) (mc_set_reading (firstn 95 L) mc), None) 0 (lines s)).

Lemma mfe_model : forall mc s lab L, match lab with Some l => l | None => S_base end = L -> ~ In 0 L ->
  m_file mc s lab = mfe_fin mc s L.
Proof.
  intros mc s lab L E HN. unfold m_file, mfe_fin. rewrite E. unfold snprintf_s.
  rewrite fmt_s1, cut_nul_id by exact HN. reflexivity.
Qed.

(** ** The walk *)
Lemma mf_entry_holds : snprintf_contract -> S_MF_ENTRY.
Proof.
  intros HSN HH HX. unfold m_file_contract, m_file_pre.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo mc s lab
    (Hc0 & Hc16 & HNI & HMC & HWR & HSL & HAc & Hgen & Href & Hov & Ht0 & HTNI & HTC & HTlen & HTap & HTapc &
     HLAB & HLX & HPE & HCAT & HWDS & HSO & MI).
  destruct HPE as (FRM & TM & SSP & HIE & HS63).
  destruct HSO as (ST & HK & HS16 & HROM).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HK. unfold SA in HIE. cbn [sa_img_end SEG_UBSAN] in HIE.
  assert (HN65 : Z.of_nat 65535 = 65535) by (vm_compute; reflexivity).
  assert (HTl : Z.of_nat (length s) <= 65535) by (rewrite <- HN65; apply (proj1 (Nat2Z.inj_le _ _)); exact HTlen).
  clear HN65.
  pose proof HWR as (HCge & HCle & _).
  pose proof (u64_range sp) as Rsp. pose proof (u64_range a0) as Ra0. pose proof (u64_range a1) as Ra1.
  pose proof (u64_range a2) as Ra2.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1. pose proof (Z_to_bv_lit_self a2) as Ea2.
  assert (WV0 : forall x, lo <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; exact (proj1 (proj2 (proj2 ST) x Hx))).
  assert (WVB : forall i, 0 <= i < SEG_M_SIZE -> wview rsegs m (wa (bv_unsigned a0 + i)) <> None)
    by (intros i Hi; exact (proj2 (proj2 HWR) i Hi)).
  set (Sp := bv_unsigned sp) in *. set (C := bv_unsigned a0) in *. set (T := bv_unsigned a1) in *.
  set (LP := bv_unsigned a2) in *.
  rewrite <- Esp, <- Ea0, <- Ea1, <- Ea2. clearbody Sp C T LP. clear Esp Ea0 Ea1 Ea2.
  unfold M_FILE.
  (* arithmetic shapes the walk needs *)
  pose proof (proj1 ST) as Hlo0.
  pose proof (mfe_noimg C SEG_M_SIZE ltac:(lia) ltac:(unfold SEG_M_SIZE; lia) HNI) as HCPL.
  unfold SEG_M_SIZE in HCPL, HCle. unfold SEG_M_SIZE, apart in HAc.
  unfold MC_READING in HLX. unfold apart in HTap.
  assert (HL3 : Z.land C 3 = 0)
    by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4;
        Z.div_mod_to_equations; lia).
  clear HTlen.
  pose proof (mconf_atp_bytes rsegs false m C mc HMC) as (bs0 & _ & HE0 & _).
  pose proof (mconf_enc_bounds false mc bs0 HE0)
    as (_ & Hseg32 & Hkept8 & Hgen0 & Href0 & Hov0 & Hrdlen & Hrdnf & Hrdr & _).
  unfold apart in HTapc. unfold SEG_M_SIZE in HTapc.
  pose proof (Z.mod_pos_bound (- (T + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as HTk.
  unfold cstr_span in HTapc.
  pose proof (mfe_base_cstr m MI) as HBASE. unfold STR_BASE in HBASE.
  (* the prologue: the frame [Sp - 272, Sp) *)
  pose proof (munch_refl [(Sp - 6224, Sp); (C + 9132, C + 9236)] m) as MU.
  pose proof (munch_refl [(Sp - 6224, Sp)] m) as MUf.
  pose proof (wmono_refl rsegs m) as WM.
  step. carve_frame 272%nat ST.
  do 13 step.
  (* the continuation from 0x142d0, where the label pointer (or the base literal) is in a3 *)
  assert (K : forall (A3 : Z) (L : list Z) (a0' a1' a3' s8' : word),
    a0' = Z_to_bv 64 (C + 9140) -> a3' = Z_to_bv 64 A3 -> s8' = Z_to_bv 64 (C + 8192) ->
    cstr_at rsegs m A3 L -> A3 <> 0 -> 0 <= A3 ->
    (A3 + Z.of_nat (length L) + 8 <= lo \/ Sp <= A3) ->
    (A3 + Z.of_nat (length L) + 8 <= C + 9140 \/ C + 9236 <= A3) ->
    Z.of_nat (length L) < 2 ^ 31 - 1 ->
    evt rsegs
      (ret_void_fp ra (Z_to_bv 64 Sp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F m
         (M_FILE_W Sp C (length (mc_kept mc)) (mfe_fin mc s L)) lo
         (fun m' => mconf_at rsegs m' C (mfe_fin mc s L)))
      (MS (mkR ra (Z_to_bv 64 (Sp + -272)) gp tp t0 t1 t2 (Z_to_bv 64 C) s1 a0' a1' (Z_to_bv 64 LP) a3'
               a4 a5 a6 a7 (Z_to_bv 64 T) s3 s4 s5 s6 s7 s8' s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x142d0) fc None m0 (seg_rom rsegs))).
  { intros A3 L a0' a1' a3' s8' E0 E3 E8 HCL HA30 HA3n HB1 HB2 HLlen. subst a0' a3' s8'.
    pose proof (mfe_cstr_range m A3 L HCL) as HLr.
    pose proof (cstr_cut rsegs m A3 L HCL) as (bsL & slL & _ & _ & HLnf & _ & _ & _ & _).
    pose proof (Z.mod_pos_bound (- (A3 + Z.of_nat (length L) + 1)) 8 ltac:(lia)) as HAk.
    do 5 step.
    (* the frame cells, the block and the machine at the call *)
    destruct (stk_split rsegs m1 lo (Sp - 6224) (Sp + -272) ST ltac:(lia)) as [STlo STcall].
    assert (HMC1 : mconf_atp rsegs false m1 C mc)
      by (eapply mconf_atp_transport; [exact HMC | exact MUf |
          cbn [disjoint_from]; unfold SEG_M_SIZE; split; [lia | exact I]]).
    destruct (mconf_field_cells rsegs false m1 C mc MC_READING HMC1 HWR
                ltac:(unfold MC_READING; lia) ltac:(unfold MC_READING, SEG_M_SIZE; lia)) as [junkD FRD].
    unfold MC_READING in FRD.
    assert (TM1 : MemNorm.task_mem rsegs m1).
    { eapply mfe_task_mem; [exact TM | exact MUf |].
      intros x Hx. cbn [outside] in Hx.
      destruct (Z.le_gt_cases (Sp - 6224) (bv_unsigned x)) as [H1|H1];
        destruct (Z.lt_ge_cases (bv_unsigned x) Sp) as [H2|H2];
        try (exfalso; apply Hx; split; [lia | exact I]).
      pose proof (WV0 (bv_unsigned x) ltac:(lia)) as Wv. unfold wa in Wv.
      rewrite Z_to_bv_lit_self in Wv. exact Wv. }
    destruct SSP as (HGG & gw & HG).
    unfold SA in HGG, HG. cbn [sa_got_guard sa_guard SEG_UBSAN] in HGG, HG.
    assert (HGG1 : bytes_at rsegs m1 0x221b0 (le8 (Z_to_bv 64 0x53820)))
      by (eapply bytes_at_transport; [exact HGG | exact MUf |
          cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I]]).
    assert (HG1 : bytes_at rsegs m1 0x53820 (le8 gw))
      by (eapply bytes_at_transport; [exact HG | exact MUf |
          cbn [disjoint_from]; rewrite length_le8; split; [lia | exact I]]).
    assert (HCL1 : cstr_at rsegs m1 A3 L)
      by (eapply mfe_cstr_transport; [exact HCL | exact MUf |
          cbn [disjoint_from]; unfold cstr_span; split; [lia | exact I]]).
    eapply evt_cut.
    { eapply HSN with (lo := Sp - 6224) (canary := gw) (fmt := [37; 115]) (args := [APtr L]) (junk := junkD).
      - rewrite unsigned_lit by lia. exact (mfe_fmt_s m1 MI).
      - rewrite unsigned_lit by lia. unfold RO_LO. lia.
      - rewrite unsigned_lit by lia. unfold RO_END. cbn [length]. lia.
      - reflexivity.
      - cbn [pf_args_ok]. split; [|exact I].
        rewrite !unsigned_lit by lia. apply mfe_arg_str; try assumption; lia.
      - reflexivity.
      - rewrite !unsigned_lit by lia. change (Z.to_nat 96) with 96%nat. exact FRD.
      - rewrite unsigned_lit by lia. lia.
      - rewrite app_nil_r. lia.
      - rewrite unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by lia. lia.
      - rewrite !unsigned_lit by lia.
        apply (mfe_img_free C SEG_M_SIZE 9140 96 HNI); unfold SEG_M_SIZE; lia.
      - rewrite unsigned_lit by lia. replace (Sp - 272) with (Sp + -272) by lia. exact STcall.
      - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
      - unfold IMG_END. lia.
      - rewrite unsigned_lit by lia. lia.
      - exact FRM.
      - exact MI.
      - exact TM1.
      - unfold GOT_GUARD, GUARD. exact HGG1.
      - unfold GUARD. exact HG1. }
    intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fcs & m2 & -> &
                MU2 & WM2 & MI2 & TM2 & FRM2 & HF2 & ST2 & HBD).
    rewrite ret_pc_even by (try lia; reflexivity).
    assert (E272 : bv_unsigned (Z_to_bv 64 (Sp + -272)) = Sp + -272) by (apply unsigned_lit; lia).
    assert (E9140 : bv_unsigned (Z_to_bv 64 (C + 9140)) = C + 9140) by (apply unsigned_lit; lia).
    assert (E96 : bv_unsigned (Z_to_bv 64 96) = 96) by (apply unsigned_lit; lia).
    assert (E95 : Z.to_nat (96 - 1) = 95%nat) by (vm_compute; reflexivity).
    rewrite E272 in MU2.
    rewrite E272 in ST2.
    rewrite E9140 in MU2.
    rewrite E9140 in HBD.
    rewrite E96 in MU2.
    rewrite E96 in HBD.
    rewrite E95 in MU2.
    rewrite E95 in HBD.
    rewrite app_nil_r in MU2.
    rewrite app_nil_r in HBD.
    assert (HNB : Z.of_nat (length (pf_bytes (firstn 95 L ++ [0]))) = Z.of_nat (length (firstn 95 L)) + 1)
      by (unfold pf_bytes; rewrite map_length, app_length; cbn [length]; lia).
    assert (HTwlen : (length (firstn 95 L) <= 95)%nat) by (rewrite firstn_length; lia).
    assert (HTwnf : ~ In 0 (firstn 95 L))
      by (intros Hin; apply HLnf; rewrite <- (firstn_skipn 95 L); apply in_or_app; left; exact Hin).
    assert (HTwr : Forall (fun x => 0 <= x < 256) (firstn 95 L)).
    { pose proof HLr as HLr'. rewrite <- (firstn_skipn 95 L) in HLr'. apply Forall_app in HLr'. tauto. }
    (* the block now holds the new reading *)
    assert (HMC2 : mconf_atp rsegs false m2 C (mc_set_reading (firstn 95 L) mc)).
    { eapply (mconf_atp_upd rsegs false false m1 m2 C mc _ (C + 9140) (pf_bytes (firstn 95 L ++ [0])));
        [exact HMC1 | exact MU2 | | exact HBD | lia | rewrite HNB; unfold SEG_M_SIZE; lia |].
      - intros x Hx Ho. rewrite HNB. unfold SEG_M_SIZE in Hx.
        destruct (Z.le_gt_cases (C + 9140) x) as [Ha|Ha];
          destruct (Z.lt_ge_cases x (C + 9140 + Z.of_nat (length (firstn 95 L)) + 1)) as [Hb|Hb];
          try lia;
          exfalso; apply Ho; cbn [outside]; (split; [lia|]); (split; [lia|]); exact I.
      - intros bs Hbs.
        replace (Z.to_nat (C + 9140 - C)) with (Z.to_nat MC_READING) by (unfold MC_READING; f_equal; lia).
        replace (pf_bytes (firstn 95 L ++ [0])) with (zb (firstn 95 L) ++ [ZERO])
          by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
        apply mconf_enc_reading; [exact Hbs | lia | exact HTwnf | exact HTwr]. }
    (* carry the footprint, the stack and the frame across the call *)
    assert (MU' : munch [(Sp - 6224, Sp); (C + 9132, C + 9236)] m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
      unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). split; [lia|]. split; [lia|]. exact I. }
    assert (STlo2 : stk rsegs m2 lo (Sp - 6224)).
    { eapply stk_transport_disjoint; [exact STlo | exact MU2 | exact WM2 |
        cbn [disjoint_from]; split; [lia|]; split; [lia | exact I]]. }
    assert (ST' : stk rsegs m2 lo (Sp + -272)) by (eapply stk_merge; [exact STlo2 | exact ST2 | lia]).
    eapply rw_cells_transport in FR; [| exact MU2 | exact WM2 |
      cbn [disjoint_from cells_size csize Nat.add]; split; [lia|]; split; [lia | exact I]].
    eapply wr_at_transport in HWR; [| exact WM2].
    assert (WM' : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
    clear MU MUf MU2 WM ST STlo STcall MI HMC1 FRD TM1 HGG1 HG1 HCL1.
    rename MU' into MU. rename WM' into WM. rename ST' into ST. rename MI2 into MI.
    (* c->gen++ *)
    pose proof (mconf_rd_gen rsegs false m2 C (mc_set_reading (firstn 95 L) mc) HMC2) as RG.
    cbn [mc_gen mc_set_reading] in RG. unfold MC_GEN in RG.
    step. rewrite (mfe_sx32 (mc_gen mc)) by lia.
    step. rewrite (mfe_addiw1 (mc_gen mc)) by lia.
    step. rewrite (mfe_slts_false (mc_gen mc + 1) (mc_gen mc)) by lia. cbv iota.
    pose proof (wr_at_store_ok rsegs m2 C SEG_M_SIZE 9136 4 HWR ltac:(lia)
                  ltac:(unfold SEG_M_SIZE; cbn [Z.of_nat]; lia)) as HS.
    step.
    assert (HMC3 : mconf_atp rsegs false (write_to_mem m2 (wa (C + 9136)) (le4 (Z_to_bv 64 (mc_gen mc + 1))))
                     C (mc_set_gen (mc_gen mc + 1) (mc_set_reading (firstn 95 L) mc))).
    { eapply mconf_atp_store; [exact HMC2 | lia | rewrite length_le4; unfold SEG_M_SIZE; lia |].
      intros bs Hbs.
      replace (Z.to_nat (C + 9136 - C)) with (Z.to_nat MC_GEN) by (unfold MC_GEN; f_equal; lia).
      apply mconf_enc_gen; [exact Hbs | lia]. }
    store_done.
    assert (HTC3 : cstr_at rsegs m0 T s).
    { eapply mfe_cstr_transport; [exact HTC | exact MU |
        cbn [disjoint_from]; unfold cstr_span; split; [lia|]; split; [lia | exact I]]. }
    destruct (mfe_cstr_first m0 T s HTC3) as (bT & RDT & HbT0 & HbT1).
    (* the frame's saved registers and the released stack, for the exit and for the head *)
    assert (E168 : Z.of_nat 168 = 168) by (vm_compute; reflexivity).
    assert (SAV : bytes_at rsegs m0 (Sp + -272 + 168)
      (le8 s11 ++ le8 s10 ++ le8 s9 ++ le8 s8 ++ le8 s7 ++ le8 s6 ++ le8 s5 ++ le8 s4 ++ le8 s3 ++
       le8 s2 ++ le8 s1 ++ le8 s0 ++ le8 ra ++ [])).
    { match type of FR with
      | rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
          pose proof (mfe_cells_suffix m0 (Sp + -272) [c1; c2; c3] rest FR) as B
      end.
      cbn [cells_size csize Nat.add] in B. rewrite E168 in B.
      cbn [cells_bytes cbytes] in B. exact B. }
    assert (SUB : forall mcf, sub_fp [(Sp - 6224, Sp); (C + 9132, C + 9236)]
                    (M_FILE_W Sp C (length (mc_kept mc)) mcf)).
    { intros mcf. unfold sub_fp, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K, MC_NKEPT, MC_READING.
      cbn [outside]. intros x (H1 & _ & _ & _ & _ & H6 & _). split; [lia|]. split; [lia|]. exact I. }
    step. step. rewrite mfe_zxb_eq0.
    destruct s as [|c0 cs].
    - (* the text is empty: the epilogue 0x14980 with the state after gen++ *)
      rewrite (HbT0 eq_refl). cbn [Z.eqb]. cbv iota.
      release_frame FR ST Sp.
      eapply evt_mono.
      { eapply HX with (lo := lo) (W := [(Sp - 6224, Sp); (C + 9132, C + 9236)])
          (Q := fun m' => mconf_at rsegs m' C (mfe_fin mc [] L)) (sp0 := Z_to_bv 64 Sp).
        - rewrite !unsigned_lit by lia. unfold M_FILE_FRAME. lia.
        - unfold M_FILE_SAVE. rewrite unsigned_lit by lia. exact SAV.
        - exact FRM2.
        - exact MI.
        - eapply mfe_task_mem; [exact TM | exact MU |].
          intros x Hx. cbn [outside] in Hx.
          destruct (Z.le_gt_cases (Sp - 6224) (bv_unsigned x)) as [H1|H1];
            destruct (Z.lt_ge_cases (bv_unsigned x) Sp) as [H2|H2];
            [ pose proof (WV0 (bv_unsigned x) ltac:(lia)) as Wv; unfold wa in Wv;
              rewrite Z_to_bv_lit_self in Wv; exact Wv | | | ];
          destruct (Z.le_gt_cases (C + 9132) (bv_unsigned x)) as [H3|H3];
            destruct (Z.lt_ge_cases (bv_unsigned x) (C + 9236)) as [H4|H4];
            try (exfalso; apply Hx; split; [lia|]; split; [lia | exact I]);
          pose proof (WVB (bv_unsigned x - C) ltac:(unfold SEG_M_SIZE; lia)) as Wv;
          replace (C + (bv_unsigned x - C)) with (bv_unsigned x) in Wv by lia;
          unfold wa in Wv; rewrite Z_to_bv_lit_self in Wv; exact Wv.
        - rewrite unsigned_lit by lia. exact ST.
        - unfold mfe_fin. cbn [lines lines_go m_lines fst]. exact HMC3. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 &
                  F' & fc' & m' & -> & HFx & HKx & MUx & WMx & MIx & TMx & STy & HQx).
      exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, F', fc', m'.
      rewrite unsigned_lit in STy by lia.
      split; [reflexivity|]. split; [exact HFx|].
      split; [intros k Hk; rewrite (HKx k Hk); exact (HF2 k Hk)|].
      split; [eapply munch_weaken; [apply SUB | eapply munch_trans; [exact MU | exact MUx]]|].
      split; [eapply wmono_trans; [exact WM | exact WMx]|].
      split; [exact MIx|]. split; [exact TMx|].
      split; [rewrite unsigned_lit by lia; exact STy|]. exact HQx.
    - (* a line follows: the set-up 0x142fc-0x14344 *)
      assert (Hne : c0 :: cs <> []) by discriminate.
      rewrite (proj2 (Z.eqb_neq _ 0) (HbT1 Hne)). cbv iota.
      pose proof (munch_refl [(Sp - 6224, Sp)] m0) as MUs.
      do 19 step.
      (* the frame cells the loop keeps *)
      assert (CEL1 : cell8 m3 (Sp + -272 + 8) (- 1 - C)).
      { unfold cell8. eapply (mfe_cell8_at _ _ _ 8%nat _ _ (Z_to_bv 64 (- 1 - C)));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity |].
        rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. apply mfe_not. lia. }
      assert (CEL2 : cell8 m3 (Sp + -272 + 16) (C + MC_KNOCK)).
      { unfold cell8, MC_KNOCK. eapply (mfe_cell8_at _ _ _ 16%nat _ _ (Z_to_bv 64 (C + 9100)));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity | reflexivity]. }
      assert (CEL3 : cell8 m3 (Sp + -272 + 24) (- 1 - (C + MC_KNOCK))).
      { unfold cell8, MC_KNOCK. eapply (mfe_cell8_at _ _ _ 24%nat _ _ (Z_to_bv 64 (- 1 - (C + 9100))));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity |].
        rewrite unsigned_lit by lia. rewrite zb_lxor_ones by lia. apply mfe_not. lia. }
      assert (CEL4 : cell8 m3 (Sp + -272 + 32) (C + MC_READING)).
      { unfold cell8, MC_READING. eapply (mfe_cell8_at _ _ _ 32%nat _ _ (Z_to_bv 64 (C + 9140)));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity | reflexivity]. }
      assert (CEL5 : cell8 m3 (Sp + -272 + 40) (C + MC_N)).
      { unfold cell8, MC_N. eapply (mfe_cell8_at _ _ _ 40%nat _ _ (Z_to_bv 64 (C + 8192)));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity | reflexivity]. }
      assert (CEL6 : cell8 m3 (Sp + -272 + 48) (cur_ptr C None)).
      { unfold cell8, cur_ptr. eapply (mfe_cell8_at _ _ _ 48%nat _ _ (Z_to_bv 64 0));
          [exact FR | cells_cbv; reflexivity | f_equal; vm_compute; reflexivity | reflexivity]. }
      (* the block, the text and the environment at the head *)
      assert (HMCh : mconf_at rsegs m3 C (mc_set_gen (mc_gen mc + 1) (mc_set_reading (firstn 95 L) mc))).
      { eapply mconf_atp_transport; [exact HMC3 | exact MUs |
          cbn [disjoint_from]; unfold SEG_M_SIZE; split; [lia | exact I]]. }
      assert (HSL3 : blk_slack rsegs m3 C SEG_M_SIZE).
      { eapply mfe_slack_transport; [exact HSL | exact MU |
          cbn [disjoint_from]; unfold SEG_M_SIZE; split; [lia|]; split; [lia | exact I]]. }
      assert (HTCh : cstr_at rsegs m3 T (c0 :: cs)).
      { eapply mfe_cstr_transport; [exact HTC3 | exact MUs |
          cbn [disjoint_from]; unfold cstr_span; split; [lia | exact I]]. }
      assert (TM3 : MemNorm.task_mem rsegs m3).
      { eapply mfe_task_mem; [exact TM | exact MU |].
        intros x Hx. cbn [outside] in Hx.
        destruct (Z.le_gt_cases (Sp - 6224) (bv_unsigned x)) as [H1|H1];
          destruct (Z.lt_ge_cases (bv_unsigned x) Sp) as [H2|H2];
          [ pose proof (WV0 (bv_unsigned x) ltac:(lia)) as Wv; unfold wa in Wv;
            rewrite Z_to_bv_lit_self in Wv; exact Wv | | | ];
        destruct (Z.le_gt_cases (C + 9132) (bv_unsigned x)) as [H3|H3];
          destruct (Z.lt_ge_cases (bv_unsigned x) (C + 9236)) as [H4|H4];
          try (exfalso; apply Hx; split; [lia|]; split; [lia | exact I]);
        pose proof (WVB (bv_unsigned x - C) ltac:(unfold SEG_M_SIZE; lia)) as Wv;
        replace (C + (bv_unsigned x - C)) with (bv_unsigned x) in Wv by lia;
        unfold wa in Wv; rewrite Z_to_bv_lit_self in Wv; exact Wv. }
      assert (SSP3 : ssp_ok m3).
      { unfold ssp_ok, SA. cbn [sa_got_guard sa_guard SEG_UBSAN]. split.
        - eapply bytes_at_transport; [exact HGG | exact MU |
            cbn [disjoint_from]; rewrite length_le8; split; [lia|]; split; [lia | exact I]].
        - exists gw. eapply bytes_at_transport; [exact HG | exact MU |
            cbn [disjoint_from]; rewrite length_le8; split; [lia|]; split; [lia | exact I]]. }
      assert (CAT3 : cat_img rsegs m3 (sa_catalogue SA)).
      { unfold cat_img, SA in HCAT |- *. cbn [sa_catalogue SEG_UBSAN] in HCAT |- *.
        eapply mfe_mrd_transport; [exact MU |
          cbn [disjoint_from]; unfold CAT_BYTES; split; [lia|]; split; [lia | exact I] |
          lia | unfold CAT_BYTES; lia | exact HCAT]. }
      assert (WDS3 : words_img m3).
      { unfold words_img in HWDS |- *. unfold M_KEY_WORDS in HWDS |- *.
        eapply mfe_mrd_transport; [exact MU |
          cbn [disjoint_from]; split; [lia|]; split; [lia | exact I] | lia | lia | exact HWDS]. }
      release_frame FR ST Sp.
      (* the loop invariant and the registers at the head *)
      assert (MFL : m_file_loop m3 fcs Sp (Sp + -272) lo C T
                      (mc_set_gen (mc_gen mc + 1) (mc_set_reading (firstn 95 L) mc)) None 0
                      (length (mc_kept mc)) (c0 :: cs) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
      { unfold m_file_loop.
        split; [unfold M_FILE_FRAME; lia|].
        split; [unfold saved_at, M_FILE_SAVE; exact SAV|].
        split; [exact CEL1|]. split; [exact CEL2|]. split; [exact CEL3|].
        split; [exact CEL4|]. split; [exact CEL5|]. split; [exact CEL6|].
        split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HNI|].
        split; [exact HMCh|]. split; [exact HWR|]. split; [exact HSL3|].
        split; [unfold apart, SEG_M_SIZE; lia|].
        split; [exact I|].
        split; [cbn [mc_kept mc_set_gen mc_set_reading]; lia|].
        split; [lia|]. split; [lia|].
        split; [cbn [mc_refused mc_set_gen mc_set_reading]; lia|].
        split; [cbn [mc_overflow mc_set_gen mc_set_reading]; lia|].
        split; [exact Ht0|]. split; [exact HTNI|]. split; [exact HTCh|].
        split; [unfold apart; lia|].
        split; [unfold apart, SEG_M_SIZE, cstr_span; lia|].
        split; [unfold printf_env; split; [exact FRM2|]; split; [exact TM3|]; split; [exact SSP3|];
                split; [unfold SA; cbn [sa_img_end SEG_UBSAN]; lia | lia]|].
        split; [exact CAT3|]. split; [exact WDS3|].
        split; [unfold stack_ok, M_FILE_STACK, M_FILE_FRAME, PRINTF_K;
                split; [exact ST|]; split; [lia|]; split; [exact HS16 | exact HROM]|].
        exact MI. }
      assert (MFR : m_file_regs C T 0 (Z_to_bv 64 C) (Z_to_bv 64 T) (Z_to_bv 64 0) (Z_to_bv 64 1)
                      (Z_to_bv 64 511) (Z_to_bv 64 35) (Z_to_bv 64 (C + 8192))
                      (Z_to_bv 64 4294976000) (Z_to_bv 64 32) (Z_to_bv 64 59)).
      { unfold m_file_regs, MC_N, BLANK_MASK. repeat split; reflexivity. }
      eapply evt_mono.
      { eapply (HH (S (length (c0 :: cs)))) with (sp0 := Z_to_bv 64 Sp) (ra0 := ra)
          (e0 := s0) (e1 := s1) (e2 := s2) (e3 := s3) (e4 := s4) (e5 := s5) (e6 := s6) (e7 := s7)
          (e8 := s8) (e9 := s9) (e10 := s10) (e11 := s11) (lo := lo)
          (c := C) (p := T) (line := 0) (cur := None) (k0 := length (mc_kept mc)) (rest := c0 :: cs)
          (mc := mc_set_gen (mc_gen mc + 1) (mc_set_reading (firstn 95 L) mc)).
        - lia.
        - exact Hne.
        - rewrite !unsigned_lit by lia. exact MFL.
        - exact MFR. }
      intros ms' (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 &
                  F' & fc' & m' & -> & HFx & HKx & MUx & WMx & MIx & TMx & STy & HQx).
      rewrite !unsigned_lit in MUx, STy by lia.
      unfold mfe_fin.
      exists z0, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, F', fc', m'.
      split; [reflexivity|]. split; [exact HFx|].
      split; [intros k Hk; rewrite (HKx k Hk); exact (HF2 k Hk)|].
      split; [eapply munch_trans; [eapply munch_weaken; [apply SUB | exact MU] | exact MUx]|].
      split; [eapply wmono_trans; [exact WM | exact WMx]|].
      split; [exact MIx|]. split; [exact TMx|].
      split; [rewrite unsigned_lit by lia; exact STy|]. exact HQx. }
  step. step.
  rewrite unsigned_lit by lia. rewrite HL3.
  step. if_cases Ktr; cbv iota; [exfalso; zify_cond Ktr; lia|].
  do 6 step.
  assert (HLB : Z.of_nat (length S_base) = 12) by (vm_compute; reflexivity).
  destruct lab as [l|].
  - (* a label: a3 = label *)
    destruct HLAB as (HLP0 & HLPC).
    destruct HLX as (HLn & HLap1 & HLap2). unfold apart in HLap1, HLap2.
    pose proof HLPC as HLPC'. destruct HLPC' as (bsl & sll & _ & _ & HLnf0 & _).
    rewrite (mfe_model mc s (Some l) l eq_refl HLnf0).
    step. if_cases Kb; cbv iota.
    + eapply K with (A3 := LP) (L := l);
        [reflexivity | reflexivity | reflexivity | exact HLPC | exact HLP0 | lia | lia | lia | lia].
    + exfalso. zify_cond Kb. try (rewrite unsigned_lit in Kb by lia). lia.
  - (* no label: a3 = "reac-pw.conf" *)
    cbn [ocstr_at] in HLAB. subst LP.
    assert (HBnf : ~ In 0 S_base) by (apply mfe_nulfree_of; vm_compute; reflexivity).
    rewrite (mfe_model mc s None S_base eq_refl HBnf).
    step. if_cases Kb; cbv iota.
    + exfalso. zify_cond Kb. lia.
    + do 2 step.
      eapply K with (A3 := 0x10463) (L := S_base);
        [reflexivity | first [reflexivity | (rewrite ?unsigned_lit by lia; f_equal; lia)] | reflexivity
        | exact HBASE | lia | lia | rewrite HLB; lia | rewrite HLB; lia | rewrite HLB; lia].
Qed.
