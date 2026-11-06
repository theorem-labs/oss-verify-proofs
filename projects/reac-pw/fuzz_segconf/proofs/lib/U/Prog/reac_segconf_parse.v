(** reac_segconf_parse (reac_segconf.c:327-332), UBSan build: at 0x15e7c in the UBSan image 1696d6c34ffd, 18
    instructions, level-3 identical to the plain build's 0x156f0 (frame 0x20: ra at sp+0x18, s0 = c at sp+0x10, s1 at
    sp+8; no sanitizer check in it):
      n = reac_segconf_parse_file(c, text, "reac-pw.conf")   (jal 0x15248 at 0x15e9c, the label at STR_BASE 0x10463)
      cross_check(c)                                        (jal 0x15ec4 at 0x15ea8)
      return n                                              (kept in s1)
    The walk is Prog/reac_segconf_parse.v's over this build's image, contracts and seg_env (SA = SEG_UBSAN; the
    callee frames: parse_file 0x420, cross_check 0x50, below refuse's). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel SegRefusedBound.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import refuse_c cross_check_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** ** Memory facts over any segment list *)
Section Gen.
Variable segs : list Segment.

Lemma disjoint_from_sub : forall W a n a' n',
  disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; cbn [disjoint_from]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia | exact (IH a n a' n' D2 H1 H2)].
Qed.

Lemma rconf_at_munch : forall W m m' c rc,
  rconf_at segs m c rc -> munch W m m' -> disjoint_from W c SEG_C_SIZE -> rconf_at segs m' c rc.
Proof.
  intros W m m' c rc (bs & B & E) MU D. exists bs. split; [|exact E].
  eapply bytes_at_transport; [exact B | exact MU |]. destruct E as [L _]. rewrite L. exact D.
Qed.

(** A write apart from [a, a + length s + 8) keeps the C string at a: cstr_at needs at most 7 bytes of slack. *)
Lemma cstr_at_munch : forall W m m' a s,
  cstr_at segs m a s -> munch W m m' -> disjoint_from W a (Z.of_nat (length s) + 8) -> cstr_at segs m' a s.
Proof.
  intros W m m' a s (bs & sl & B & Ez & N & S) MU D.
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  pose (k := Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)).
  assert (Hk : Z.of_nat k = (- (a + Z.of_nat (length s) + 1)) mod 8) by (unfold k; lia).
  clearbody k.
  assert (Lbs : length bs = length s) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  assert (Lk : length (firstn k sl) = k) by (rewrite length_firstn; lia).
  exists bs, (firstn k sl). split; [|split; [exact Ez|split; [exact N|rewrite Lk; lia]]].
  rewrite <- (firstn_skipn k sl) in B.
  replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in B as [B _].
  eapply bytes_at_transport; [exact B | exact MU |].
  eapply disjoint_from_sub; [exact D | lia |].
  rewrite length_app; cbn [length]. rewrite Lk, Lbs. lia.
Qed.

(** Every byte of a present stack region is a task byte (MemNorm.task_mem's condition). *)
Lemma stk_task : forall m lo hi, MemNorm.task_mem segs m -> stk segs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped segs x Nf) in Hb. discriminate.
Qed.

Lemma task_mem_frame : forall lo' hi' m m', MemNorm.task_mem segs m -> munch [(lo', hi')] m m' ->
  (forall x : word, lo' <= bv_unsigned x < hi' ->
     find_segment segs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE) ->
  MemNorm.task_mem segs m'.
Proof.
  intros lo' hi' m m' T MU H a b E.
  destruct (Z_lt_le_dec (bv_unsigned a) lo') as [L|L].
  - assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
  - destruct (Z_lt_le_dec (bv_unsigned a) hi') as [L2|L2]; [apply H; lia|].
    assert (Q : m' a = m a) by (apply MU; cbn [outside]; split; [lia | exact I]).
    rewrite Q in E. exact (T a b E).
Qed.

Lemma munch3 : forall W W0 W1 W2 m m1 m2 m3,
  munch W0 m m1 -> munch W1 m1 m2 -> munch W2 m2 m3 -> sub_fp W0 W -> sub_fp W1 W -> sub_fp W2 W -> munch W m m3.
Proof.
  intros W W0 W1 W2 m m1 m2 m3 H0 H1 H2 S0 S1 S2.
  apply (munch_trans W m m1 m3); [exact (munch_weaken W0 W m m1 S0 H0)|].
  apply (munch_trans W m1 m2 m3); [exact (munch_weaken W1 W m1 m2 S1 H1) | exact (munch_weaken W2 W m2 m3 S2 H2)].
Qed.

(** A block no byte of which lies in a reserved segment is apart from any range inside one reserved segment. *)
Lemma noimg_apart : forall a n x k, blk_noimg segs a n -> 0 < n -> 0 < k ->
  existsb (fun s => (bv_unsigned (fst s) <=? x) && (x + k <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved segs) = true ->
  x + k <= a \/ a + n <= x.
Proof.
  intros a n x k NI Hn Hk E. apply existsb_exists in E as (s & Hs & Hb).
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (Z_le_gt_dec (x + k) a) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (a + n) x) as [L2|L2]; [right; exact L2|].
  exfalso. destruct (Z_le_gt_dec a x) as [L3|L3].
  - apply (NI (x - a) ltac:(lia) s Hs). lia.
  - apply (NI 0 ltac:(lia) s Hs). lia.
Qed.
End Gen.

(** ** The spine *)
Lemma r_parse_snd rc s : snd (r_parse rc s) = snd (r_parse_file rc s (Some S_base)).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.
Lemma r_parse_fst rc s : fst (r_parse rc s) = cross_check (fst (r_parse_file rc s (Some S_base))).
Proof. unfold r_parse. destruct (r_parse_file rc s (Some S_base)). reflexivity. Qed.

(** ** This build's image *)
Ltac sa_num := cbn [SA SEG_PLAIN SEG_UBSAN sa_img_end sa_img_top sa_guard sa_got_guard sa_catalogue] in *.
Ltac stack_num := unfold cross_check_W in *;
  unfold PARSE_STACK, PARSE_FILE_STACK, PARSE_FILE_FRAME, CROSS_CHECK_STACK, REFUSE_STACK, PRINTF_K in *.
Ltac c_num := unfold RC_PARSE_W, cross_check_W, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN, RSEG_SIZE,
  SEG_C_SIZE in *.
Ltac dj := cbn [disjoint_from]; repeat split; first [exact I | lia].

(** A write apart from the two stack-protector cells keeps them. *)
Lemma ssp_ok_munch : forall W m m', ssp_ok m -> munch W m m' ->
  disjoint_from W (sa_got_guard SA) 8 -> disjoint_from W (sa_guard SA) 8 -> ssp_ok m'.
Proof.
  intros W m m' (G1 & g & G2) MU D1 D2. split; [|exists g].
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8. exact D1.
  - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8. exact D2.
Qed.

(** The n bytes at x lie inside one reserved segment of the image (decided on the image by vm_compute). *)
Definition in_resv (x k : Z) : bool :=
  existsb (fun s => (bv_unsigned (fst s) <=? x) && (x + k <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs).
(** The label with its 8 bytes of read span (.rodata), the GOT cell and the guard (.got and .bss). *)
Lemma label_resv : in_resv STR_BASE 20 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma got_resv : in_resv (sa_got_guard SA) 8 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma guard_resv : in_resv (sa_guard SA) 8 = true.
Proof. vm_compute. reflexivity. Qed.

(** So the reader block (blk_noimg) is apart from each of them. *)
Lemma c_apart_resv : forall c x k, blk_noimg rsegs c SEG_C_SIZE -> 0 < k -> in_resv x k = true ->
  x + k <= c \/ c + SEG_C_SIZE <= x.
Proof. intros c x k NI Hk E. exact (noimg_apart rsegs c SEG_C_SIZE x k NI ltac:(unfold SEG_C_SIZE; lia) Hk E). Qed.

Lemma cat_img_munch : forall W m m', cat_img rsegs m (sa_catalogue SA) -> munch W m m' ->
  disjoint_from W 0 (sa_img_end SA) -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros W m m' CAT MU D a Ha. rewrite <- (CAT a Ha). unfold mrd.
  sa_num. unfold CAT_BYTES in Ha.
  assert (Q : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  rewrite Q. reflexivity.
Qed.

(** The label "reac-pw.conf" at STR_BASE: its 12 bytes and NUL end at 0x10470, 8-aligned (no slack). *)
Lemma label_ro : ro_bytes_b rsegs STR_BASE (zb S_base ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma label_at : forall m, mem_inv rsegs m -> cstr_at rsegs m STR_BASE S_base.
Proof.
  intros m MI. exists (zb S_base), [].
  assert (LB : length (zb S_base ++ [ZERO]) = 13%nat) by (vm_compute; reflexivity).
  split; [|split; [vm_compute; reflexivity | split]].
  - apply (ro_bytes_at rsegs m); [exact MI | unfold STR_BASE; lia | rewrite LB; unfold STR_BASE; lia |].
    apply ro_bytes_b_sound. exact label_ro.
  - intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H.
  - apply Z.leb_le. vm_compute. reflexivity.
Qed.

Lemma label_len : (length S_base <= 65535)%nat.
Proof. apply Nat.leb_le. vm_compute. reflexivity. Qed.

Lemma mod16_sub32 : forall sp, sp mod 16 = 0 -> (sp - 32) mod 16 = 0.
Proof.
  intros sp H. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z_mod_plus_full. exact H.
Qed.

(** parse_file's premise at the call 0x15e9c: the callee's sp is sp - 32, the frame [sp - 32, sp) written. *)
Lemma pf_pre : forall m m1 fc sp lo c t rc s,
  reader_pre PARSE_STACK m fc sp lo c t rc s ->
  munch [(sp - 32, sp)] m m1 -> stk rsegs m1 lo (sp - 32) -> mem_inv rsegs m1 ->
  reac_segconf_parse_file_pre m1 fc (sp - 32) lo c t STR_BASE rc s (Some S_base).
Proof.
  intros m m1 fc sp lo c t rc s PRE MU ST MI1.
  destruct PRE as (C0 & C16 & RC & APc & IEc & G1 & R1 & O1 & T0 & CS & LS & APt & APtc & PE & CAT & STK & MI).
  destruct STK as (ST0 & DEP & SP16 & NR). destruct PE as (FRM & TM & SSP & IL & SPH).
  pose proof (stk_task rsegs m lo sp TM ST0) as TSK.
  assert (LO0 : 0 <= lo) by (destruct ST0 as [? _]; assumption).
  assert (D0 : disjoint_from [(sp - 32, sp)] 0 (sa_img_end SA)) by (stack_num; sa_num; dj).
  assert (D0a : disjoint_from [(sp - 32, sp)] (sa_got_guard SA) 8)
    by (eapply disjoint_from_sub; [exact D0 | sa_num; lia | sa_num; lia]).
  assert (D0b : disjoint_from [(sp - 32, sp)] (sa_guard SA) 8)
    by (eapply disjoint_from_sub; [exact D0 | sa_num; lia | sa_num; lia]).
  pose proof (c_apart_resv c STR_BASE 20 IEc ltac:(lia) label_resv) as LA.
  unfold reac_segconf_parse_file_pre, reader_pre.
  split; [|split].
  - split; [exact C0|]. split; [exact C16|].
    split; [eapply rconf_at_munch; [exact RC | exact MU |]; unfold apart in APc; stack_num; c_num; dj|].
    split; [unfold apart in *; stack_num; c_num; lia|]. split; [exact IEc|].
    split; [exact G1|]. split; [exact R1|]. split; [exact O1|]. split; [exact T0|].
    split; [eapply cstr_at_munch; [exact CS | exact MU |]; unfold apart in APt; stack_num; dj|].
    split; [exact LS|]. split; [unfold apart in *; stack_num; lia|]. split; [exact APtc|].
    split.
    { split; [exact FRM|]. split.
      - eapply task_mem_frame; [exact TM | exact MU |]. intros x Hx. apply TSK. stack_num. lia.
      - split; [eapply ssp_ok_munch; [exact SSP | exact MU | exact D0a | exact D0b]|]. split; [exact IL | lia]. }
    split; [eapply cat_img_munch; [exact CAT | exact MU | exact D0]|].
    split; [|exact MI1].
    split; [exact ST|]. split; [stack_num; lia|]. split; [apply mod16_sub32; exact SP16|].
    intros a Ha. apply NR. lia.
  - split; [unfold STR_BASE; lia | apply label_at; exact MI1].
  - split; [exact label_len|]. assert (L : length S_base = 12%nat) by (vm_compute; reflexivity).
    rewrite L. unfold apart. sa_num. stack_num. c_num. unfold STR_BASE in *. split; [left; lia | lia].
Qed.

(** cross_check's premise at the call 0x15ea8, after parse_file's post. *)
Lemma cc_pre : forall m m1 m2 fc fc2 sp lo c t rc s,
  reader_pre PARSE_STACK m fc sp lo c t rc s ->
  munch [(sp - 32, sp)] m m1 -> munch ((sp - 32 - PARSE_FILE_STACK, sp - 32) :: RC_PARSE_W c) m1 m2 ->
  frm0 fc2 -> MemNorm.task_mem rsegs m2 -> stk rsegs m2 lo (sp - 32) -> mem_inv rsegs m2 ->
  rconf_at rsegs m2 c (fst (r_parse_file rc s (Some S_base))) ->
  cross_check_pre m2 fc2 (sp - 32) lo c (fst (r_parse_file rc s (Some S_base))).
Proof.
  intros m m1 m2 fc fc2 sp lo c t rc s PRE MU0 MU1 FRM2 TM2 ST2 MI2 RC2.
  destruct PRE as (C0 & C16 & RC & APc & IEc & G1 & R1 & O1 & T0 & CS & LS & APt & APtc & PE & CAT & STK & MI).
  destruct STK as (ST0 & DEP & SP16 & NR). destruct PE as (FRM & TM & SSP & IL & SPH).
  destruct CS as (bs & sl & _ & _ & NUL & _).
  assert (LO0 : 0 <= lo) by (destruct ST0 as [? _]; assumption).
  pose proof (c_apart_resv c _ 8 IEc ltac:(lia) got_resv) as GA.
  pose proof (c_apart_resv c _ 8 IEc ltac:(lia) guard_resv) as GB.
  assert (D0a : disjoint_from [(sp - 32, sp)] (sa_got_guard SA) 8) by (stack_num; sa_num; dj).
  assert (D0b : disjoint_from [(sp - 32, sp)] (sa_guard SA) 8) by (stack_num; sa_num; dj).
  assert (D1a : disjoint_from ((sp - 32 - PARSE_FILE_STACK, sp - 32) :: RC_PARSE_W c) (sa_got_guard SA) 8)
    by (stack_num; sa_num; c_num; dj).
  assert (D1b : disjoint_from ((sp - 32 - PARSE_FILE_STACK, sp - 32) :: RC_PARSE_W c) (sa_guard SA) 8)
    by (stack_num; sa_num; c_num; dj).
  unfold cross_check_pre.
  split; [exact C0|]. split; [exact C16|]. split; [exact RC2|].
  split; [unfold apart in *; stack_num; c_num; lia|]. split; [exact IEc|].
  split; [apply r_parse_file_refused_bound; [exact NUL | exact LS | exact R1]|].
  split.
  { split; [exact FRM2|]. split; [exact TM2|].
    split; [eapply ssp_ok_munch; [eapply ssp_ok_munch; [exact SSP | exact MU0 | exact D0a | exact D0b]
                                 | exact MU1 | exact D1a | exact D1b]|].
    split; [exact IL | lia]. }
  split; [|exact MI2].
  split; [exact ST2|]. split; [stack_num; lia|]. split; [apply mod16_sub32; exact SP16|].
  intros a Ha. apply NR. lia.
Qed.

Ltac sub_tac := unfold sub_fp; stack_num; c_num; intros ? Hx; cbn [outside] in *;
  repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [exact I | lia].

Ltac fix_ret_pc :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Theorem reac_segconf_parse_holds :
  reac_segconf_parse_file_contract -> cross_check_contract -> reac_segconf_parse_contract.
Proof.
  intros PF CC. unfold reac_segconf_parse_contract, REAC_SEGCONF_PARSE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo rc s PRE.
  rewrite r_parse_snd, r_parse_fst.
  pose proof PRE as PRE0.
  destruct PRE as (C0 & C16 & RC & APc & IEc & G1 & R1 & O1 & T0 & CS & LS & APt & APtc & PE & CAT & STK & MI).
  destruct STK as (ST & DEP & SP16 & NR).
  clear RC CS PE CAT APt APtc G1 R1 O1 IEc T0 LS.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold PARSE_STACK, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K in DEP.
  unfold apart, SEG_C_SIZE in APc.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MUF.
  pose proof (wmono_refl rsegs m) as WM.
  (* prologue: the frame, ra/s0/s1 saved, s0 = c, a2 = the label, a0 = c *)
  zstep. carve_frame 32%nat ST.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep.
  (* n = reac_segconf_parse_file(c, text, "reac-pw.conf") *)
  zstep.
  eapply evt_cut.
  { eapply (PF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo rc s (Some S_base)).
    rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    eapply pf_pre; [exact PRE0 | exact MUF | exact ST | exact MI]. }
  intros ms' PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1'
    & E1 & FRM1 & FF1 & MU1 & WM1 & MI1 & TM1 & ST1 & RC1).
  subst ms'. rewrite ?unsigned_lit in MU1 by lia. rewrite ?unsigned_lit in ST1 by lia. fix_ret_pc.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU1 WM1) as FR1.
  specialize (FR1 ltac:(stack_num; c_num; simpl_sizes; dj)).
  clear FR ST. rename FR1 into FR. rename ST1 into ST.
  (* s1 = n, a0 = c; cross_check(c) *)
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply (CC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo
              (fst (r_parse_file rc s (Some S_base)))).
    rewrite ?unsigned_lit by lia.
    replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia.
    eapply cc_pre; [exact PRE0 | exact MUF | exact MU1 | exact FRM1 | exact TM1 | exact ST | exact MI1 | exact RC1]. }
  intros ms' PO.
  destruct PO as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5''
    & t6'' & F2 & fc2 & m2' & E2 & FRM2 & FF2 & MU2 & WM2 & MI2 & TM2 & ST2 & RC2).
  subst ms'. rewrite ?unsigned_lit in MU2 by lia. rewrite ?unsigned_lit in ST2 by lia. fix_ret_pc.
  pose proof (rw_cells_transport rsegs _ _ _ _ _ FR MU2 WM2) as FR2.
  specialize (FR2 ltac:(stack_num; c_num; simpl_sizes; dj)).
  clear FR ST. rename FR2 into FR.
  (* epilogue: a0 = n, ra/s0/s1 restored, the frame released *)
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR ST2 (bv_unsigned sp).
  zstep.
  apply evt_done. unfold ret_post_fp. do 17 eexists.
  split; [reflexivity|].
  split; [exact FRM2|].
  split; [intros k Hk; rewrite (FF2 k Hk); exact (FF1 k Hk)|].
  split; [eapply munch3; [exact MUF | exact MU1 | exact MU2 | sub_tac | sub_tac | sub_tac]|].
  split; [eapply wmono_trans; [exact WM | eapply wmono_trans; [exact WM1 | exact WM2]]|].
  split; [exact MI2|]. split; [exact TM2|]. split; [exact ST2|]. exact RC2.
Qed.
