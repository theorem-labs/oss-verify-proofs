(** m_file (UBSan build, image 1696d6c34ffd, 0x14268): the sub-piece S_MFU_HDRA of S_MF_LINE (U/Prog/mfu_cuts.v).
    From the cut HDR 0x14434 (the stripped line sl = h_strip (h_cut_comment (mf_line rest)) = slice i j (mf_line
    rest), its first byte '[') through m_header's checks to the cut HFIND 0x144ec, or to the tail 0x146b4 through
    the refusal 0x14668-0x14688.

    The walk:
      0x14434 a1 = ']' ; a0 = s5 = s ; 0x1443c jal memchr(s, ']', e - s)
      0x14440 beqz a0 -> 0x14668 (no ']': refuse)       0x14448 beq a0,-1 -> trap (dead: close < 2^64 - 1)
      0x14450 bne close+1,s4 -> 0x14668 (text after ']') 0x14458 beq s5,-1 -> trap (dead: s < 2^64 - 1)
      0x1445c s5 = s + 1 ; 0x14460 sd 0x48(sp) = b ; 0x14464 sd 0xa0(sp) = be ; 0x14470 jal strip(&b, &be)
      0x14484 blt be'-b',8 -> 0x14668                    0x14494 jal ieq(b', 7, "segment" 0x10313)
      0x14498 beqz a0 -> 0x14668                         0x144a8 bltu b'+7,8 -> trap (dead: b' >= 1)
      0x144ac lbu b'[7] ; not '\t' and not ' ' -> 0x14668
      0x144c0 sd 0x98(sp) = nm ; 0x144c4 sd 0x90(sp) = ne ; 0x144d0 jal strip(&nm, &ne)
      0x144dc beq ne',nm' -> 0x14668 (empty name)        0x144e8 bgeu s5,16 -> 0x14668 (name too long)
      0x144ec HFIND with a1 = nm', the cell 0x98 = nm', s5 = n.
      0x14668 jal m_refuse(c, line + 1) ; 0x14674 sd 0x30(sp) = 0 (cur = NULL) ; 0x14688 s4 = 1 ; tail 0x146b4.

    The model: SegModel.m_header on sl, split by Prog/mfp_facts.v (m_header_find after the checks = mfu_facts.mh_find,
    m_header_refuse for every failed check, with cur = NULL). The two strips are the kit's mfu_strip, ieq is
    mfu_ieq with mfu_lits, the refusal is mfu_refuse and the tail mfu_tail (U/Prog/mfu_kit.v).

    Of this file's own lemmas, [hdra_loop_keep] (the head's loop facts at a memory the line has changed only inside
    the frame's scratch cells and below sp) is what every sub-piece walk with an exit cut needs; it is stated here
    with a free footprint W so it can be lifted into the kit (U/Prog/mfu_kit.v) unchanged. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame FP Tac ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge
  mfu_facts mfp_facts mfp_mconf.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env m_file_c mfu_cuts mfu_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import memchr_c strip_c ieq_c m_refuse_c.
Import ListNotations.
Open Scope Z_scope.

(** * Lists and the model *)

(** [slice] at the two ends. *)
Lemma hdra_slice_full : forall (l : list Z) k, (k <= length l)%nat -> slice k (length l) l = skipn k l.
Proof.
  intros l k Hk. unfold slice. apply firstn_all2. rewrite length_skipn. lia.
Qed.

Lemma hdra_slice_pre : forall (l : list Z) k, slice 0 k l = firstn k l.
Proof. intros l k. unfold slice. rewrite Nat.sub_0_r. reflexivity. Qed.

(** strip as a window of its argument. *)
Lemma hdra_strip_win : forall (u : list Z), h_strip u = slice (strip_lead u) (length u - strip_trail u) u.
Proof.
  intros u. pose proof (strip_le u) as HLE. rewrite <- (strip_mid u). unfold slice. f_equal. lia.
Qed.

(** strip of a window of L is a window of L. *)
Lemma hdra_strip_slice : forall (L : list Z) i j, (i <= j <= length L)%nat ->
  h_strip (slice i j L) = slice (i + strip_lead (slice i j L)) (j - strip_trail (slice i j L)) L.
Proof.
  intros L i j H. pose proof (strip_le (slice i j L)) as HLE. pose proof (slice_length L i j H) as HL.
  rewrite hdra_strip_win at 1. rewrite slice_slice by lia. f_equal. lia.
Qed.

(** memchr over a byte list is SegModel.memchr over its values. *)
Lemma hdra_find_memchr : forall (bs : list byte) (cz : Z), find_byte cz bs = memchr (zs bs) cz.
Proof.
  unfold zs. induction bs as [|b bs IH]; intros cz; [reflexivity|].
  cbn [map find_byte memchr]. destruct (Z.eqb_spec (bv_unsigned b) cz) as [E|E].
  - reflexivity.
  - rewrite IH. destruct (memchr (map bv_unsigned bs) cz); reflexivity.
Qed.

Lemma hdra_memchr_ok_full : forall A cz n (buf : list byte), n = Z.of_nat (length buf) -> memchr_ok A cz n buf.
Proof. intros A cz n buf ->. unfold memchr_ok. destruct (find_byte _ _); [left|]; lia. Qed.

Lemma hdra_memchr_res_full : forall A cz n (buf : list byte), n = Z.of_nat (length buf) ->
  memchr_res A cz n buf = match memchr (zs buf) cz with Some i => A + Z.of_nat i | None => 0 end.
Proof.
  intros A cz n buf ->. unfold memchr_res. rewrite Nat2Z.id, firstn_all, hdra_find_memchr. reflexivity.
Qed.

(** The bytes of a window of the text, as the model sees them. *)
Lemma hdra_zs_firstn : forall (bs : list byte) k, zs (firstn k bs) = firstn k (zs bs).
Proof. intros bs k. unfold zs. rewrite firstn_map. reflexivity. Qed.
Lemma hdra_zs_skipn : forall (bs : list byte) k, zs (skipn k bs) = skipn k (zs bs).
Proof. intros bs k. unfold zs. rewrite skipn_map. reflexivity. Qed.

(** * Memory kept outside a footprint *)

Lemma hdra_bytes_out : forall (W : list ivl) (m0 m : word -> option byte) (a : Z) (bs : list byte),
  bytes_at rsegs m0 a bs -> munch W m0 m ->
  (forall x, a <= x < a + Z.of_nat (length bs) -> outside W x) ->
  bytes_at rsegs m a bs.
Proof.
  intros W m0 m a bs (Ha & Hl & H) MU HO. split; [lia|]. split; [lia|].
  intros i Hi. unfold mrd. rewrite (MU (wa (a + Z.of_nat i))).
  - exact (H i Hi).
  - rewrite wa_unsigned by lia. apply HO. lia.
Qed.

Lemma hdra_mrd_out : forall (W : list ivl) (m0 m : word -> option byte) (a : Z),
  munch W m0 m -> 0 <= a < 2 ^ 64 -> outside W a -> mrd rsegs m (wa a) = mrd rsegs m0 (wa a).
Proof.
  intros W m0 m a MU Ha HO. unfold mrd. rewrite (MU (wa a)); [reflexivity|]. rewrite wa_unsigned by lia. exact HO.
Qed.

Lemma hdra_cstr_out : forall (W : list ivl) (m0 m : word -> option byte) (a : Z) (s : list Z),
  cstr_at rsegs m0 a s -> munch W m0 m ->
  (forall x, a <= x < a + Z.of_nat (length s) + 8 -> outside W x) ->
  cstr_at rsegs m a s.
Proof.
  intros W m0 m a s HC MU HO.
  destruct (cstr_cut rsegs m0 a s HC) as (bs & sl & HB & Hz & Hn & Hnb & Hlen & Hk & Hlt).
  exists bs, sl. split; [|split; [exact Hz | split; [exact Hn|]]].
  - eapply hdra_bytes_out; [exact HB | exact MU |].
    rewrite length_app. cbn [length]. intros x Hx. apply HO. lia.
  - rewrite Hlen in Hk. exact Hk.
Qed.

Lemma hdra_saved_len : forall ws : list word, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, length_le8, IH. cbn [length]. lia.
Qed.

(** The task-memory invariant: the writes are inside the stack region, whose bytes are already the task's. *)
Lemma hdra_task_keep : forall (W : list ivl) (m0 m : word -> option byte) (lo sp0 : Z),
  MemNorm.task_mem rsegs m0 -> stk rsegs m0 lo sp0 ->
  (forall x, lo <= x < sp0 -> seg_rom rsegs (wa x) = None) ->
  munch W m0 m -> (forall x, x < lo \/ sp0 <= x -> outside W x) ->
  MemNorm.task_mem rsegs m.
Proof.
  intros W m0 m lo sp0 TM ST HROM MU HO a b Ha.
  assert (Ea : wa (bv_unsigned a) = a) by apply Z_to_bv_lit_self.
  destruct (Z.lt_ge_cases (bv_unsigned a) lo) as [H1|H1].
  - rewrite (MU a (HO _ (or_introl H1))) in Ha. exact (TM a b Ha).
  - destruct (Z.le_gt_cases sp0 (bv_unsigned a)) as [H2|H2].
    + rewrite (MU a (HO _ (or_intror H2))) in Ha. exact (TM a b Ha).
    + destruct ST as (_ & _ & HSTK). destruct (HSTK (bv_unsigned a) ltac:(lia)) as (_ & (b0 & Hb0)).
      pose proof (HROM (bv_unsigned a) ltac:(lia)) as HR. rewrite Ea in Hb0, HR.
      unfold mrd in Hb0. rewrite HR in Hb0. destruct (m0 a) as [b1|] eqn:E; [|discriminate].
      exact (TM a b1 E).
Qed.

(** The stack region is writable. *)
Lemma hdra_stk_wr : forall (m : word -> option byte) (l h : Z), stk rsegs m l h -> wr_at rsegs m l (h - l).
Proof.
  intros m l h (H1 & H2 & H). split; [lia|]. split; [lia|].
  intros i Hi. exact (proj1 (H (l + i) ltac:(lia))).
Qed.

Lemma hdra_stk_store_ok : forall (m : word -> option byte) (l h a : Z) (j : nat),
  stk rsegs m l h -> l <= a -> a + Z.of_nat j <= h -> store_ok rsegs m (wa a) j = true.
Proof.
  intros m l h a j ST Hl Hh.
  pose proof (hdra_stk_wr m l h ST) as HW.
  pose proof (wr_at_store_ok rsegs m l (h - l) (a - l) j HW ltac:(lia) ltac:(lia)) as HS.
  replace (l + (a - l)) with a in HS by lia. exact HS.
Qed.

(** The head's loop facts at a memory the line has changed only inside [lo, sp0), away from the frame's fixed
    cells (sp + 8 .. sp + 0x38) and saved registers (sp + 0xa8 .. sp + 0x110). *)
Lemma hdra_loop_keep : forall (W : list ivl) (m0 m : word -> option byte) (fc fc' : bv 32)
    (sp0 sp lo c p : Z) (mc : mconf) (cur : option nat) (line : Z) (k0 : nat) (rest : list Z)
    (ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word),
  m_file_loop m0 fc sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 ->
  mfu_mid m0 m sp0 lo c k0 mc false ->
  munch W m0 m ->
  (forall x, x < lo \/ sp0 <= x -> outside W x) ->
  (forall x, sp + 8 <= x < sp + 0x38 -> outside W x) ->
  (forall x, sp + M_FILE_SAVE <= x < sp + M_FILE_SAVE + 104 -> outside W x) ->
  frm0 fc' ->
  m_file_loop m fc' sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros W m0 m fc fc' sp0 sp lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
    HL MID MU HO HFR HSV HFRM.
  destruct HL as (Hsp & HS & Cc8 & Cc10 & Cc18 & Cc20 & Cc28 & Cc30 & Hc0 & Hc16 & HBN & HMA & HWR & HBS & HAP &
                  HCUR & HK0 & HLN0 & HLN1 & HRF & HOV & Hp0 & HPBN & HPC & HPA & HPA2 & HPE & HCAT & HWD & HSO & HMI).
  destruct MID as (MUW & WM & MI' & ST' & MATP).
  destruct HPE as (HF0 & HTM & HSSP & HIMG & HSP63).
  pose proof HSO as HSO0. destruct HSO as (STK & HDEEP & HAL & HROM).
  pose proof STK as STK0. destruct STK0 as (Hlo0 & Hsp0 & _).
  assert (EI : sa_img_end SA = 0x54088) by reflexivity.
  assert (HLOSP : lo + M_FILE_STACK <= sp0) by exact HDEEP.
  (* each 8-byte frame cell and the saved block are outside W *)
  assert (CELL : forall v a, cell8 m0 a v -> sp + 8 <= a -> a + 8 <= sp + 0x38 -> cell8 m a v).
  { intros v a HC Ha1 Ha2. unfold cell8 in *.
    eapply hdra_bytes_out; [exact HC | exact MU |]. rewrite length_le8. intros x Hx. apply HFR. lia. }
  split; [exact Hsp|].
  split.
  { unfold saved_at in *. eapply hdra_bytes_out; [exact HS | exact MU |].
    rewrite hdra_saved_len. cbn [length]. intros x Hx. apply HSV. unfold M_FILE_SAVE in *. lia. }
  split; [apply (CELL _ _ Cc8); lia|].
  split; [apply (CELL _ _ Cc10); lia|].
  split; [apply (CELL _ _ Cc18); lia|].
  split; [apply (CELL _ _ Cc20); lia|].
  split; [apply (CELL _ _ Cc28); lia|].
  split; [apply (CELL _ _ Cc30); lia|].
  split; [exact Hc0|]. split; [exact Hc16|]. split; [exact HBN|].
  split; [exact MATP|].
  split; [eapply wr_at_transport; [exact HWR | exact WM]|].
  split.
  { destruct HBS as (sl & HBsl & Hmod).
    assert (E4 : (- (c + SEG_M_SIZE)) mod 8 = 4).
    { unfold SEG_M_SIZE. Z.div_mod_to_equations. lia. }
    rewrite E4 in Hmod.
    assert (HL4 : (4 <= length sl)%nat) by lia.
    exists (firstn 4 sl). split.
    - eapply hdra_bytes_out; [| exact MU |].
      + rewrite <- (firstn_skipn 4 sl) in HBsl. apply bytes_at_app in HBsl. exact (proj1 HBsl).
      + rewrite length_firstn. intros x Hx. apply HO.
        unfold apart in HAP. unfold SEG_M_SIZE in *. lia.
    - rewrite length_firstn, E4. lia. }
  split; [exact HAP|]. split; [exact HCUR|]. split; [exact HK0|].
  split; [exact HLN0|]. split; [exact HLN1|]. split; [exact HRF|]. split; [exact HOV|].
  split; [exact Hp0|]. split; [exact HPBN|].
  split.
  { eapply hdra_cstr_out; [exact HPC | exact MU |]. intros x Hx. apply HO. unfold apart in HPA. lia. }
  split; [exact HPA|]. split; [exact HPA2|].
  split.
  { split; [exact HFRM|]. split.
    { eapply hdra_task_keep; [exact HTM | exact STK | exact HROM | exact MU | exact HO]. }
    split; [|split; [exact HIMG | exact HSP63]].
    destruct HSSP as (HG1 & (g & HG2)). split.
    - eapply hdra_bytes_out; [exact HG1 | exact MU |]. rewrite length_le8.
      intros x Hx. apply HO. left. revert Hx. unfold SA, SEG_UBSAN, sa_got_guard in *. cbn. lia.
    - exists g. eapply hdra_bytes_out; [exact HG2 | exact MU |]. rewrite length_le8.
      intros x Hx. apply HO. left. revert Hx. unfold SA, SEG_UBSAN, sa_guard in *. cbn. lia. }
  split.
  { intros a Ha. rewrite (hdra_mrd_out W m0 m a MU).
    - exact (HCAT a Ha).
    - revert Ha. unfold SA, SEG_UBSAN, sa_catalogue, CAT_BYTES. cbn. lia.
    - apply HO. left. revert Ha. unfold SA, SEG_UBSAN, sa_catalogue, CAT_BYTES in *. cbn. lia. }
  split.
  { intros a Ha. rewrite (hdra_mrd_out W m0 m a MU).
    - exact (HWD a Ha).
    - revert Ha. unfold M_KEY_WORDS. lia.
    - apply HO. left. revert Ha. unfold M_KEY_WORDS in *. lia. }
  split; [split; [exact ST' | split; [exact HDEEP | split; [exact HAL | exact HROM]]]|].
  exact MI'.
Qed.

Lemma hdra_bat_sub : forall (m : word -> option byte) (a : Z) (l : list byte) (k n : nat),
  bytes_at rsegs m a l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk.
  assert (Lk : length (firstn k l) = k) by (rewrite length_firstn; lia).
  rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H]. rewrite Lk in H.
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

Lemma hdra_fs_app : forall {A} (l r : list A) (k n : nat), (k + n <= length l)%nat ->
  firstn n (skipn k (l ++ r)) = firstn n (skipn k l).
Proof.
  intros A l r k n H. rewrite skipn_app. replace (k - length l)%nat with 0%nat by lia. cbn [skipn].
  rewrite firstn_app, length_skipn. replace (n - (length l - k))%nat with 0%nat by lia. cbn [firstn].
  apply app_nil_r.
Qed.

(** * The walk *)
Section Walk.
Variables (gp tp s0 s1 s2 s3 s6 s7 s8 s9 s10 s11 sp sp0 ra0 : word).
Variables (e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : word).
Variables (F : bvmap 5 word) (fc : bv 32) (mcut : word -> option byte).
Variables (lo c p line : Z) (mc : mconf) (cur : option nat) (k0 : nat) (rest : list Z) (i j nb : nat).

Hypothesis HMEMCHR : memchr_contract.
Hypothesis HSTRIP : strip_contract.
Hypothesis HIEQ : ieq_contract.
Hypothesis HREF : m_refuse_contract.
Hypothesis HTAIL : H_MF_TAIL nb.
Hypothesis HFIND : H_MFU_HFIND nb.
Hypothesis Hnb : (length rest <= nb)%nat.
Hypothesis Hne : rest <> [].
Hypothesis HL : m_file_loop mcut fc (bv_unsigned sp0) (bv_unsigned sp) lo c p mc cur line k0 rest
                  ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Hypothesis HR : mfu_lregs c (mf_next p rest) (line + 1) s0 s2 s3 s7 s8 s9 s10 s11.
Hypothesis Hs6 : s6 = Z_to_bv 64 0x1ff.
Hypothesis Hij : (i < j)%nat.
Hypothesis Hjl : (j <= length (mf_line rest))%nat.
Hypothesis Hsl : slice i j (mf_line rest) = h_strip (h_cut_comment (mf_line rest)).

Local Notation SP := (bv_unsigned sp).
Local Notation SP0 := (bv_unsigned sp0).
Local Notation LL := (mf_line rest).

Definition hdW : list ivl := [(bv_unsigned sp - 32, bv_unsigned sp);
                              (bv_unsigned sp + 0x48, bv_unsigned sp + 0xa8)].

(** The parts of the loop invariant this walk uses. *)
Lemma hdra_facts :
  cstr_at rsegs mcut p rest /\
  apart p (Z.of_nat (length rest) + 8) lo SP0 /\
  apart c (SEG_M_SIZE + 4) lo SP0 /\
  stack_ok rsegs mcut lo SP0 M_FILE_STACK /\
  printf_env mcut fc lo SP0 /\
  mconf_at rsegs mcut c mc /\
  SP + M_FILE_FRAME = SP0 /\
  0 <= line /\ line + Z.of_nat (length rest) <= 65535 /\
  saved_at rsegs mcut (SP + M_FILE_SAVE) [e11; e10; e9; e8; e7; e6; e5; e4; e3; e2; e1; e0; ra0] /\
  cell8 mcut (SP + 0x8) (- 1 - c) /\ cell8 mcut (SP + 0x10) (c + MC_KNOCK) /\
  cell8 mcut (SP + 0x18) (- 1 - (c + MC_KNOCK)) /\ cell8 mcut (SP + 0x20) (c + MC_READING) /\
  cell8 mcut (SP + 0x28) (c + MC_N) /\ cell8 mcut (SP + 0x30) (cur_ptr c cur) /\ mem_inv rsegs mcut.
Proof.
  destruct HL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 &
                  E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28 & E29 & E30 & E31).
  split; [exact E24|]. split; [exact E25|]. split; [exact E15|]. split; [exact E30|].
  split; [exact E27|]. split; [exact E12|]. split; [exact E1|]. split; [exact E18|].
  split; [exact E19|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
  split; [exact E5|]. split; [exact E6|]. split; [exact E7|]. split; [exact E8|]. exact E31.
Qed.

Lemma hdra_nums :
  0 <= lo /\ lo + 6224 <= SP0 /\ SP + 272 = SP0 /\ SP0 <= 2 ^ 64 /\ SP0 < 2 ^ 63 /\
  344200 <= lo /\ 0 < p /\ p + Z.of_nat (length rest) + 1 <= 2 ^ 64 /\
  (length LL <= length rest)%nat /\ 0 <= c /\ c + 9236 <= 2 ^ 64 /\ c mod 16 = 0.
Proof.
  destruct hdra_facts as (HPC & HPA & HAP & HSO & HPE & HMA & HSP & HLN0 & HLN1 & _).
  destruct HSO as (STK & HDEEP & HAL & HROM). destruct STK as (Hlo & Hhi & _).
  destruct HPE as (_ & _ & _ & HIMG & HSP63).
  assert (EI : sa_img_end SA = 344200) by reflexivity. rewrite EI in HIMG.
  destruct (cstr_cut rsegs mcut p rest HPC) as (bs & slk & HB & Hz & _ & _ & Hlen & _ & Hlt).
  pose proof (bytes_at_bound rsegs mcut p _ HB) as HBB. rewrite length_app in HBB. cbn [length] in HBB.
  destruct HMA as (bm & HBM & HEM). pose proof (mconf_enc_bounds false mc bm HEM) as (Lbm & _).
  assert (LbZ : Z.of_nat (length bm) = 9236) by (rewrite Lbm; reflexivity).
  pose proof (bytes_at_bound rsegs mcut c bm HBM) as HCB. rewrite LbZ in HCB.
  assert (Hp0 : p <> 0) by
    (destruct HL as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&X&_); exact X).
  assert (Hc16 : c mod 16 = 0) by (destruct HL as (_&_&_&_&_&_&_&_&_&X&_); exact X).
  assert (HLle : (length LL <= length rest)%nat).
  { destruct (mf_line_rest rest) as [[E _]|[E _]].
    - assert (HE : length rest = length (mf_line rest ++ NL :: mf_rest rest)) by (f_equal; exact E).
      rewrite length_app in HE. cbn [length] in HE. lia.
    - assert (HE : length rest = length (mf_line rest)) by (f_equal; exact E). lia. }
  destruct HBB as (HBB0 & HBB1). destruct HCB as (HCB0 & HCB1).
  unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HDEEP. unfold M_FILE_FRAME in HSP.
  repeat split; try assumption; try lia.
Qed.

Lemma hdra_out_stack : forall x, x < lo \/ SP0 <= x -> outside hdW x.
Proof.
  intros x Hx. pose proof hdra_nums as (A1 & A2 & A3 & _).
  unfold hdW. cbn [outside]. repeat split; lia.
Qed.

Lemma hdra_out_fix : forall x, SP + 8 <= x < SP + 0x38 -> outside hdW x.
Proof. intros x Hx. unfold hdW. cbn [outside]. repeat split; lia. Qed.

Lemma hdra_out_saved : forall x, SP + M_FILE_SAVE <= x < SP + M_FILE_SAVE + 104 -> outside hdW x.
Proof.
  intros x Hx. pose proof hdra_nums as (_ & _ & A3 & _).
  unfold hdW, M_FILE_SAVE in *. cbn [outside]. repeat split; lia.
Qed.

(** The memory inside the line, before any write to the block. *)
Definition hst (m : word -> option byte) : Prop :=
  mfu_mid mcut m SP0 lo c k0 mc false /\ munch hdW mcut m.

Lemma hst_init : hst mcut.
Proof. split; [eapply mfu_mid_init, HL | apply munch_refl]. Qed.

Lemma hst_sub : forall (W : list ivl) (m m' : word -> option byte),
  hst m -> mfu_mid mcut m' SP0 lo c k0 mc false -> munch W m m' -> sub_fp W hdW -> hst m'.
Proof.
  intros W m m' (MID & MU) MID' MUW HS. split; [exact MID'|].
  eapply munch_trans; [exact MU | eapply munch_weaken; [exact HS | exact MUW]].
Qed.

Lemma hst_loop : forall m fc', hst m -> frm0 fc' ->
  m_file_loop m fc' SP0 SP lo c p mc cur line k0 rest ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11.
Proof.
  intros m fc' (MID & MU) Hf.
  eapply hdra_loop_keep;
    [exact HL | exact MID | exact MU | exact hdra_out_stack | exact hdra_out_fix | exact hdra_out_saved | exact Hf].
Qed.

(** The bytes of the window [a, a + k) of the line, at p + a. *)
Lemma hst_text : forall (m : word -> option byte) (a k : nat), hst m -> (a + k <= length LL)%nat ->
  exists bs, bytes_at rsegs m (p + Z.of_nat a) bs /\ zs bs = slice a (a + k) LL /\ length bs = k.
Proof.
  intros m a k HS Hk. pose proof HS as (MID & MU).
  destruct hdra_facts as (HPC & HPA & _).
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & _).
  destruct (cstr_cut rsegs mcut p rest HPC) as (bs & slk & HB & Hz & _ & _ & Hlen & _ & Hlt).
  assert (Hak : (a + k <= length bs)%nat) by lia.
  exists (firstn k (skipn a bs)).
  assert (HBS : bytes_at rsegs mcut (p + Z.of_nat a) (firstn k (skipn a bs))).
  { rewrite <- (hdra_fs_app bs (ZERO :: slk) a k ltac:(lia)).
    eapply hdra_bat_sub; [exact HB | rewrite length_app; cbn [length]; lia]. }
  assert (Lk : length (firstn k (skipn a bs)) = k) by (rewrite length_firstn, length_skipn; lia).
  split; [| split].
  - eapply hdra_bytes_out; [exact HBS | exact MU |]. rewrite Lk. intros x Hx.
    apply hdra_out_stack. unfold apart in HPA. lia.
  - rewrite hdra_zs_firstn, hdra_zs_skipn, Hz. rewrite mf_line_firstn by lia. reflexivity.
  - exact Lk.
Qed.

Local Notation POST :=
  (mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0
     (mf_fin (m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1)) line rest)).

(** A store of 8 bytes into the frame's scratch cells keeps the line's memory state. *)
Lemma hdra_mid_store : forall (m : word -> option byte) (mcx : mconf) (a : Z) (v : word),
  mfu_mid mcut m SP0 lo c k0 mcx false -> SP + 0x30 <= a -> a + 8 <= SP + 0xa8 ->
  mfu_mid mcut (write_to_mem m (wa a) (le8 v)) SP0 lo c k0 mcx false.
Proof.
  intros m mcx a v (MUW & WM & MI & ST & MA) Ha1 Ha2.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (_ & _ & HAP & _).
  unfold apart, SEG_M_SIZE in HAP.
  split; [| split; [| split; [| split]]].
  - eapply munch_write; [exact MUW | lia | rewrite length_le8; lia |].
    unfold mfu_W, M_FILE_W, M_FILE_STACK, M_FILE_FRAME, PRINTF_K. cbn [app inside]. left.
    rewrite length_le8. lia.
  - apply wmono_write. exact WM.
  - apply mem_inv_store; [exact MI |]. rewrite length_le8.
    eapply hdra_stk_store_ok; [exact ST | lia | lia].
  - apply stk_write; [exact ST | lia | rewrite length_le8; lia].
  - destruct MA as (bm & HBM & HEM). exists bm. split; [| exact HEM].
    pose proof (mconf_enc_bounds false mcx bm HEM) as (Lbm & _).
    assert (LbZ : Z.of_nat (length bm) = 9236) by (rewrite Lbm; reflexivity).
    eapply bytes_at_write_other; [exact HBM | lia | rewrite length_le8; lia |].
    rewrite LbZ, length_le8. destruct HAP as [HAP|HAP]; [left | right]; lia.
Qed.

Lemma hdra_cell_store : forall (m : word -> option byte) (b w a : Z) (v : word),
  cell8 m b w -> 0 <= a -> a + 8 <= 2 ^ 64 -> (b + 8 <= a \/ a + 8 <= b) ->
  cell8 (write_to_mem m (wa a) (le8 v)) b w.
Proof.
  intros m b w a v H Ha1 Ha2 Hd. unfold cell8 in *.
  eapply bytes_at_write_other; [exact H | lia | rewrite length_le8; lia |].
  rewrite !length_le8. lia.
Qed.

Lemma hdra_saved_store : forall (m : word -> option byte) (b a : Z) (v : word) (ws : list word),
  saved_at rsegs m b ws -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (b + 8 * Z.of_nat (length ws) <= a \/ a + 8 <= b) ->
  saved_at rsegs (write_to_mem m (wa a) (le8 v)) b ws.
Proof.
  intros m b a v ws H Ha1 Ha2 Hd. unfold saved_at in *.
  eapply bytes_at_write_other; [exact H | lia | rewrite length_le8; lia |].
  rewrite hdra_saved_len, length_le8. lia.
Qed.

(** m_refuse's writes miss the frame's fixed cells and saved registers. *)
Lemma hdra_out_refuse : forall (mcx : mconf) (x : Z),
  SP + 8 <= x < SP + 0x38 \/ SP + M_FILE_SAVE <= x < SP + M_FILE_SAVE + 104 ->
  outside (m_refuse_W SP c mcx) x.
Proof.
  intros mcx x Hx.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (_ & _ & HAP & _).
  unfold M_FILE_SAVE, apart, SEG_M_SIZE in *.
  assert (HD : forall y z : Z, c <= y -> z <= c + 9236 -> ~ (y <= x < z))
    by (intros y z Hy Hz [D1 D2]; lia).
  unfold m_refuse_W, M_REFUSE_STACK, PRINTF_K, kept_addr, MC_KEPT, MC_KEPT_LEN, MC_NKEPT, MC_REFUSED.
  destruct (Z.ltb_spec0 (Z.of_nat (length (mc_kept mcx))) 8) as [Hk8|Hk8];
    cbn [app outside]; repeat split; first [ lia | apply HD; lia ].
Qed.

(** The join of m_header's refusals, 0x14668: m_refuse(c, line + 1), cur = NULL, then the tail. *)
Lemma hdra_refuse : forall (m : word -> option byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word),
  hst m ->
  m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1) = (m_refuse mc (line + 1) false, None) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14668) fc None m (seg_rom rsegs)).
Proof.
  intros m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 HS Hmh.
  pose proof HS as (MID & MU).
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (HPC & HPA & HAP & HSO & HPE & HMA & HSP & HLN0 & HLN1 & HSV0 &
                          Cc8 & Cc10 & Cc18 & Cc20 & Cc28 & Cc30 & MI0).
  destruct HPE as (HFRM0 & HTM & HSSP & HIMG & HSP63).
  destruct HR as (ER0 & ER2 & ER3 & ER7 & ER8 & ER9 & ER10 & ER11).
  pose proof (hst_loop m fc HS HFRM0) as HLm.
  destruct HLm as (_ & HSVm & Cm8 & Cm10 & Cm18 & Cm20 & Cm28 & Cm30 & _).
  rewrite Hmh.
  do 3 step.
  eapply (mfu_refuse HREF); [exact HL | exact Hne | exact MID | apply mf_grows_refl | reflexivity
                            | exact HFRM0 | rewrite ER0; apply unsigned_lit; lia
                            | rewrite ER3; apply unsigned_lit; lia |].
  intros m1 F1 fc1 u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 MID1 MUR WMR FRM1 HFeq.
  replace (ret_pc (Z_to_bv 64 83572)) with (Z_to_bv 64 83572)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (SOK : store_ok rsegs m1 (wa (SP + 0x30)) 8 = true).
  { destruct MID1 as (_ & _ & _ & ST1 & _). eapply hdra_stk_store_ok; [exact ST1 | lia | lia]. }
  do 4 step.
  eapply (mfu_tail nb) with (mcut := mcut) (mc' := m_refuse mc (line + 1) false) (cur' := None)
                            (Fc := F) (fcc := fc) (mc := mc) (cur := cur) (p := p) (line := line);
    [ exact HTAIL | exact Hnb | exact Hne | exact HL | | | | | | | | | | | | | | | ].
  - apply hdra_mid_store; [exact MID1 | lia | lia].
  - apply hdra_saved_store;
      [ eapply hdra_bytes_out; [exact HSVm | exact MUR |];
        rewrite hdra_saved_len; cbn [length]; intros x Hx; apply hdra_out_refuse; right; lia
      | lia | lia | cbn [length]; unfold M_FILE_SAVE; lia ].
  - apply hdra_cell_store;
      [ eapply hdra_bytes_out; [exact Cm8 | exact MUR |];
        rewrite length_le8; intros x Hx; apply hdra_out_refuse; left; lia
      | lia | lia | lia ].
  - apply hdra_cell_store;
      [ eapply hdra_bytes_out; [exact Cm10 | exact MUR |];
        rewrite length_le8; intros x Hx; apply hdra_out_refuse; left; lia
      | lia | lia | lia ].
  - apply hdra_cell_store;
      [ eapply hdra_bytes_out; [exact Cm18 | exact MUR |];
        rewrite length_le8; intros x Hx; apply hdra_out_refuse; left; lia
      | lia | lia | lia ].
  - apply hdra_cell_store;
      [ eapply hdra_bytes_out; [exact Cm20 | exact MUR |];
        rewrite length_le8; intros x Hx; apply hdra_out_refuse; left; lia
      | lia | lia | lia ].
  - apply hdra_cell_store;
      [ eapply hdra_bytes_out; [exact Cm28 | exact MUR |];
        rewrite length_le8; intros x Hx; apply hdra_out_refuse; left; lia
      | lia | lia | lia ].
  - unfold cur_ptr, cell8. apply bytes_at_write_same; [lia | rewrite length_le8; lia].
  - apply m_refuse_grows.
  - exact I.
  - unfold m_refuse. cbn [mc_refused]. lia.
  - unfold m_refuse. cbn [mc_overflow]. lia.
  - exact FRM1.
  - exact HFeq.
  - unfold m_file_regs. repeat split; try assumption; try reflexivity.
Qed.
Hypothesis Hlbr : nth i (mf_line rest) 0 = LBR.

(** ** The model's refusals *)
Lemma hdra_refuse_none : memchr (slice i j (mf_line rest)) RBR = None ->
  m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1) = (m_refuse mc (line + 1) false, None).
Proof. intros H. rewrite <- Hsl. apply m_header_refuse. intros c0 H0. rewrite H in H0. discriminate. Qed.

Lemma hdra_refuse_end : forall ci, memchr (slice i j (mf_line rest)) RBR = Some ci ->
  (S ci <> j - i)%nat ->
  m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1) = (m_refuse mc (line + 1) false, None).
Proof.
  intros ciX H Hd. rewrite <- Hsl. apply m_header_refuse. intros c0 H0 Hend.
  rewrite H in H0. injection H0 as <-. rewrite slice_length in Hend by lia. contradiction.
Qed.

Lemma hdra_refuse_body : forall (ci A B : nat),
  memchr (slice i j (mf_line rest)) RBR = Some ci ->
  h_strip (slice 1 ci (slice i j (mf_line rest))) = slice A B (mf_line rest) ->
  (A <= B)%nat -> (B <= length (mf_line rest))%nat ->
  ( (B - A < 8)%nat
    \/ ieq (firstn 7 (slice A B (mf_line rest))) S_segment = false
    \/ sp_tab (nth 7 (slice A B (mf_line rest)) 0) = false
    \/ (length (h_strip (skipn 7 (slice A B (mf_line rest)))) = 0)%nat
    \/ (16 <= length (h_strip (skipn 7 (slice A B (mf_line rest)))))%nat ) ->
  m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1) = (m_refuse mc (line + 1) false, None).
Proof.
  intros ciX A B Hci Hb HAB HBL Hcase.
  rewrite <- Hsl. apply m_header_refuse. intros c0 H0 Hend H8 Hieq Hsp.
  rewrite Hci in H0. injection H0 as <-. rewrite Hb in H8, Hieq, Hsp |- *.
  rewrite (slice_length (mf_line rest) A B ltac:(lia)) in H8.
  destruct Hcase as [HC|[HC|[HC|[HC|HC]]]].
  - exfalso. lia.
  - exfalso. rewrite HC in Hieq. discriminate.
  - exfalso. rewrite HC in Hsp. discriminate.
  - left. exact HC.
  - right. exact HC.
Qed.

Lemma hdra_find_model : forall (ci A B : nat),
  memchr (slice i j (mf_line rest)) RBR = Some ci -> (S ci = j - i)%nat ->
  h_strip (slice 1 ci (slice i j (mf_line rest))) = slice A B (mf_line rest) ->
  (A <= B)%nat -> (B <= length (mf_line rest))%nat ->
  (8 <= B - A)%nat ->
  ieq (firstn 7 (slice A B (mf_line rest))) S_segment = true ->
  sp_tab (nth 7 (slice A B (mf_line rest)) 0) = true ->
  (0 < length (h_strip (skipn 7 (slice A B (mf_line rest)))) < 16)%nat ->
  m_header mc (h_strip (h_cut_comment (mf_line rest))) (line + 1) =
  mh_find mc (h_strip (skipn 7 (slice A B (mf_line rest)))) (line + 1).
Proof.
  intros ciX A B Hci Hend Hb HAB HBL H8 Hieq Hsp Hn.
  rewrite <- Hsl. rewrite (m_header_find mc (slice i j (mf_line rest)) (line + 1) ciX);
    [ rewrite Hb; reflexivity
    | exact Hci
    | rewrite slice_length by lia; exact Hend
    | rewrite Hb, slice_length by lia; exact H8
    | rewrite Hb; exact Hieq
    | rewrite Hb; exact Hsp
    | rewrite Hb; exact Hn ].
Qed.

(** ** Small memory helpers *)
Lemma hdra_cell_ro : forall (m : word -> option byte) (a v : Z),
  cell8 m a v -> ro_cells rsegs m a [C8 (Z_to_bv 64 v)].
Proof.
  intros m a v H. split; [split; exact I|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H.
Qed.

Lemma hdra_cell_keep : forall (W : list ivl) (m m' : word -> option byte) (b v : Z),
  cell8 m b v -> munch W m m' -> (forall x, b <= x < b + 8 -> outside W x) -> cell8 m' b v.
Proof.
  intros W m m' b v H MU HO. unfold cell8 in *.
  eapply hdra_bytes_out; [exact H | exact MU |]. rewrite length_le8. exact HO.
Qed.

Lemma hdra_apart_win : forall (a k : Z), p <= a -> a + k <= p + Z.of_nat (length rest) -> apart a k lo SP0.
Proof.
  intros a k H1 H2. pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (_ & HPA & _). unfold apart in *.
  destruct HPA as [HPA|HPA]; [left | right]; lia.
Qed.

Lemma hdra_bsigned : forall X, 0 <= X < 2 ^ 63 -> bv_signed (Z_to_bv 64 X) = X.
Proof.
  intros X H. rewrite zb_signed, unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt X (2 ^ 63))) by lia. reflexivity.
Qed.

Lemma hdra_one_byte : forall (l : list Z) (k : nat) (x : Z), firstn 1 (skipn k l) = [x] -> nth k l 0 = x.
Proof.
  intros l k x H. rewrite <- hd0_skipn. destruct (skipn k l) as [|y r]; cbn in H; [discriminate|].
  injection H as <-. reflexivity.
Qed.

Lemma hst_call0 : forall (m m' : word -> option byte),
  hst m -> munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> hst m'.
Proof.
  intros m m' HS MU0 WM0 MIN. pose proof HS as (MID & MU).
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & _).
  split.
  - eapply (mfu_stack_call mcut m m' fc SP0 SP lo c p mc cur line k0 rest
              ra0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 mc false 0);
      [ exact HL | exact MID | unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K; lia
      | (eapply munch_weaken; [| exact MU0]); intros x _; exact I
      | exact WM0 | exact MIN
      | split; [lia | split; [lia | intros a Ha; lia]] ].
  - eapply munch_trans; [exact MU |]. (eapply munch_weaken; [| exact MU0]); intros x _; exact I.
Qed.

Lemma hst_store : forall (m : word -> option byte) (a : Z) (v : word),
  hst m -> SP + 0x48 <= a -> a + 8 <= SP + 0xa8 -> hst (write_to_mem m (wa a) (le8 v)).
Proof.
  intros m a v (MID & MU) Ha1 Ha2.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & _).
  split.
  - apply hdra_mid_store; [exact MID | lia | lia].
  - eapply munch_write; [exact MU | lia | rewrite length_le8; lia |].
    unfold hdW. cbn [inside]. right. left. rewrite length_le8. lia.
Qed.

Lemma hdra_post_back : forall (m : word -> option byte) (mf : mconf) (ms : machine_state),
  hst m -> mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F m lo c k0 mf ms ->
  mfu_post ra0 sp0 gp tp e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 F mcut lo c k0 mf ms.
Proof.
  intros m mf ms (MID & MU) H.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & _).
  destruct MID as (_ & WM & _ & _ & _).
  unfold mfu_post, ret_void_fp in *.
  destruct H as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & F' & fc' & m'
                 & E & HFrm & HK & MUp & WMp & MIp & TMp & STp & Qp).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, F', fc', m'.
  split; [exact E|]. split; [exact HFrm|]. split; [exact HK|].
  split; [| split; [| split; [exact MIp | split; [exact TMp | split; [exact STp | exact Qp]]]]].
  - eapply munch_trans; [| exact MUp]. eapply munch_weaken; [| exact MU].
    intros x Hx. unfold M_FILE_W in Hx. cbn [outside] in Hx. destruct Hx as (HX & _).
    unfold M_FILE_STACK, M_FILE_FRAME, PRINTF_K in HX. unfold hdW. cbn [outside]. repeat split; lia.
  - eapply wmono_trans; [exact WM | exact WMp].
Qed.

(** 0x144bc: the name [nm, ne) = [b' + 7, be'), its strip, and the cut HFIND (or the last two refusals). *)
Lemma hdra_s3 : forall (m : word -> option byte) (ci A B : nat)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word),
  hst m ->
  memchr (slice i j (mf_line rest)) RBR = Some ci -> (S ci = j - i)%nat ->
  h_strip (slice 1 ci (slice i j (mf_line rest))) = slice A B (mf_line rest) ->
  (8 <= B - A)%nat -> (B <= length (mf_line rest))%nat ->
  ieq (firstn 7 (slice A B (mf_line rest))) S_segment = true ->
  sp_tab (nth 7 (slice A B (mf_line rest)) 0) = true ->
  cell8 m (SP + 0x48) (p + Z.of_nat A) -> cell8 m (SP + 0xa0) (p + Z.of_nat B) ->
  a0 = Z_to_bv 64 (p + Z.of_nat A + 7) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x144bc) fc None m (seg_rom rsegs)).
Proof.
  intros m ci A B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6
    HS Hci Hend Hb H8 HBL Hieq Hsp C48 C0a0 Ea0. subst a0.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (HPC & HPA & HAP & HSO & HPE & HMA & HSP & HLN0 & HLN1 & HSV0 &
                          Cc8 & Cc10 & Cc18 & Cc20 & Cc28 & Cc30 & MI0).
  destruct HPE as (HFRM0 & HTM & HSSP & HIMG & HSP63).
  assert (HBrest : (B <= length rest)%nat) by lia.
  pose proof (hdra_cell_ro m _ _ C0a0) as R0a0.
  assert (SOK98 : store_ok rsegs m (wa (SP + 0x98)) 8 = true).
  { destruct HS as ((_ & _ & _ & STm & _) & _). eapply hdra_stk_store_ok; [exact STm | lia | lia]. }
  do 2 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS1 : hst mm) by (apply hst_store; [exact HS | lia | lia]);
    assert (C98a : cell8 mm (SP + 0x98) (p + Z.of_nat A + 7))
      by (unfold cell8; apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
    assert (C48a : cell8 mm (SP + 0x48) (p + Z.of_nat A))
      by (apply hdra_cell_store; [exact C48 | lia | lia | lia]);
    assert (C0a0a : cell8 mm (SP + 0xa0) (p + Z.of_nat B))
      by (apply hdra_cell_store; [exact C0a0 | lia | lia | lia]);
    assert (SOK90 : store_ok rsegs mm (wa (SP + 0x90)) 8 = true)
      by (destruct HS1 as ((_ & _ & _ & ST1 & _) & _); eapply hdra_stk_store_ok; [exact ST1 | lia | lia])
  end.
  step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HS2 : hst mm) by (apply hst_store; [exact HS1 | lia | lia]);
    assert (C90b : cell8 mm (SP + 0x90) (p + Z.of_nat B))
      by (unfold cell8; apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
    assert (C98b : cell8 mm (SP + 0x98) (p + Z.of_nat A + 7))
      by (apply hdra_cell_store; [exact C98a | lia | lia | lia]);
    assert (C48b : cell8 mm (SP + 0x48) (p + Z.of_nat A))
      by (apply hdra_cell_store; [exact C48a | lia | lia | lia])
  end.
  do 3 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    destruct (hst_text mm (A + 7) (B - A - 7) HS2 ltac:(lia)) as (l2 & HB2 & HZ2 & HL2)
  end.
  replace (A + 7 + (B - A - 7))%nat with B in HZ2 by lia.
  replace (p + Z.of_nat (A + 7)) with (p + Z.of_nat A + 7) in HB2 by lia.
  eapply (mfu_strip HSTRIP) with (ox := 0x98) (oy := 0x90)
      (sv := p + Z.of_nat A + 7) (ev := p + Z.of_nat B) (l := l2);
    [ exact HL | apply (proj1 HS2) | lia | lia | lia | lia | reflexivity | reflexivity | lia
    | exact C98b | exact C90b
    | rewrite unsigned_lit by lia; reflexivity
    | rewrite unsigned_lit by lia; reflexivity
    | exact HB2 | rewrite HL2; lia | lia | lia
    | apply hdra_apart_win; lia | ].
  intros m3 w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 MID3 MU3 WM3 Cs98 Cs90.
  rewrite HZ2 in Cs98, Cs90.
  assert (HS3 : hst m3).
  { eapply hst_sub; [exact HS2 | exact MID3 | exact MU3 |].
    intros x Hx. unfold hdW in Hx. cbn [outside] in Hx |- *. repeat split; lia. }
  replace (ret_pc (Z_to_bv 64 83156)) with (Z_to_bv 64 83156)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (hdra_cell_ro m3 _ _ Cs98) as Rs98.
  pose proof (hdra_cell_ro m3 _ _ Cs90) as Rs90.
  assert (Hsk7 : skipn 7 (slice A B (mf_line rest)) = slice (A + 7) B (mf_line rest)).
  { rewrite <- (hdra_slice_full (slice A B (mf_line rest)) 7) by (rewrite slice_length by lia; lia).
    rewrite slice_length by lia. rewrite slice_slice by lia. f_equal. lia. }
  remember (strip_lead (slice (A + 7) B (mf_line rest))) as ld2 eqn:Eld2.
  remember (strip_trail (slice (A + 7) B (mf_line rest))) as tr2 eqn:Etr2.
  assert (HLE2 : (ld2 + tr2 <= B - (A + 7))%nat).
  { rewrite Eld2, Etr2. pose proof (strip_le (slice (A + 7) B (mf_line rest))) as HH.
    rewrite slice_length in HH by lia. exact HH. }
  assert (Hnm : h_strip (slice (A + 7) B (mf_line rest)) =
                slice (A + 7 + ld2) (B - tr2) (mf_line rest))
    by (rewrite Eld2, Etr2; apply hdra_strip_slice; lia).
  assert (Hlnm : length (h_strip (slice (A + 7) B (mf_line rest))) = (B - tr2 - (A + 7 + ld2))%nat)
    by (rewrite Hnm; apply slice_length; lia).
  do 3 step. if_cases K0; cbv iota.
  { apply hdra_refuse; [exact HS3 |].
    eapply hdra_refuse_body; [exact Hci | exact Hb | lia | lia |].
    right. right. right. left. rewrite Hsk7, Hlnm.
    zify_cond K0. rewrite ?Z.mod_small in K0 by lia. lia. }
  zify_cond K0. rewrite ?Z.mod_small in K0 by lia.
  step. rewrite !unsigned_lit by lia.
  do 2 step. if_cases K1; cbv iota.
  { apply hdra_refuse; [exact HS3 |].
    eapply hdra_refuse_body; [exact Hci | exact Hb | lia | lia |].
    right. right. right. right. rewrite Hsk7, Hlnm.
    zify_cond K1. rewrite ?Z.mod_small in K1 by lia. lia. }
  zify_cond K1. rewrite ?Z.mod_small in K1 by lia.
  rewrite (hdra_find_model ci A B Hci Hend Hb ltac:(lia) ltac:(lia) ltac:(lia) Hieq Hsp
             ltac:(rewrite Hsk7, Hlnm; lia)).
  rewrite Hsk7.
  eapply (evt_mono rsegs).
  - unfold H_MFU_HFIND in HFIND.
    eapply HFIND with (o := (A + 7 + ld2)%nat)
                      (nm := h_strip (slice (A + 7) B (mf_line rest)));
      [ exact Hnb | exact Hne | exact (hst_loop m3 fc HS3 HFRM0) | exact HR | exact Hs6
      | rewrite Hlnm; lia
      | rewrite Hlnm; lia
      | rewrite Hlnm, mf_line_firstn by lia; rewrite Hnm; f_equal; lia
      | f_equal; lia
      | replace (p + Z.of_nat (A + 7 + ld2))
          with (p + Z.of_nat A + 7 + Z.of_nat ld2) by lia;
        exact Cs98
      | rewrite Hlnm; f_equal; lia ].
  - intros ms' HP. eapply hdra_post_back; [exact HS3 | exact HP].
Qed.

(** 0x14474: the length check, ieq "segment" and the blank after it. *)
Lemma hdra_s2 : forall (m : word -> option byte) (ci A B : nat)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word),
  hst m ->
  memchr (slice i j (mf_line rest)) RBR = Some ci -> (S ci = j - i)%nat ->
  h_strip (slice 1 ci (slice i j (mf_line rest))) = slice A B (mf_line rest) ->
  (A <= B)%nat -> (B <= length (mf_line rest))%nat ->
  cell8 m (SP + 0x48) (p + Z.of_nat A) -> cell8 m (SP + 0xa0) (p + Z.of_nat B) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14474) fc None m (seg_rom rsegs)).
Proof.
  intros m ci A B ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6
    HS Hci Hend Hb HAB HBL C48 C0a0.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (HPC & HPA & HAP & HSO & HPE & HMA & HSP & HLN0 & HLN1 & HSV0 &
                          Cc8 & Cc10 & Cc18 & Cc20 & Cc28 & Cc30 & MI0).
  destruct HPE as (HFRM0 & HTM & HSSP & HIMG & HSP63).
  pose proof HR as (ER0 & ER2 & ER3 & ER7 & ER8 & ER9 & ER10 & ER11).
  pose proof (proj1 HS) as MIDm. pose proof MIDm as (MUw & WMw & MIm & STm & MAm).
  assert (HBrest : (B <= length rest)%nat) by lia.
  pose proof (hdra_cell_ro m _ _ C48) as R48.
  pose proof (hdra_cell_ro m _ _ C0a0) as R0a0.
  do 3 step.
  rewrite !unsigned_lit by lia.
  do 2 step. if_cases K8; cbv iota.
  { apply hdra_refuse; [exact HS |].
    eapply hdra_refuse_body; [exact Hci | exact Hb | lia | lia |].
    left. zify_cond K8. rewrite hdra_bsigned in K8 by lia. lia. }
  zify_cond K8. rewrite hdra_bsigned in K8 by lia.
  assert (H8A : (8 <= B - A)%nat) by lia.
  destruct (hst_text m A 7 HS ltac:(lia)) as (l7 & HB7 & HZ7 & HL7).
  assert (Hf7 : firstn 7 (slice A B (mf_line rest)) = slice A (A + 7) (mf_line rest)).
  { rewrite <- hdra_slice_pre. rewrite slice_slice by lia. f_equal; lia. }
  assert (Eiq : ieq (firstn 7 (slice A B (mf_line rest))) S_segment = ieq (zs l7) S_segment)
    by (rewrite Hf7, HZ7; reflexivity).
  do 4 step.
  eapply (mfu_ieq HIEQ) with (l := l7) (w := S_segment);
    [ exact HL | exact MIDm
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; exact HB7
    | rewrite unsigned_lit by lia; rewrite HL7; reflexivity
    | rewrite unsigned_lit by lia; rewrite HL7; apply hdra_apart_win; lia
    | rewrite unsigned_lit by lia; lia
    | rewrite unsigned_lit by lia; exact (proj1 (mfu_lits m MIm))
    | rewrite unsigned_lit by lia; apply Z.leb_le; vm_compute; reflexivity
    | rewrite unsigned_lit by lia; apply Z.leb_le; vm_compute; reflexivity
    | ].
  intros m2 u0 u1 u2 ub1 ub2 ub3 ub4 ub5 ub6 ub7 u3 u4 u5 u6 MID2 MU2 WM2.
  replace (ret_pc (Z_to_bv 64 83096)) with (Z_to_bv 64 83096)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (HSUBI : sub_fp [(SP - IEQ_STACK, SP)] hdW).
  { intros x Hx. unfold hdW in Hx. unfold IEQ_STACK. cbn [outside] in Hx |- *. repeat split; lia. }
  assert (HS2 : hst m2) by (eapply hst_sub; [exact HS | exact MID2 | exact MU2 | exact HSUBI]).
  assert (HOUTI : forall x : Z, SP + 0x48 <= x < SP + 0x48 + 8 -> outside [(SP - IEQ_STACK, SP)] x).
  { intros x Hx. unfold IEQ_STACK. cbn [outside]. repeat split; lia. }
  assert (HOUTJ : forall x : Z, SP + 0xa0 <= x < SP + 0xa0 + 8 -> outside [(SP - IEQ_STACK, SP)] x).
  { intros x Hx. unfold IEQ_STACK. cbn [outside]. repeat split; lia. }
  assert (C48b : cell8 m2 (SP + 0x48) (p + Z.of_nat A))
    by (eapply hdra_cell_keep; [exact C48 | exact MU2 | exact HOUTI]).
  assert (C0a0b : cell8 m2 (SP + 0xa0) (p + Z.of_nat B))
    by (eapply hdra_cell_keep; [exact C0a0 | exact MU2 | exact HOUTJ]).
  pose proof (hdra_cell_ro m2 _ _ C48b) as R48b.
  destruct (ieq (zs l7) S_segment) eqn:Eieq; cbn [b2z].
  - step. if_cases K9; cbv iota.
    { exfalso. zify_cond K9. lia. }
    do 4 step. if_cases Kt; cbv iota.
    { exfalso. zify_cond Kt. rewrite ?Z.mod_small in Kt by lia. lia. }
    destruct (hst_text m2 (A + 7) 1 HS2 ltac:(lia)) as (l1 & HB1 & HZ1 & HL1).
    destruct l1 as [|b7 l1r]; cbn [length] in HL1; [lia|].
    destruct l1r as [|? ?]; cbn [length] in HL1; [|lia].
    assert (Rb7 : 0 <= bv_unsigned b7 < 256).
    { pose proof (bv_unsigned_in_range 8 b7) as HH. change (bv_modulus 8) with 256 in HH. lia. }
    assert (Hs1 : firstn 1 (skipn (A + 7) (mf_line rest)) = [bv_unsigned b7]).
    { unfold slice in HZ1. replace (A + 7 + 1 - (A + 7))%nat with 1%nat in HZ1 by lia.
      rewrite <- HZ1. unfold zs. reflexivity. }
    pose proof (hdra_one_byte (mf_line rest) (A + 7) (bv_unsigned b7) Hs1) as Eb7.
    assert (Hn7 : nth 7 (slice A B (mf_line rest)) 0 = bv_unsigned b7)
      by (rewrite slice_nth by lia; exact Eb7).
    pose proof (bytes_at_ov_read rsegs m2 (p + Z.of_nat (A + 7)) [b7] 0 1 HB1 ltac:(cbn [length]; lia)) as HR7.
    cbn [firstn skipn] in HR7.
    do 3 step. if_cases Ktab; cbv iota.
    + eapply hdra_s3;
        [ exact HS2 | exact Hci | exact Hend | exact Hb | lia | lia
        | exact Eiq
        | rewrite Hn7; unfold sp_tab; apply orb_true_iff; right; apply Z.eqb_eq;
          zify_cond Ktab; rewrite ?unsigned_lit in Ktab by lia; rewrite ?Z.mod_small in Ktab by lia; lia
        | exact C48b | exact C0a0b | reflexivity ].
    + zify_cond Ktab. rewrite ?unsigned_lit in Ktab by lia. rewrite ?Z.mod_small in Ktab by lia.
      step. if_cases Ksp; cbv iota.
      * apply hdra_refuse; [exact HS2 |].
        eapply hdra_refuse_body; [exact Hci | exact Hb | lia | lia |].
        right. right. left. rewrite Hn7. unfold sp_tab. apply orb_false_iff. split; apply Z.eqb_neq.
        -- rewrite ER10 in Ksp. zify_cond Ksp.
           rewrite ?unsigned_lit in Ksp by lia. rewrite ?Z.mod_small in Ksp by lia. lia.
        -- lia.
      * eapply hdra_s3;
          [ exact HS2 | exact Hci | exact Hend | exact Hb | lia | lia
          | exact Eiq
          | rewrite Hn7; unfold sp_tab; apply orb_true_iff; left; apply Z.eqb_eq;
            rewrite ER10 in Ksp; zify_cond Ksp;
            rewrite ?unsigned_lit in Ksp by lia; rewrite ?Z.mod_small in Ksp by lia; lia
          | exact C48b | exact C0a0b | reflexivity ].
  - step. if_cases K9; cbv iota.
    + apply hdra_refuse; [exact HS2 |].
      eapply hdra_refuse_body; [exact Hci | exact Hb | lia | lia |].
      right. left. exact Eiq.
    + exfalso. zify_cond K9. lia.
Qed.

(** 0x14434: memchr(s, ']', e - s), the two pointer traps, the close test and the first strip. *)
Lemma hdra_main : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 : word),
  s5 = Z_to_bv 64 (p + Z.of_nat i) -> s4 = Z_to_bv 64 (p + Z.of_nat j) ->
  a2 = Z_to_bv 64 (Z.of_nat (j - i)) ->
  evt rsegs POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14434) fc None mcut (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 t3 t4 t5 t6 Es5 Es4 Ea2.
  pose proof hdra_nums as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
  destruct hdra_facts as (HPC & HPA & HAP & HSO & HPE & HMA & HSP & HLN0 & HLN1 & HSV0 &
                          Cc8 & Cc10 & Cc18 & Cc20 & Cc28 & Cc30 & MI0).
  destruct HPE as (HFRM0 & HTM & HSSP & HIMG & HSP63).
  assert (HJR : (j <= length rest)%nat) by lia.
  pose proof hst_init as HS0.
  destruct (hst_text mcut i (j - i) HS0 ltac:(lia)) as (bsl & HBsl & HZsl & HLsl).
  replace (i + (j - i))%nat with j in HZsl by lia.
  subst s5 s4 a2.
  unfold memchr_contract in HMEMCHR.
  do 3 step.
  eapply evt_cut.
  { eapply HMEMCHR with (buf := bsl);
      [ rewrite unsigned_lit by lia; exact HBsl
      | apply hdra_memchr_ok_full; rewrite unsigned_lit by lia; lia
      | exact MI0 ]. }
  intros ms' (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m1 & -> &
              MU1 & WM1 & MI1 & BY1).
  pose proof (hst_call0 mcut m1 HS0 MU1 WM1 MI1) as HS1.
  replace (ret_pc (Z_to_bv 64 83008)) with (Z_to_bv 64 83008)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite ?unsigned_lit by lia.
  try change (93 mod 256) with 93.
  match goal with |- context [memchr_res ?AA ?CC ?NN bsl] =>
    rewrite (hdra_memchr_res_full AA CC NN bsl ltac:(lia)) end.
  rewrite HZsl.
  destruct (memchr (slice i j (mf_line rest)) RBR) as [ci|] eqn:Eci.
  - assert (Hcilt : (ci < j - i)%nat).
    { pose proof (memchr_lt _ _ _ Eci) as HH. rewrite slice_length in HH by lia. exact HH. }
    assert (Hci1 : (1 <= ci)%nat).
    { destruct (Nat.eq_dec ci 0) as [E0|E0]; [|lia]. exfalso. subst ci.
      destruct (memchr_some _ _ _ Eci) as (_ & Hnth & _).
      rewrite slice_nth in Hnth by lia. rewrite Nat.add_0_r, Hlbr in Hnth. discriminate. }
    step. if_cases Kz; cbv iota.
    { exfalso. zify_cond Kz. rewrite ?unsigned_lit in Kz by lia. rewrite ?Z.mod_small in Kz by lia. lia. }
    do 2 step. if_cases Kt1; cbv iota.
    { exfalso. zify_cond Kt1. rewrite ?unsigned_lit in Kt1 by lia. rewrite ?Z.mod_small in Kt1 by lia. lia. }
    do 2 step. if_cases Kne; cbv iota.
    { apply hdra_refuse; [exact HS1 |].
      eapply hdra_refuse_end; [exact Eci |].
      zify_cond Kne. rewrite ?unsigned_lit in Kne by lia. rewrite ?Z.mod_small in Kne by lia. lia. }
    zify_cond Kne. rewrite ?unsigned_lit in Kne by lia. rewrite ?Z.mod_small in Kne by lia.
    assert (Hend : (S ci = j - i)%nat) by lia.
    do 2 step. if_cases Kt2; cbv iota.
    { exfalso. zify_cond Kt2. rewrite ?unsigned_lit in Kt2 by lia. rewrite ?Z.mod_small in Kt2 by lia. lia. }
    assert (SOK48 : store_ok rsegs m1 (wa (SP + 0x48)) 8 = true).
    { destruct HS1 as ((_ & _ & _ & ST1 & _) & _). eapply hdra_stk_store_ok; [exact ST1 | lia | lia]. }
    do 2 step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS2 : hst mm) by (apply hst_store; [exact HS1 | lia | lia]);
      assert (C48 : cell8 mm (SP + 0x48) (p + Z.of_nat i + 1))
        by (unfold cell8; apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
      assert (SOKa0 : store_ok rsegs mm (wa (SP + 0xa0)) 8 = true)
        by (destruct HS2 as ((_ & _ & _ & ST2 & _) & _); eapply hdra_stk_store_ok; [exact ST2 | lia | lia])
    end.
    step.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HS3 : hst mm) by (apply hst_store; [exact HS2 | lia | lia]);
      assert (C0a0 : cell8 mm (SP + 0xa0) (p + Z.of_nat i + Z.of_nat ci))
        by (unfold cell8; apply bytes_at_write_same; [lia | rewrite length_le8; lia]);
      assert (C48b : cell8 mm (SP + 0x48) (p + Z.of_nat i + 1))
        by (apply hdra_cell_store; [exact C48 | lia | lia | lia]);
      destruct (hst_text mm (i + 1) (ci - 1) HS3 ltac:(lia)) as (l1 & HB1 & HZ1 & HL1)
    end.
    replace (i + 1 + (ci - 1))%nat with (i + ci)%nat in HZ1 by lia.
    replace (p + Z.of_nat (i + 1)) with (p + Z.of_nat i + 1) in HB1 by lia.
    do 3 step.
    eapply (mfu_strip HSTRIP) with (ox := 0x48) (oy := 0xa0)
        (sv := p + Z.of_nat i + 1) (ev := p + Z.of_nat i + Z.of_nat ci) (l := l1);
      [ exact HL | apply (proj1 HS3) | lia | lia | lia | lia | reflexivity | reflexivity | lia
      | exact C48b | exact C0a0
      | rewrite unsigned_lit by lia; reflexivity
      | rewrite unsigned_lit by lia; reflexivity
      | exact HB1 | rewrite HL1; lia | lia | lia
      | apply hdra_apart_win; lia | ].
    intros m4 y0 y1 y2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 MID4 MU4 WM4 Cq48 Cqa0.
    rewrite HZ1 in Cq48, Cqa0.
    assert (HS4 : hst m4).
    { eapply hst_sub; [exact HS3 | exact MID4 | exact MU4 |].
      intros x Hx. unfold hdW in Hx. cbn [outside] in Hx |- *. repeat split; lia. }
    replace (ret_pc (Z_to_bv 64 83060)) with (Z_to_bv 64 83060)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    remember (strip_lead (slice (i + 1) (i + ci) (mf_line rest))) as ld1 eqn:Eld1.
    remember (strip_trail (slice (i + 1) (i + ci) (mf_line rest))) as tr1 eqn:Etr1.
    assert (HLE1 : (ld1 + tr1 <= i + ci - (i + 1))%nat).
    { rewrite Eld1, Etr1. pose proof (strip_le (slice (i + 1) (i + ci) (mf_line rest))) as HH.
      rewrite slice_length in HH by lia. exact HH. }
    eapply hdra_s2 with (ci := ci) (A := (i + 1 + ld1)%nat) (B := (i + ci - tr1)%nat);
      [ exact HS4 | exact Eci | exact Hend
      | rewrite slice_slice by lia; rewrite Eld1, Etr1; apply hdra_strip_slice; lia
      | lia | lia
      | replace (p + Z.of_nat (i + 1 + ld1)) with (p + Z.of_nat i + 1 + Z.of_nat ld1) by lia; exact Cq48
      | replace (p + Z.of_nat (i + ci - tr1)) with (p + Z.of_nat i + Z.of_nat ci - Z.of_nat tr1) by lia;
        exact Cqa0 ].
  - step. if_cases Kz; cbv iota.
    + apply hdra_refuse; [exact HS1 |]. apply hdra_refuse_none. exact Eci.
    + exfalso. zify_cond Kz. lia.
Qed.

End Walk.

Theorem mfu_hdra_holds :
  memchr_contract -> strip_contract -> ieq_contract -> m_refuse_contract -> S_MFU_HDRA.
Proof.
  intros HM HSt HI HRf. unfold S_MFU_HDRA. intros n HT HF. unfold H_MFU_HDR.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ra0 sp0 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 c p line mc cur k0 rest i j
    Hn Hne HL HR Hs6 Hshort Hij Hjl Hsl Hlbr Es5 Es4 Ea2.
  unfold MFU_PC_HDR.
  eapply hdra_main; eassumption.
Qed.
