(** ent_build's kind 0 (the head-amp key, pod.h:224-262) in the UBSan image, from the cut 0x13abc (Ent0Mid.v,
    [case0_mid_at]) to the join 0x13df0: param[p % 8] through the .data.rel.ro pointer table at 0x1f318, the
    separator by p's bit 7, the four part pointers at sp + 0x140, the strlen/memcpy loop into t[96] at sp + 0x178
    (four turns, the part clamp never fires), then ent_text's memcpy of t into e's body, its NUL, type and size. The
    trap branches (the table index, e's body + n) are not taken. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout HeadampImg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog.HeadBuild Require Import EntCut EntFacts EntRo Ent0Mid.
Import ListNotations.
Open Scope Z_scope.

(** ** Model facts *)
Lemma join_part_nc : forall t s, (length t + length s <= 95)%nat -> join_part t s = t ++ s.
Proof.
  intros t s H. unfold join_part.
  replace (96 <=? length t + length s)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  rewrite firstn_all. reflexivity.
Qed.

Lemma join_parts4 : forall a b c d, (length a + length b + length c + length d <= 95)%nat ->
  join_parts [a; b; c; d] = a ++ b ++ c ++ d.
Proof.
  intros a b c d H. unfold join_parts. cbn [fold_left].
  rewrite (join_part_nc [] a) by (cbn [length]; lia). cbn [app].
  rewrite (join_part_nc a b) by lia.
  rewrite (join_part_nc (a ++ b) c) by (rewrite length_app; lia).
  rewrite (join_part_nc ((a ++ b) ++ c) d) by (rewrite !length_app; lia).
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma ent_text_nul : forall s, (length s <= 95)%nat ->
  ent_text s true = Ent POD_STRING (Z.of_nat (length (s ++ [NUL]))) (s ++ [NUL]).
Proof. intros s H. unfold ent_text. rewrite firstn_all2 by exact H. reflexivity. Qed.

Lemma param_len : forall k, (length (nth k param []) <= 9)%nat.
Proof.
  intros k. rewrite <- (map_nth (@length byte) param [] k). rewrite param_strlen.
  do 8 (destruct k as [|k]; [cbn; lia|]). destruct k; cbn; lia.
Qed.

(** p's bit 7 is the top bit of p << 56 (0x13ad4 `slli s7,s7,0x38`, `bgez`). *)
Lemma sign56 : forall p, 0 <= p < 256 -> (2^63 <=? bv_unsigned (Z_to_bv 64 (Z.shiftl p 56))) = Z.testbit p 7.
Proof.
  intros p Hp.
  apply (byte_checkb (fun p => 2^63 <=? bv_unsigned (Z_to_bv 64 (Z.shiftl p 56))) (fun p => Z.testbit p 7));
    [vm_compute; reflexivity | exact Hp].
Qed.

(** ** The image: the param pointers and the texts *)
Definition PARAM_TBL : Z := 0x1f318.

Lemma param_relro : relro8_ok PARAM_TBL (pa_param_s headamp_ubsan_addrs) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma param_strs : forallb (fun k => rostr_ok (nth k (pa_param_s headamp_ubsan_addrs) 0) (nth k param []))
  (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma param_str : forall k, (k < 8)%nat -> rostr_ok (nth k (pa_param_s headamp_ubsan_addrs) 0) (nth k param []) = true.
Proof. intros k Hk. pose proof param_strs as H. rewrite forallb_forall in H. apply H. apply in_seq. lia. Qed.

Lemma fixed_strs : rostr_ok 0x102bd HPFX = true /\ rostr_ok 0x1032d DOT = true /\ rostr_ok 0x10323 [] = true.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(** ** Byte runs *)
Ltac simpl_len := rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app, ?length_zeros;
  cbn [length].

Lemma bytes_at_sub : forall m a l k n, bytes_at rsegs m a l -> (k <= length l)%nat ->
  bytes_at rsegs m (a + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m a l k n H Hk. rewrite <- (firstn_skipn k l) in H. apply bytes_at_app in H as [_ H2].
  rewrite length_firstn in H2. replace (Nat.min k (length l)) with k in H2 by lia.
  rewrite <- (firstn_skipn n (skipn k l)) in H2. apply bytes_at_app in H2 as [H3 _]. exact H3.
Qed.

Lemma bytes_at_cons8 : forall m1 A w rest, bytes_at rsegs m1 A (le8 w) -> bytes_at rsegs m1 (A + 8) rest ->
  bytes_at rsegs m1 A (le8 w ++ rest).
Proof. intros m1 A w rest H1 H2. apply bytes_at_app. rewrite length_le8. split; assumption. Qed.

(** The part pointers at sp + 0x140, 8 bytes each. *)
Definition ptrs_bytes (ps : list Z) : list byte := flat_map (fun a => le8 (Z_to_bv 64 a)) ps.

Lemma ptrs_bytes_length : forall ps, length (ptrs_bytes ps) = (8 * length ps)%nat.
Proof.
  induction ps as [|x ps IH]; [reflexivity|].
  unfold ptrs_bytes in *. cbn [flat_map length]. rewrite length_app, length_le8, IH. lia.
Qed.

Lemma ptrs_bytes_cons : forall x ps, ptrs_bytes (x :: ps) = le8 (Z_to_bv 64 x) ++ ptrs_bytes ps.
Proof. reflexivity. Qed.

Lemma ptrs_bytes_nth : forall ps i, (i < length ps)%nat ->
  firstn 8 (skipn (8 * i) (ptrs_bytes ps)) = le8 (Z_to_bv 64 (nth i ps 0)).
Proof.
  induction ps as [|x ps IH]; intros i Hi; cbn [length] in Hi; [lia|].
  rewrite ptrs_bytes_cons.
  destruct i as [|i].
  - rewrite Nat.mul_0_r, skipn_O. cbn [nth].
    rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    apply firstn_all2. rewrite length_le8. lia.
  - replace (8 * S i)%nat with (8 + 8 * i)%nat by lia.
    rewrite skipn_app, length_le8. rewrite skipn_all2 by (rewrite length_le8; lia).
    replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia. cbn [app nth]. apply IH. lia.
Qed.

(** ** Tactics *)
Local Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(** Carry one bytes_at fact across a callee whose footprint is in MU. *)
Local Ltac tr1 H MU :=
  let T := fresh "T" in
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H MU) as T;
  specialize (T ltac:(cbn [disjoint_from]; simpl_len; repeat split; lia));
  clear H; rename T into H.

(** Carry the bytes_at facts on m1 across a store of bs at a. *)
Local Ltac carry m1 a bs :=
  repeat match goal with
  | H : bytes_at rsegs m1 ?A ?cs |- _ =>
      apply (bytes_at_write_other rsegs m1 a bs A cs) in H;
      [ cbv delta [wa] in H | lia | simpl_len; lia | simpl_len; lia ]
  end.

Section Mid.
Variables (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Local Abbreviation QE := (QJ sp gp tp s1 F fc m r src pp lo (ent_build r)).
Local Abbreviation Z0 := (Z_to_bv 64 0).

(** A store of n bytes at a (a Z expression) in [sp + 0x140, sp + 0x1d8): MemC and the other runs carried, the
    stored run named HW. *)
Local Ltac sthi a n :=
  lazymatch goal with MC : MemC ?sp' ?m' ?lo' ?m1 ?t ?sz ?bd |- _ =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa a) n = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd a n MC); unfold FRAME_LOCALS; lia);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 ?a') ?bs) _) =>
      let MC2 := fresh "MC" in let HW := fresh "HW" in
      pose proof (MemC_st_hi _ _ _ _ _ _ HE m1 t sz bd a' bs MC ltac:(lia) ltac:(simpl_len; unfold FRAME_LOCALS; lia))
        as MC2;
      carry m1 a' bs;
      assert (HW : bytes_at rsegs (write_to_mem m1 (Z_to_bv 64 a') bs) a' bs)
        by (apply bytes_at_write_same; simpl_len; lia);
      clear MC; rename MC2 into MC; name_mem
    end
  end.

(** At 0x13b1c (after i turns) or 0x13b58 (after the four): s4 = &parts[i], s6 = n = |acc|, the part pointers ps
    at sp + 0x140, ch and its NUL at sp + 0x160, acc at t = sp + 0x178. *)
Definition loop_st (r' ch : list byte) (ps : list Z) (i : nat) (acc : list byte) (pc : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 : word) m1,
    s4 = Z_to_bv 64 (bv_unsigned sp + 320 + 8 * Z.of_nat i) ->
    s6 = Z_to_bv 64 (Z.of_nat (length acc)) ->
    MemC sp m lo m1 Z0 Z0 (zeros 96) ->
    bytes_at rsegs m1 (bv_unsigned sp + 320) (ptrs_bytes ps) ->
    bytes_at rsegs m1 (bv_unsigned sp + 352) (ch ++ [NUL]) ->
    bytes_at rsegs m1 (bv_unsigned sp + 376) acc ->
    evt rsegs QE
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (Z.of_nat (length r'))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4
               (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) s6 s7 s8
               (Z_to_bv 64 95)
               (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) (Z_to_bv 64 4) t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

(** One turn 0x13b1c -> 0x13b54: s7 = parts[i] = a, l = strlen(a) (no clamp), memcpy(t + n, a, l), n += l. *)
Lemma turn_ok : forall (r' ch : list byte) (ps : list Z) (i : nat) (acc s : list byte) (a pc' : Z),
  (i < 4)%nat -> length ps = 4%nat -> nth i ps 0 = a ->
  pc' = (if (S i =? 4)%nat then 0x13b58 else 0x13b1c) ->
  (length ch <= 21)%nat -> ~ In NUL s ->
  Z.of_nat (length acc) + Z.of_nat (length s) <= 95 ->
  (forall d, bv_unsigned sp + 376 <= d -> d + Z.of_nat (length s) <= bv_unsigned sp + FRAME_LOCALS ->
     a + Z.of_nat (length s) <= d \/ d + Z.of_nat (length s) <= a) ->
  (forall m1, MemC sp m lo m1 Z0 Z0 (zeros 96) -> bytes_at rsegs m1 (bv_unsigned sp + 352) (ch ++ [NUL]) ->
     exists slack, bytes_at rsegs m1 a (s ++ NUL :: slack) /\
       (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)) ->
  loop_st r' ch ps (S i) (acc ++ s) pc' ->
  loop_st r' ch ps i acc 0x13b1c.
Proof.
  intros r' ch ps i acc s a pc' Hi Lps Ea Epc Lch Ns Hlen Hdis SRC K.
  unfold loop_st in K.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 m1 -> -> MC HPA Hch Hacc.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 472) by reflexivity.
  assert (LP : length (ptrs_bytes ps) = 32%nat) by (rewrite ptrs_bytes_length, Lps; reflexivity).
  destruct (SRC m1 MC Hch) as (slack & Hs & Hsl).
  pose proof Hs as (Ha0 & Ha1 & _). rewrite length_app in Ha1. cbn [length] in Ha1.
  (* 0x13b1c ld s7,0(s4) *)
  assert (HR : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 320 + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 a))).
  { apply bytes_at_read8; [|apply length_le8].
    pose proof (bytes_at_sub m1 _ _ (8 * i) 8 HPA ltac:(lia)) as X.
    rewrite ptrs_bytes_nth, Ea in X by lia.
    replace (bv_unsigned sp + 320 + 8 * Z.of_nat i) with (bv_unsigned sp + 320 + Z.of_nat (8 * i)) by lia.
    exact X. }
  step. clear HR.
  (* mv a0,s7; jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack).
    - rewrite unsigned_lit by lia. exact Hs.
    - exact Ns.
    - rewrite unsigned_lit by lia. exact Hsl.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & BS2).
  subst ms'. rewrite unsigned_lit in BS2 by lia.
  apply bytes_at_app in BS2 as [Bs _].
  assert (MC2 : MemC sp m lo m2 Z0 Z0 (zeros 96)) by (eapply MemC_call_nil; eassumption).
  tr1 HPA MU2. tr1 Hch MU2. tr1 Hacc MU2.
  clear MC MU2 WM2 MI2 Hs Hsl.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13b28 mv s8,a0; add a0,a0,s6; bgeu s9,a0 (n + l <= 95: no clamp) *)
  do 3 step. brt.
  (* 0x13b38 add a0,s0,s6; mv a1,s7; mv a2,s8; jal memcpy *)
  do 4 step.
  destruct (MemC_cells _ _ _ _ _ _ HE m2 Z0 Z0 (zeros 96) (bv_unsigned sp + 376 + Z.of_nat (length acc)) (length s)
              MC2 ltac:(lia) ltac:(lia)) as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := s) (junk := junk).
    - rewrite unsigned_lit by lia. exact Bs.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id.
      match goal with |- rw_cells _ _ ?A _ =>
        replace A with (bv_unsigned sp + 376 + Z.of_nat (length acc)) by lia end.
      exact CJ.
    - rewrite !unsigned_lit by lia.
      destruct (Hdis (bv_unsigned sp + 376 + Z.of_nat (length acc)) ltac:(lia) ltac:(lia)); lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ MC2). }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E & MU3 & WM3 & MI3 & RC3 & _).
  subst ms'. rewrite !unsigned_lit in MU3, RC3 by lia. rewrite Nat2Z.id in RC3.
  apply rw_CB_bytes in RC3 as [B3 _].
  assert (MC3 : MemC sp m lo m3 Z0 Z0 (zeros 96)).
  { match type of MU3 with munch [(?D, ?D2)] _ _ =>
      eapply (MemC_call_hi _ _ _ _ _ _ HE _ m3 _ _ _ D (Z.of_nat (length s)) _ MC2);
      [replace (D + Z.of_nat (length s)) with D2 by lia; exact MU3 | exact WM3 | exact MI3 | exact B3 | reflexivity
      | lia | lia] end. }
  tr1 HPA MU3. tr1 Hch MU3. tr1 Hacc MU3.
  assert (Hacc2 : bytes_at rsegs m3 (bv_unsigned sp + 376) (acc ++ s)).
  { apply bytes_at_app. split; [exact Hacc|].
    match type of B3 with bytes_at _ _ ?D _ =>
      replace (bv_unsigned sp + 376 + Z.of_nat (length acc)) with D by lia end.
    exact B3. }
  clear MC2 MU3 WM3 MI3 B3 Hacc CJ Lj junk Bs.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13b48 addi s4,s4,8; add s6,s8,s6; addi a0,sp,0x160; bne s4,a0 *)
  do 4 step.
  destruct (Nat.eqb_spec (S i) 4) as [E4|N4].
  - brf.
    replace (Z_to_bv 64 0x13b58) with (Z_to_bv 64 pc') by (rewrite Epc; reflexivity).
    eapply K; [| | exact MC3 | exact HPA | exact Hch | exact Hacc2].
    + f_equal. lia.
    + ulit. rewrite length_app. f_equal. lia.
  - brt.
    replace (Z_to_bv 64 0x13b1c) with (Z_to_bv 64 pc')
      by (rewrite Epc; reflexivity).
    eapply K; [| | exact MC3 | exact HPA | exact Hch | exact Hacc2].
    + f_equal. lia.
    + ulit. rewrite length_app. f_equal. lia.
Qed.

(** 0x13b58 -> 0x13df0: n < 95, memcpy(e's body, t, n), the frame cells pp and pp + 0x4000 back in s8 and s7, the
    body + n check, e's body[n] = 0, type 8, size n + 1. *)
Lemma tail_ok : forall (r' ch : list byte) (ps : list Z) (key : list byte),
  ent_build r = (ent_text key true, r') -> (length key <= 44)%nat ->
  loop_st r' ch ps 4 key 0x13b58.
Proof.
  intros r' ch ps key Eb Lk.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 m1 -> -> MC HPA Hch Hkey.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 472) by reflexivity.
  rewrite ent_text_nul in Eb by lia.
  clear HPA Hch.
  (* 0x13b58 addi a0,zero,95; bltu s6,a0 *)
  do 2 step. brt.
  (* 0x13b64 addi a1,sp,0x178; addi s4,sp,0xc0; mv a0,s4; mv a2,s6; jal memcpy *)
  do 5 step.
  destruct (MemC_cells _ _ _ _ _ _ HE m1 Z0 Z0 (zeros 96) (bv_unsigned sp + 192) (length key) MC
              ltac:(lia) ltac:(lia)) as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := key) (junk := junk).
    - rewrite unsigned_lit by lia. exact Hkey.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact CJ.
    - rewrite !unsigned_lit by lia. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & RC2 & _).
  subst ms'. rewrite !unsigned_lit in MU2, RC2 by lia. rewrite Nat2Z.id in RC2.
  apply rw_CB_bytes in RC2 as [B2 _].
  pose proof (MemC_call_bd _ _ _ _ _ _ HE _ m2 _ _ _ (bv_unsigned sp + 192) 0 key MC MU2 WM2 MI2 B2
                ltac:(lia) ltac:(lia)) as MC2.
  clear MC MU2 WM2 MI2 B2 CJ Lj junk Hkey. rename MC2 into MC.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13b78 ld s8,0x70(sp); ld s7,0x78(sp); ld a0,0x80(sp); bltu a0,s6 (trap) *)
  pose proof (MemC_c70 _ _ _ _ _ _ HE _ _ _ _ MC) as H68.
  pose proof (MemC_c78 _ _ _ _ _ _ HE _ _ _ _ MC) as H78.
  pose proof (MemC_c80 _ _ _ _ _ _ HE _ _ _ _ MC) as H80.
  do 4 step. brf. clear H68 H78 H80.
  (* 0x13b88 add a0,s4,s6; addi s6,s6,1; sb zero,0(a0) *)
  do 2 step.
  est_bd HE MC (bv_unsigned sp + 192 + Z.of_nat (length key)) (length key) 1%nat.
  (* 0x13b94 addi a0,zero,8; sw a0,0xb8(sp); sw s6,0xbc(sp); j 0x13df0 *)
  step. est_t HE MC. est_sz HE MC. step.
  eapply join_13df0; [exact Eb | reflexivity | reflexivity | reflexivity | exact MC | | | ].
  - rewrite le4_le32. reflexivity.
  - rewrite le4_le32. cbn [e_size]. f_equal. rewrite length_app. cbn [length]. ulit. lia.
  - cbn [e_body]. rewrite upd_zeros0 by lia. rewrite upd_app_zeros by (simpl_len; lia).
    rewrite <- app_assoc. f_equal. simpl_len. f_equal; try (f_equal; lia); try reflexivity; vm_compute; reflexivity.
Qed.

(** The four turns and the tail, from 0x13b1c with the parts HPFX, ch, the separator and the param stored. *)
Lemma loop_all : forall (r' ch sep prm : list byte) (sa pa : Z),
  ent_build r = (ent_text (HPFX ++ ch ++ sep ++ prm) true, r') ->
  rostr_ok sa sep = true -> rostr_ok pa prm = true -> (length sep <= 1)%nat -> (length prm <= 9)%nat ->
  (length ch <= 21)%nat -> ~ In NUL ch ->
  loop_st r' ch [0x102bd; bv_unsigned sp + 352; sa; pa] 0 [] 0x13b1c.
Proof.
  intros r' ch sep prm sa pa Eb Hsep Hprm Lsep Lprm Lch Nch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 472) by reflexivity.
  assert (LH : length HPFX = 13%nat) by reflexivity.
  destruct fixed_strs as (Hh & _ & _).
  (* the parts of the image: no NUL, the bytes with strlen's slack, apart from t *)
  assert (IMG : forall a s, rostr_ok a s = true ->
     ~ In NUL s /\
     (forall d, bv_unsigned sp + 376 <= d -> d + Z.of_nat (length s) <= bv_unsigned sp + FRAME_LOCALS ->
        a + Z.of_nat (length s) <= d \/ d + Z.of_nat (length s) <= a) /\
     (forall m1, MemC sp m lo m1 Z0 Z0 (zeros 96) -> bytes_at rsegs m1 (bv_unsigned sp + 352) (ch ++ [NUL]) ->
        exists slack, bytes_at rsegs m1 a (s ++ NUL :: slack) /\
          (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack))).
  { intros a s Hok. pose proof (rostr_bytes m a s (ep_mem_inv _ _ _ _ _ _ HE) Hok) as (_ & N & _ & A0 & A1 & _).
    split; [exact N|]. split.
    - intros d D1 D2. destruct (Z.eq_dec (Z.of_nat (length s)) 0) as [Z|Z]; [lia|].
      apply (ro_apart sp m r src pp lo HE a s d (Z.of_nat (length s)) Hok); lia.
    - intros m1 MC _. destruct (rostr_bytes m1 a s (MemC_mem_inv _ _ _ _ _ _ _ MC) Hok) as (B & _ & Sl & _).
      exists (img_slack a s). split; [exact B | exact Sl]. }
  destruct (IMG 0x102bd HPFX Hh) as (N0 & D0 & G0).
  destruct (IMG sa sep Hsep) as (N2 & D2 & G2).
  destruct (IMG pa prm Hprm) as (N3 & D3 & G3).
  clear IMG.
  (* parts[0] = HPFX *)
  apply (turn_ok r' ch _ 0 [] HPFX 0x102bd 0x13b1c);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N0 | cbn [length]; lia | exact D0
    | exact G0 |].
  (* parts[1] = ch, on the stack *)
  apply (turn_ok r' ch _ 1 HPFX ch (bv_unsigned sp + 352) 0x13b1c);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact Nch | lia | intros; left; lia | |].
  { intros m1 MC Hc.
    pose proof (Z.mod_pos_bound (- (bv_unsigned sp + 352 + Z.of_nat (length ch) + 1)) 8 ltac:(lia)) as Hm.
    destruct (MemC_any_bytes _ _ _ _ _ _ HE m1 Z0 Z0 (zeros 96) (bv_unsigned sp + 352 + Z.of_nat (length ch) + 1)
                (Z.to_nat ((- (bv_unsigned sp + 352 + Z.of_nat (length ch) + 1)) mod 8)) MC ltac:(lia) ltac:(lia))
      as (sl & Lsl & Bsl).
    exists sl. split.
    - replace (ch ++ NUL :: sl) with ((ch ++ [NUL]) ++ sl) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact Hc|].
      rewrite length_app. cbn [length].
      replace (bv_unsigned sp + 352 + Z.of_nat (length ch + 1))
        with (bv_unsigned sp + 352 + Z.of_nat (length ch) + 1) by lia.
      exact Bsl.
    - rewrite Lsl. lia. }
  (* parts[2] = the separator *)
  apply (turn_ok r' ch _ 2 (HPFX ++ ch) sep sa 0x13b1c);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N2 | rewrite length_app; lia | exact D2
    | exact G2 |].
  (* parts[3] = param[p % 8] *)
  apply (turn_ok r' ch _ 3 ((HPFX ++ ch) ++ sep) prm pa 0x13b58);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N3 | rewrite !length_app; lia | exact D3
    | exact G3 |].
  apply tail_ok.
  - rewrite <- !app_assoc. exact Eb.
  - rewrite !length_app. lia.
Qed.

(** 0x13af0: n = 0, the param pointer read from the table at 0x1f318 + 8 k, the four part stores, s4 = parts. *)
Lemma head_c : forall (k : nat) (sep : list byte) (sa : Z) (ch r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 : word) m1,
  (k < 8)%nat ->
  ent_build r = (ent_text (HPFX ++ ch ++ sep ++ nth k param []) true, r') ->
  rostr_ok sa sep = true -> (length sep <= 1)%nat ->
  (length ch <= 21)%nat -> ~ In NUL ch ->
  a0 = Z_to_bv 64 (8 * Z.of_nat k) -> a1 = Z_to_bv 64 PARAM_TBL -> a2 = Z_to_bv 64 sa ->
  MemC sp m lo m1 Z0 Z0 (zeros 96) ->
  bytes_at rsegs m1 (bv_unsigned sp + 352) (ch ++ [NUL]) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x178)) s1 a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (Z.of_nat (length r'))) (Z_to_bv 64 (0xcccccccd * 2^32)) s4
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) s6 s7 s8
             (Z_to_bv 64 95)
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) (Z_to_bv 64 4) t3 t4 t5 t6)
        F (Z_to_bv 64 0x13af0) fc None m1 (seg_rom rsegs)).
Proof.
  intros k sep sa ch r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 t3 t4 t5 t6 m1
    Hk Eb Hsep Lsep Lch Nch -> -> -> MC Hch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 472) by reflexivity.
  pose proof (param_len k) as Lprm.
  pose proof (param_str k Hk) as Hprm.
  pose proof (rostr_bytes m _ _ (ep_mem_inv _ _ _ _ _ _ HE) Hsep) as (_ & _ & _ & SA0 & SA1 & _).
  (* 0x13af0 mv s6,zero; add a0,a1,a0; auipc a1 *)
  do 3 step.
  (* 0x13afc ld a0,0(a0): the param pointer *)
  assert (HR : ov_read_bytes rsegs m1 (wa (PARAM_TBL + 8 * Z.of_nat k)) 8 =
               Some (le8 (Z_to_bv 64 (nth k (pa_param_s headamp_ubsan_addrs) 0)))).
  { assert (L8 : length (pa_param_s headamp_ubsan_addrs) = 8%nat) by reflexivity.
    apply relro8_read; rewrite ?L8; [exact param_relro | exact Hk | unfold PARAM_TBL; lia | unfold PARAM_TBL; lia |].
    intros a Ha. apply (MemC_relro _ _ _ _ _ _ HE _ _ _ _ a MC).
    unfold PARAM_TBL, RELRO_TBL, RELRO_TBL_END in *. lia. }
  unfold PARAM_TBL in HR. ulit.
  step. clear HR.
  (* addi a1 = HPFX; sd a1,0x140(sp) *)
  step. sthi (bv_unsigned sp + 320) 8%nat. rename HW into P0.
  (* addi a1,sp,0x160; sd a1,0x148(sp) *)
  step. sthi (bv_unsigned sp + 328) 8%nat. rename HW into P1.
  (* sd a2,0x150(sp) *)
  sthi (bv_unsigned sp + 336) 8%nat. rename HW into P2.
  (* sd a0,0x158(sp) *)
  sthi (bv_unsigned sp + 344) 8%nat. rename HW into P3.
  (* addi s4,sp,0x140 *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HPA : bytes_at rsegs mm (bv_unsigned sp + 320)
                    (ptrs_bytes [0x102bd; bv_unsigned sp + 352; sa; nth k (pa_param_s headamp_ubsan_addrs) 0])) end.
  { rewrite !ptrs_bytes_cons. change (ptrs_bytes []) with (@nil byte). rewrite app_nil_r.
    apply bytes_at_cons8; [exact P0|].
    apply bytes_at_cons8; [replace (bv_unsigned sp + 320 + 8) with (bv_unsigned sp + 328) by lia; exact P1|].
    apply bytes_at_cons8; [replace (bv_unsigned sp + 320 + 8 + 8) with (bv_unsigned sp + 336) by lia; exact P2|].
    replace (bv_unsigned sp + 320 + 8 + 8 + 8) with (bv_unsigned sp + 344) by lia.
    exact P3. }
  pose proof (loop_all r' ch sep (nth k param []) sa (nth k (pa_param_s headamp_ubsan_addrs) 0) Eb Hsep Hprm Lsep Lprm
                Lch Nch) as LA.
  unfold loop_st in LA.
  eapply LA.
  - f_equal. lia.
  - reflexivity.
  - eassumption.
  - exact HPA.
  - exact Hch.
  - apply bytes_at_nil. lia.
Qed.

(** 0x13abc: the table index p & 7 (the bound check of 0x1f318 + 8 (p & 7)), the separator by p's bit 7, then
    head_c. *)
Lemma case0_mid_ok_sec : case0_mid_at sp gp tp s1 F fc m r src pp lo.
Proof.
  intros ra t0 t1 t2 s2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s10 t3 t4 t5 t6 m1 p ch r' Eb Hp -> Nch Lch Hch
    -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Hk : (Z.to_nat (p mod 8) < 8)%nat) by lia.
  pose proof (param_len (Z.to_nat (p mod 8))) as Lprm.
  assert (LH : length HPFX = 13%nat) by reflexivity.
  assert (LD : length DOT = 1%nat) by reflexivity.
  assert (Eb' : ent_build r = (ent_text (HPFX ++ ch ++ (if Z.testbit p 7 then [] else DOT) ++
                                          nth (Z.to_nat (p mod 8)) param []) true, r')).
  { rewrite Eb. rewrite join_parts4; [reflexivity|]. destruct (Z.testbit p 7); cbn [length]; lia. }
  clear Eb.
  destruct fixed_strs as (_ & Hdot & Hemp).
  (* 0x13abc andi a0,s7,7; auipc a1; slli a0,a0,3; addi a1 (0x1f318); not a2,a1; bltu a2,a0 (trap) *)
  do 6 step.
  assert (EA : Z.shiftl (bv_unsigned (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 p)) 7))) 3 =
               8 * Z.of_nat (Z.to_nat (p mod 8))).
  { rewrite (unsigned_lit p) by lia.
    assert (L7 : Z.land p 7 = p mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    rewrite L7, (unsigned_lit (p mod 8)) by lia. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z2Nat.id by lia. lia. }
  rewrite EA. clear EA.
  brf.
  (* 0x13ad4 slli s7,s7,0x38; bgez s7 *)
  do 2 step.
  rewrite bv_lts_zero_r, (unsigned_lit p) by lia. rewrite (sign56 p Hp).
  destruct (Z.testbit p 7) eqn:B7; cbn [negb]; cbv iota.
  - (* bit 7 set: "" at 0x10323; 0x13adc auipc a2; addi a2; j 0x13af0 *)
    do 3 step.
    eapply (head_c (Z.to_nat (p mod 8)) [] 0x10323 ch r');
      [exact Hk | exact Eb' | exact Hemp | cbn [length]; lia | exact Lch | exact Nch
      | reflexivity | reflexivity | reflexivity | exact MC | exact Hch].
  - (* bit 7 clear: "." at 0x1032d; 0x13ae8 auipc a2; addi a2 *)
    do 2 step.
    eapply (head_c (Z.to_nat (p mod 8)) DOT 0x1032d ch r');
      [exact Hk | exact Eb' | exact Hdot | lia | exact Lch | exact Nch
      | reflexivity | reflexivity | reflexivity | exact MC | exact Hch].
Qed.

End Mid.

Theorem case0_mid_ok : forall (sp gp tp s1 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (r : list byte) (src pp lo : Z),
  ent_pre sp m r src pp lo -> memcpy_contract -> strlen_contract -> case0_mid_at sp gp tp s1 F fc m r src pp lo.
Proof. intros. apply case0_mid_ok_sec; assumption. Qed.
