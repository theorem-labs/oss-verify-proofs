(** ent_build's kind 0 (pod.h:224-262) from the cut 0x13538 (Ent0Cut.v, [parts_at]) to the join 0x13600:
    param[p % 8] through the relative table at 0x105f0, the separator by p's bit 7, the four part pointers at
    sp + 0x118, the strlen/memcpy loop into t[96] at sp + 0x150 (four turns, the part clamp never fires), then
    ent_text's memcpy of t into e.body and its NUL. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Tables Model Layout HeadampImg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog.HeadBuild Require Import EntCut EntFacts EntTbl EntText Ent0Cut.
Import ListNotations.
Open Scope Z_scope.

(** ** Model facts *)
(** A part that keeps the text under 96 bytes is appended whole. *)
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

(** p's bit 7 is the sign of p << 56. *)
Lemma sign_shl56 : forall p, 0 <= p < 256 ->
  (bv_signed (Z_to_bv 64 (Z.shiftl p 56)) < 0 <-> Z.testbit p 7 = true).
Proof.
  intros p Hp.
  assert (C : forallb (fun z => Bool.eqb (bv_signed (Z_to_bv 64 (Z.shiftl z 56)) <? 0) (Z.testbit z 7))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in C.
  specialize (C p ltac:(apply in_map_iff; exists (Z.to_nat p); split; [lia | apply in_seq; lia])).
  apply Bool.eqb_prop in C. rewrite <- C. rewrite Z.ltb_lt. reflexivity.
Qed.

(** The bytes of ch[24] after ch's NUL cover what strlen reads to the next 8-byte boundary. *)
Lemma slack_ch : forall S c, S mod 16 = 0 -> 0 <= c <= 21 -> (- (S + 312 + c + 1)) mod 8 <= 23 - c.
Proof. intros S c H1 H2. Z.div_mod_to_equations. lia. Qed.

(** ** Byte runs *)
Lemma bytes_at_nil : forall m1 a, 0 <= a <= 2^64 -> bytes_at rsegs m1 a [].
Proof. intros m1 a H. unfold bytes_at. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia. Qed.

Lemma bytes_at_cons8 : forall m1 A w rest, bytes_at rsegs m1 A (le8 w) -> bytes_at rsegs m1 (A + 8) rest ->
  bytes_at rsegs m1 A (le8 w ++ rest).
Proof. intros m1 A w rest H1 H2. apply bytes_at_app. rewrite length_le8. split; assumption. Qed.

(** The part pointers at sp + 0x118, 8 bytes each. *)
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

(** ** The image strings *)
Lemma str_ok_pure : forall a s, str_ok a s = true ->
  ~ In NUL s /\ forallb (fun j => rom_some (a + Z.of_nat j)) (seq 0 (S (length s))) = true /\ 0 <= a /\
  a + Z.of_nat (length s) + 8 <= 2^32.
Proof.
  intros a s H. unfold str_ok in H.
  apply andb_prop in H as [H H6]. apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4].
  apply andb_prop in H as [H H3]. apply Z.leb_le in H6. apply Z.leb_le in H5.
  split; [apply no_nul_not_in; exact H3|]. split; [exact H4|]. lia.
Qed.

Lemma fixed_ok : str_ok 0x102bd HPFX = true /\ str_ok 0x1032d DOT = true /\ str_ok 0x10323 [] = true.
Proof.
  pose proof fixed_strs as FS.
  apply andb_prop in FS as [FS _]. apply andb_prop in FS as [FS H3]. apply andb_prop in FS as [H1 H2].
  split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

(** ** Tactics *)
(** Read every [bv_unsigned (Z_to_bv 64 z)] of the goal whose z lia bounds. *)
Local Ltac ulit :=
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia end.

(** Carry one bytes_at fact across a callee whose footprint is in MU. *)
Local Ltac tr1 H MU :=
  let T := fresh "T" in
  pose proof (bytes_at_transport rsegs _ _ _ _ _ H MU) as T;
  specialize (T ltac:(cbn [disjoint_from]; simpl_len; repeat split; lia));
  clear H; rename T into H.

Section Parts.
Variables (sp gp tp s1 s8 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.

Local Abbreviation QE := (QJ sp gp tp s1 s8 F fc m r src pp lo (ent_build r)).
Local Abbreviation S0 := (Z_to_bv 64 (bv_unsigned sp + 0x150)).
Local Abbreviation S7 := (Z_to_bv 64 95).
Local Abbreviation S9 := (Z_to_bv 64 (0xcccccccd * 2^32)).
Local Abbreviation S10 := (Z_to_bv 64 (bv_unsigned sp + 0x118)).
Local Abbreviation S11 := (Z_to_bv 64 10).

(** At 0x13594 (pc = 0x13594) after i turns, or at 0x135d0 (pc = 0x135d0) after the four: s4 = n = |acc|,
    s2 = &parts[i], the part pointers ps at sp + 0x118, ch and its NUL at sp + 0x138, acc at t = sp + 0x150. *)
Definition loop_st (r' ch : list byte) (ps : list Z) (i : nat) (acc : list byte) (pc : Z) : Prop :=
  forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) m1,
    s4 = Z_to_bv 64 (Z.of_nat (length acc)) ->
    s2 = Z_to_bv 64 (bv_unsigned sp + 280 + 8 * Z.of_nat i) ->
    MemC sp m r src pp lo m1 (zeros 104) ->
    bytes_at rsegs m1 (bv_unsigned sp + 136) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
    bytes_at rsegs m1 (bv_unsigned sp + 280) (ptrs_bytes ps) ->
    bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
    bytes_at rsegs m1 (bv_unsigned sp + 336) acc ->
    evt rsegs QE
      (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
               (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) S7 s8 S9 S10 S11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

(** A string of the image as a part: no NUL in it, apart from t, and its bytes with strlen's slack. *)
Lemma img_turn : forall (ch s : list byte) a, str_ok a s = true ->
  ~ In NUL s /\ (a + Z.of_nat (length s) <= bv_unsigned sp + 336 \/ bv_unsigned sp + FRAME_LOCALS <= a) /\
  (forall m1, MemC sp m r src pp lo m1 (zeros 104) -> bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
     exists slack, bytes_at rsegs m1 a (s ++ NUL :: slack) /\
       (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)).
Proof.
  intros ch s a H. pose proof (ep_range sp m r src pp lo HE) as R.
  destruct (str_ok_pure a s H) as (N & RS & A0 & A1).
  split; [exact N|]. split.
  - destruct (img_apart sp m r src pp lo HE a (S (length s)) RS ltac:(lia)) as [X|X]; [left | right]; lia.
  - intros m1 MC _. destruct (str_ok_facts m1 a s (MemC_mem_inv _ _ _ _ _ _ _ _ MC) H) as (B & Sl & _).
    exists (slack_of (a + Z.of_nat (length s) + 1)). split; [exact B | exact Sl].
Qed.

(** One turn 0x13594 -> 0x135cc: s3 = parts[i] = a, l = strlen(a) (no clamp), memcpy(t + n, a, l), n += l. *)
Lemma turn_ok : forall (r' ch : list byte) (ps : list Z) (i : nat) (acc s : list byte) (a pc' : Z),
  (i < 4)%nat -> length ps = 4%nat -> nth i ps 0 = a ->
  pc' = (if (S i =? 4)%nat then 0x135d0 else 0x13594) ->
  (length ch <= 21)%nat -> ~ In NUL s ->
  Z.of_nat (length acc) + Z.of_nat (length s) <= 95 ->
  (a + Z.of_nat (length s) <= bv_unsigned sp + 336 \/ bv_unsigned sp + FRAME_LOCALS <= a) ->
  (forall m1, MemC sp m r src pp lo m1 (zeros 104) -> bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
     exists slack, bytes_at rsegs m1 a (s ++ NUL :: slack) /\
       (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)) ->
  loop_st r' ch ps (S i) (acc ++ s) pc' ->
  loop_st r' ch ps i acc 0x13594.
Proof.
  intros r' ch ps i acc s a pc' Hi Lps Ea Epc Lch Ns Hlen Hdis SRC K.
  unfold loop_st in K.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m1 -> -> MC H88 HPA Hch Hacc.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 432) by reflexivity.
  assert (LP : length (ptrs_bytes ps) = 32%nat) by (rewrite ptrs_bytes_length, Lps; reflexivity).
  destruct (SRC m1 MC Hch) as (slack & Hs & Hsl).
  pose proof Hs as (Ha0 & Ha1 & _). rewrite length_app in Ha1. cbn [length] in Ha1.
  (* 0x13594 ld s3,0(s2) *)
  assert (HR : ov_read_bytes rsegs m1 (wa (bv_unsigned sp + 280 + 8 * Z.of_nat i)) 8 = Some (le8 (Z_to_bv 64 a))).
  { apply bytes_at_read8; [|apply length_le8].
    pose proof (bytes_at_sub m1 _ _ (8 * i) 8 HPA ltac:(lia)) as X.
    rewrite ptrs_bytes_nth, Ea in X by lia.
    replace (bv_unsigned sp + 280 + 8 * Z.of_nat i) with (bv_unsigned sp + 280 + Z.of_nat (8 * i)) by lia.
    exact X. }
  step. clear HR.
  (* mv a0,s3; jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := slack).
    - rewrite unsigned_lit by lia. exact Hs.
    - exact Ns.
    - rewrite unsigned_lit by lia. exact Hsl.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & BS2).
  subst ms'. rewrite unsigned_lit in BS2 by lia.
  apply bytes_at_app in BS2 as [Bs _].
  assert (MC2 : MemC sp m r src pp lo m2 (zeros 104)) by (eapply MemC_call_nil; eassumption).
  tr1 H88 MU2. tr1 HPA MU2. tr1 Hch MU2. tr1 Hacc MU2.
  clear MC MU2 WM2 MI2 Hs Hsl.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x135a0 mv s5,a0; add a0,a0,s4; bgeu s7,a0 (n + l <= 95: no clamp) *)
  do 3 step.
  unfold_cond. ulit. if_true.
  (* 0x135b0 add a0,s0,s4; mv a1,s3; mv a2,s5; jal memcpy *)
  do 4 step.
  destruct (MemC_cells sp m r src pp lo HE m2 (zeros 104) (bv_unsigned sp + 336 + Z.of_nat (length acc)) (length s)
              MC2 ltac:(lia) ltac:(lia)) as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := s) (junk := junk).
    - rewrite unsigned_lit by lia. exact Bs.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id.
      match goal with |- rw_cells _ _ ?A _ =>
        replace A with (bv_unsigned sp + 336 + Z.of_nat (length acc)) by lia end.
      exact CJ.
    - rewrite !unsigned_lit by lia. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC2). }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E & MU3 & WM3 & MI3 & RC3 & _).
  subst ms'. rewrite !unsigned_lit in MU3, RC3 by lia. rewrite Nat2Z.id in RC3.
  apply rw_CB_bytes in RC3 as [B3 _].
  assert (MC3 : MemC sp m r src pp lo m3 (zeros 104)).
  { eapply (MemC_call_hi sp m r src pp lo HE _ m3 _ _ (Z.of_nat (length s)) _ MC2 MU3 WM3 MI3 B3 eq_refl); lia. }
  tr1 H88 MU3. tr1 HPA MU3. tr1 Hch MU3. tr1 Hacc MU3.
  assert (Hacc2 : bytes_at rsegs m3 (bv_unsigned sp + 336) (acc ++ s)).
  { apply bytes_at_app. split; [exact Hacc|].
    match type of B3 with bytes_at _ _ ?D _ =>
      replace (bv_unsigned sp + 336 + Z.of_nat (length acc)) with D by lia end.
    exact B3. }
  clear MC2 MU3 WM3 MI3 B3 Hacc CJ Lj junk Bs.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x135c0 addi s2,s2,8; add s4,s5,s4; addi a0,sp,0x138; bne s2,a0 *)
  do 4 step.
  unfold_cond. ulit.
  destruct (Nat.eqb_spec (S i) 4) as [E4|N4].
  - if_false.
    replace (Z_to_bv 64 0x135d0) with (Z_to_bv 64 pc') by (rewrite Epc; try rewrite E4; reflexivity).
    eapply K; [| | exact MC3 | exact H88 | exact HPA | exact Hch | exact Hacc2].
    + rewrite length_app. f_equal. lia.
    + f_equal. lia.
  - if_true.
    replace (Z_to_bv 64 0x13594) with (Z_to_bv 64 pc')
      by (rewrite Epc; try (apply Nat.eqb_neq in N4; rewrite N4); reflexivity).
    eapply K; [| | exact MC3 | exact H88 | exact HPA | exact Hch | exact Hacc2].
    + rewrite length_app. f_equal. lia.
    + f_equal. lia.
Qed.

(** 0x135d0 -> 0x13600: n < 95, memcpy(e.body, t, n), e.body[n] = 0, type 8, size n + 1. *)
Lemma tail_ok : forall (r' ch : list byte) (ps : list Z) (key : list byte),
  ent_build r = (ent_text key true, r') -> (length key <= 94)%nat ->
  loop_st r' ch ps 4 key 0x135d0.
Proof.
  intros r' ch ps key Eb Lk.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m1 -> -> MC H88 HPA Hch Hkey.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 432) by reflexivity.
  rewrite ent_text_nul in Eb by lia.
  clear HPA Hch.
  (* 0x135d0 addi a0,zero,95; bltu s4,a0 *)
  do 2 step. unfold_cond. ulit. if_true.
  (* 0x135dc addi a1,sp,0x150; addi s2,sp,0x98; mv a0,s2; mv a2,s4; jal memcpy *)
  do 5 step.
  destruct (MemC_cells sp m r src pp lo HE m1 (zeros 104) (bv_unsigned sp + 152) (length key) MC
              ltac:(lia) ltac:(lia)) as (junk & Lj & CJ).
  eapply evt_cut.
  { eapply MCPY with (src := key) (junk := junk).
    - rewrite unsigned_lit by lia. exact Hkey.
    - rewrite unsigned_lit by lia. rewrite Nat2Z.id. reflexivity.
    - rewrite !unsigned_lit by lia. rewrite Nat2Z.id. exact CJ.
    - rewrite !unsigned_lit by lia. lia.
    - exact (MemC_mem_inv _ _ _ _ _ _ _ _ MC). }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & RC2 & _).
  subst ms'. rewrite !unsigned_lit in MU2, RC2 by lia. rewrite Nat2Z.id in RC2.
  apply rw_CB_bytes in RC2 as [B2 _].
  pose proof (MemC_call_e sp m r src pp lo HE _ m2 _ _ (Z.of_nat (length key)) _ MC MU2 WM2 MI2 B2 eq_refl
                ltac:(lia) ltac:(lia)) as MC2.
  replace (bv_unsigned sp + 152 - (bv_unsigned sp + 144)) with 8 in MC2 by lia.
  tr1 H88 MU2.
  clear MC MU2 WM2 MI2 B2 CJ Lj junk Hkey.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x135f0 add a0,s2,s4; addi s3,zero,8; addi s4,s4,1; sb zero,0(a0) *)
  do 3 step.
  pre_store HE (bv_unsigned sp + 152 + Z.of_nat (length key)) 1%nat. step. mstore_e HE (8 + Z.of_nat (length key)).
  eapply (join_13600 sp gp tp s1 s8 F fc m r src pp lo HE) with (h := zeros 8).
  - exact Eb.
  - reflexivity.
  - cbn [e_type]. unfold POD_STRING. lia.
  - cbn [e_size]. rewrite length_app. cbn [length]. lia.
  - reflexivity.
  - cbn [e_size]. rewrite length_app. cbn [length]. f_equal. lia.
  - reflexivity.
  - eapply MemC_e_ext; [eassumption|]. cbn [e_body].
    rewrite (text_head key); [reflexivity | reflexivity | reflexivity | lia | lia].
  - exact H88.
Qed.

(** The four turns and the tail, from 0x13594 with the parts HPFX, ch, the separator and the param stored. *)
Lemma loop_all : forall (r' ch sep prm : list byte) (sa pa : Z),
  ent_build r = (ent_text (HPFX ++ ch ++ sep ++ prm) true, r') ->
  str_ok sa sep = true -> str_ok pa prm = true -> (length sep <= 1)%nat -> (length prm <= 9)%nat ->
  (length ch <= 21)%nat -> ~ In NUL ch ->
  loop_st r' ch [0x102bd; bv_unsigned sp + 312; sa; pa] 0 [] 0x13594.
Proof.
  intros r' ch sep prm sa pa Eb Hsep Hprm Lsep Lprm Lch Nch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 432) by reflexivity.
  assert (LH : length HPFX = 13%nat) by reflexivity.
  destruct fixed_ok as (Hh & _ & _).
  destruct (img_turn ch HPFX 0x102bd Hh) as (N0 & D0 & G0).
  destruct (img_turn ch sep sa Hsep) as (N2 & D2 & G2).
  destruct (img_turn ch prm pa Hprm) as (N3 & D3 & G3).
  (* parts[0] = HPFX *)
  apply (turn_ok r' ch _ 0 [] HPFX 0x102bd 0x13594);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N0 | cbn [length]; lia | exact D0
    | exact G0 |].
  (* parts[1] = ch, on the stack *)
  apply (turn_ok r' ch _ 1 HPFX ch (bv_unsigned sp + 312) 0x13594);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact Nch | lia | left; lia | |].
  { intros m1 MC Hc.
    destruct (stk_bytes_at m1 lo (bv_unsigned sp + FRAME_LOCALS) (bv_unsigned sp + 312 + Z.of_nat (length ch) + 1)
                (23 - length ch) (MemC_stk _ _ _ _ _ _ _ _ MC) ltac:(lia) ltac:(lia)) as (sl & Lsl & Bsl).
    exists sl. split.
    - replace (ch ++ NUL :: sl) with ((ch ++ [NUL]) ++ sl) by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app. split; [exact Hc|].
      rewrite length_app. cbn [length].
      replace (bv_unsigned sp + 312 + Z.of_nat (length ch + 1))
        with (bv_unsigned sp + 312 + Z.of_nat (length ch) + 1) by lia.
      exact Bsl.
    - rewrite Lsl. pose proof (slack_ch (bv_unsigned sp) (Z.of_nat (length ch)) ltac:(lia) ltac:(lia)). lia. }
  (* parts[2] = the separator *)
  apply (turn_ok r' ch _ 2 (HPFX ++ ch) sep sa 0x13594);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N2 | rewrite length_app; lia | exact D2
    | exact G2 |].
  (* parts[3] = param[p % 8] *)
  apply (turn_ok r' ch _ 3 ((HPFX ++ ch) ++ sep) prm pa 0x135d0);
    [lia | reflexivity | reflexivity | reflexivity | exact Lch | exact N3 | rewrite !length_app; lia | exact D3
    | exact G3 |].
  apply tail_ok.
  - rewrite <- !app_assoc. exact Eb.
  - rewrite !length_app. lia.
Qed.

(** 0x1356c: n = 0, a0 = param's address, the four stores parts[0..3], s2 = parts. *)
Lemma head_c : forall (sep prm : list byte) (sa pa : Z) (ch r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) m1,
  ent_build r = (ent_text (HPFX ++ ch ++ sep ++ prm) true, r') ->
  str_ok sa sep = true -> str_ok pa prm = true -> (length sep <= 1)%nat -> (length prm <= 9)%nat ->
  (length ch <= 21)%nat -> ~ In NUL ch ->
  a0 = Z_to_bv 64 0x105f0 -> a1 = Z_to_bv 64 (pa - 0x105f0) -> a2 = Z_to_bv 64 sa ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 136) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) S7 s8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1356c) fc None m1 (seg_rom rsegs)).
Proof.
  intros sep prm sa pa ch r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m1
    Eb Hsep Hprm Lsep Lprm Lch Nch -> -> -> MC H88 Hch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (FL : FRAME_LOCALS = 432) by reflexivity.
  (* 0x1356c mv s4,zero; add a0,a0,a1; auipc a1; addi a1,a1,-0x2b7 *)
  do 4 step.
  (* sd a1,0x118(sp) *)
  pre_store HE (bv_unsigned sp + 280) 8%nat. step. mstore_out HE. rename HW into P0.
  (* addi a1,sp,0x138; sd a1,0x120(sp) *)
  step.
  pre_store HE (bv_unsigned sp + 288) 8%nat. step. mstore_out HE. rename HW into P1.
  (* sd a2,0x128(sp) *)
  pre_store HE (bv_unsigned sp + 296) 8%nat. step. mstore_out HE. rename HW into P2.
  (* sd a0,0x130(sp) *)
  pre_store HE (bv_unsigned sp + 304) 8%nat. step. mstore_out HE. rename HW into P3.
  (* addi s2,sp,0x118 *)
  step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (HPA : bytes_at rsegs mm (bv_unsigned sp + 280) (ptrs_bytes [0x102bd; bv_unsigned sp + 312; sa; pa])) end.
  { rewrite !ptrs_bytes_cons. change (ptrs_bytes []) with (@nil byte). rewrite app_nil_r.
    apply bytes_at_cons8; [exact P0|].
    apply bytes_at_cons8; [replace (bv_unsigned sp + 280 + 8) with (bv_unsigned sp + 288) by lia; exact P1|].
    apply bytes_at_cons8; [replace (bv_unsigned sp + 280 + 8 + 8) with (bv_unsigned sp + 296) by lia; exact P2|].
    replace (bv_unsigned sp + 280 + 8 + 8 + 8) with (bv_unsigned sp + 304) by lia.
    match type of P3 with bytes_at _ _ _ (le8 (Z_to_bv 64 ?z)) =>
      replace (Z_to_bv 64 pa) with (Z_to_bv 64 z) by (f_equal; lia) end.
    exact P3. }
  pose proof (loop_all r' ch sep prm sa pa Eb Hsep Hprm Lsep Lprm Lch Nch) as LA. unfold loop_st in LA.
  eapply LA.
  - reflexivity.
  - f_equal. lia.
  - eassumption.
  - exact H88.
  - exact HPA.
  - exact Hch.
  - apply bytes_at_nil. lia.
Qed.

(** 0x13550: s4 = p << 56; bgez picks "" (bit 7 set, 0x10323) or "." (0x1032d); to 0x1356c. *)
Lemma head_rest : forall (p : Z) (ch r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) m1,
  ent_build r = (ent_text (join_parts [HPFX; ch; if Z.testbit p 7 then [] else DOT;
                                       nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  0 <= p < 256 -> s4 = Z_to_bv 64 p -> a0 = Z_to_bv 64 0x105f0 ->
  a1 = Z_to_bv 64 (nth (Z.to_nat (p mod 8)) (pa_param_s headamp_plain_addrs) 0 - 0x105f0) ->
  (length ch <= 21)%nat -> ~ In NUL ch ->
  MemC sp m r src pp lo m1 (zeros 104) ->
  bytes_at rsegs m1 (bv_unsigned sp + 136) (le8 (Z_to_bv 64 (Z.of_nat (length r')))) ->
  bytes_at rsegs m1 (bv_unsigned sp + 312) (ch ++ [NUL]) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 S0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5
             (Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r'))) S7 s8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13550) fc None m1 (seg_rom rsegs)).
Proof.
  intros p ch r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 m1 Eb Hp -> -> -> Lch Nch MC H88 Hch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Hk : (Z.to_nat (p mod 8) < 8)%nat) by lia.
  pose proof (param_len (Z.to_nat (p mod 8))) as Lprm.
  assert (Hprm : str_ok (nth (Z.to_nat (p mod 8)) (pa_param_s headamp_plain_addrs) 0)
                        (nth (Z.to_nat (p mod 8)) param []) = true).
  { apply strs_ok_nth; [exact param_strs|]. unfold param. rewrite length_map. exact Hk. }
  assert (LH : length HPFX = 13%nat) by reflexivity.
  assert (LD : length DOT = 1%nat) by reflexivity.
  assert (Eb' : ent_build r = (ent_text (HPFX ++ ch ++ (if Z.testbit p 7 then [] else DOT) ++
                                          nth (Z.to_nat (p mod 8)) param []) true, r')).
  { rewrite Eb. rewrite join_parts4; [reflexivity|]. destruct (Z.testbit p 7); cbn [length]; lia. }
  clear Eb.
  destruct fixed_ok as (_ & Hdot & Hemp).
  (* 0x13550 slli s4,s4,56; bgez s4 *)
  do 2 step.
  ulit.
  pose proof (sign_shl56 p Hp) as SG.
  destruct (Z.testbit p 7) eqn:B7.
  - (* bit 7 set: "" at 0x10323; 0x13558 auipc a2; addi a2,a2,-0x235; j 0x1356c *)
    assert (X : bv_signed (Z_to_bv 64 (Z.shiftl p 56)) < 0) by (apply SG; reflexivity).
    clear SG. if_false.
    do 3 step.
    try rewrite B7 in Eb'.
    eapply (head_c [] (nth (Z.to_nat (p mod 8)) param []) 0x10323
              (nth (Z.to_nat (p mod 8)) (pa_param_s headamp_plain_addrs) 0) ch r');
      [exact Eb' | exact Hemp | exact Hprm | cbn [length]; lia | exact Lprm | exact Lch | exact Nch
      | reflexivity | reflexivity | reflexivity | eassumption | exact H88 | exact Hch].
  - (* bit 7 clear: "." at 0x1032d; 0x13564 auipc a2; addi a2,a2,-0x237 *)
    assert (X : 0 <= bv_signed (Z_to_bv 64 (Z.shiftl p 56))).
    { destruct (Z.lt_ge_cases (bv_signed (Z_to_bv 64 (Z.shiftl p 56))) 0) as [Y|Y]; [|exact Y].
      apply SG in Y. try rewrite B7 in Y. discriminate Y. }
    clear SG. if_true.
    do 2 step.
    try rewrite B7 in Eb'.
    eapply (head_c DOT (nth (Z.to_nat (p mod 8)) param []) 0x1032d
              (nth (Z.to_nat (p mod 8)) (pa_param_s headamp_plain_addrs) 0) ch r');
      [exact Eb' | exact Hdot | exact Hprm | lia | exact Lprm | exact Lch | exact Nch
      | reflexivity | reflexivity | reflexivity | eassumption | exact H88 | exact Hch].
Qed.

Lemma parts_ok : parts_at sp gp tp s1 s8 F fc m r src pp lo.
Proof.
  intros p ch r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 m1 Eb Hp -> -> Lch Nch MC H88 Hch.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13538 andi a0,s4,7; auipc a1; slli a2,a0,2; addi a0,a1,0xb4 (0x105f0); add a2,a0,a2 *)
  do 5 step.
  ulit.
  assert (L7 : Z.land p 7 = p mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
  rewrite L7. ulit.
  mmi.
  (* 0x1354c lw a1,0(a2): param's offset from the table, for each p % 8 *)
  assert (Hm : p mod 8 = 0 \/ p mod 8 = 1 \/ p mod 8 = 2 \/ p mod 8 = 3 \/ p mod 8 = 4 \/ p mod 8 = 5 \/
               p mod 8 = 6 \/ p mod 8 = 7) by lia.
  destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]; rewrite Hm; step;
    (eapply head_rest;
      [exact Eb | exact Hp | reflexivity | reflexivity | rewrite Hm; apply bv_eq; vm_compute; reflexivity
      | exact Lch | exact Nch | eassumption | exact H88 | exact Hch]).
Qed.

End Parts.
