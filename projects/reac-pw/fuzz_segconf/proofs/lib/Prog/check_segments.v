(** check_segments (plain image 3776ca44d75c, 0x14788, 39 instructions, frame 48: ra s0 s1 s2 s3 at sp+40 .. sp+8):
    proof of [check_segments_contract] (Prog/check_segments_c.v) from strcmp's contract (Prog/strcmp_c.v, 0x1ebf8).

    Code (plain binary):
      0x14788-0x1479c  frame; s0 = m, s1 = c
      0x147a8-0x147c0  s3 = `lw` c->n (c + 0x2c80), a3 = `lw` m->n (m + 0x2000); bne -> abort
      0x147c4-0x147d4  `lw` c->overflow (c + 0x34d0) vs m->overflow (m + 0x2004); bne -> abort
      0x147d8 s2 = returned; 0x147dc blez s3 -> EXIT
      LOOP 0x147e0  strcmp(s1, s0); bnez -> abort; s3 -= 1; s0 += 256; s1 += 356; bnez s3 -> LOOP
      EXIT 0x14800  beqz s2 -> abort; restore; ret
    The premise (SegModel.check_segments rc mc true) makes every abort branch dead: n and overflow agree, each name
    pair is equal ([names_at], through [bridge_strcmp]), so strcmp returns 0; returned is 1.

    [CsPure] holds the lemmas that do not mention the image; the UBSan walk (lib/U/Prog/check_segments.v) uses them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec strcmp_c check_segments_c.
Import ListNotations.
Open Scope Z_scope.

Module CsPure.

Lemma zs_inj : forall a b : list byte, zs a = zs b -> a = b.
Proof.
  unfold zs. induction a as [|x a IH]; intros [|y b] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.

Lemma zs_nulfree : forall s : list byte, ~ In (Z_to_bv 8 0) s -> nulfree (zs s).
Proof.
  unfold nulfree. intros s H Hin. unfold zs in Hin. apply in_map_iff in Hin as (b & Hb & Hi). apply H.
  replace (Z_to_bv 8 0) with b; [exact Hi|]. apply bv_eq. rewrite Hb. reflexivity.
Qed.

Lemma zs_nul : forall s : list byte, ~ In 0 (zs s) -> ~ In ZERO s.
Proof. intros s H Hin. apply H. exact (in_map (@bv_unsigned 8) s ZERO Hin). Qed.

(** SegModel.strcmp on two NUL-free byte strings is 0 exactly when they are equal (the statement Spec/SegBridge.v
    is to carry under this name). *)
Lemma bridge_strcmp : forall sx sy : list byte, ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  strcmp (zs sx) (zs sy) = 0 <-> sx = sy.
Proof.
  intros sx sy Hx Hy.
  pose proof (strcmp_eq (zs sx) (zs sy) (zs_nulfree sx Hx) (zs_nulfree sy Hy)) as E.
  split.
  - intros H. apply zs_inj. apply leqb_eq. rewrite <- E. apply Z.eqb_eq. exact H.
  - intros ->. apply strcmp_refl.
Qed.

Lemma firstn_zs : forall n (l : list byte), firstn n (zs l) = zs (firstn n l).
Proof. unfold zs. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. f_equal. apply IH. Qed.

Lemma forallb2_nth : forall {A B} (P : A -> B -> bool) l1 l2 d1 d2 i, forallb2 P l1 l2 = true ->
  (i < length l1)%nat -> P (nth i l1 d1) (nth i l2 d2) = true.
Proof.
  intros A B P l1. induction l1 as [|x l1 IH]; intros [|y l2] d1 d2 i H Hi; cbn in H, Hi; try discriminate;
    [lia|].
  apply andb_true_iff in H as [H1 H2]. destruct i as [|i]; cbn; [exact H1|]. apply IH; [exact H2|lia].
Qed.

(** What SegModel.check_segments = true says. *)
Lemma cs_true : forall rc mc ret, check_segments rc mc ret = true ->
  length (rc_seg rc) = length (mc_seg mc) /\ rc_overflow rc = mc_overflow mc /\
  forallb2 (fun s g => strcmp (rs_name s) (ms_name g) =? 0) (rc_seg rc) (mc_seg mc) = true /\ ret = true.
Proof.
  intros rc mc ret H. unfold check_segments in H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2.
  rewrite <- H1, firstn_all in H3. auto.
Qed.

Lemma sx32_small : forall v, 0 <= v < 2 ^ 31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia.
  rewrite bv_swrap_small; [reflexivity|]. change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Section Pure.
Variable segs : list Segment.

Lemma bytes_at_eq : forall m a a' bs, bytes_at segs m a bs -> a = a' -> bytes_at segs m a' bs.
Proof. intros; subst; assumption. Qed.

Lemma bytes_at_sub : forall m a bs k l, bytes_at segs m a bs -> (k + l <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn l (skipn k bs)).
Proof.
  intros m a bs k l H Hl.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn l (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** A char[cap] field holding the C string s: s and its NUL are bytes sx ++ [0] in memory. *)
Lemma cstr_bytes : forall m a f cap s, bytes_at segs m a f -> (cap <= length f)%nat ->
  cstr_enc cap s (firstn cap f) ->
  exists sx, bytes_at segs m a (sx ++ [ZERO]) /\ ~ In ZERO sx /\ zs sx = s.
Proof.
  intros m a f cap s H Hc (_ & Ls & N & E).
  rewrite firstn_zs, firstn_firstn, Nat.min_l in E by lia.
  remember (firstn (S (length s)) f) as g eqn:Hg.
  assert (Lg : length g = S (length s)) by (subst g; rewrite length_firstn; lia).
  destruct (skipn (length s) g) as [|b [|b' r]] eqn:Sk.
  - apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
  - assert (Eg : g = firstn (length s) g ++ [b]) by (rewrite <- Sk; symmetry; apply firstn_skipn).
    rewrite Eg in E. unfold zs in E. rewrite map_app in E. cbn [map] in E.
    apply app_inj_tail in E as [E1 E2].
    assert (Eb : b = ZERO) by (apply bv_eq; rewrite E2; reflexivity). subst b.
    exists (firstn (length s) g). split; [|split].
    + rewrite <- Eg, Hg. rewrite <- (firstn_skipn (S (length s)) f) in H.
      apply bytes_at_app in H as [H _]. exact H.
    + apply zs_nul. unfold zs. rewrite E1. exact N.
    + unfold zs. exact E1.
  - apply (f_equal (@length byte)) in Sk. rewrite length_skipn in Sk. cbn in Sk. lia.
Qed.

(** The name of c->seg[i] (offset 0 of the 356-byte entry) and of m->seg[i] (offset 0 of the 256-byte entry). *)
Lemma rname_at : forall m c bs rc i, bytes_at segs m c bs -> rconf_enc rc bs -> (i < length (rc_seg rc))%nat ->
  exists sx, bytes_at segs m (c + 356 * Z.of_nat i) (sx ++ [ZERO]) /\ ~ In ZERO sx /\
             zs sx = rs_name (nth i (rc_seg rc) rseg_d).
Proof.
  intros m c bs rc i H (L & L32 & HS & _) Hi.
  destruct (HS i Hi) as (Lf & Hn & _).
  unfold SEG_C_SIZE in L.
  assert (B : bytes_at segs m (c + Z.of_nat (356 * i)) (fld (356 * i) 356 bs))
    by (unfold fld; apply bytes_at_sub; [exact H | lia]).
  replace (c + 356 * Z.of_nat i) with (c + Z.of_nat (356 * i)) by lia.
  apply (cstr_bytes m _ _ 16 _ B); [lia | exact Hn].
Qed.

Lemma mname_at : forall m a bs mc i, bytes_at segs m a bs -> mconf_enc mc bs -> (i < length (mc_seg mc))%nat ->
  exists sx, bytes_at segs m (a + 256 * Z.of_nat i) (sx ++ [ZERO]) /\ ~ In ZERO sx /\
             zs sx = ms_name (nth i (mc_seg mc) mseg_d).
Proof.
  intros m a bs mc i H (L & L32 & HS & _) Hi.
  destruct (HS i Hi) as (Lf & Hn & _).
  unfold SEG_M_SIZE in L.
  assert (B : bytes_at segs m (a + Z.of_nat (256 * i)) (fld (256 * i) 256 bs))
    by (unfold fld; apply bytes_at_sub; [exact H | lia]).
  replace (a + 256 * Z.of_nat i) with (a + Z.of_nat (256 * i)) by lia.
  apply (cstr_bytes m _ _ 16 _ B); [lia | exact Hn].
Qed.

(** Under the premise, the i-th names of the two blocks are one byte string sx (strcmp's sx = sy). *)
Lemma names_at : forall m c mb bsc bsm rc mc i,
  bytes_at segs m c bsc -> rconf_enc rc bsc -> bytes_at segs m mb bsm -> mconf_enc mc bsm ->
  check_segments rc mc true = true -> (i < length (mc_seg mc))%nat ->
  exists sx, bytes_at segs m (c + 356 * Z.of_nat i) (sx ++ [ZERO]) /\ ~ In ZERO sx /\
             bytes_at segs m (mb + 256 * Z.of_nat i) (sx ++ [ZERO]).
Proof.
  intros m c mb bsc bsm rc mc i HC EC HM EM CS Hi.
  destruct (cs_true _ _ _ CS) as (Ln & _ & Hf & _).
  destruct (rname_at m c bsc rc i HC EC ltac:(lia)) as (sx & Bx & Nx & Zx).
  destruct (mname_at m mb bsm mc i HM EM Hi) as (sy & By & Ny & Zy).
  pose proof (forallb2_nth _ _ _ rseg_d mseg_d i Hf ltac:(lia)) as P. cbv beta in P.
  apply Z.eqb_eq in P. rewrite <- Zx, <- Zy in P.
  apply (proj1 (bridge_strcmp sx sy Nx Ny)) in P. subst sy.
  exists sx. auto.
Qed.

(** A u32 field at offset k of a block, read as 4 bytes. *)
Lemma cs_rd4 : forall m a bs k v, bytes_at segs m a bs -> 0 <= k -> k + 4 <= Z.of_nat (length bs) ->
  u32_enc v (fldz k 4 bs) -> ov_read_bytes segs m (wa (a + k)) 4 = Some (le4 (Z_to_bv 64 v)).
Proof.
  intros m a bs k v H Hk Hl (_ & E). rewrite <- E. unfold fldz, fld.
  apply bytes_at_read; [exact H | exact Hk |].
  apply Nat2Z.inj_le. rewrite Nat2Z.inj_add, Z2Nat.id by exact Hk. lia.
Qed.

End Pure.

(** Branch tactics: [cs_ntk] for a branch the premise refutes (not taken), [cs_tkn] for one it forces. *)
Ltac cs_ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia
      | clear K ]
  | _ => idtac end.
Ltac cs_tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ clear K
      | exfalso; zify_cond K;
        try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
               ?Z.eqb_neq in K);
        lia ]
  | _ => idtac end.
(** `addiw` of literals leaves a closed [bv_swrap 32 _]: compute it. *)
Ltac cs_swrap := repeat match goal with |- context [bv_swrap 32 ?z] =>
  let v := eval vm_compute in (bv_swrap 32 z) in is_Zlit v; change (bv_swrap 32 z) with v end.

End CsPure.

Import CsPure.

Theorem check_segments_holds : strcmp_contract -> check_segments_contract.
Proof.
  intros SC. unfold check_segments_contract, check_segments_pre, CHECK_SEGMENTS, CHECK_SEGMENTS_STACK.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    rc mc ret (C0 & C16 & (bsc & BC & EC) & AC & M0 & M16 & (bsm & BM & EM) & AM & RV & CS & (ST & SLO & S16 & SRO)
    & MI).
  clear C0 C16 M0 M16 S16.
  destruct (cs_true _ _ _ CS) as (Ln & Ov & _ & ->).
  pose proof EC as (LC & _ & _ & UNc & _ & _ & _ & _ & UOc & _).
  pose proof EM as (LM & N32 & _ & UNm & UOm & _).
  unfold SEG_C_SIZE in LC. unfold SEG_M_SIZE in LM. unfold apart, SEG_C_SIZE, SEG_M_SIZE in AC, AM.
  rewrite Ln in UNc. rewrite Ov in UOc.
  pose proof (bytes_at_bound _ _ _ _ BC) as BCb. pose proof (bytes_at_bound _ _ _ _ BM) as BMb.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. pose proof (bv_unsigned_in_range 64 a0) as RA0.
  pose proof (bv_unsigned_in_range 64 a1) as RA1.
  change (bv_modulus 64) with (2^64) in RSP, RA0, RA1.
  assert (Ea2 : a2 = Z_to_bv 64 1) by (rewrite <- (Z_to_bv_lit_self a2), RV; reflexivity).
  subst a2. clear RV.
  pose proof (Z_to_bv_lit_self sp) as Esp. pose proof (Z_to_bv_lit_self a0) as Ea0.
  pose proof (Z_to_bv_lit_self a1) as Ea1.
  set (Sp := bv_unsigned sp) in *. set (c := bv_unsigned a0) in *. set (mb := bv_unsigned a1) in *.
  rewrite <- Esp, <- Ea0, <- Ea1. clearbody Sp c mb. clear Esp Ea0 Ea1.
  set (n := length (mc_seg mc)) in *.
  assert (En : n = length (mc_seg mc)) by reflexivity. clearbody n.
  pose proof (munch_refl [(Sp - 48, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* prologue: 0x14788 - 0x1479c *)
  zstep. carve_frame 48%nat ST.
  do 5 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?M _) => rename M into M1 end.
  pose proof (cs_rd4 rsegs M1 c bsc 11392 _ BC ltac:(lia) ltac:(lia) UNc) as RN.
  pose proof (cs_rd4 rsegs M1 mb bsm 8192 _ BM ltac:(lia) ltac:(lia) UNm) as MN.
  pose proof (cs_rd4 rsegs M1 c bsc 13520 _ BC ltac:(lia) ltac:(lia) UOc) as RO.
  pose proof (cs_rd4 rsegs M1 mb bsm 8196 _ BM ltac:(lia) ltac:(lia) UOm) as MO.
  assert (NM : forall i, (i < n)%nat -> exists sx, bytes_at rsegs M1 (c + 356 * Z.of_nat i) (sx ++ [ZERO]) /\
      ~ In ZERO sx /\ bytes_at rsegs M1 (mb + 256 * Z.of_nat i) (sx ++ [ZERO])).
  { intros i Hi. apply (names_at rsegs M1 c mb bsc bsm rc mc i BC EC BM EM CS). rewrite <- En. exact Hi. }
  lazymatch goal with |- evt _ ?Q _ => set (Post := Q) end.
  (* EXIT 0x14800: s2 = 1, so beqz falls through; restore and return. *)
  assert (EPI : forall x1 x8 x9 x10 x11 x12 x13 x19 : word,
    evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp t0 t1 t2 x8 x9 x10 x11 x12 x13 a4 a5 a6 a7
                            (Z_to_bv 64 1) x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x14800) fc None M1 (seg_rom rsegs))).
  { intros x1 x8 x9 x10 x11 x12 x13 x19.
    zstep. cs_ntk.
    do 7 zstep.
    release_frame FR ST Sp.
    apply evt_done. unfold Post, ret_void. cbv beta.
    exists t0, t1, t2, x10, x11, x12, x13, a4, a5, a6, a7, t3, t4, t5, t6, M1.
    split; [unfold mkR; repeat f_equal; lia|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [rewrite unsigned_lit by lia; exact ST | exact I]. }
  (* LOOP 0x147e0 after i entries, k = n - i left: s0 = m + 256 i, s1 = c + 356 i, s3 = k. *)
  assert (LOOP : forall k i (x1 x10 x11 x12 x13 w8 w9 w19 : word),
    (i + k = n)%nat -> (0 < k)%nat ->
    w8 = Z_to_bv 64 (mb + 256 * Z.of_nat i) -> w9 = Z_to_bv 64 (c + 356 * Z.of_nat i) ->
    w19 = Z_to_bv 64 (Z.of_nat k) ->
    evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (Sp + -48)) gp tp t0 t1 t2 w8 w9 x10 x11 x12 x13 a4 a5 a6 a7
                            (Z_to_bv 64 1) w19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x147e0) fc None M1 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i x1 x10 x11 x12 x13 w8 w9 w19 Hik Hk E8 E9 E19; [lia|].
    subst w8 w9 w19.
    destruct (NM i ltac:(lia)) as (sx & Bx & Nx & By).
    zstep. zstep. zstep.
    eapply evt_cut.
    { eapply SC with (sx := sx) (sy := sx).
      - eapply bytes_at_eq; [exact Bx | rewrite ?unsigned_lit by lia; lia].
      - exact Nx.
      - eapply bytes_at_eq; [exact By | rewrite ?unsigned_lit by lia; lia].
      - exact Nx. }
    intros ms' (r & y11 & y12 & y13 & -> & Hr).
    assert (R0 : r = Z_to_bv 64 0) by (apply Hr; reflexivity). subst r.
    rewrite ret_pc_even by (try lia; reflexivity).
    zstep. cs_ntk.
    do 3 zstep.
    zstep.
    destruct k as [|k].
    - cs_ntk. eapply EPI.
    - cs_tkn. eapply (IH (S i)); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia]. }
  (* 0x147a0 - 0x147dc *)
  do 6 zstep.
  zstep. clear RN.
  zstep. clear MN.
  rewrite (sx32_small (Z.of_nat n)) by lia.
  zstep. cs_ntk.
  zstep. cs_swrap. zstep.
  zstep. clear RO. zstep. clear MO.
  zstep. cs_ntk.
  zstep.
  zstep.
  destruct (Nat.eq_dec n 0) as [N0|N0].
  - cs_tkn. eapply EPI.
  - cs_ntk. eapply (LOOP n 0%nat); [lia | lia | f_equal; lia | f_equal; lia | f_equal; lia].
Qed.
