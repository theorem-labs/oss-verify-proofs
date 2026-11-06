(* index_of (fuzz_link.c:111-118) and fuzz_if_nametoindex (netlink.h:148-154), PLAIN build: the walk of their one
   contract (lib/Prog/index_of_c.v) at both entries, 0x15120 and 0x137c0 (35 instructions each, a 48-byte frame).
   The two copies are the same code except the auipc/addi pair (both give g_nl = 0x31b80) and the jal to strcmp
   (0x1f274), so the walk is written once, as the tactics `idx_walk` (prologue, count test, early return) and
   `idx_loop` (one iteration of the loop over if_name[0 .. n_if)), and run at each entry; `zstep` fetches and decodes
   every instruction from the image at its own address, so each run is checked against the bytes at that entry.
   g_nl is only read: every load from it is an `ov_read_bytes` fact taken from `nlk_at` / `iftab_at` of the entry
   memory and carried over the frame stores by `munch` (no cells). The index i is symbolic: the loop is a lemma
   over i, by induction on n_if - i, with the register values written as Z expressions in i (`f_equal; lia`
   rewrites them at each back edge). strcmp is called by its released walk (lib/Prog/strcmp.v, strcmp_holds). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf kn_nlk mk_str strcmp_c strcmp index_of_c.
Local Open Scope Z_scope.

(* ==========================================================================
   1. The table is fixed by memory: the Post's (bs, tab, nm) are the Pre's
   ========================================================================== *)

Lemma u_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z H. exact (wz_unsigned z H). Qed.

Lemma u64_at_unique : forall m a p1 p2, u64_at m a p1 -> u64_at m a p2 ->
  0 <= p1 < 2 ^ 64 -> 0 <= p2 < 2 ^ 64 -> p1 = p2.
Proof.
  intros m a p1 p2 H1 H2 R1 R2. unfold u64_at in H1, H2.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le8; reflexivity)) as E.
  assert (X : rdn (le8 (wz p1) ++ []) 0 8 = rdn (le8 (wz p2) ++ []) 0 8) by (rewrite E; reflexivity).
  rewrite !rdn_le8_head in X by reflexivity.
  rewrite !wz_unsigned in X by assumption. exact X.
Qed.

Lemma u32_at_unique : forall m a v1 v2, u32_at m a v1 -> u32_at m a v2 ->
  0 <= v1 < 2 ^ 32 -> 0 <= v2 < 2 ^ 32 -> v1 = v2.
Proof.
  intros m a v1 v2 H1 H2 R1 R2. unfold u32_at in H1, H2.
  pose proof (bytes_at_unique m a _ _ H1 H2 ltac:(rewrite !length_le4; reflexivity)) as E.
  assert (X : rdn (le4 (wz v1) ++ []) 0 4 = rdn (le4 (wz v2) ++ []) 0 4) by (rewrite E; reflexivity).
  rewrite !rdn_le4_head in X by reflexivity.
  rewrite !wz_unsigned in X by lia. rewrite !Z.mod_small in X by lia. exact X.
Qed.

Lemma iftab_at_unique : forall m bs t1 t2, iftab_at m bs t1 -> iftab_at m bs t2 -> t1 = t2.
Proof.
  intros m bs t1 t2 (L1 & _ & H1) (L2 & _ & H2).
  apply list_eq_nth. intros i.
  destruct (nth_error t1 i) as [[n1 x1]|] eqn:E1; destruct (nth_error t2 i) as [[n2 x2]|] eqn:E2.
  - destruct (H1 i n1 x1 E1) as (R1 & p1 & U1 & _ & C1 & V1).
    destruct (H2 i n2 x2 E2) as (R2 & p2 & U2 & _ & C2 & V2).
    pose proof C1 as [(P1a & P1b & _) _]. pose proof C2 as [(P2a & P2b & _) _].
    rewrite length_app in P1b, P2b. cbn [length] in P1b, P2b.
    assert (Ep : p1 = p2) by (apply (u64_at_unique m _ _ _ U1 U2); lia).
    subst p2. rewrite (cstr_at_unique m n1 p1 n2 C1 C2).
    rewrite (u32_at_unique m _ _ _ V1 V2) by lia. reflexivity.
  - exfalso. apply nth_error_None in E2.
    assert (i < length t1)%nat by (apply nth_error_Some; congruence). lia.
  - exfalso. apply nth_error_None in E1.
    assert (i < length t2)%nat by (apply nth_error_Some; congruence). lia.
  - reflexivity.
Qed.

(* ==========================================================================
   2. Lists and reads
   ========================================================================== *)

Lemma skipn_nth_cons : forall {A} (l : list A) i x, nth_error l i = Some x -> skipn i l = x :: skipn (S i) l.
Proof.
  intros A l. induction l as [|y l IH]; intros [|i] x H; cbn in H |- *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

(* a read of bytes the entry memory holds, from a memory that differs from it only in `W` *)
Lemma rd_through : forall W m m1 A l, bytes_at rsegs m A l -> munch W m m1 ->
  disjoint_from W A (Z.of_nat (length l)) -> ov_read_bytes rsegs m1 (wa A) (length l) = Some l.
Proof.
  intros W m m1 A l B MU D.
  pose proof (bytes_at_transport rsegs W m m1 A l B MU D) as B1.
  pose proof (bytes_at_ov_read rsegs m1 A l 0 (length l) B1 ltac:(lia)) as R.
  change (Z.of_nat 0) with 0 in R. change (skipn 0 l) with l in R.
  rewrite Z.add_0_r, firstn_all in R. exact R.
Qed.

(* ==========================================================================
   3. The walk, once, over the entry registers
   ========================================================================== *)

Section Walk.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
          (bs : list byte) (tab : list (list byte * Z)) (nm : list byte).
Local Abbreviation R0 := (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6).
Hypothesis NK : nlk_at m bs.
Hypothesis FA : frame_apart_gnl R0 48.
Hypothesis IT : iftab_at m bs tab.
Hypothesis CS : cstr_at m (bv_unsigned a0) nm.
Hypothesis AF0 : apart_frame R0 48 (bv_unsigned a0) (Z.of_nat (length nm) + 1).
Hypothesis AFT : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
  u64_at m (A_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> apart_frame R0 48 p (Z.of_nat (length n2) + 1).
Hypothesis LO : lo + 48 <= bv_unsigned sp.
Hypothesis SP : bv_unsigned sp < 2 ^ 63.

(* the leaf Post of the contract, at these registers *)
Local Abbreviation QQ := (fun ms' : machine_state => exists (regs' : bvmap 5 word) (m' : word -> option byte),
  ms' = MS regs' F (ret_pc ra) fc None m' (seg_rom rsegs) /\
  regs_preserved R0 regs' /\
  munch ((bv_unsigned sp - 48, bv_unsigned sp) :: writes_nothing R0 m) m m' /\
  wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\
  (forall bs0 tab0 nm0, nlk_at m bs0 -> iftab_at m bs0 tab0 -> cstr_at m (arg R0 0) nm0 ->
     getr regs' 10 = wz (index_of tab0 nm0))).

Lemma idx_post : forall R' : bvmap 5 word, getr R' 10 = wz (index_of tab nm) ->
  forall bs0 tab0 nm0, nlk_at m bs0 -> iftab_at m bs0 tab0 -> cstr_at m (arg R0 0) nm0 ->
  getr R' 10 = wz (index_of tab0 nm0).
Proof.
  intros R' H bs0 tab0 nm0 NK0 IT0 CS0.
  rewrite <- (nlk_at_unique m bs bs0 NK NK0) in IT0.
  rewrite <- (iftab_at_unique m bs tab tab0 IT IT0).
  rewrite <- (cstr_at_unique m nm (bv_unsigned a0) nm0 CS CS0). exact H.
Qed.

(* the loop head (pc L: `ld a0, 0(s3)`) at index i: s0 = name, s1 = n_if - i, s2 = &if_index[i],
   s3 = &if_name[i]; the frame holds ra and s0 .. s3; memory is the entry memory outside the frame *)
Local Abbreviation LOOP L := (forall (m1 : word -> option byte) (j : list byte),
  munch [(bv_unsigned sp - 48, bv_unsigned sp)] m m1 -> wmono rsegs m m1 -> mem_inv rsegs m1 ->
  stk rsegs m1 lo (bv_unsigned sp + -48) ->
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 j; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  forall (k ii : nat) (ra1 x10 x11 x12 x13 v9 v18 v19 : word),
    k = (length tab - ii)%nat -> (ii < length tab)%nat ->
    index_of tab nm = index_of (skipn ii tab) nm ->
    v9 = Z_to_bv 64 (Z.of_nat (length tab) - Z.of_nat ii) ->
    v18 = Z_to_bv 64 (475312 + 4 * Z.of_nat ii) ->
    v19 = Z_to_bv 64 (474672 + 8 * Z.of_nat ii) ->
    evt rsegs QQ
      (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 a0 v9 x10 x11 x12 x13 a4 a5 a6 a7
               v18 v19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 L) fc None m1 (seg_rom rsegs))).

(* the epilogue (5 loads, the frame release, ret) and the Post up to the answer in a0 *)
Ltac idx_ret :=
  zstep; zstep; zstep; zstep; zstep; zstep;
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _, STh : stk _ _ _ (bv_unsigned sp + -48) |- _ =>
    release_frame FRh STh (bv_unsigned sp) end;
  zstep;
  apply evt_done; eexists; eexists; split; [reflexivity|];
  split; [eapply regs_preserved_mkR|];
  split; [cbv [writes_nothing];
          lazymatch goal with MU : munch [(?l1, _)] ?m ?m1 |- munch [(?l2, _)] ?m ?m1 =>
            replace l2 with l1 by lia; exact MU end|];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  apply idx_post.

(* one iteration from the loop head: load if_name[i], call strcmp, then either answer if_index[i] (a hit), take
   the back edge to i + 1 (a miss, more entries), or answer 0 (a miss on the last entry). By induction on
   n_if - i. *)
Ltac idx_loop :=
  intros m1 j MU WM MI ST FR k;
  pose proof FA as FA'; unfold frame_apart_gnl, apart_gnl, A_G_NL, NK_SIZE in FA';
  change (spZ R0) with (bv_unsigned sp) in FA';
  pose proof AF0 as AF0'; unfold apart_frame in AF0'; change (spZ R0) with (bv_unsigned sp) in AF0';
  pose proof IT as (ITn & ITb & ITe);
  induction k as [|k IH]; intros ii ra1 x10 x11 x12 x13 v9 v18 v19 Hk Hi Hinv E9 E18 E19; subst v9 v18 v19;
  [ lia | ];
  destruct (nth_error tab ii) as [[nni ixx]|] eqn:Ei;
  [ | exfalso; apply nth_error_None in Ei; lia ];
  destruct (ITe ii nni ixx Ei) as (Rix & pp & Un & Pnz & Cn & Vn);
  pose proof (AFT ii nni ixx pp Ei Un) as Ap;
  unfold apart_frame in Ap; change (spZ R0) with (bv_unsigned sp) in Ap;
  pose proof Cn as [(Cp0 & Cp1 & _) _]; rewrite length_app in Cp1; cbn [length] in Cp1;
  pose proof (rd_through _ m m1 _ _ Un MU
                ltac:(cbn [disjoint_from]; rewrite length_le8; unfold A_G_NL, NK_IF_NAME; lia)) as HR;
  rewrite length_le8 in HR;
  replace (A_G_NL + NK_IF_NAME + 8 * Z.of_nat ii) with (474672 + 8 * Z.of_nat ii) in HR
    by (unfold A_G_NL, NK_IF_NAME; lia);
  zstep; zstep; zstep;
  eapply evt_cut;
  [ eapply strcmp_holds with (sx := nni) (sy := nm);
    [ first [ rewrite u_lit by lia | unfold wz; rewrite u_lit by lia ];
      eapply bytes_at_transport;
      [ exact (proj1 Cn) | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia ]
    | exact (proj2 Cn)
    | eapply bytes_at_transport;
      [ exact (proj1 CS) | exact MU | cbn [disjoint_from]; rewrite length_app; cbn [length]; lia ]
    | exact (proj2 CS) ]
  | intros ms' (r & y11 & y12 & y13 & -> & Hr);
    rewrite ret_pc_even by (lia || reflexivity);
    zstep;
    case_eq (bv_eqb r (Z_to_bv 64 0)); intros Er; cbv iota;
    [ (* strcmp answered 0: the names are equal, a0 = if_index[i] *)
      apply bv_eqb_true in Er;
      assert (Heq : nni = nm) by (apply Hr; exact Er);
      pose proof (rd_through _ m m1 _ _ Vn MU
                    ltac:(cbn [disjoint_from]; rewrite length_le4; unfold A_G_NL, NK_IF_INDEX; lia)) as HR2;
      rewrite length_le4 in HR2;
      replace (A_G_NL + NK_IF_INDEX + 4 * Z.of_nat ii) with (475312 + 4 * Z.of_nat ii) in HR2
        by (unfold A_G_NL, NK_IF_INDEX; lia);
      zstep; rewrite sx32_wz by lia;
      idx_ret;
      rewrite Hinv, (skipn_nth_cons tab ii _ Ei); cbn [index_of];
      rewrite (proj2 (bl_eqb_iff nni nm) Heq); reflexivity
    | (* a miss *)
      apply bv_eqb_false in Er;
      assert (Hne : nni <> nm) by (intros E; apply Er; rewrite (proj2 Hr E); reflexivity);
      assert (Hinv' : index_of tab nm = index_of (skipn (S ii) tab) nm)
        by (rewrite Hinv, (skipn_nth_cons tab ii _ Ei); cbn [index_of];
            destruct (bl_eqb nni nm) eqn:Eb; [apply bl_eqb_iff in Eb; contradiction | reflexivity]);
      zstep; zstep; zstep; zstep;
      (* bnez s1: taken while n_if - (i + 1) <> 0 *)
      let K := fresh "K" in if_cases K; zify_cond K;
      [ (* the back edge to the loop head at index i + 1 *)
        eapply (IH (S ii)); [ lia | lia | exact Hinv' | word_eq_tac | word_eq_tac | word_eq_tac ]
      | (* the last entry missed: a0 = 0 *)
        zstep; zstep; idx_ret; rewrite Hinv', skipn_all2 by lia; reflexivity ] ] ].

(* n_if (u32 at g_nl + 0x42670) read from the entry memory *)
Ltac idx_bn :=
  let B := fresh "B" in let En := fresh "En" in
  destruct (nlk_split_u32 m bs NK_N_IF 1 NK ltac:(nk_nums; lia) ltac:(nk_nums; lia)) as (_ & [[_ B] _] & _ & _);
  destruct IT as [En _];
  change (cells_bytes (u32_cells bs NK_N_IF 1)) with (le4 (wz (nk_n_if bs)) ++ []) in B;
  rewrite app_nil_r, En in B; exact B.

(* the prologue, the count test, the empty-table return, and the jump into the loop lemma LP *)
Ltac idx_walk LP :=
  intros MI ST;
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU;
  pose proof (wmono_refl rsegs m) as WM;
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia);
  pose proof FA as FA'; unfold frame_apart_gnl, apart_gnl, A_G_NL, NK_SIZE in FA';
  change (spZ R0) with (bv_unsigned sp) in FA';
  pose proof IT as (ITn & ITb & _);
  lazymatch goal with STh : stk _ _ _ _ |- _ => carve_frame 48%nat STh end;
  do 10 zstep;
  assert (BN : bytes_at rsegs m 475632 (le4 (wz (Z.of_nat (length tab))))) by idx_bn;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (rd_through _ m mc 475632 _ BN MU ltac:(cbn [disjoint_from]; rewrite length_le4; lia)) as HR;
    rewrite length_le4 in HR
  end;
  zstep; rewrite sx32_wz by lia;
  zstep;
  rewrite bv_lts_zero_l, wz_unsigned by lia;
  replace (Z.of_nat (length tab) <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia);
  destruct (Z.ltb_spec 0 (Z.of_nat (length tab))) as [Hpos|Hz]; cbn [andb negb]; cbv iota;
  [ do 5 zstep;
    lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -48) _ |- _ =>
      apply (LP _ _ MU WM MI ST FRh (length tab) 0%nat) end;
    [ lia | lia | reflexivity | unfold wz; f_equal; lia | reflexivity | reflexivity ]
  | assert (E0 : tab = []) by (apply length_zero_iff_nil; lia);
    zstep; zstep; idx_ret; rewrite E0; reflexivity ].

(* index_of at 0x15120: loop head 0x15164 *)
Lemma loop_P : LOOP 86372.
Proof. idx_loop. Qed.

Lemma walk_P : mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs QQ (MS R0 F (Z_to_bv 64 86304) fc None m (seg_rom rsegs)).
Proof. idx_walk loop_P. Qed.

(* fuzz_if_nametoindex at 0x137c0: loop head 0x13804 *)
Lemma loop_N : LOOP 79876.
Proof. idx_loop. Qed.

Lemma walk_N : mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) ->
  evt rsegs QQ (MS R0 F (Z_to_bv 64 79808) fc None m (seg_rom rsegs)).
Proof. idx_walk loop_N. Qed.

End Walk.

(* ==========================================================================
   4. The contract at each entry
   ========================================================================== *)

(* `leaf` from the walk over named registers: the Pre, Wr and Post read registers only through `getr` *)
Ltac idx_top WALK :=
  apply leaf_intro;
  [ intros r1 r2 m E H; cbv beta in H |- *;
    unfold frame_apart_gnl, apart_frame, apart_gnl, arg, spZ in *; rewrite <- ?E; exact H
  | intros r1 r2 m E; reflexivity
  | intros r1 r2 m q1 q2 m' E E' H bs tab nm NK IT CS; cbv beta in H |- *;
    rewrite <- E'; apply (H bs tab nm NK IT); unfold arg in *; rewrite E; exact CS
  | unfold leaf_walk;
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo;
    cbv zeta; intros (bs & tab & nm & NK & FA & IT & NZ & CS & AF0 & AFT) MI ST LO SP;
    rewrite mkR_a0 in CS, AF0;
    eapply WALK; eassumption ].

Theorem index_of_holds : index_of_contract_P.
Proof. unfold index_of_contract_P, index_of_contract, INDEX_OF. idx_top walk_P. Qed.

Theorem fuzz_if_nametoindex_holds : fuzz_if_nametoindex_contract.
Proof. unfold fuzz_if_nametoindex_contract, index_of_contract, FUZZ_IF_NAMETOINDEX. idx_top walk_N. Qed.
