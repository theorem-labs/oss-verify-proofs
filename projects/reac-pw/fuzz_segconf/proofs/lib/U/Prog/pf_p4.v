(** reac-pw/fuzz_segconf: piece P4 of reac_segconf_parse_file, UBSan build (image 1696d6c34ffd; unstripped twin
    afc060e3cc9c): the header branch and the inlined seg_get, from the cut HDR (0x154d4)
    to HREF (0x1569c: not closed, text after, unknown), CLR (0x156a0: too long, past the bound, no name) or CNAME
    (0x15b78, an accepted header).
    Statement: lib/U/Prog/reac_segconf_parse_file_pieces_c.v, S_P4 := forall n, H_HREF n -> H_CLR n -> H_CNAME n ->
    H_HDR n. The plain twin is lib/Prog/pf_p4.v (the same structure); the build-independent part is
    lib/Prog/pfB_p4_spine.v, the kit lib/Prog/pfB_facts.v and lib/U/Prog/pfB_kit.v.

    Code (UBSan binary): c is in the frame slot sp + 0x90, the spill slots hold &c->overflow (0x10), 0x2c80
    (0x18), &c->gen (0x38), ~c (0x48) and &c->n (0x58); s1 = ' ', s4 = '\t', s5 = -1.
    - 0x154dc strchr(line, ']'); NULL -> F_notclosed, line[ci + 1] <> 0 -> F_after: a0-a3 set at 0x15578, `j` HREF.
      Trap 0x154e4 (close == -1).
    - 0x155a0 `*close = 0`; trap 0x155a4 (line == -1); 0x155ac trim(line + 1) -> body (s6); 0x155c4
      strncasecmp(body, "segment", 7) <> 0 -> F_unknown at 0x155cc (a3 = body), `j` HREF. Trap 0x15744 (body > -8);
      body[7] in {s4, s1}, else F_unknown.
    - 0x15758 trim(body + 7) -> name (s7); name[0] = 0 -> refuse(F_noname) at 0x15a88; 0x1576c strlen(name) >= 16 ->
      refuse(F_toolong, name, 15) at 0x15790; both then `j` CLR.
    - seg_get 0x15a90: n = c->n; n <= 0 -> the new entry; else the slot sp + 0x88 := n (0x15aa8), the search loop at
      0x15ac0 (s6 = 356 i, s9 = 0x2c80 - 356 i, s4 = c + 356 i, s8 = 356 n; traps 0x15ac0 (s9 == 0) and 0x15ac8
      (~c < 356 i)) with strcmp at 0x15ad4; not found: n reloaded from the slot (0x15aec), n >= 32 -> overflow++ and
      refuse(F_bound, name, 32) at 0x15790, then CLR; else c->n = n + 1 (0x15b88; traps 0x15b8c (32 < n), 0x15b9c
      (~c < 356 n)), memset(c + 356 n, 0, 356) at 0x15bb4 and snprintf(c + 356 n, 16, "%s", name) at 0x15bcc.
    - found at i: seen_gen == gen -> refuse(F_twice, name) at 0x15bf8; then 0x15bfc the slot sp + 0x88 := &c->seg[i],
      trap 0x15c04 (cur & 3), seen_gen = gen (0x15c14) and the CNAME arguments (sp + 0x3a8, 16, "%s", name), `j`
      CNAME. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require Import SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strchr_c trim_c strncasecmp_c strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strcmp_c memset_c printf_facts_c snprintf_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_facts pfB_p4_spine.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import pfB_kit.
Import ListNotations.
Open Scope Z_scope.

Ltac ret_lit := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.

Lemma p4_refuse_refused : forall c l f a, rc_refused (refuse c l f a) = rc_refused c + 1.
Proof. intros c l f a. unfold refuse; cbv zeta. destruct (8 <=? _); [reflexivity|]. destruct (_ || _); reflexivity. Qed.

Lemma p4_ci_pos : forall l ci, hd0 l = LBR -> strchr l RBR = Some ci -> (1 <= ci)%nat.
Proof.
  intros [|x r] ci H1 H2; cbn in H1; [discriminate|]. subst x. cbn in H2.
  destruct (strchr r 93); cbn in H2; inversion H2; lia.
Qed.

Lemma p4_nth0 : forall l, nth 0 l 0 = hd0 l.
Proof. intros [|x l]; reflexivity. Qed.

Lemma p4_cstr_bytes0 : forall segs m a l, cstr_at segs m a l ->
  bytes_at segs m a (zb l ++ [ZERO]) /\ ~ In (Z_to_bv 8 0) (zb l) /\ zs (zb l) = l /\ Forall zbyte l.
Proof.
  intros segs m a l (bs & sl & B & Hz & Hn & Hs).
  assert (E : zb l = bs) by (rewrite <- Hz; apply p4_zb_zs).
  rewrite E. split; [|split; [|split]].
  - change (bs ++ ZERO :: sl) with (bs ++ [ZERO] ++ sl) in B. rewrite app_assoc in B.
    apply bytes_at_app in B as [B _]. exact B.
  - apply nul_free_bytes. rewrite Hz. exact Hn.
  - exact Hz.
  - rewrite <- Hz. apply p4_zs_byte.
Qed.

Lemma p4_slice_len : forall l ci, (1 <= ci)%nat -> (ci <= length l)%nat -> length (slice 1 ci l) = (ci - 1)%nat.
Proof. intros l ci H1 H2. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma p4_bv_eqb_false : forall r : word, r <> Z_to_bv 64 0 -> bv_eqb r (Z_to_bv 64 0) = false.
Proof.
  intros r H. destruct (bv_eqb r (Z_to_bv 64 0)) eqn:E; [|reflexivity]. exfalso. apply H.
  unfold bv_eqb in E. apply Z.eqb_eq in E. apply bv_eq. exact E.
Qed.

(** "segment" and "%s" in .rodata (the strncasecmp literal 0x10313, snprintf's format 0x104e0). *)
Lemma seg_lit_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x10313 (zb S_segment ++ [ZERO]).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI | lia | change (length (zb S_segment ++ [ZERO])) with 8%nat; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma seg_lit_nul : ~ In (Z_to_bv 8 0) (zb S_segment).
Proof. intros H. vm_compute in H. repeat (destruct H as [H|H]; [discriminate H|]). exact H. Qed.

Lemma fmt_s_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104e0 (pf_bytes ([37; 115] ++ [0])).
Proof.
  intros m MI. apply (ro_bytes_at rsegs m); [exact MI | lia | change (length (pf_bytes ([37; 115] ++ [0]))) with 3%nat; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(** `lw` sign-extends a u32 field; `sw` stores its low 4 bytes. *)
Lemma p4_le4_eqm : forall x y : word, bv_unsigned x mod 2 ^ 32 = bv_unsigned y mod 2 ^ 32 -> le4 x = le4 y.
Proof.
  intros x y H. unfold le4. rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned x) 32) by lia.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned y) 32) by lia. rewrite H. reflexivity.
Qed.

Lemma p4_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. apply bv_swrap_small.
  change (bv_half_modulus 32) with (2 ^ 31). lia.
Qed.

Lemma p4_le4_inc : forall r, 0 <= r < 2 ^ 32 ->
  le4 (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 r)) + 1)) = le4 (Z_to_bv 64 (r + 1)).
Proof.
  intros r Hr. apply p4_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma p4_le4_sx32 : forall r, 0 <= r < 2 ^ 32 -> le4 (sx32 (Z_to_bv 64 r)) = le4 (Z_to_bv 64 r).
Proof.
  intros r Hr. apply p4_le4_eqm. unfold sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma p4_sx32_eqb : forall x y, 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 ->
  bv_eqb (sx32 (Z_to_bv 64 x)) (sx32 (Z_to_bv 64 y)) = (x =? y).
Proof.
  intros x y Hx Hy. destruct (Z.eqb_spec x y) as [->|NE].
  - unfold bv_eqb. apply Z.eqb_refl.
  - unfold bv_eqb, sx32. rewrite !unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
    change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
    apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma p4_lts_small : forall x y, 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  bv_lts (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof.
  intros x y Hx Hy. unfold bv_lts. rewrite !zb_signed, !unsigned_lit by lia.
  rewrite (proj2 (Z.ltb_lt x (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt y (2 ^ 63))) by lia. reflexivity.
Qed.

(** ~c as the spill slot sp + 0x48 holds it. *)
Lemma p4_not_c : forall c, pf_not c = Z_to_bv 64 (18446744073709551615 - c).
Proof.
  intros c. unfold pf_not. apply bv_eq. rewrite !unsigned_lit_wrap.
  replace (18446744073709551615 - c) with ((- c - 1) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.

(** seg_get's loop bound: `sgtz`, `neg` and `and` give n itself for 0 < n. *)
Lemma p4_lx : forall y, 0 <= y < 2 ^ 63 -> Z.lxor y 9223372036854775808 = y + 9223372036854775808.
Proof. intros y Hy. change 9223372036854775808 with (2 ^ 63). apply zb_lxor_pow2_small; lia. Qed.

Lemma p4_mask : forall x, 0 < x < 2 ^ 31 ->
  Z.land ((0 - Z.b2z (9223372036854775808 <? Z.lxor x 9223372036854775808)) mod 18446744073709551616) x = x.
Proof.
  intros x Hx. rewrite p4_lx by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [Z.b2z].
  change ((0 - 1) mod 18446744073709551616) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Section P4Gen.
Variable segs : list Segment.

Lemma p4_rw_cb : forall m A bs, bytes_at segs m A bs -> wr_at segs m A (Z.of_nat (length bs)) ->
  rw_cells segs m A [CB (length bs) bs].
Proof.
  intros m A bs B W. split; [split|].
  - cbn [cells_wf cell_wf]. split; [reflexivity | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact W.
Qed.

Lemma p4_cb_bytes : forall m A n bs, rw_cells segs m A [CB n bs] ->
  bytes_at segs m A bs /\ length bs = n /\ wr_at segs m A (Z.of_nat n).
Proof.
  intros m A n bs ((Wf & B) & W). cbn [cells_wf cell_wf] in Wf. cbn [cells_bytes cbytes cells_size csize] in B, W.
  rewrite app_nil_r in B. rewrite Nat.add_0_r in W. split; [exact B|]. split; [exact (proj1 Wf) | exact W].
Qed.

Lemma p4_wr_sub : forall m a n a' n', wr_at segs m a n -> a <= a' -> 0 <= n' -> a' + n' <= a + n ->
  wr_at segs m a' n'.
Proof.
  intros m a n a' n' (H0 & H1 & H) Ha Hn Hl. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a' + i) with (a + (a' - a + i)) by lia. apply H. lia.
Qed.

Lemma p4_bytes_sub : forall m a bs k n, bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros m a bs k n H L.
  rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H as [H _]. exact H.
Qed.

(** A C string with its slack cut to the bytes up to the next 8-byte boundary. *)
Lemma p4_cstr_min : forall m a s, cstr_at segs m a s ->
  exists sl, bytes_at segs m a (zb s ++ ZERO :: sl) /\ Z.of_nat (length sl) = (- (a + Z.of_nat (length s) + 1)) mod 8.
Proof.
  intros m a s (bs & sl & B & Hz & Hn & Hs).
  pose proof (Z.mod_pos_bound (- (a + Z.of_nat (length s) + 1)) 8 ltac:(lia)) as MB.
  set (k := Z.to_nat ((- (a + Z.of_nat (length s) + 1)) mod 8)).
  exists (firstn k sl). split.
  - rewrite <- Hz, p4_zb_zs. rewrite <- (firstn_skipn k sl) in B.
    replace (bs ++ ZERO :: firstn k sl ++ skipn k sl) with ((bs ++ ZERO :: firstn k sl) ++ skipn k sl) in B
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in B as [B _]. exact B.
  - rewrite length_firstn. unfold k. lia.
Qed.

(** An 8-byte frame slot, as `ld` reads it. *)
Lemma p4_rd_slot : forall m a w, bytes_at segs m a (le8 w) -> ov_read_bytes segs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w B. pose proof (bytes_at_ov_read segs m a _ 0 8 B ltac:(rewrite length_le8; lia)) as H.
  replace (a + Z.of_nat 0) with a in H by lia. rewrite skipn_O, firstn_all2 in H by (rewrite length_le8; lia).
  exact H.
Qed.
End P4Gen.

(** One variadic argument of a refusal P4 makes: a C string in parse_file's frame, or an int in [0, 2^31). *)
Definition pf_va (m : word -> option byte) (sp : Z) (r : word) (a : arg) : Prop :=
  match a with
  | AS x => sp <= bv_unsigned r /\ bv_unsigned r + Z.of_nat (length x) + 8 <= sp + PARSE_FILE_FRAME /\
            cstr_at rsegs m (bv_unsigned r) x
  | AI z => 0 <= z < 2 ^ 31 /\ bv_unsigned r = z
  end.
Fixpoint pf_vas (m : word -> option byte) (sp : Z) (rs : list word) (args : list arg) : Prop :=
  match args, rs with
  | [], _ => True
  | a :: args', r :: rs' => pf_va m sp r a /\ pf_vas m sp rs' args'
  | _ :: _, [] => False
  end.

Ltac in_href := cbn [In]; repeat (first [left; reflexivity | right]).
Ltac in_fmts := unfold PF_FMTS; repeat (first [left; reflexivity | right]).
Ltac uns := repeat first [ rewrite Z.add_0_r | rewrite Z_to_bv_bv_unsigned | rewrite unsigned_lit by lia ];
  first [ assumption | reflexivity | lia ].

Ltac p4_wp := unfold pf_Wp, PF_LO, PF_FLAGS, PF_CURSLOT, PF_CSLOT, PF_SCRATCH, PF_NAMEBUF, RC_PARSE_W, RC_N,
  RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN, PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in *.

Ltac p4_kill K := exfalso; zify_cond K; rewrite ?unsigned_lit in K by lia;
  repeat match goal with H : bv_unsigned ?w = _ |- _ =>
    is_var w; tryif constr_eq H K then fail else rewrite H in K end; lia.
Ltac p4_br := try lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let K := fresh "K" in destruct cnd eqn:K; [ try p4_kill K | try p4_kill K ]
  end.
Ltac p4_ks := repeat match goal with
  | K : _ = true |- _ => progress (zify_cond K)
  | K : _ = false |- _ => progress (zify_cond K)
  end.

(** The UBSan alignment check `andi r,s,3`: s mod 4 = 0 (M4) makes it 0. *)
Ltac chk4 M4 :=
  match goal with |- context [Z.land ?x 3] =>
    let L := fresh "L3" in
    assert (L : Z.land x 3 = 0)
      by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; rewrite ?unsigned_lit by lia; exact M4);
    rewrite L; clear L
  end.

Section P4.
Hypothesis HSTRCHR : strchr_contract.
Hypothesis HTRIM : trim_contract.
Hypothesis HNCASE : strncasecmp_contract.
Hypothesis HSTRLEN : strlen_contract.
Hypothesis HREFUSE : refuse_contract.
Hypothesis HSTRCMP : strcmp_contract.
Hypothesis HMEMSET : memset_contract.
Hypothesis HSNPRINTF : snprintf_contract.
Variable n : nat.
Hypothesis HHREF : H_HREF n.
Hypothesis HCLR : H_CLR n.
Hypothesis HCNAME : H_CNAME n.

(** The cut HDR's state: what no instruction of P4 changes. *)
Variables (sp gp tp : word) (F0 : bvmap 5 word) (fc0 : bv 32) (m0 : word -> option byte) (lo : Z) (v : pf_sv)
  (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
  (lp : Z) (s0 s1 s2 s3 s5 s10 s11 : word).
Hypothesis HCTX : pf_ctx m0 fc0 (bv_unsigned sp) lo v c t s o ln d n.
Hypothesis HST : pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)).
Hypothesis HREGS : pf_regs s0 s1 s2 s3 s5 s10 s11 (t + Z.of_nat (pf_next s o)) (ln + 1).
Hypothesis HLINE : cstr_at rsegs m0 lp (pf_tline s o).
Hypothesis HINB : pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o).
Hypothesis HLBR : hd0 (pf_tline s o) = LBR.

Local Notation spz := (bv_unsigned sp).
Local Notation L := (pf_tline s o).

Definition Post : machine_state -> Prop :=
  pf_fin v sp gp tp F0 m0 lo c (r_lines (r_header rc nm (ln + 1) L) (ln + 1) (lines (skipn (pf_next s o) s))).

Definition Fok (F : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get F k = reg_get F0 k.

Local Notation MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 F pc fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F pc fc None m (seg_rom rsegs)).

(** ** The numbers *)
Lemma p4_nums : 344200 <= lo /\ lo + 7088 <= spz + 1056 /\ spz + 1056 < 2 ^ 63 /\ spz mod 16 = 0 /\
  0 < c /\ c mod 16 = 0 /\ (c + 16616 <= lo \/ spz + 1056 <= c) /\ c + 16616 <= 2 ^ 64 /\
  spz + 424 <= lp /\ lp + Z.of_nat (length L) < spz + 936.
Proof.
  destruct HCTX as ((C0 & C16 & AP & _ & (_ & _ & _ & IL & SPH) & _ & (ST & DEP & SP16 & _) & _) & _).
  destruct HLINE as (bs & sl & B & _). pose proof (bytes_at_bound rsegs _ _ _ B) as BB.
  destruct HINB as [I1 I2].
  unfold apart, SEG_C_SIZE, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, PF_BUF in *.
  cbn [SA SEG_UBSAN sa_img_end] in IL.
  destruct ST as (ST0 & _).
  assert (Cpos : 0 <= c).
  { destruct HST as ((bc & BC & _) & _). exact (proj1 (bytes_at_bound rsegs _ _ _ BC)). }
  assert (Cb : c + 16616 <= 2 ^ 64).
  { destruct HST as ((bc & BC & (Lc & _)) & _). pose proof (bytes_at_bound rsegs _ _ _ BC) as H.
    unfold SEG_C_SIZE in Lc. lia. }
  repeat split; try lia.
Qed.

(** ** Facts of the cut *)
Lemma env0 : pf_env m0 fc0 spz lo c v.
Proof. exact (proj1 HCTX). Qed.

Lemma rc0 : rconf_at rsegs m0 c rc.
Proof. exact (proj1 HST). Qed.

Lemma pm0 : pf_mem m0 m0 spz lo c.
Proof. exact (pf_mem_refl _ _ _ _ _ _ _ env0 rc0). Qed.

Lemma fok0 : Fok F0.
Proof. intros k _. reflexivity. Qed.

Lemma frm0_0 : frm0 fc0.
Proof. destruct env0 as (_ & _ & _ & _ & (FRM & _) & _). exact FRM. Qed.

Lemma p4_le65535 : forall k, (k <= 65535)%nat -> Z.of_nat k <= 65535.
Proof. intros k H. apply Nat2Z.inj_le in H. exact H. Qed.

Lemma ln_rng : 0 <= ln + 1 < 2 ^ 31.
Proof.
  destruct HCTX as (_ & (_ & _ & Ls & _) & _ & _ & _ & (Hle & _ & Hd & Hln)). apply p4_le65535 in Ls. lia.
Qed.

Lemma regs_u : bv_unsigned s3 = ln + 1 /\ s3 = Z_to_bv 64 (ln + 1) /\ bv_unsigned s1 = 32 /\
  s1 = Z_to_bv 64 32 /\ bv_unsigned s5 = 18446744073709551615.
Proof.
  pose proof ln_rng as R.
  destruct HREGS as (_ & E3 & _ & E1 & E5 & _).
  split; [rewrite E3; rewrite unsigned_lit by lia; reflexivity|]. split; [exact E3|].
  split; [rewrite E1; reflexivity|]. split; [exact E1|].
  rewrite E5. vm_compute. reflexivity.
Qed.

Lemma cnt_o : pf_cnt rc (length (skipn o s)).
Proof. exact (proj2 (proj2 (proj2 HST))). Qed.

(** refuse's counters at a call site of P4 (the line has at least one byte left). *)
Lemma cnt0 : forall rc1, rc_refused rc1 = rc_refused rc -> rc_overflow rc1 <= rc_overflow rc + 1 -> pf_cnt rc1 0.
Proof.
  intros rc1 H1 H2. destruct HCTX as (_ & _ & _ & Ho & _). destruct HST as (_ & _ & _ & (C1 & C2)).
  rewrite length_skipn in C1, C2. unfold pf_cnt. lia.
Qed.

Lemma cnt_ref : forall rc1 f args, rc_refused rc1 = rc_refused rc -> rc_overflow rc1 <= rc_overflow rc + 1 ->
  pf_cnt (refuse rc1 (ln + 1) f args) (length (skipn (pf_next s o) s)).
Proof.
  intros rc1 f args H1 H2. destruct HCTX as (_ & _ & _ & Ho & _). destruct HST as (_ & _ & _ & CNT).
  eapply pfb_cnt_next; [exact Ho | exact CNT | rewrite p4_refuse_refused; lia |].
  destruct (refuse_proj rc1 (ln + 1) f args) as (_ & Hov & _). lia.
Qed.

Lemma cnt_upd : forall rc2 i f, rc_refused rc2 <= rc_refused rc + 1 -> rc_overflow rc2 <= rc_overflow rc + 1 ->
  pf_cnt (r_upd rc2 i f) (length (skipn (pf_next s o) s)).
Proof.
  intros rc2 i f H1 H2. destruct HCTX as (_ & _ & _ & Ho & _). destruct HST as (_ & _ & _ & CNT).
  eapply pfb_cnt_next; [exact Ho | exact CNT | exact H1 | exact H2].
Qed.

Lemma p4_u8 : forall x, 0 <= x < 256 -> bv_unsigned (Z_to_bv 8 x) = x.
Proof. intros x Hx. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia. Qed.

Lemma line_bytes : Forall zbyte L /\ ~ In 0 L.
Proof.
  destruct HLINE as (bs & sl & _ & Hz & Hn & _). split; [rewrite <- Hz; apply p4_zs_byte | exact Hn].
Qed.

Lemma nth_byte : forall l k, Forall zbyte l -> 0 <= nth k l 0 < 256.
Proof.
  intros l k H. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
  - pose proof (proj1 (Forall_forall zbyte l) H (nth k l 0) (nth_In l 0 Hk)) as Hb. exact Hb.
  - rewrite nth_overflow by exact Hk. lia.
Qed.

(** The frame's present stack: the callees' premises. *)
Lemma stk_at : forall m, pf_mem m0 m spz lo c -> stk rsegs m lo spz.
Proof. intros m PM. exact (pf_stk_sp _ _ _ _ _ PM). Qed.

Lemma rom_below : forall a, lo <= a < spz -> seg_rom rsegs (wa a) = None.
Proof.
  intros a Ha. destruct env0 as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & NR) & _). apply NR.
  unfold PARSE_FILE_FRAME. lia.
Qed.

(** The cut's context in a later memory of the piece. *)
Lemma p4_ctx_mem : forall m fc, pf_mem m0 m spz lo c -> frm0 fc -> pf_ctx m fc spz lo v c t s o ln d n.
Proof.
  intros m fc PM FC. destruct HCTX as (ENV & TX & SPL & R).
  split; [exact (pf_env_mem _ _ _ _ _ _ _ _ ENV PM FC)|].
  split; [exact (pf_text_mem _ _ _ _ _ _ _ TX PM)|].
  split; [exact (pf_spill_mem _ _ _ _ _ SPL PM) | exact R].
Qed.

(** The c block is writable (blk_noimg), whatever its bytes hold. *)
Lemma p4_c_wr : forall m bs, pf_mem m0 m spz lo c -> bytes_at rsegs m c bs -> Z.of_nat (length bs) = SEG_C_SIZE ->
  wr_at rsegs m c SEG_C_SIZE.
Proof.
  intros m bs PM B Lb. pose proof (proj1 PM) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & BN & _).
  pose proof p4_nums as (_ & _ & _ & _ & N5 & _ & _ & N8 & _).
  pose proof B as (Hc & Hb & H). rewrite Lb in Hb. unfold SEG_C_SIZE in *.
  split; [lia|]. split; [lia|]. intros j Hj.
  specialize (H (Z.to_nat j) ltac:(lia)). rewrite Z2Nat.id in H by lia.
  destruct (nth_error bs (Z.to_nat j)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  unfold wview. destruct (m (wa (c + j))) as [b'|] eqn:Em; [discriminate|].
  unfold mrd in H. rewrite Em in H.
  rewrite (pf_blk_rom c 16616 (c + j) BN ltac:(lia) ltac:(lia)) in H. discriminate.
Qed.

Lemma p4_vas_ok : forall m rc1 va args, pf_mem m0 m spz lo c -> (length (rc_refusal rc1) <= 8)%nat ->
  pf_vas m spz va args -> va_args_ok rsegs m (pf_vaW spz c rc1) va args.
Proof.
  intros m rc1 va args PM Lk. revert va. induction args as [|a args IH]; intros va H; [destruct va; exact I|].
  destruct va as [|r va]; [destruct H|]. destruct H as [Ha Hr]. split; [|exact (IH va Hr)].
  destruct a as [x|z]; cbn [pf_va] in Ha.
  - destruct Ha as (H1 & H2 & H3). exact (pf_va_frame m spz lo c rc1 r x (proj1 PM) Lk H3 H1 H2).
  - exact Ha.
Qed.

(** ** The frame slots P4 loads (pf_spill, and the c slot sp + 0x90) *)
Lemma rd_sp : forall m k, pf_mem m0 m spz lo c -> (k < 10)%nat ->
  ov_read_bytes rsegs m (wa (spz + 16 + 8 * Z.of_nat k)) 8 =
  Some (le8 (nth k [Z_to_bv 64 (c + RC_OVERFLOW); Z_to_bv 64 (RSEG_SIZE * 32); Z_to_bv 64 PF_BOX_WORD;
     Z_to_bv 64 PF_TAP_WORD; pf_not (spz + PF_LOWM); Z_to_bv 64 (c + RC_GEN); pf_not (spz + PF_LOW); pf_not c;
     Z_to_bv 64 (c + RC_READING); Z_to_bv 64 (c + RC_N)] (Z_to_bv 64 0))).
Proof.
  intros m k PM Hk. destruct HCTX as (_ & _ & SPL & _).
  destruct (pf_spill_mem _ _ _ _ _ SPL PM) as (S1 & _ & _).
  exact (p4_saved_read rsegs m (spz + 16) _ k S1 ltac:(cbn [length]; lia)).
Qed.

Lemma rd_ovf : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 16)) 8 = Some (le8 (Z_to_bv 64 (c + 13520))).
Proof.
  intros m PM. pose proof (rd_sp m 0 PM ltac:(lia)) as H. cbn [nth] in H.
  replace (spz + 16 + 8 * Z.of_nat 0) with (spz + 16) in H by lia. exact H.
Qed.

Lemma rd_sz : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 24)) 8 = Some (le8 (Z_to_bv 64 11392)).
Proof.
  intros m PM. pose proof (rd_sp m 1 PM ltac:(lia)) as H. cbn [nth] in H.
  replace (spz + 16 + 8 * Z.of_nat 1) with (spz + 24) in H by lia. exact H.
Qed.

Lemma rd_gen : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 56)) 8 = Some (le8 (Z_to_bv 64 (c + 16608))).
Proof.
  intros m PM. pose proof (rd_sp m 5 PM ltac:(lia)) as H. cbn [nth] in H.
  replace (spz + 16 + 8 * Z.of_nat 5) with (spz + 56) in H by lia. exact H.
Qed.

Lemma rd_notc : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 72)) 8 = Some (le8 (Z_to_bv 64 (18446744073709551615 - c))).
Proof.
  intros m PM. pose proof (rd_sp m 7 PM ltac:(lia)) as H. cbn [nth] in H.
  replace (spz + 16 + 8 * Z.of_nat 7) with (spz + 72) in H by lia. rewrite p4_not_c in H. exact H.
Qed.

Lemma rd_n : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 88)) 8 = Some (le8 (Z_to_bv 64 (c + 11392))).
Proof.
  intros m PM. pose proof (rd_sp m 9 PM ltac:(lia)) as H. cbn [nth] in H.
  replace (spz + 16 + 8 * Z.of_nat 9) with (spz + 88) in H by lia. exact H.
Qed.

Lemma rd_c : forall m, pf_mem m0 m spz lo c ->
  ov_read_bytes rsegs m (wa (spz + 144)) 8 = Some (le8 (Z_to_bv 64 c)).
Proof.
  intros m PM. destruct HCTX as (_ & _ & SPL & _).
  destruct (pf_spill_mem _ _ _ _ _ SPL PM) as (_ & _ & B). unfold PF_CSLOT in B.
  exact (p4_rd_slot rsegs m (spz + 144) _ B).
Qed.

(** ** The exits *)
Lemma ex_href : forall m F fc f fp xp x (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  In (f, fp) [(F_notclosed, PF_STR_NOTCLOSED); (F_after, PF_STR_AFTER); (F_unknown, PF_STR_UNKNOWN);
              (F_outside, PF_STR_OUTSIDE)] ->
  a0 = Z_to_bv 64 c -> a1 = Z_to_bv 64 (ln + 1) -> a2 = Z_to_bv 64 fp -> a3 = Z_to_bv 64 xp ->
  cstr_at rsegs m xp x -> pf_inb (spz + PF_BUF) xp x ->
  r_header rc nm (ln + 1) L = (refuse rc (ln + 1) f [AS x], None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 PF_PC_HREF) fc m).
Proof.
  intros m F fc f fp xp x ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC HF
    E0 E1 E2 E3 XA XB HH.
  eapply evt_mono.
  - eapply (HHREF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc nm o ln d f fp xp x);
      [exact (p4_ctx_mem _ _ PM FC) | | exact HREGS | exact HF | exact E0 | exact E1 | exact E2 | exact E3
      | exact XA | exact XB].
    split; [exact RC|]. split; [exact I|]. split; [|exact cnt_o].
    destruct HST as (_ & _ & NM & _). exact (pf_nm_at_mem _ _ _ _ _ _ NM PM).
  - intros ms' H. unfold Post. rewrite HH. eapply pf_fin_weaken; [exact FK | exact PM | exact H].
Qed.

Lemma ex_clr : forall m F fc rc' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F ->
  rconf_at rsegs m c rc' -> pf_cnt rc' (length (skipn (pf_next s o) s)) ->
  r_header rc nm (ln + 1) L = (rc', None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 PF_PC_CLR) fc m).
Proof.
  intros m F fc rc' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC CNT HH.
  eapply evt_mono.
  - eapply (HCLR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc' nm o ln d);
      [exact (p4_ctx_mem _ _ PM FC) | | exact HREGS].
    split; [exact RC|]. split; [exact I|]. split; [|exact CNT].
    destruct HST as (_ & _ & NM & _). exact (pf_nm_at_mem _ _ _ _ _ _ NM PM).
  - intros ms' H. unfold Post. rewrite HH. eapply pf_fin_weaken; [exact FK | exact PM | exact H].
Qed.

Lemma ex_cname : forall m F fc rc' gi np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F ->
  rconf_at rsegs m c rc' -> (gi < length (rc_seg rc'))%nat -> pf_cnt rc' (length (skipn (pf_next s o) s)) ->
  pf_curslot m spz c (Some gi) ->
  cstr_at rsegs m np name -> pf_inb (spz + PF_BUF) np name -> (length name <= 15)%nat ->
  a0 = Z_to_bv 64 (spz + PF_NAMEBUF) -> a1 = Z_to_bv 64 16 -> a2 = Z_to_bv 64 PF_STR_S -> a3 = Z_to_bv 64 np ->
  r_header rc nm (ln + 1) L = (rc', Some gi, snprintf_s 16 F_s [AS name]) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 PF_PC_CNAME) fc m).
Proof.
  intros m F fc rc' gi np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC Hgi CNT
    CS NA NB NL E0 E1 E2 E3 HH.
  eapply evt_mono.
  - eapply (HCNAME ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo v c t s rc' nm o ln d gi np name);
      [exact (p4_ctx_mem _ _ PM FC) | | exact HREGS | exact CS
      | exact E0 | exact E1 | exact E2 | exact E3 | exact NA | exact NB | exact NL].
    split; [exact RC|]. split; [exact Hgi|]. split; [|exact CNT].
    destruct HST as (_ & _ & NM & _). exact (pf_nm_at_mem _ _ _ _ _ _ NM PM).
  - intros ms' H. unfold Post. rewrite HH. eapply pf_fin_weaken; [exact FK | exact PM | exact H].
Qed.

(** ** refuse *)
(** The bytes refuse writes are among the piece's. *)
Lemma refuse_W_sub : forall rc1, (length (rc_refusal rc1) <= 8)%nat ->
  sub_fp (refuse_W spz c rc1) (pf_Wp spz c).
Proof.
  intros rc1 Hk. unfold sub_fp. intros x Hx.
  unfold refuse_W, pf_Wp, PF_LO, PF_FLAGS, PF_CURSLOT, PF_CSLOT, PF_SCRATCH, PF_NAMEBUF, RC_PARSE_W,
    PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, RC_REFUSED, RC_NREF, refusal_addr, RC_REFUSAL,
    RC_REFUSAL_LEN, RC_N, RC_OVERFLOW, RC_READING, RC_GEN in *.
  destruct (length (rc_refusal rc1) <? 8)%nat eqn:E; cbn [outside app] in *;
    [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; repeat split; try lia; exact I.
Qed.

(** refuse(c, lineno, f, args) from its entry, then the code at the return point R. *)
Lemma ref_at : forall (R : Z) m F fc rc1 f fp args (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word),
  0 <= R < 2 ^ 64 -> R mod 2 = 0 ->
  bv_unsigned a0 = c -> bv_unsigned a1 = ln + 1 -> bv_unsigned a2 = fp ->
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc1 -> pf_cnt rc1 0 ->
  In (f, fp) PF_FMTS -> conv_kinds f = map arg_is_s args -> pf_vas m spz [a3; a4; a5; a6; a7] args ->
  (forall m' F' fc' (x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
     pf_mem m0 m' spz lo c -> frm0 fc' -> Fok F' -> rconf_at rsegs m' c (refuse rc1 (ln + 1) f args) ->
     munch (refuse_W spz c rc1) m m' ->
     evt rsegs Post (MSt (Z_to_bv 64 R) x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 s4 s6 s7 s8 s9 x3 x4 x5 x6
                         F' (Z_to_bv 64 R) fc' m')) ->
  evt rsegs Post (MSt (Z_to_bv 64 R) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 REFUSE) fc m).
Proof.
  intros R m F fc rc1 f fp args t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 HR HR2 Ha0 Ha1 Ha2
    PM FC FK RC CNT HF HK HVA K.
  assert (Lk : (length (rc_refusal rc1) <= 8)%nat) by (destruct RC as (bs & _ & (_ & _ & _ & _ & H & _)); exact H).
  pose proof (pf_env_mem _ _ _ _ _ _ _ _ env0 PM FC) as ENV.
  pose proof (pf_mem_refl _ _ _ _ _ _ _ ENV RC) as PMm.
  pose proof (pf_refuse_pre m m fc spz lo c v rc1 (ln + 1) f fp 0 [a3; a4; a5; a6; a7] args ENV PMm FC RC CNT
                ln_rng HF HK (p4_vas_ok m rc1 _ args PM Lk HVA)) as PRE.
  eapply evt_cut.
  { eapply HREFUSE with (lo := PF_LO spz) (ln := ln + 1) (rc := rc1) (f := f) (args := args).
    rewrite Ha0, Ha1, Ha2. exact PRE. }
  intros ms' PO.
  destruct PO as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & F' & fc' & m' &
                  E & FC' & FK' & MU & WM & MI & TM & ST & RC').
  subst ms'. rewrite ret_pc_even by (try lia; exact HR2).
  rewrite Ha0 in MU, RC'.
  apply K; [| exact FC' | | exact RC' | exact MU].
  - eapply pf_mem_call; [exact PM | exact (refuse_W_sub rc1 Lk) | exact MU | exact WM | exact MI].
  - intros k Hk. rewrite (FK' k Hk). exact (FK k Hk).
Qed.

(** 0x15578: the HREF arguments (c from its slot, lineno, the line) for F_notclosed and F_after, `j` HREF. *)
Lemma site_578 : forall m F fc f fp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc -> cstr_at rsegs m lp L ->
  In (f, fp) [(F_notclosed, PF_STR_NOTCLOSED); (F_after, PF_STR_AFTER); (F_unknown, PF_STR_UNKNOWN);
              (F_outside, PF_STR_OUTSIDE)] ->
  a2 = Z_to_bv 64 fp ->
  r_header rc nm (ln + 1) L = (refuse rc (ln + 1) f [AS L], None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 lp) s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15578) fc m).
Proof.
  intros m F fc f fp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC LA HF E2 HH.
  destruct regs_u as (U3 & E3 & _).
  pose proof (rd_c m PM) as RS.
  zstep. clear RS. zstep. zstep. zstep.
  eapply ex_href; [exact PM | exact FC | exact FK | exact RC | exact HF | reflexivity | exact E3 | exact E2
                  | reflexivity | exact LA | exact HINB | exact HH].
Qed.

(** 0x155cc: the HREF arguments for F_unknown (a3 = body), `j` HREF. *)
Lemma site_unk : forall m F fc ci bp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  cstr_at rsegs m bp (p4_body L ci) -> pf_inb (spz + PF_BUF) bp (p4_body L ci) ->
  r_header rc nm (ln + 1) L = (refuse rc (ln + 1) F_unknown [AS (p4_body L ci)], None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 bp) s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x155cc) fc m).
Proof.
  intros m F fc ci bp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC BA BI HH.
  destruct regs_u as (U3 & E3 & _).
  pose proof (rd_c m PM) as RS.
  zstep. zstep. zstep. clear RS. zstep. zstep. zstep.
  eapply ex_href with (f := F_unknown) (fp := PF_STR_UNKNOWN);
    [exact PM | exact FC | exact FK | exact RC | in_href | reflexivity | exact E3 | reflexivity
    | reflexivity | exact BA | exact BI | exact HH].
Qed.

(** 0x15784: refuse(c, lineno, f, name, z) for F_toolong (15) and F_bound (32), then 0x15794 `j` CLR. *)
Lemma site_784 : forall m F fc rc1 f fp z np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc1 ->
  rc_refused rc1 = rc_refused rc -> rc_overflow rc1 <= rc_overflow rc + 1 ->
  a2 = Z_to_bv 64 fp -> 0 <= fp < 2 ^ 64 -> In (f, fp) PF_FMTS -> conv_kinds f = [true; false] ->
  a4 = Z_to_bv 64 z -> 0 <= z < 2 ^ 31 ->
  cstr_at rsegs m np name -> spz <= np -> np + Z.of_nat (length name) + 8 <= spz + PARSE_FILE_FRAME ->
  r_header rc nm (ln + 1) L = (refuse rc1 (ln + 1) f [AS name; AI z], None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 np) s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15784) fc m).
Proof.
  intros m F fc rc1 f fp z np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC HR1 HO1
    E2 Hfp HF HK E4 Hz NA B1 B2 HH.
  subst a2 a4. pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  destruct regs_u as (U3 & E3 & _). unfold PARSE_FILE_FRAME in B2.
  pose proof (rd_c m PM) as RS.
  zstep. clear RS. zstep. zstep. zstep.
  eapply (ref_at 0x15794) with (rc1 := rc1) (f := f) (args := [AS name; AI z]);
    [lia | reflexivity | uns | uns | uns | exact PM | exact FC | exact FK | exact RC | apply cnt0; [exact HR1 | exact HO1]
    | exact HF | exact HK | | ].
  - cbn [pf_vas pf_va].
    assert (E : bv_unsigned (Z_to_bv 64 np) = np) by (rewrite unsigned_lit by lia; reflexivity).
    assert (Ez : bv_unsigned (Z_to_bv 64 z) = z) by (rewrite unsigned_lit by lia; reflexivity).
    unfold PARSE_FILE_FRAME. rewrite ?E, ?Ez. split; [split; [lia|]; split; [lia | exact NA]|].
    split; [split; [lia | reflexivity] | exact I].
  - intros m' F' fc' x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 PM' FC' FK' RC' _.
    zstep.
    eapply ex_clr; [exact PM' | exact FC' | exact FK' | exact RC' | apply cnt_ref; [exact HR1 | exact HO1] | exact HH].
Qed.

(** 0x15a78: refuse(c, lineno, F_noname), then 0x15a8c `j` CLR. *)
Lemma site_a78 : forall m F fc (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  r_header rc nm (ln + 1) L = (refuse rc (ln + 1) F_noname [], None, nm) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 F (Z_to_bv 64 0x15a78) fc m).
Proof.
  intros m F fc ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  destruct regs_u as (U3 & E3 & _).
  pose proof (rd_c m PM) as RS.
  zstep. zstep. zstep. clear RS. zstep. zstep.
  eapply (ref_at 0x15a8c) with (rc1 := rc) (f := F_noname) (args := []);
    [lia | reflexivity | uns | uns | uns | exact PM | exact FC | exact FK | exact RC | apply cnt0; [reflexivity | lia]
    | in_fmts | vm_compute; reflexivity | exact I | ].
  intros m' F' fc' x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 PM' FC' FK' RC' _.
  zstep.
  eapply ex_clr; [exact PM' | exact FC' | exact FK' | exact RC' | apply cnt_ref; [reflexivity | lia] | exact HH].
Qed.

(** 0x15bfc: the slot sp + 0x88 := &c->seg[i], the alignment trap, seen_gen = gen (R:210), then the CNAME arguments
    (sp + 0x3a8, 16, "%s", name) and `j` CNAME. *)
Lemma w_seen : forall m F fc rc2 i np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc2 -> (i < length (rc_seg rc2))%nat ->
  rc_refused rc2 <= rc_refused rc + 1 -> rc_overflow rc2 = rc_overflow rc ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat ->
  r_header rc nm (ln + 1) L = (r_upd rc2 i (rs_with_gen (rc_gen rc2)), Some i, snprintf_s 16 F_s [AS name]) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (c + 356 * Z.of_nat i)) s6 (Z_to_bv 64 np)
                      s8 s9 t3 t4 t5 t6 F (Z_to_bv 64 0x15bfc) fc m).
Proof.
  intros m F fc rc2 i np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC Hi HR2 HO2
    NA B1 B2 Hl HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  assert (M4 : (c + 356 * Z.of_nat i) mod 4 = 0) by lia.
  (* sd s4, 0x88(sp) *)
  pose proof (pf_frame_store_ok m0 m spz lo c (spz + 136) 8 PM ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia)) as HS.
  pose proof HS as HS'. cbv delta [wa] in HS'.
  zstep. clear HS'.
  set (W8 := le8 (Z_to_bv 64 (c + 356 * Z.of_nat i))) in *.
  assert (LW8 : length W8 = 8%nat) by apply length_le8.
  set (m1 := write_to_mem m (Z_to_bv 64 (spz + 136)) W8).
  assert (PM1 : pf_mem m0 m1 spz lo c).
  { apply (pf_mem_store m0 m spz lo c (spz + 136) W8 PM); rewrite ?LW8.
    - lia.
    - lia.
    - p4_wp. cbn [inside]. right. right. left. lia.
    - exact HS. }
  assert (CS1 : bytes_at rsegs m1 (spz + 136) W8)
    by exact (bytes_at_write_same rsegs m (spz + 136) W8 ltac:(lia) ltac:(rewrite LW8; lia)).
  assert (HB1 : bytes_at rsegs m1 c bs)
    by exact (bytes_at_write_other rsegs m (spz + 136) W8 c bs HB ltac:(lia) ltac:(rewrite LW8; lia)
                ltac:(rewrite LW8, HL; lia)).
  assert (RC1 : rconf_at rsegs m1 c rc2) by (exists bs; split; [exact HB1 | exact HE]).
  assert (NA1 : cstr_at rsegs m1 np name).
  { eapply pfb_cstr_at_munch; [exact NA | apply p4_munch_write; rewrite ?LW8; lia |].
    rewrite LW8. cbn [disjoint_from]. split; [lia | exact I]. }
  clearbody m1. clear HB HS.
  (* andi a0, s4, 3; bnez a0 -> trap *)
  zstep. chk4 M4. zstep. p4_br.
  (* seen_gen = gen *)
  destruct (p4_read_gen rsegs m1 c bs rc2 HB1 HE) as [GR RG].
  pose proof (rd_gen m1 PM1) as RS.
  zstep. clear RS. zstep. clear RG.
  pose proof (p4_rd_slot rsegs m1 (spz + 136) _ CS1) as RS.
  zstep. clear RS.
  pose proof (p4_c_wr m1 bs PM1 HB1 HL) as WC.
  pose proof (wr_at_store_ok rsegs m1 c SEG_C_SIZE (356 * Z.of_nat i + 352) 4 WC ltac:(lia)
                ltac:(unfold SEG_C_SIZE; lia)) as HS.
  pose proof HS as HS'. cbv delta [wa] in HS'.
  zstep. clear HS'.
  rewrite (p4_le4_sx32 (rc_gen rc2) GR).
  set (m2 := write_to_mem m1 (Z_to_bv 64 (c + (356 * Z.of_nat i + 352))) (le4 (Z_to_bv 64 (rc_gen rc2)))).
  assert (HB2 : bytes_at rsegs m2 c (upd_bytes bs (356 * i + 352) (le4 (Z_to_bv 64 (rc_gen rc2))))).
  { pose proof (bytes_at_write_inside rsegs m1 c bs (356 * Z.of_nat i + 352) (le4 (Z_to_bv 64 (rc_gen rc2))) HB1
      ltac:(lia) ltac:(rewrite length_le4; lia)) as H.
    replace (Z.to_nat (356 * Z.of_nat i + 352)) with (356 * i + 352)%nat in H by lia. exact H. }
  assert (RC2 : rconf_at rsegs m2 c (r_upd rc2 i (rs_with_gen (rc_gen rc2)))).
  { exists (upd_bytes bs (356 * i + 352) (le4 (Z_to_bv 64 (rc_gen rc2)))). split; [exact HB2|].
    apply p4_rconf_seen; [exact HE | exact Hi | exact GR]. }
  assert (PM2 : pf_mem m0 m2 spz lo c).
  { apply (pf_mem_store m0 m1 spz lo c (c + (356 * Z.of_nat i + 352)) (le4 (Z_to_bv 64 (rc_gen rc2))) PM1);
      rewrite ?length_le4.
    - lia.
    - lia.
    - p4_wp. cbn [inside]. right. right. right. right. left. lia.
    - exact HS. }
  assert (NA2 : cstr_at rsegs m2 np name).
  { eapply pfb_cstr_at_munch; [exact NA1 | apply p4_munch_write; [lia | rewrite length_le4; lia] |].
    rewrite length_le4. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (CS2 : pf_curslot m2 spz c (Some i)).
  { unfold pf_curslot, PF_CURSLOT, pf_cur_ptr, rseg_addr, RSEG_SIZE.
    exact (bytes_at_write_other rsegs m1 (c + (356 * Z.of_nat i + 352)) (le4 (Z_to_bv 64 (rc_gen rc2)))
             (spz + 136) W8 CS1 ltac:(lia) ltac:(rewrite length_le4; lia) ltac:(rewrite length_le4, LW8; lia)). }
  zstep. zstep. zstep. zstep. zstep. zstep.
  eapply ex_cname with (rc' := r_upd rc2 i (rs_with_gen (rc_gen rc2))) (gi := i) (np := np) (name := name);
    [exact PM2 | exact FC | exact FK | exact RC2 | unfold r_upd, r_set_segs; cbn [rc_seg]; rewrite upd_nth_len; exact Hi
    | apply cnt_upd; lia | exact CS2 | exact NA2 | split; unfold PF_BUF; lia | lia | reflexivity | reflexivity
    | reflexivity | reflexivity | exact HH].
Qed.

(** 0x15bd4: the entry i holds name; seen_gen == gen -> refuse(F_twice, name) at 0x15bf8; then 0x15bfc. *)
Lemma w_found : forall m F fc i np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc -> (i < length (rc_seg rc))%nat ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat -> r_find_go (rc_seg rc) name 0 = Some i ->
  r_header rc nm (ln + 1) L = p4_get rc nm (ln + 1) name ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (c + 356 * Z.of_nat i)) s6 (Z_to_bv 64 np)
                      s8 s9 t3 t4 t5 t6 F (Z_to_bv 64 0x15bd4) fc m).
Proof.
  intros m F fc i np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC Hi NA B1 B2 Hl HF HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  destruct (p4_read_seen rsegs m c bs rc i HB HE Hi) as [SR RSn].
  destruct (p4_read_gen rsegs m c bs rc HB HE) as [GR RG].
  pose proof (rd_gen m PM) as RS.
  zstep. clear RSn. zstep. clear RS. zstep. clear RG.
  zstep. rewrite p4_sx32_eqb by lia.
  destruct (Z.eq_dec (rs_seen_gen (nth i (rc_seg rc) rseg_d)) (rc_gen rc)) as [EQ|NE].
  - p4_br.
    destruct regs_u as (U3 & E3 & _).
    pose proof (rd_c m PM) as RS.
    zstep. zstep. zstep. clear RS. zstep. zstep. zstep.
    eapply (ref_at 0x15bfc) with (rc1 := rc) (f := F_twice) (args := [AS name]);
      [lia | reflexivity | uns | uns | uns | exact PM | exact FC | exact FK | exact RC
      | apply cnt0; [reflexivity | lia] | in_fmts
      | vm_compute; reflexivity | | ].
    + cbn [pf_vas pf_va]. split; [|exact I].
      assert (E : bv_unsigned (Z_to_bv 64 np) = np) by (unfold PF_BUF in *; rewrite unsigned_lit by lia; reflexivity).
      unfold PARSE_FILE_FRAME, PF_BUF in *. rewrite ?E. split; [lia|]. split; [lia | exact NA].
    + intros m' F' fc' x0 x1 x2 y0 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 PM' FC' FK' RC' MU'.
      destruct (refuse_proj rc (ln + 1) F_twice [AS name]) as (Hsg & Hov & _).
      eapply w_seen with (rc2 := refuse rc (ln + 1) F_twice [AS name]) (i := i);
        [exact PM' | exact FC' | exact FK' | exact RC' | rewrite Hsg; exact Hi | rewrite p4_refuse_refused; lia
        | exact Hov | | exact B1 | exact B2 | exact Hl |].
      * eapply pfb_cstr_at_munch; [exact NA | exact MU' |].
        assert (Lk : (length (rc_refusal rc) <= 8)%nat) by (destruct HE as (_ & _ & _ & _ & H & _); exact H).
        unfold refuse_W, REFUSE_STACK, PRINTF_K, RC_REFUSED, refusal_addr, RC_REFUSAL, RC_REFUSAL_LEN, RC_NREF,
          PF_BUF in *.
        destruct (length (rc_refusal rc) <? 8)%nat eqn:EK; cbn [disjoint_from app];
          [apply Nat.ltb_lt in EK | apply Nat.ltb_ge in EK]; repeat split; try lia; exact I.
      * rewrite HH. exact (p4_get_seen rc nm (ln + 1) name i HF EQ).
  - p4_br.
    eapply w_seen with (rc2 := rc) (i := i); [exact PM | exact FC | exact FK | exact RC | exact Hi | lia | reflexivity
      | exact NA | exact B1 | exact B2 | exact Hl |].
    rewrite HH. exact (p4_get_unseen rc nm (ln + 1) name i HF NE).
Qed.

(** 0x15b80 (a2 = n < 32): c->n = n + 1, memset(&seg[n], 0, 356), snprintf(seg[n].name, 16, "%s", name), then
    0x15bfc. *)
Lemma w_new : forall m F fc np name (ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc -> (length (rc_seg rc) < 32)%nat ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat -> r_find_go (rc_seg rc) name 0 = None ->
  r_header rc nm (ln + 1) L = p4_get rc nm (ln + 1) name ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc)))) a3 a4 a5 a6 a7 s4 s6
                      (Z_to_bv 64 np) s8 s9 t3 t4 t5 t6 F (Z_to_bv 64 0x15b80) fc m).
Proof.
  intros m F fc np name ra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC Hlt NA B1 B2 Hl HF HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  destruct regs_u as (U3 & E3 & U1 & E1 & U5).
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  set (N := length (rc_seg rc)) in *.
  zstep.
  pose proof (rd_n m PM) as RS.
  zstep. clear RS.
  pose proof (p4_c_wr m bs PM HB HL) as WC.
  pose proof (wr_at_store_ok rsegs m c SEG_C_SIZE 11392 4 WC ltac:(lia) ltac:(unfold SEG_C_SIZE; lia)) as HS.
  pose proof HS as HS'. cbv delta [wa] in HS'.
  zstep. clear HS'.
  assert (Hnn : ~ In 0 name) by (destruct NA as (? & ? & _ & _ & H & _); exact H).
  pose proof (p4_cstr_bytes0 rsegs m np name NA) as (_ & _ & _ & NBY).
  set (W4 := le4 (Z_to_bv 64 (Z.of_nat N + 1))) in *.
  assert (LW4 : length W4 = 4%nat) by apply length_le4.
  set (m1 := write_to_mem m (Z_to_bv 64 (c + 11392)) W4).
  set (bs1 := upd_bytes bs (Z.to_nat 11392) W4).
  assert (HB1 : bytes_at rsegs m1 c bs1) by exact (bytes_at_write_inside rsegs m c bs 11392 W4 HB ltac:(lia) ltac:(lia)).
  assert (L1 : length bs1 = length bs) by (apply upd_bytes_length; lia).
  assert (PM1 : pf_mem m0 m1 spz lo c).
  { apply (pf_mem_store m0 m spz lo c (c + 11392) W4 PM); rewrite ?LW4.
    - lia.
    - lia.
    - p4_wp. cbn [inside]. right. right. right. right. left. lia.
    - exact HS. }
  assert (NA1 : cstr_at rsegs m1 np name).
  { eapply pfb_cstr_at_munch; [exact NA | apply p4_munch_write; lia |].
    rewrite LW4. cbn [disjoint_from]. split; [lia | exact I]. }
  assert (EB1 : bs1 = upd_bytes bs (Z.to_nat 11392) W4) by reflexivity.
  clearbody m1 bs1. clear HB HS WC.
  (* bltu s1, a2 -> trap (32 < n) *)
  zstep. p4_br.
  zstep. zstep.
  pose proof (rd_notc m1 PM1) as RS.
  zstep. clear RS.
  (* bltu a1, a0 -> trap (~c < 356 n) *)
  zstep. p4_br.
  pose proof (rd_c m1 PM1) as RS.
  zstep. clear RS.
  zstep.
  set (D := c + Z.of_nat N * 356) in *.
  zstep. zstep. zstep. zstep.
  pose proof PM1 as (_ & _ & _ & MI1 & _ & _).
  set (junk := firstn 356 (skipn (356 * N) bs1)).
  assert (Lj : length junk = 356%nat) by (unfold junk; rewrite length_firstn, length_skipn; lia).
  assert (BJ : bytes_at rsegs m1 D junk).
  { pose proof (p4_bytes_sub rsegs m1 c bs1 (356 * N) 356 HB1 ltac:(lia)) as H.
    replace (c + Z.of_nat (356 * N)) with D in H by (unfold D; lia). exact H. }
  assert (WJ : wr_at rsegs m1 D (Z.of_nat (length junk))).
  { pose proof (p4_c_wr m1 bs1 PM1 HB1 ltac:(rewrite L1; exact HL)) as W.
    eapply p4_wr_sub; [exact W | unfold D; lia | lia | rewrite Lj; unfold D, SEG_C_SIZE; lia]. }
  pose proof (p4_rw_cb rsegs m1 D junk BJ WJ) as RWJ. rewrite Lj in RWJ.
  eapply evt_cut.
  { eapply HMEMSET with (junk := junk). rewrite !unsigned_lit by (unfold D; lia).
    change (Z.to_nat 356) with 356%nat. exact RWJ. exact MI1. }
  intros ms' PO.
  destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & E & MU2 & WM2 & MI2 & RW2).
  subst ms'. ret_lit.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (rewrite unsigned_lit by (unfold D; lia); reflexivity).
  rewrite ED in RW2, MU2. change (bv_unsigned (Z_to_bv 64 356)) with 356 in RW2, MU2.
  change (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 in RW2. change (Z.to_nat 356) with 356%nat in RW2.
  destruct (p4_cb_bytes rsegs m2 D 356 _ RW2) as (BZ & _ & WZ).
  change (Z_to_bv 8 0) with ZERO in BZ.
  set (bs2 := upd_bytes bs1 (Z.to_nat (D - c)) (repeat ZERO 356)).
  assert (HB2 : bytes_at rsegs m2 c bs2).
  { apply (p4_bytes_upd_munch rsegs [(D, D + 356)] m1 m2 c bs1 D (repeat ZERO 356) HB1 MU2 BZ);
      rewrite ?repeat_length; [unfold D; lia | unfold D; lia |].
    intros z Hz Hn'. cbn [outside]. split; [lia | exact I]. }
  assert (L2 : length bs2 = length bs) by (unfold bs2; rewrite upd_bytes_length; [lia | rewrite repeat_length; unfold D; lia]).
  assert (PM2 : pf_mem m0 m2 spz lo c).
  { eapply pf_mem_call; [exact PM1 | | exact MU2 | exact WM2 | exact MI2].
    unfold sub_fp. intros z Hz. p4_wp. unfold D in *. cbn [outside app] in *.
    repeat split; try lia; exact I. }
  assert (NA2 : cstr_at rsegs m2 np name).
  { eapply pfb_cstr_at_munch; [exact NA1 | exact MU2 |]. cbn [disjoint_from]. unfold D. split; [lia | exact I]. }
  assert (EB2 : bs2 = upd_bytes bs1 (Z.to_nat (D - c)) (repeat ZERO 356)) by reflexivity.
  clearbody bs2. clear MU2 WM2 RW2 HB1 BJ WJ RWJ.
  zstep. zstep. zstep. zstep. zstep. zstep.
  destruct (p4_ctx_mem _ _ PM2 FC) as (ENV2 & _).
  pose proof ENV2 as (_ & _ & APc & BLK & (FRM2 & TM2 & (G1 & g & G2) & IL & SPH) & _).
  cbn [SA SEG_UBSAN sa_img_end sa_got_guard sa_guard] in IL, G1, G2.
  unfold apart, SEG_C_SIZE, PARSE_FILE_FRAME in APc.
  pose proof PM2 as (_ & _ & _ & _ & _ & STF2).
  destruct (p4_cstr_min rsegs m2 np name NA2) as (sl & BS & LSL).
  set (lo' := spz + PARSE_FILE_FRAME - PARSE_FILE_STACK).
  assert (Hlo' : lo' = spz - 6032) by (unfold lo', PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME; lia).
  eapply evt_cut.
  { eapply HSNPRINTF with (lo := lo') (canary := g) (fmt := [37; 115]) (ps := [Ps]) (args := [APtr name])
      (T := name ++ []) (junk := repeat ZERO 16).
    - exact (fmt_s_at m2 MI2).
    - unfold RO_LO. rewrite unsigned_lit by lia. lia.
    - unfold RO_END. rewrite unsigned_lit by lia. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. rewrite !unsigned_lit by (unfold D; lia).
      split.
      { rewrite Forall_forall in NBY |- *. intros x Hx. pose proof (NBY x Hx) as Hb. unfold zbyte in Hb.
        assert (x <> 0) by (intros ->; exact (Hnn Hx)). lia. }
      exists sl. split; [|split; [lia | split; [lia | split; unfold D in *; lia]]].
      unfold pf_bytes. rewrite map_app, <- app_assoc. exact BS.
    - reflexivity.
    - rewrite unsigned_lit by (unfold D; lia). change (Z.to_nat (bv_unsigned (Z_to_bv 64 16))) with 16%nat.
      change 16%nat with (length (repeat ZERO 16)) at 1. apply p4_rw_cb.
      + pose proof (p4_bytes_sub rsegs m2 D (repeat ZERO 356) 0 16 BZ ltac:(rewrite repeat_length; lia)) as H.
        rewrite Z.add_0_r, skipn_O, firstn_repeat_gen in H. exact H.
      + rewrite repeat_length. eapply p4_wr_sub; [exact WZ | lia | lia | lia].
    - change (bv_unsigned (Z_to_bv 64 16)) with 16. lia.
    - rewrite app_nil_r. lia.
    - rewrite unsigned_lit by (unfold D; lia). unfold D. lia.
    - rewrite !unsigned_lit by (unfold D; lia). change (bv_unsigned (Z_to_bv 64 16)) with 16. unfold D. lia.
    - rewrite !unsigned_lit by (unfold D; lia). change (bv_unsigned (Z_to_bv 64 16)) with 16.
      intros j Hj sg Hin. specialize (BLK (D - c + j) ltac:(unfold SEG_C_SIZE, D; lia) sg Hin).
      replace (c + (D - c + j)) with (D + j) in BLK by lia. exact BLK.
    - assert (ST' : stk rsegs m2 lo' (spz + PARSE_FILE_FRAME))
        by exact (proj2 (stk_split rsegs m2 lo lo' (spz + PARSE_FILE_FRAME) STF2
                           ltac:(rewrite Hlo'; unfold PARSE_FILE_FRAME; lia))).
      exact (proj1 (stk_split rsegs m2 lo' spz (spz + PARSE_FILE_FRAME) ST'
                      ltac:(rewrite Hlo'; unfold PARSE_FILE_FRAME; lia))).
    - unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - lia.
    - exact FC.
    - exact MI2.
    - exact TM2.
    - exact G1.
    - exact G2. }
  intros ms' PO.
  destruct PO as (x0' & x1' & x2' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & Ft & fc' & m3 &
                  E' & MU3 & WM3 & MI3 & TM3 & FRM3 & FK3 & ST3 & B3).
  subst ms'. ret_lit.
  rewrite ED in B3, MU3. change (bv_unsigned (Z_to_bv 64 16)) with 16 in B3, MU3.
  change (Z.to_nat (16 - 1)) with 15%nat in B3, MU3. rewrite app_nil_r in B3, MU3.
  rewrite firstn_all2 in B3, MU3 by lia.
  assert (EP : pf_bytes (name ++ [0]) = zb name ++ [ZERO]) by (unfold pf_bytes, zb; rewrite map_app; reflexivity).
  rewrite EP in B3.
  set (bs3 := upd_bytes bs2 (Z.to_nat (D - c)) (zb name ++ [ZERO])).
  assert (HB3 : bytes_at rsegs m3 c bs3).
  { apply (p4_bytes_upd_munch rsegs _ m2 m3 c bs2 D (zb name ++ [ZERO]) HB2 MU3 B3);
      rewrite ?length_app, ?p4_length_zb, ?L2; cbn [length]; [unfold D; lia | unfold D, SEG_C_SIZE in *; lia |].
    intros z Hz Hn'. cbn [outside]. unfold D in *. repeat split; try lia; exact I. }
  assert (EB3 : bs3 = upd_bytes (upd_bytes (upd_bytes bs (Z.to_nat RC_N) W4) (356 * N) (repeat ZERO 356))
                        (356 * N) (zb name ++ [ZERO])).
  { unfold bs3. rewrite EB2, EB1. replace (Z.to_nat (D - c)) with (356 * N)%nat by (unfold D; lia). reflexivity. }
  clearbody bs3.
  assert (RC3 : rconf_at rsegs m3 c (r_set_segs rc (rc_seg rc ++ [rseg0 name]))).
  { exists bs3. split; [exact HB3|]. rewrite EB3. apply p4_rconf_new; assumption. }
  assert (PM3 : pf_mem m0 m3 spz lo c).
  { eapply pf_mem_call; [exact PM2 | | exact MU3 | exact WM3 | exact MI3].
    unfold sub_fp. intros z Hz. p4_wp. unfold D in *. cbn [outside app] in *.
    repeat split; try lia; exact I. }
  assert (NA3 : cstr_at rsegs m3 np name).
  { eapply pfb_cstr_at_munch; [exact NA2 | exact MU3 |]. cbn [disjoint_from]. unfold D.
    repeat split; try lia; exact I. }
  assert (FK3' : Fok Ft) by (intros k Hk; rewrite (FK3 k Hk); exact (FK k Hk)).
  zstep.
  replace (Z_to_bv 64 D) with (Z_to_bv 64 (c + 356 * Z.of_nat N)) by (f_equal; unfold D; lia).
  eapply w_seen with (rc2 := r_set_segs rc (rc_seg rc ++ [rseg0 name])) (i := N);
    [exact PM3 | exact FRM3 | exact FK3' | exact RC3
    | unfold r_set_segs; cbn [rc_seg]; rewrite length_app; cbn [length]; lia
    | unfold r_set_segs; cbn [rc_refused]; lia | reflexivity
    | exact NA3 | unfold PF_BUF; lia | unfold PF_BUF; lia | exact Hl | ].
  rewrite HH, (p4_get_new rc nm (ln + 1) name HF Hlt).
  rewrite (snprintf_s1 16 name Hnn ltac:(lia)). reflexivity.
Qed.

(** 0x15aec: not found; n reloaded from the slot sp + 0x88; n >= 32 -> c->overflow++ and refuse(F_bound, name, 32)
    through 0x15784; else the new entry at 0x15b80. *)
Lemma w_notfound : forall m F fc np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  bytes_at rsegs m (spz + 136) (le8 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc))))) ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat -> r_find_go (rc_seg rc) name 0 = None ->
  r_header rc nm (ln + 1) L = p4_get rc nm (ln + 1) name ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 np) s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15aec) fc m).
Proof.
  intros m F fc np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC CS NA B1 B2 Hl HF HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  destruct regs_u as (U3 & E3 & U1 & E1 & U5).
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  set (N := length (rc_seg rc)) in *.
  pose proof (p4_rd_slot rsegs m (spz + 136) _ CS) as RS.
  zstep. clear RS.
  assert (LT : bv_lts (Z_to_bv 64 (Z.of_nat N)) s1 = (Z.of_nat N <? 32))
    by (rewrite E1; apply p4_lts_small; lia).
  zstep. rewrite LT.
  destruct (Z.ltb_spec (Z.of_nat N) 32) as [Hlt|Hge].
  - eapply w_new; [exact PM | exact FC | exact FK | exact RC | lia | exact NA | unfold PF_BUF; lia
                  | unfold PF_BUF; lia | exact Hl | exact HF | exact HH].
  - pose proof (rd_ovf m PM) as RS.
    destruct (p4_read_ovf rsegs m c bs rc HB HE) as [OR RO].
    assert (Hov : rc_overflow rc + 1 < 2 ^ 32) by (destruct HST as (_ & _ & _ & (_ & C2)); lia).
    zstep. clear RS. zstep. clear RO.
    zstep.
    pose proof (p4_c_wr m bs PM HB HL) as WC.
    pose proof (wr_at_store_ok rsegs m c SEG_C_SIZE 13520 4 WC ltac:(lia) ltac:(unfold SEG_C_SIZE; lia)) as HS.
    pose proof HS as HS'. cbv delta [wa] in HS'.
    zstep. clear HS'.
    rewrite ?(p4_le4_inc (rc_overflow rc) OR).
    set (W4 := le4 (Z_to_bv 64 (rc_overflow rc + 1))).
    assert (LW4 : length W4 = 4%nat) by apply length_le4.
    set (m1 := write_to_mem m (Z_to_bv 64 (c + 13520)) W4).
    assert (HB1 : bytes_at rsegs m1 c (upd_bytes bs (Z.to_nat 13520) W4))
      by exact (bytes_at_write_inside rsegs m c bs 13520 W4 HB ltac:(lia) ltac:(lia)).
    assert (RC1 : rconf_at rsegs m1 c (p4_ovf rc)).
    { exists (upd_bytes bs (Z.to_nat 13520) W4). split; [exact HB1|]. exact (p4_rconf_ovf rc bs HE Hov). }
    assert (PM1 : pf_mem m0 m1 spz lo c).
    { apply (pf_mem_store m0 m spz lo c (c + 13520) W4 PM); rewrite ?LW4.
      - lia.
      - lia.
      - p4_wp. cbn [inside]. right. right. right. right. right. left. lia.
      - exact HS. }
    assert (NA1 : cstr_at rsegs m1 np name).
    { eapply pfb_cstr_at_munch; [exact NA | apply p4_munch_write; lia |].
      rewrite LW4. cbn [disjoint_from]. split; [lia | exact I]. }
    clearbody m1. clear HB HS WC HB1.
    zstep. zstep. zstep. zstep.
    eapply site_784 with (rc1 := p4_ovf rc) (f := F_bound) (fp := 0x10817) (z := 32) (name := name);
      [exact PM1 | exact FC | exact FK | exact RC1 | reflexivity | unfold p4_ovf; cbn [rc_overflow]; lia
      | reflexivity | lia | in_fmts | vm_compute; reflexivity | reflexivity | lia | exact NA1 | lia
      | unfold PARSE_FILE_FRAME; lia |].
    rewrite HH. apply p4_get_full; [exact HF | lia].
Qed.

(** The search loop at 0x15ac0: entry i, k entries left, s6 = 356 i, s9 = 0x2c80 - 356 i, s4 = c + 356 i,
    s8 = 356 n, the slot sp + 0x88 holds n, the names before i differ from name. *)
Lemma w_loop : forall k i m F fc np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  (i + k = length (rc_seg rc))%nat -> (0 < k)%nat ->
  bv_unsigned s4 = c + 356 * Z.of_nat i -> bv_unsigned s6 = 356 * Z.of_nat i ->
  bv_unsigned s9 = 11392 - 356 * Z.of_nat i -> bv_unsigned s8 = 356 * Z.of_nat (length (rc_seg rc)) ->
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  bytes_at rsegs m (spz + 136) (le8 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc))))) ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat ->
  r_find_go (rc_seg rc) name 0 = r_find_go (skipn i (rc_seg rc)) name i ->
  r_header rc nm (ln + 1) L = p4_get rc nm (ln + 1) name ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 np) s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15ac0) fc m).
Proof.
  induction k as [|k IH]; intros i m F fc np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6
    Hik Hk E4 E6 E9 E8 PM FC FK RC CS NA B1 B2 Hl HF HH; [lia|].
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  assert (Hi : (i < length (rc_seg rc))%nat) by lia.
  destruct (p4_name_at rsegs m c bs rc i HB HE Hi) as (EA & EL).
  set (e := rs_name (nth i (rc_seg rc) rseg_d)) in *.
  pose proof (p4_cstr_bytes0 rsegs m _ _ EA) as (EB & EN & EZ & EY).
  pose proof (p4_cstr_bytes0 rsegs m _ _ NA) as (NB & NN & NZ & NY).
  (* beqz s9 -> trap; bltu ~c, s6 -> trap *)
  zstep. p4_br.
  pose proof (rd_notc m PM) as RS.
  zstep. clear RS.
  zstep. p4_br.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSTRCMP with (sx := zb e) (sy := zb name).
    - rewrite E4. exact EB.
    - exact EN.
    - rewrite unsigned_lit by lia. exact NB.
    - exact NN. }
  intros ms' PO. destruct PO as (r & x11 & x12 & x13 & E & HR). subst ms'. ret_lit.
  assert (HS : strcmp e name = 0 <-> r = Z_to_bv 64 0).
  { rewrite HR. rewrite <- (bridge_strcmp (zb e) (zb name) EN NN), EZ, NZ. reflexivity. }
  pose proof (p4_find_step (rc_seg rc) name i i Hi) as FS.
  zstep.
  destruct (Z.eq_dec (strcmp e name) 0) as [EQ|NE].
  - rewrite (proj1 HS EQ). p4_br.
    replace s4 with (Z_to_bv 64 (c + 356 * Z.of_nat i))
      by (apply bv_eq; rewrite E4; rewrite unsigned_lit by lia; reflexivity).
    eapply w_found with (i := i); [exact PM | exact FC | exact FK | exact RC | exact Hi | exact NA
      | unfold PF_BUF; lia | unfold PF_BUF; lia | exact Hl | | exact HH].
    rewrite HF, FS. fold e. rewrite EQ. reflexivity.
  - assert (Hr : r <> Z_to_bv 64 0) by (intros C; apply NE; apply HS; exact C).
    rewrite (p4_bv_eqb_false r Hr).
    assert (HF' : r_find_go (rc_seg rc) name 0 = r_find_go (skipn (S i) (rc_seg rc)) name (S i)).
    { rewrite HF, FS. fold e. apply Z.eqb_neq in NE. rewrite NE. reflexivity. }
    zstep. zstep. zstep.
    rewrite ?E4, ?E6, ?E9.
    zstep.
    destruct k as [|k'].
    + p4_br.
      eapply w_notfound; [exact PM | exact FC | exact FK | exact RC | exact CS | exact NA | unfold PF_BUF; lia
                         | unfold PF_BUF; lia | exact Hl | | exact HH].
      rewrite HF'. replace (S i) with (length (rc_seg rc)) by lia. apply p4_find_end.
    + p4_br.
      eapply (IH (S i)); [lia | lia | | | | exact E8 | exact PM | exact FC | exact FK | exact RC | exact CS | exact NA
                         | unfold PF_BUF; lia | unfold PF_BUF; lia | exact Hl | exact HF' | exact HH].
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia. lia.
      * rewrite unsigned_lit by lia. lia.
Qed.

(** seg_get from 0x15a90: n = c->n (through the slot sp + 0x58); n <= 0 -> the new entry, else the slot sp + 0x88 := n,
    s8 = 356 n, s4 = c, s9 = 0x2c80 and the loop. *)
Lemma w_segget : forall m F fc np name (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  cstr_at rsegs m np name -> spz + PF_BUF <= np -> np + Z.of_nat (length name) < spz + PF_BUF + 512 ->
  (length name < 16)%nat ->
  r_header rc nm (ln + 1) L = p4_get rc nm (ln + 1) name ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 (Z_to_bv 64 np) s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15a90) fc m).
Proof.
  intros m F fc np name ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC NA B1 B2 Hl HH.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  pose proof RC as (bs & HB & HE).
  pose proof HE as (HL & HLS & _). unfold SEG_C_SIZE in HL.
  set (N := length (rc_seg rc)) in *.
  pose proof (rd_n m PM) as RS.
  pose proof (p4_read_n rsegs m c bs rc HB HE) as RN.
  zstep. clear RS. zstep. clear RN.
  rewrite p4_sx32_small by lia.
  zstep.
  rewrite p4_lts_small by lia.
  destruct (Nat.eq_dec N 0) as [H0|H0].
  - assert (H0' : length (rc_seg rc) = 0%nat) by exact H0.
    rewrite (proj2 (Z.ltb_ge 0 (Z.of_nat (length (rc_seg rc))))) by lia. cbn [negb].
    assert (HF : r_find_go (rc_seg rc) name 0 = None).
    { pose proof (p4_find_end (rc_seg rc) name 0) as FE. rewrite H0' in FE. exact FE. }
    eapply w_new; [exact PM | exact FC | exact FK | exact RC | lia | exact NA | unfold PF_BUF; lia
                  | unfold PF_BUF; lia | exact Hl | exact HF | exact HH].
  - rewrite (proj2 (Z.ltb_lt 0 (Z.of_nat (length (rc_seg rc))))) by lia. cbn [negb].
    zstep. zstep. zstep.
    pose proof (pf_frame_store_ok m0 m spz lo c (spz + 136) 8 PM ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia)) as HS.
    pose proof HS as HS'. cbv delta [wa] in HS'.
    zstep. clear HS'.
    set (W8 := le8 (Z_to_bv 64 (Z.of_nat (length (rc_seg rc))))) in *.
    assert (LW8 : length W8 = 8%nat) by apply length_le8.
    set (m1 := write_to_mem m (Z_to_bv 64 (spz + 136)) W8).
    assert (PM1 : pf_mem m0 m1 spz lo c).
    { apply (pf_mem_store m0 m spz lo c (spz + 136) W8 PM); rewrite ?LW8.
      - lia.
      - lia.
      - p4_wp. cbn [inside]. right. right. left. lia.
      - exact HS. }
    assert (CS1 : bytes_at rsegs m1 (spz + 136) W8)
      by exact (bytes_at_write_same rsegs m (spz + 136) W8 ltac:(lia) ltac:(rewrite LW8; lia)).
    assert (HB1 : bytes_at rsegs m1 c bs)
      by exact (bytes_at_write_other rsegs m (spz + 136) W8 c bs HB ltac:(lia) ltac:(rewrite LW8; lia)
                  ltac:(rewrite LW8, HL; lia)).
    assert (RC1 : rconf_at rsegs m1 c rc) by (exists bs; split; [exact HB1 | exact HE]).
    assert (NA1 : cstr_at rsegs m1 np name).
    { eapply pfb_cstr_at_munch; [exact NA | apply p4_munch_write; rewrite ?LW8; lia |].
      rewrite LW8. cbn [disjoint_from]. split; [lia | exact I]. }
    clearbody m1. clear HB HS.
    zstep. zstep. zstep.
    pose proof (rd_c m1 PM1) as RS.
    zstep. clear RS.
    pose proof (rd_sz m1 PM1) as RS.
    zstep. clear RS.
    unfold N in *.
    eapply (w_loop (length (rc_seg rc)) 0); [lia | lia | rewrite unsigned_lit by lia; lia
                         | rewrite unsigned_lit by lia; reflexivity | rewrite unsigned_lit by lia; reflexivity
                         | rewrite ?p4_mask by lia; rewrite ?unsigned_lit by lia; lia | exact PM1 | exact FC
                         | exact FK | exact RC1 | exact CS1 | exact NA1 | unfold PF_BUF; lia | unfold PF_BUF; lia
                         | exact Hl | reflexivity | exact HH].
Qed.

(** 0x15758 (a0 = body + 7): trim(body + 7) -> name (s7), name[0] = 0 -> F_noname, strlen(name) >= 16 -> F_toolong,
    else seg_get. *)
Lemma w_name : forall m F fc ci bp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  strchr L RBR = Some ci -> nth (S ci) L 0 = 0 ->
  cstr_at rsegs m bp (p4_body L ci) -> spz + PF_BUF <= bp -> bp + Z.of_nat (length (p4_body L ci)) < spz + PF_BUF + 512 ->
  strncasecmp (p4_body L ci) S_segment 7 = 0 -> sp_tab (nth 7 (p4_body L ci) 0) = true ->
  a0 = Z_to_bv 64 (bp + 7) ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 (Z_to_bv 64 bp) s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15758) fc m).
Proof.
  intros m F fc ci bp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC SC Z0 BA B1 B2 KW SPT E0.
  subst a0.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  unfold PF_BUF in B1, B2.
  set (body := p4_body L ci) in *.
  assert (Hnb : ~ In 0 body) by (destruct BA as (? & ? & _ & _ & HN & _); exact HN).
  assert (H7 : (7 <= length body)%nat).
  { pose proof (strncasecmp_segment body Hnb) as E.
    rewrite KW, Z.eqb_refl in E. symmetry in E. apply andb_true_iff in E as [E _]. apply Nat.leb_le in E. exact E. }
  assert (H8 : (8 <= length body)%nat).
  { destruct (Nat.eq_dec 7 (length body)) as [E|E]; [|lia].
    rewrite (nth_overflow body 0) in SPT by lia. cbn in SPT. discriminate. }
  pose proof (L_cstr_skipn_holds rsegs m bp body 7%nat BA ltac:(lia)) as LB7.
  change (Z.of_nat 7) with 7 in LB7.
  pose proof PM as (_ & _ & _ & MI & _ & STF).
  zstep.
  assert (E1 : bv_unsigned (Z_to_bv 64 (bp + 7)) = bp + 7) by (rewrite unsigned_lit by lia; reflexivity).
  set (x := skipn 7 body) in *.
  assert (Lx : length x = (length body - 7)%nat) by (unfold x; apply length_skipn).
  eapply evt_cut.
  { eapply HTRIM with (lo := lo) (s := x). unfold trim_pre. rewrite ?E1.
    split; [lia|]. split; [exact LB7|]. split.
    { eapply p4_stk_wr; [exact STF | lia | lia | unfold PARSE_FILE_FRAME; lia]. }
    split; [unfold apart; right; lia|].
    split; [split; [exact (stk_at m PM) | split; [unfold TRIM_STACK; lia | split; [exact N4 | exact rom_below]]]|].
    exact MI. }
  intros ms' PO.
  destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m5 & E & MU & WM & MI5 & ST5
                  & B5).
  subst ms'. ret_lit. rewrite ?E1. rewrite ?E1 in MU, B5. unfold TRIM_STACK in MU.
  assert (Hnx : ~ In 0 x) by (apply nulfree_skipn; exact Hnb).
  destruct (L_trim_holds x Hnx) as (T1 & T2 & T3).
  assert (LA5 : cstr_at rsegs m5 (bp + 7 + Z.of_nat (trim_lead x)) (r_trim x)).
  { eapply p4_cstr_trim; [exact LB7 | exact MU | | exact B5 | exact T1 | exact T2 | exact T3].
    intros y Hy. unfold trim_end_addr.
    destruct (Z.eq_dec y (bp + 7 + Z.of_nat (trim_lead x + length (r_trim x)))) as [EQ|NE]; [right; exact EQ|left].
    cbn [outside]. repeat split; try lia; exact I. }
  assert (PM5 : pf_mem m0 m5 spz lo c).
  { eapply pf_mem_call; [exact PM | | exact MU | exact WM | exact MI5].
    unfold sub_fp. intros z Hz. unfold trim_end_addr in *. p4_wp. cbn [outside app] in *.
    repeat split; try lia; exact I. }
  assert (RC5 : rconf_at rsegs m5 c rc).
  { eapply pfb_rconf_at_munch; [exact RC | exact MU |]. unfold trim_end_addr. cbn [disjoint_from].
    unfold SEG_C_SIZE. repeat split; try lia; exact I. }
  clear MU WM B5 LB7.
  set (np := bp + 7 + Z.of_nat (trim_lead x)) in *.
  change (r_trim x) with (p4_name body) in LA5, T1, T3.
  pose proof (p4_cstr_bytes0 rsegs m5 np _ LA5) as (_ & _ & _ & BYn).
  zstep.
  pose proof (nth_byte (p4_name body) 0 BYn) as XB.
  pose proof (p4_cstr_byte rsegs m5 np (p4_name body) 0 LA5 ltac:(lia)) as RD.
  zstep. clear RD. cbv beta. rewrite p4_u8 by exact XB. rewrite p4_nth0. rewrite p4_nth0 in XB.
  zstep.
  destruct (Z.eq_dec (hd0 (p4_name body)) 0) as [H0|HN0].
  - rewrite H0. p4_br.
    eapply site_a78; [exact PM5 | exact FC | exact FK | exact RC5 |].
    exact (p4_hdr_noname rc nm (ln + 1) L ci SC Z0 KW SPT H0).
  - p4_br.
    pose proof LA5 as (bsn & sln & BN & HZn & HNn & HSn).
    assert (Lbn : length bsn = length (p4_name body))
      by (rewrite <- HZn; unfold zs; rewrite length_map; reflexivity).
    zstep. zstep.
    eapply evt_cut.
    { eapply HSTRLEN with (str := bsn) (slack := sln).
      - uns.
      - apply nul_free_bytes. rewrite HZn. exact HNn.
      - rewrite ?unsigned_lit by lia. rewrite Lbn. exact HSn.
      - exact MI5. }
    intros ms' PO.
    destruct PO as (x0' & x1' & x2' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & m6 & E' & MU
                    & WM & MI6 & _).
    subst ms'. ret_lit. rewrite Lbn.
    assert (PM6 : pf_mem m0 m6 spz lo c).
    { eapply pf_mem_call with (W := []); [exact PM5 | intros z Hz; exact I | exact MU | exact WM | exact MI6]. }
    assert (RC6 : rconf_at rsegs m6 c rc) by (eapply pfb_rconf_at_munch; [exact RC5 | exact MU | exact I]).
    assert (LA6 : cstr_at rsegs m6 np (p4_name body)) by (eapply pfb_cstr_at_munch; [exact LA5 | exact MU | exact I]).
    zstep. zstep.
    destruct (Nat.ltb_spec (length (p4_name body)) 16) as [LT|GE].
    + p4_br.
      eapply w_segget; [exact PM6 | exact FC | exact FK | exact RC6 | exact LA6 | unfold PF_BUF; lia
                       | unfold PF_BUF; lia | exact LT |].
      apply (p4_hdr_get rc nm (ln + 1) L ci SC Z0 KW SPT HN0). rewrite strlen_id by exact T3. exact LT.
    + p4_br. zstep. zstep. zstep.
      eapply site_784 with (rc1 := rc) (f := F_toolong) (fp := 0x102a9) (z := 15) (name := p4_name body);
        [exact PM6 | exact FC | exact FK | exact RC6 | reflexivity | lia | reflexivity | lia | in_fmts
        | vm_compute; reflexivity | reflexivity | lia | exact LA6 | lia | unfold PARSE_FILE_FRAME; lia |].
      apply (p4_hdr_toolong rc nm (ln + 1) L ci SC Z0 KW SPT HN0). rewrite strlen_id by exact T3. exact GE.
Qed.

(** 0x15740: the trap on body > -8, then body[7] is '\t' (s4) or ' ' (s1), else F_unknown. *)
Lemma w_kw : forall m F fc ci bp (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc ->
  strchr L RBR = Some ci -> nth (S ci) L 0 = 0 ->
  cstr_at rsegs m bp (p4_body L ci) -> spz + PF_BUF <= bp -> bp + Z.of_nat (length (p4_body L ci)) < spz + PF_BUF + 512 ->
  strncasecmp (p4_body L ci) S_segment 7 = 0 ->
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 9) (Z_to_bv 64 bp) s7 s8 s9 t3 t4 t5 t6
                      F (Z_to_bv 64 0x15740) fc m).
Proof.
  intros m F fc ci bp ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 t3 t4 t5 t6 PM FC FK RC SC Z0 BA B1 B2 KW.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  destruct regs_u as (U3 & E3 & U1 & E1 & U5).
  unfold PF_BUF in B1, B2.
  pose proof (p4_cstr_bytes0 rsegs m bp _ BA) as (_ & _ & _ & BY).
  assert (H7 : (7 <= length (p4_body L ci))%nat).
  { pose proof (strncasecmp_segment (p4_body L ci) ltac:(destruct BA as (? & ? & _ & _ & HN & _); exact HN)) as E.
    rewrite KW, Z.eqb_refl in E. symmetry in E. apply andb_true_iff in E as [E _]. apply Nat.leb_le in E. exact E. }
  pose proof (nth_byte (p4_body L ci) 7 BY) as XB.
  pose proof (p4_cstr_byte rsegs m bp (p4_body L ci) 7 BA H7) as RD.
  zstep. zstep. p4_br.
  zstep. zstep. clear RD. cbv beta. rewrite p4_u8 by exact XB.
  zstep. p4_br.
  - p4_ks. rewrite ?U1 in *.
    eapply w_name; try eassumption; try (unfold PF_BUF; lia); [|reflexivity].
    unfold sp_tab. apply orb_true_iff. right. apply Z.eqb_eq. lia.
  - zstep. p4_br.
    + p4_ks. rewrite ?U1 in *.
      eapply site_unk; try eassumption; [split; unfold PF_BUF; lia |].
      apply p4_hdr_unknown with (ci := ci); [exact SC | exact Z0 | right].
      unfold sp_tab. apply orb_false_iff. split; apply Z.eqb_neq; lia.
    + p4_ks. rewrite ?U1 in *.
      eapply w_name; try eassumption; try (unfold PF_BUF; lia); [|reflexivity].
      unfold sp_tab. apply orb_true_iff. left. apply Z.eqb_eq. lia.
Qed.

(** 0x155a0: `*close = 0`, the trap on line == -1, trim(line + 1) -> body (s6), strncasecmp(body, "segment", 7). *)
Lemma w_hdr_close : forall m F fc ci (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 : word),
  pf_mem m0 m spz lo c -> frm0 fc -> Fok F -> rconf_at rsegs m c rc -> cstr_at rsegs m lp L ->
  strchr L RBR = Some ci -> nth (S ci) L 0 = 0 ->
  evt rsegs Post (MSt ra t0 t1 t2 (Z_to_bv 64 (lp + Z.of_nat ci)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 9) s6
                      (Z_to_bv 64 lp) s8 s9 t3 t4 t5 t6 F (Z_to_bv 64 0x155a0) fc m).
Proof.
  intros m F fc ci ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 PM FC FK RC LA SC Z0.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  destruct regs_u as (U3 & E3 & U1 & E1 & U5).
  pose proof line_bytes as (LBy & Hn).
  assert (Hci : (ci < length L)%nat).
  { rewrite (strchr_memchr L 93 Hn ltac:(lia)) in SC. exact (memchr_lt _ _ _ SC). }
  assert (Hlen : S ci = length L).
  { pose proof (nth_after_close L ci Hn Hci) as E. rewrite Z0, Z.eqb_refl in E. symmetry in E.
    apply Nat.eqb_eq in E. exact E. }
  pose proof (p4_ci_pos L ci HLBR SC) as Hc1.
  pose proof PM as (_ & _ & _ & MI & TM & STF).
  pose proof (pf_frame_store_ok m0 m spz lo c (lp + Z.of_nat ci) 1 PM ltac:(lia)
                ltac:(unfold PARSE_FILE_FRAME; lia)) as HS.
  pose proof HS as HS'. cbv delta [wa] in HS'.
  zstep. clear HS'.
  change (le1 (Z_to_bv 64 0)) with [ZERO].
  set (m2 := write_to_mem m (Z_to_bv 64 (lp + Z.of_nat ci)) [ZERO]).
  assert (PM2 : pf_mem m0 m2 spz lo c).
  { apply (pf_mem_store m0 m spz lo c (lp + Z.of_nat ci) [ZERO] PM); cbn [length].
    - lia.
    - lia.
    - p4_wp. cbn [inside]. right. right. right. left. lia.
    - exact HS. }
  assert (RC2 : rconf_at rsegs m2 c rc).
  { eapply pfb_rconf_at_munch; [exact RC | apply (p4_munch_write m (lp + Z.of_nat ci) [ZERO]); cbn [length]; lia |].
    cbn [disjoint_from length]. unfold SEG_C_SIZE. split; [lia | exact I]. }
  assert (LA2 : cstr_at rsegs m2 (lp + 1) (slice 1 ci L)) by exact (p4_cstr_close rsegs m lp L ci LA Hlen Hc1).
  pose proof (p4_slice_len L ci Hc1 ltac:(lia)) as LS.
  (* beq s7, s5 -> trap *)
  zstep. p4_br.
  zstep. zstep.
  assert (E1' : bv_unsigned (Z_to_bv 64 (lp + 1)) = lp + 1) by (rewrite unsigned_lit by lia; reflexivity).
  pose proof PM2 as (_ & _ & _ & MI2 & _ & STF2).
  eapply evt_cut.
  { eapply HTRIM with (lo := lo) (s := slice 1 ci L). unfold trim_pre. rewrite ?E1'.
    split; [lia|]. split; [exact LA2|]. split.
    { eapply p4_stk_wr; [exact STF2 | lia | lia | unfold PARSE_FILE_FRAME; rewrite LS; lia]. }
    split; [unfold apart; right; lia|].
    split; [split; [exact (stk_at m2 PM2) | split; [unfold TRIM_STACK; lia | split; [exact N4 | exact rom_below]]]|].
    exact MI2. }
  intros ms' PO.
  destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m3 & E & MU & WM & MI3 & ST3
                  & B3).
  subst ms'. ret_lit. rewrite ?E1'. rewrite ?E1' in MU, B3. unfold TRIM_STACK in MU.
  set (x := slice 1 ci L) in *.
  assert (Hnx : ~ In 0 x) by (apply nulfree_slice; exact Hn).
  destruct (L_trim_holds x Hnx) as (T1 & T2 & T3).
  assert (LA3 : cstr_at rsegs m3 (lp + 1 + Z.of_nat (trim_lead x)) (r_trim x)).
  { eapply p4_cstr_trim; [exact LA2 | exact MU | | exact B3 | exact T1 | exact T2 | exact T3].
    intros y Hy. unfold trim_end_addr.
    destruct (Z.eq_dec y (lp + 1 + Z.of_nat (trim_lead x + length (r_trim x)))) as [EQ|NE]; [right; exact EQ|left].
    cbn [outside]. repeat split; try lia; exact I. }
  assert (PM3 : pf_mem m0 m3 spz lo c).
  { eapply pf_mem_call; [exact PM2 | | exact MU | exact WM | exact MI3].
    unfold sub_fp. intros z Hz. unfold trim_end_addr in *. p4_wp. cbn [outside app] in *.
    repeat split; try lia; exact I. }
  assert (RC3 : rconf_at rsegs m3 c rc).
  { eapply pfb_rconf_at_munch; [exact RC2 | exact MU |]. unfold trim_end_addr. cbn [disjoint_from].
    unfold SEG_C_SIZE. repeat split; try lia; exact I. }
  clear MU WM B3 LA2 PM2 RC2 MI2 STF2.
  set (bp := lp + 1 + Z.of_nat (trim_lead x)) in *.
  change (r_trim x) with (p4_body L ci) in LA3, T1, T3.
  pose proof (p4_cstr_bytes0 rsegs m3 bp _ LA3) as (BB & BN & BZ & BY).
  zstep. zstep. zstep. zstep. zstep. zstep.
  pose proof PM3 as (_ & _ & _ & _ & _ & STF3).
  eapply evt_cut.
  { eapply HNCASE with (ls := zb (p4_body L ci)) (rs := zb S_segment) (lo := lo).
    - exact ST3.
    - uns.
    - exact BN.
    - rewrite ?unsigned_lit by lia. exact (seg_lit_at m3 MI3).
    - exact seg_lit_nul.
    - exact MI3.
    - lia.
    - rewrite ?unsigned_lit by lia. right. lia.
    - rewrite ?unsigned_lit by lia. left. change (length (zb S_segment)) with 7%nat. lia. }
  intros ms' PO.
  destruct PO as (r & x0' & x1' & x2' & y1' & y2' & y3' & y4' & y5' & y6' & y7' & x3' & x4' & x5' & x6' & m4 & E' &
                  MU & WM & MI4 & ST4 & _ & _ & HR).
  subst ms'. ret_lit.
  rewrite unsigned_lit in HR by lia.
  rewrite (bridge_strncasecmp _ _ 7 BN seg_lit_nul), BZ in HR.
  change (zs (zb S_segment)) with S_segment in HR. change (Z.to_nat 7) with 7%nat in HR.
  assert (PM4 : pf_mem m0 m4 spz lo c).
  { eapply pf_mem_call; [exact PM3 | | exact MU | exact WM | exact MI4].
    unfold sub_fp. intros z Hz. p4_wp. cbn [outside app] in *. repeat split; try lia; exact I. }
  assert (RC4 : rconf_at rsegs m4 c rc).
  { eapply pfb_rconf_at_munch; [exact RC3 | exact MU |]. cbn [disjoint_from]. unfold SEG_C_SIZE.
    split; [lia | exact I]. }
  assert (LA4 : cstr_at rsegs m4 bp (p4_body L ci)).
  { eapply pfb_cstr_at_munch; [exact LA3 | exact MU |]. cbn [disjoint_from]. split; [lia | exact I]. }
  zstep.
  destruct (Z.eq_dec (strncasecmp (p4_body L ci) S_segment 7) 0) as [KW|NKW].
  - rewrite (proj2 HR KW). p4_br.
    eapply w_kw; try eassumption; try (unfold PF_BUF; lia).
  - assert (Hr : r <> Z_to_bv 64 0) by (intros C; apply NKW; apply HR; exact C).
    lazymatch goal with |- evt _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let K := fresh "K" in destruct cnd eqn:K;
      [exfalso; apply Hr; apply bv_eq; unfold bv_eqb in K; apply Z.eqb_eq in K; exact K |] end.
    eapply site_unk; try eassumption; [split; unfold PF_BUF in *; lia |].
    apply p4_hdr_unknown with (ci := ci); [exact SC | exact Z0 | left; exact NKW].
Qed.

Lemma w_hdr : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6 : word),
  evt rsegs Post (MSt ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 9) s6 (Z_to_bv 64 lp) s8 s9 t3 t4 t5 t6
                      F0 (Z_to_bv 64 PF_PC_HDR) fc0 m0).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 t3 t4 t5 t6.
  pose proof p4_nums as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10).
  destruct regs_u as (U3 & E3 & U1 & E1 & U5).
  pose proof HLINE as (bs & sl & B & Hz & Hn & Hs).
  assert (Lb : length bs = length L) by (rewrite <- Hz; unfold zs; rewrite length_map; reflexivity).
  pose proof env0 as (_ & _ & _ & _ & _ & _ & (ST & _) & MI & _).
  unfold PF_PC_HDR.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply HSTRCHR with (str := bs) (slack := sl) (lo := lo).
    - exact (stk_at m0 pm0).
    - uns.
    - apply nul_free_bytes. rewrite Hz. exact Hn.
    - rewrite ?unsigned_lit by lia. rewrite Lb. exact Hs.
    - exact MI.
    - lia.
    - rewrite ?unsigned_lit by lia. right. lia. }
  intros ms' PO. unfold strchr_post in PO.
  destruct PO as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m1 & E & MU & WM & MI1 & ST1
                  & B1).
  subst ms'. ret_lit.
  rewrite ?(unsigned_lit lp) in B1 by lia. rewrite ?(unsigned_lit lp) by lia.
  change (bv_unsigned (Z_to_bv 64 93) mod 256) with 93.
  assert (Hbs : ~ In (Z_to_bv 8 0) bs) by (apply nul_free_bytes; rewrite Hz; exact Hn).
  rewrite (bridge_strchr lp 93 bs Hbs ltac:(lia)), Hz.
  assert (PM1 : pf_mem m0 m1 spz lo c).
  { eapply pf_mem_call; [exact pm0 | | exact MU | exact WM | exact MI1].
    unfold sub_fp. intros x Hx. p4_wp. cbn [outside app] in *. repeat split; try lia; exact I. }
  assert (RC1 : rconf_at rsegs m1 c rc).
  { eapply pfb_rconf_at_munch; [exact rc0 | exact MU |]. cbn [disjoint_from]. unfold SEG_C_SIZE. split; [lia | exact I]. }
  assert (LA1 : cstr_at rsegs m1 lp L) by (exists bs, sl; exact (conj B1 (conj Hz (conj Hn Hs)))).
  destruct (strchr L 93) as [ci|] eqn:SC.
  - assert (Hci : (ci < length L)%nat).
    { rewrite (strchr_memchr L 93 Hn ltac:(lia)) in SC. exact (memchr_lt _ _ _ SC). }
    pose proof (nth_byte L (S ci) (proj1 line_bytes)) as XB.
    zstep. p4_br.
    zstep. p4_br.
    pose proof (p4_cstr_byte rsegs m1 lp L (S ci) LA1 ltac:(lia)) as RD.
    zstep. clear RD.
    cbv beta.
    rewrite p4_u8 by exact XB.
    destruct (Z.eqb_spec (nth (S ci) L 0) 0) as [Z0|NZ].
    + rewrite Z0. zstep. p4_br.
      eapply w_hdr_close; [exact PM1 | exact frm0_0 | exact fok0 | exact RC1 | exact LA1 | exact SC | exact Z0].
    + zstep. p4_br. zstep. zstep. zstep.
      eapply site_578 with (f := F_after) (fp := PF_STR_AFTER);
        [exact PM1 | exact frm0_0 | exact fok0 | exact RC1 | exact LA1 | in_href | reflexivity
        | exact (p4_hdr_after rc nm (ln + 1) L ci SC NZ)].
  - zstep. p4_br. zstep. zstep.
    eapply site_578 with (f := F_notclosed) (fp := PF_STR_NOTCLOSED);
      [exact PM1 | exact frm0_0 | exact fok0 | exact RC1 | exact LA1 | in_href | reflexivity
      | exact (p4_hdr_notclosed rc nm (ln + 1) L SC)].
Qed.

End P4.

Theorem pf_p4_holds : strchr_contract -> trim_contract -> strncasecmp_contract -> strlen_contract -> refuse_contract ->
  strcmp_contract -> memset_contract -> snprintf_contract -> S_P4.
Proof.
  intros HSTRCHR HTRIM HNCASE HSTRLEN HREFUSE HSTRCMP HMEMSET HSNPRINTF n HHREF HCLR HCNAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    c t s rc cur nm o ln d lp HCTX HST HREGS _ HS4 _ HS7 HLINE HINB HLBR.
  subst s4 s7.
  eapply w_hdr; eassumption.
Qed.
