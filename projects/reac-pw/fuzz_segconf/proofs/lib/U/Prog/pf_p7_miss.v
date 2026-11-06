(** reac-pw/fuzz_segconf, UBSan build (image 1696d6c34ffd): the miss path of piece P7 (the model key) of
    reac_segconf_parse_file, from 0x15974 (reac_box_catalogue_by_token answered NULL) to the line tail.
    lib/U/Prog/pf_p7.v uses [p7u_miss].

    Code (the UBSan binary, 0x15974 .. 0x15a6c):
      0x15974 sd zero, 0x98(sp) (ntok = 0); a0 = sp + 0x98; 0x1597c jal reac_box_catalogue (a0 = tab = 0x21468,
      ntok = 11); ld a1 = ntok; a2 = 0xf0; beqz a1 -> 0x15a4c; s4 = tab; s9 = ti = 0; s6 = kn = 0;
      the flags sp + 0x68 = (tab <> 0), sp + 0x60 = (tab & 7 == 0) && tab <> 0; s8 = tab;
      0x159b4 the join loop (s9 = ti, s6 = kn, s8 = tab + 296 ti): bltu 240, kn -> trap; a3 = ti ? "|" 0x105f0 : ""
      0x1038e; a1 = tab + 296 ti; trap if a1 == 0 (0x159e4), a1 < tab (0x159e8), 296 ti overflows (0x15a00),
      ! flag 0x60 (0x15a08); a4 = tab[ti].token (ld 0(s8)); a0 = known + kn (known = sp + 0xa0); a1 = 240 - kn;
      a2 = "%s%s" 0x1031b; 0x15a28 jal snprintf; ti++; exit when ti >= ntok; kn += ret; s8 += 296; loop while
      kn + 2 < 240;
      0x15a4c refuse(c (ld 0x90(sp)), lineno = s3, F_badmodel 0x104e3, cur_name sp + 0x3a8, val = s7,
      known = sp + 0xa0) (0x15a68 jal refuse); 0x15a6c j TAIL 0x156a4. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Arr Image Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env printf_facts_c snprintf_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_box_catalogue_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import pfC_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_p7_lemmas.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require fuzz_catalogue_row.
Import ListNotations.
Open Scope Z_scope.

(** The machine at 0x15974 after by_token said NULL: the cut context of MODEL at the memory m3 the piece has
    reached (from the entry memory m inside the function's W), val = s7 in buf, cur in its slot; the post is the
    entry's, the r_key model branch's refusal. *)
Definition P7U_MISS : Prop :=
  forall (n : nat) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 : word)
         (F F3 : bvmap 5 word) (fc3 : bv 32) (m m3 : word -> option byte) (lo : Z) (v : pf_sv)
         (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (gi : nat)
         (vp : Z) (val : list Z),
    H_TAIL n ->
    pf_ctx m3 fc3 (bv_unsigned sp) lo v c t s o ln d n ->
    pf_state m3 (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) ->
    pf_regs s0 s1 s2 s3 s5 s10 (Z_to_bv 64 1) (t + Z.of_nat (pf_next s o)) (ln + 1) ->
    pf_curslot m3 (bv_unsigned sp) c (Some gi) ->
    cstr_at rsegs m3 vp val -> pf_inb (bv_unsigned sp + PF_BUF) vp val ->
    munch (pfc_W (bv_unsigned sp) c) m m3 -> wmono rsegs m m3 ->
    (forall k : reg, bv_unsigned k <> 10 -> reg_get F3 k = reg_get F k) ->
    evt rsegs
      (pf_fin v sp gp tp F m lo c
         (r_lines (refuse rc (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) (ln + 1)
            (lines (skipn (pf_next s o) s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10
               (Z_to_bv 64 1) t3 t4 t5 t6)
          F3 (Z_to_bv 64 0x15974) fc3 None m3 (seg_rom rsegs)).

(** * Image-free and image facts the walk uses *)

(** "%s%s"'s arguments: the separator literal ("" at 0x1038e for the first token, "|" at 0x105f0 after it). *)
Definition p7m_sepp (ti : nat) : Z := if (ti =? 0)%nat then 0x1038e else 0x105f0.

Lemma p7m_J_S : forall ti, (ti <= 10)%nat -> p7_J (S ti) = p7_J ti ++ (p7_sep ti ++ p7_tok ti).
Proof. intros ti H. do 11 (destruct ti as [|ti]; [vm_compute; reflexivity|]). exfalso; lia. Qed.

Lemma p7m_kn_S : forall ti, (ti <= 10)%nat ->
  p7_kn (S ti) = p7_kn ti + Z.of_nat (length (p7_sep ti ++ p7_tok ti)).
Proof. intros ti H. unfold p7_kn. rewrite (p7m_J_S ti H), length_app. lia. Qed.

Lemma p7m_T_len : forall ti, (ti <= 10)%nat -> (length (p7_sep ti ++ p7_tok ti) <= 12)%nat.
Proof.
  intros ti H. rewrite length_app. destruct (p7_tok_ok ti H) as (_ & _ & _ & H2).
  unfold p7_sep. destruct (ti =? 0)%nat; cbn [length]; lia.
Qed.

Lemma p7m_tok_ptr : forall i, (i < 11)%nat -> 0x10000 <= tok_ptr i /\ tok_ptr i + 64 <= 0x1229c.
Proof.
  intros i Hi.
  pose proof (all_rows_spec (fun i => (0x10000 <=? tok_ptr i) && (tok_ptr i + 64 <=? 0x1229c))
                ltac:(vm_compute; reflexivity) i Hi) as H.
  cbn beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** A literal in .rodata (with the image bytes after its NUL as the slack) as printf's %s argument. *)
Lemma p7m_lit_arg : forall m S lo' D nn a s sl, mem_inv rsegs m ->
  ro_bytes_b rsegs a (pf_bytes (s ++ [0]) ++ sl) = true ->
  Forall (fun x => 0 < x < 256) s ->
  (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length sl) -> 0 < a ->
  a + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= 2 ^ 64 ->
  (a + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= lo' \/ S <= a) ->
  (a + Z.of_nat (length s) + 1 + Z.of_nat (length sl) <= D \/ D + nn <= a) ->
  pf_arg_ok m S lo' D nn (Z_to_bv 64 a) (APtr s).
Proof.
  intros m S lo' D nn a s sl MI HR Hs Hk Ha Hb H1 H2. unfold pf_arg_ok. rewrite unsigned_lit by lia.
  split; [exact Hs|]. exists sl. split; [|split; [exact Hk|split; [exact Ha|split; [exact H1|exact H2]]]].
  apply pfc_ro_str; [exact MI | lia | | exact HR].
  unfold pf_bytes. rewrite length_app, length_map, length_app. cbn [length]. lia.
Qed.

Lemma p7m_sep_arg : forall m S lo' D nn ti, mem_inv rsegs m -> 0x54088 <= lo' -> 0x54088 <= D ->
  pf_arg_ok m S lo' D nn (Z_to_bv 64 (p7m_sepp ti)) (APtr (p7_sep ti)).
Proof.
  intros m S lo' D nn ti MI H1 H2. unfold p7m_sepp, p7_sep. destruct (ti =? 0)%nat.
  - let l := eval vm_compute in (image_bytes rsegs 0x1038f 1%nat) in
    lazymatch l with
    | Some ?sl =>
        apply (p7m_lit_arg m S lo' D nn 0x1038e [] sl MI);
          [vm_compute; reflexivity | constructor | pfc_zle | lia | pfc_zle
          | left; cbn [length]; lia | left; cbn [length]; lia]
    end.
  - let l := eval vm_compute in (image_bytes rsegs 0x105f2 6%nat) in
    lazymatch l with
    | Some ?sl =>
        apply (p7m_lit_arg m S lo' D nn 0x105f0 [124] sl MI);
          [vm_compute; reflexivity | constructor; [lia | constructor] | pfc_zle | lia | pfc_zle
          | left; cbn [length]; lia | left; cbn [length]; lia]
    end.
Qed.

(** Row ti's token (fuzz_catalogue_row's tok_at) as printf's %s argument. *)
Lemma p7m_tok_arg : forall m S lo' D nn ti, (ti <= 10)%nat -> mem_inv rsegs m -> 0x54088 <= lo' -> 0x54088 <= D ->
  pf_arg_ok m S lo' D nn (Z_to_bv 64 (tok_ptr ti)) (APtr (p7_tok ti)).
Proof.
  intros m S lo' D nn ti Hti MI H1 H2.
  destruct (U.Prog.fuzz_catalogue_row.tok_at m ti MI ltac:(unfold CAT_N; lia)) as (B & Hk & H0 & Hb & Hl).
  destruct (p7m_tok_ptr ti ltac:(lia)) as [P1 P2].
  destruct (p7_tok_ok ti Hti) as (_ & Hn & _).
  assert (Ez : zs (tok_bytes ti) = p7_tok ti) by (unfold p7_tok; apply cat_tok_nth; unfold CAT_N; lia).
  assert (Hlen : length (tok_bytes ti) = length (p7_tok ti))
    by (rewrite <- Ez; unfold zs; rewrite length_map; reflexivity).
  pose proof (Z.mod_pos_bound (- (tok_ptr ti + Z.of_nat (length (p7_tok ti)) + 1)) 8 ltac:(lia)) as Hm.
  apply pfc_arg_cstr.
  - exists (tok_bytes ti), (U.Prog.fuzz_catalogue_row.tok_slack ti).
    split; [exact B|]. split; [exact Ez|]. split; [exact Hn|]. rewrite <- Hlen. exact Hk.
  - lia.
  - left. unfold cstr_span. lia.
  - left. unfold cstr_span. lia.
Qed.

Lemma p7m_not_out1 : forall a b x, ~ outside [(a, b)] x -> a <= x < b.
Proof.
  intros a b x H. cbn [outside] in H.
  destruct (Z_le_dec a x) as [Q1|Q1]; destruct (Z_lt_dec x b) as [Q2|Q2]; try (split; assumption);
    exfalso; apply H; (split; [lia | exact I]).
Qed.

Lemma p7m_not_out2 : forall a b a' b' x, ~ outside [(a, b); (a', b')] x -> a <= x < b \/ a' <= x < b'.
Proof.
  intros a b a' b' x H. cbn [outside] in H.
  destruct (Z_le_dec a x); destruct (Z_lt_dec x b); destruct (Z_le_dec a' x); destruct (Z_lt_dec x b');
    try (left; split; assumption); try (right; split; assumption);
    exfalso; apply H; (split; [lia | split; [lia | exact I]]).
Qed.

Lemma p7m_out2 : forall a b a' b' x, ~ (a <= x < b) -> ~ (a' <= x < b') -> outside [(a, b); (a', b')] x.
Proof. intros a b a' b' x H1 H2. cbn [outside]. split; [exact H1 | split; [exact H2 | exact I]]. Qed.

(** An 8-byte frame word as a load. *)
Lemma p7m_ld8 : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w H. pose proof (bytes_at_ov_read rsegs m _ _ 0 8 H ltac:(rewrite length_le8; lia)) as R.
  replace (a + Z.of_nat 0) with a in R by lia. rewrite R. f_equal.
Qed.

(** Two words a pair of `sd` stores left in a 16-byte frame window. *)
Lemma p7m_cells2 : forall m a x y, rw_cells rsegs m a [C8 x; C8 y] -> x = Z_to_bv 64 1 -> y = Z_to_bv 64 1 ->
  bytes_at rsegs m a (le8 (Z_to_bv 64 1)) /\ bytes_at rsegs m (a + 8) (le8 (Z_to_bv 64 1)).
Proof.
  intros m a x y [[_ HB] _] -> ->. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  apply bytes_at_app in HB as [H1 H2]. rewrite length_le8 in H2. split; [exact H1 | exact H2].
Qed.

(** A condition the code tests that is false for every ti <= 10: decided by computation for each ti. *)
Ltac p7m_vkill K :=
  lazymatch type of K with
  | ?e = ?b =>
      let E := fresh "E" in
      assert (E : e = negb b) by (vm_compute; reflexivity);
      rewrite E in K; cbn [negb] in K; discriminate K
  end.

Ltac p7m_cases ti tac := do 11 (destruct ti as [|ti]; [tac|]); exfalso; lia.

Ltac p7m_refute K ti Hti :=
  exfalso; clear - K Hti; revert K; p7m_cases ti ltac:(intros K; p7m_vkill K).

(** Register equations after a step. *)
Ltac p7m_eq :=
  first [ reflexivity
        | f_equal; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia
        | apply bv_eq; vm_compute; reflexivity
        | f_equal; rewrite ?unsigned_lit by lia; lia ].

Section P7M.
Hypothesis SNP : snprintf_contract.
Hypothesis REF : refuse_contract.
Hypothesis CAT : reac_box_catalogue_contract.
Variables (n : nat) (sp gp tp s0 s1 s2 s3 s5 s10 : word) (F : bvmap 5 word) (m0 : word -> option byte) (lo : Z)
  (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (gi : nat)
  (vp : Z) (val : list Z).
Hypothesis HT : H_TAIL n.
Hypothesis Hregs : pf_regs s0 s1 s2 s3 s5 s10 (Z_to_bv 64 1) (t + Z.of_nat (pf_next s o)) (ln + 1).
Hypothesis Hinb : pf_inb (bv_unsigned sp + PF_BUF) vp val.

Definition p7m_POST : machine_state -> Prop :=
  pf_fin v sp gp tp F m0 lo c
    (r_lines (refuse rc (ln + 1) F_badmodel [AS nm; AS val; AS known], Some gi, nm) (ln + 1)
       (lines (skipn (pf_next s o) s))).

Definition p7m_INV (m : word -> option byte) (fc : bv 32) (F' : bvmap 5 word) : Prop :=
  pf_ctx m fc (bv_unsigned sp) lo v c t s o ln d n /\
  pf_state m (bv_unsigned sp) c rc (Some gi) nm (length (skipn o s)) /\
  pf_curslot m (bv_unsigned sp) c (Some gi) /\ cstr_at rsegs m vp val /\
  munch (pfc_W (bv_unsigned sp) c) m0 m /\ wmono rsegs m0 m /\
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k).

(** The bytes a step of the miss path writes: printf's stack below sp, the join-loop flags, ntok and known. *)
Definition p7m_scr (x : Z) : Prop :=
  bv_unsigned sp - SNPRINTF_K <= x < bv_unsigned sp \/ bv_unsigned sp + 0x60 <= x < bv_unsigned sp + 0x70 \/
  bv_unsigned sp + 0x98 <= x < bv_unsigned sp + 0x190.

Lemma p7m_inv_lo : forall m fc F', p7m_INV m fc F' ->
  0 <= lo /\ lo + 6032 <= bv_unsigned sp /\ bv_unsigned sp + 0x420 <= 2 ^ 64 /\
  (c + SEG_C_SIZE <= lo \/ bv_unsigned sp + 0x420 <= c) /\ 0x54088 <= lo /\ bv_unsigned sp + 0x420 < 2 ^ 63 /\
  bv_unsigned sp mod 16 = 0.
Proof.
  intros m fc F' (HC & _). destruct HC as (HE & _).
  destruct (pfc_env_lo _ _ _ _ _ _ HE) as (H1 & H2 & H3 & H4 & H5 & H6). unfold apart in H4.
  pose proof (pfc_env_al _ _ _ _ _ _ HE) as H7.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6 | exact H7].
Qed.

(** The context over a step that writes only p7m_scr bytes (present afterwards when they are frame bytes). *)
Lemma p7m_inv_step : forall m m' fc fc' F' F'' W,
  p7m_INV m fc F' -> munch W m m' -> wmono rsegs m m' ->
  (forall x, ~ outside W x -> p7m_scr x) ->
  (forall x, ~ outside W x -> bv_unsigned sp <= x -> exists b, mrd rsegs m' (wa x) = Some b) ->
  stk rsegs m' lo (bv_unsigned sp) -> mem_inv rsegs m' -> MemNorm.task_mem rsegs m' -> frm0 fc' ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F'' k = reg_get F' k) ->
  p7m_INV m' fc' F''.
Proof.
  intros m m' fc fc' F' F'' W HI MU WM HW HP ST MI TM FR HF.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  destruct HI as (HC & (HR & HOK & HNM & HCN) & HCS & HV & MU0 & WM0 & HF0).
  pose proof HC as (HE & _).
  pose proof Hinb as [Hb1 Hb2]. unfold PF_BUF in Hb1, Hb2.
  assert (OUT : forall x, ~ p7m_scr x -> outside W x).
  { intros x Hx. destruct (pfc_outside_dec W x) as [H|H]; [exact H|]. exfalso. exact (Hx (HW x H)). }
  unfold p7m_scr, SNPRINTF_K in HW, OUT.
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (pfc_ctx_call m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n W HC MU WM);
      [| | exact ST | exact MI | exact TM | exact FR].
    + intros x Hx. destruct (HW x Hx) as [Q|[Q|Q]].
      * left. lia.
      * right; right. unfold pfc_scr. left. lia.
      * right; right. unfold pfc_scr, PF_SAVE. right; right. lia.
    + intros x Hx Ho. apply (HP x Ho). unfold pfc_scr, PF_CURSLOT, PF_SAVE in Hx. lia.
  - split; [|split; [exact HOK|split; [|exact HCN]]].
    + apply (pfc_rconf_munch W m m' c rc HR MU). intros x Hx. apply OUT. unfold SEG_C_SIZE in *. lia.
    + apply (pfc_nm_call m m' fc (bv_unsigned sp) lo c v nm W HE HNM MU). intros x Hx. apply OUT.
      unfold PF_NAMEBUF, PF_SAVE in Hx. lia.
  - apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) W HE HCS MU). intros x Hx. apply OUT.
    unfold PF_CURSLOT in Hx. lia.
  - apply (pfc_cstr_munch W m m' vp val HV MU). intros x Hx. apply OUT.
    unfold cstr_span in Hx. pose proof (Z.mod_pos_bound (- (vp + Z.of_nat (length val) + 1)) 8 ltac:(lia)). lia.
  - apply (munch_trans _ m0 m m' MU0). apply (munch_weaken W); [|exact MU].
    intros x Hx. unfold pfc_W in Hx. cbn [outside] in Hx. destruct Hx as [Hx _]. apply OUT.
    unfold PARSE_FILE_STACK, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in Hx. lia.
  - exact (wmono_trans rsegs _ _ _ WM0 WM).
  - intros k Hk. rewrite (HF k Hk). exact (HF0 k Hk).
Qed.

(** known (the join of the 11 tokens) and its NUL at sp + 0xa0 is a C string: its 2 slack bytes are frame bytes. *)
Lemma p7m_known_cstr : forall m fc F', p7m_INV m fc F' ->
  bytes_at rsegs m (bv_unsigned sp + 0xa0) (pf_bytes (known ++ [0])) ->
  cstr_at rsegs m (bv_unsigned sp + 0xa0) known.
Proof.
  intros m fc F' HI HB.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  destruct HI as ((HE & _) & _).
  pose proof HE as (_ & _ & _ & _ & _ & _ & (ST & _) & _).
  assert (KL : length known = 77%nat) by exact p7_known_len.
  destruct (stk_split rsegs m lo (bv_unsigned sp + 0xa0 + 78) (bv_unsigned sp + PARSE_FILE_FRAME) ST
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ ST1].
  destruct (stk_split rsegs m _ (bv_unsigned sp + 0xa0 + 80) _ ST1 ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST2 _].
  destruct (stk_bytes rsegs m _ _ ST2 ltac:(lia)) as (sl & Hsl & HSL).
  assert (Kb : Forall pfc_zbyte known) by (rewrite <- p7_J_11; exact (p7_J_byte 11 (le_n _))).
  exists (zb known), sl. split; [|split; [|split]].
  - replace (zb known ++ ZERO :: sl) with (pf_bytes (known ++ [0]) ++ sl)
      by (unfold pf_bytes, zb; rewrite map_app, <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact HB|].
    unfold pf_bytes. rewrite length_map, length_app, KL. cbn [length].
    replace (bv_unsigned sp + 0xa0 + Z.of_nat (77 + 1)) with (bv_unsigned sp + 0xa0 + 78) by lia. exact HSL.
  - apply pfc_zs_zb. exact Kb.
  - rewrite <- p7_J_11. exact (p7_J_nulfree 11 (le_n _)).
  - rewrite Hsl, KL. Z.div_mod_to_equations. lia.
Qed.

(** 0x15a4c: refuse(c, lineno, F_badmodel, cur_name, val, known), then `j` TAIL and the tail's cut. *)
Lemma p7m_ref : forall m fc F' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  p7m_INV m fc F' -> bytes_at rsegs m (bv_unsigned sp + 0xa0) (pf_bytes (known ++ [0])) ->
  evt rsegs p7m_POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10
             (Z_to_bv 64 1) t3 t4 t5 t6)
        F' (Z_to_bv 64 0x15a4c) fc None m (seg_rom rsegs)).
Proof.
  intros m fc F' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 HI HKB.
  pose proof (p7m_known_cstr m fc F' HI HKB) as HKN.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  pose proof HI as (HCTX & HST & HCS & HVC & MU0 & WM0 & HF0).
  pose proof HCTX as (HENV & HTXT & HSPL & Ho & _ & (_ & _ & Ld & Lln)).
  pose proof HST as (HRC & _ & HNM & _).
  pose proof HENV as (_ & _ & _ & _ & _ & _ & _ & MI & _).
  pose proof HRC as (cbs & HCB & (HCL & _)).
  pose proof (bytes_at_bound _ _ _ _ HCB) as HCBB.
  pose proof (pfc_next_gt s o Ho) as [G1 G2].
  pose proof HTXT as (_ & _ & Hsl & _). pose proof (pfc_len65535 s Hsl) as Hsl'.
  pose proof Hinb as [Hb1 Hb2]. unfold PF_BUF in Hb1, Hb2.
  destruct (pfc_nm_cstr m (bv_unsigned sp) nm HNM Hal) as [HNC HNL].
  unfold PF_NAMEBUF in HNC.
  destruct (pfc_fmt_at m F_badmodel PFC_STR_BADMODEL MI
              ltac:(unfold PFC_FMTS; cbn [In]; right; right; right; right; left; reflexivity))
    as (Hfp & HF & HR1 & HR2 & HFR).
  assert (HCK : conv_kinds F_badmodel = map arg_is_s [AS nm; AS val; AS known]) by (vm_compute; reflexivity).
  assert (Hcr : 0 <= c < 2 ^ 64) by (unfold SEG_C_SIZE in *; lia).
  assert (Hlnr : 0 <= ln + 1 < 2 ^ 64) by lia.
  assert (HVL : (length val <= 65535)%nat) by (apply pfc_le65535; lia).
  assert (HKL : length known = 77%nat) by exact p7_known_len.
  pose proof (pfc_ld_c m (bv_unsigned sp) c HSPL) as HLD. unfold PF_CSLOT in HLD.
  pose proof Hregs as (Hs2 & Hs3 & _).
  (* 0x15a4c .. 0x15a64: a0 = c, a1 = s3, a2 = F_badmodel, a3 = cur_name, a4 = val, a5 = known; 0x15a68 jal refuse *)
  do 8 zstep.
  eapply evt_cut.
  { eapply REF with (lo := lo) (rc := rc) (ln := ln + 1) (f := F_badmodel) (args := [AS nm; AS val; AS known]).
    rewrite Hs3.
    rewrite ?(unsigned_lit c), ?(unsigned_lit (ln + 1)), ?(unsigned_lit 0x104e3) by lia.
    eapply pfc_refuse_pre; [exact HCTX | exact HST | exact HFR | exact HCK | exact Hfp | exact HF | exact HR1
                           | exact HR2 |].
    cbn [va_args_ok]. split; [|split; [|split; [|exact I]]].
    - apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); [exact HENV | exact HRC | lia
        | unfold PARSE_FILE_FRAME; lia | apply pfc_le65535; lia | exact HNC].
    - apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); [exact HENV | exact HRC | lia
        | unfold PARSE_FILE_FRAME; lia | exact HVL | exact HVC].
    - apply (pfc_va_frame m fc (bv_unsigned sp) lo c v rc); [exact HENV | exact HRC | lia
        | rewrite HKL; unfold PARSE_FILE_FRAME; lia | apply pfc_le65535; rewrite HKL; lia | exact HKN]. }
  intros ms' POST. unfold ret_void_fp in POST.
  destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' &
                    F'' & fc' & m' & E & FRM & HF' & MU & WM & MI' & TM' & ST' & HRC').
  subst ms'. rewrite (unsigned_lit c) in MU, HRC' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x15a6c: j TAIL *)
  zstep.
  destruct (pfc_after_refuse m m' fc fc' (bv_unsigned sp) lo v c t s o ln d n rc (Some gi) nm F_badmodel
              [AS nm; AS val; AS known] HCTX HST MU WM ST' MI' TM' FRM HRC') as (HH & HS' & Hn' & MU').
  assert (HCS' : pf_curslot m' (bv_unsigned sp) c (Some gi)).
  { apply (pfc_curslot_call m m' fc (bv_unsigned sp) lo c v (Some gi) _ HENV HCS MU).
    intros y Hy. destruct (pfc_outside_dec (refuse_W (bv_unsigned sp) c rc) y) as [Q|Q]; [exact Q|].
    exfalso. destruct (pfc_refuse_W_low m fc (bv_unsigned sp) lo c v rc HENV HRC y Q);
      unfold SEG_C_SIZE, PF_CURSLOT in *; lia. }
  eapply evt_mono.
  { eapply HT; [exact HH | exact HS' | exact Hn' | exact Hregs | exact HCS']. }
  intros ms Hp. unfold p7m_POST. eapply pf_fin_weaken; [exact Hp | | |].
  - exact (munch_trans _ m0 m m' MU0 MU').
  - exact (wmono_trans rsegs _ _ _ WM0 WM).
  - intros k Hk. rewrite (HF' k Hk). exact (HF0 k Hk).
Qed.

(** What the frame holds at the join loop's head 0x159b4 after ti tokens: the two flags (1), ntok (11), and known's
    first p7_kn ti bytes. *)
Definition p7m_MEM (m : word -> option byte) (ti : nat) : Prop :=
  bytes_at rsegs m (bv_unsigned sp + 0x60) (le8 (Z_to_bv 64 1)) /\
  bytes_at rsegs m (bv_unsigned sp + 0x68) (le8 (Z_to_bv 64 1)) /\
  bytes_at rsegs m (bv_unsigned sp + 0x98) (le8 (Z_to_bv 64 11)) /\
  bytes_at rsegs m (bv_unsigned sp + 0xa0) (pf_bytes (p7_J ti)).

(** 0x15a28: snprintf(known + kn, 240 - kn, "%s%s", sep, tab[ti].token), then the continuation at 0x15a2c. *)
Lemma p7m_call : forall ti m fc F' (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word)
    (Q : machine_state -> Prop),
  (ti <= 10)%nat -> p7m_INV m fc F' -> p7m_MEM m ti ->
  a0 = Z_to_bv 64 (bv_unsigned sp + 0xa0 + p7_kn ti) -> a1 = Z_to_bv 64 (240 - p7_kn ti) ->
  a2 = Z_to_bv 64 0x1031b -> a3 = Z_to_bv 64 (p7m_sepp ti) -> a4 = Z_to_bv 64 (tok_ptr ti) ->
  (forall m' fc' F'' (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
     p7m_INV m' fc' F'' -> p7m_MEM m' (S ti) ->
     bytes_at rsegs m' (bv_unsigned sp + 0xa0) (pf_bytes (p7_J (S ti) ++ [0])) ->
     evt rsegs Q (MS (mkR (Z_to_bv 64 0x15a2c) sp gp tp t0 t1 t2 s0 s1
                         (Z_to_bv 64 (Z.of_nat (length (p7_sep ti ++ p7_tok ti)))) a1 a2 a3 a4 a5 a6 a7
                         s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
                     F'' (Z_to_bv 64 0x15a2c) fc' None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR (Z_to_bv 64 0x15a2c) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10 (Z_to_bv 64 1) t3 t4 t5 t6)
                   F' (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros ti m fc F' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 Q Hti HI HM -> -> -> -> -> K.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  pose proof (p7_kn_bound ti ltac:(lia)) as Hkn.
  pose proof (p7m_T_len ti Hti) as HTl.
  pose proof HI as ((HENV & _) & _).
  pose proof HENV as (_ & _ & _ & _ & _ & _ & (ST & _) & _).
  destruct (pfc_printf_at m fc (bv_unsigned sp) lo c v HENV)
    as (STP & HIE & HSP & HFRM & MI & TM & HG1 & (can & HG2)).
  destruct (pfc_dst_stk m lo (bv_unsigned sp + PARSE_FILE_FRAME) (bv_unsigned sp + 0xa0 + p7_kn ti) (240 - p7_kn ti)
              ST ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia) ltac:(lia)) as (junk & DST).
  pose proof SNP as SNP0. unfold snprintf_contract in SNP0. cbv zeta in SNP0.
  eapply evt_cut.
  { eapply SNP0 with (lo := bv_unsigned sp - SNPRINTF_K) (fmt := [37; 115; 37; 115]) (ps := [Ps; Ps])
                     (args := [APtr (p7_sep ti); APtr (p7_tok ti)]) (T := p7_sep ti ++ p7_tok ti)
                     (junk := junk) (canary := can);
      rewrite ?(unsigned_lit 0x1031b), ?(unsigned_lit (bv_unsigned sp + 0xa0 + p7_kn ti)),
        ?(unsigned_lit (240 - p7_kn ti)) by lia.
    - apply pfc_lit_at; [exact MI | lia | cbn [length]; lia | vm_compute; reflexivity].
    - unfold snprintf_c.RO_LO. lia.
    - unfold snprintf_c.RO_END. cbn [length]. lia.
    - reflexivity.
    - cbn [pf_args_ok]. split; [|split; [|exact I]].
      + apply p7m_sep_arg; [exact MI | unfold SNPRINTF_K; lia | lia].
      + apply p7m_tok_arg; [exact Hti | exact MI | unfold SNPRINTF_K; lia | lia].
    - cbn [printf_facts_c.pf_text option_map]. rewrite app_nil_r. reflexivity.
    - exact DST.
    - lia.
    - lia.
    - lia.
    - right. lia.
    - apply pfc_img_free_hi. lia.
    - exact STP.
    - lia.
    - exact HIE.
    - exact HSP.
    - exact HFRM.
    - exact MI.
    - exact TM.
    - exact HG1.
    - exact HG2. }
  intros ms' POST. unfold printf_post in POST.
  destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
                    E & MU & WM & MI' & TM' & FRM & HF' & ST' & HB').
  subst ms'.
  rewrite ?(unsigned_lit (bv_unsigned sp + 0xa0 + p7_kn ti)), ?(unsigned_lit (240 - p7_kn ti)) in MU, HB' by lia.
  rewrite firstn_all2 in MU, HB' by lia.
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (HW : forall x, ~ outside [(bv_unsigned sp - SNPRINTF_K, bv_unsigned sp);
                                    (bv_unsigned sp + 0xa0 + p7_kn ti,
                                     bv_unsigned sp + 0xa0 + p7_kn ti +
                                       Z.of_nat (length (p7_sep ti ++ p7_tok ti)) + 1)] x -> p7m_scr x).
  { intros x Hx. apply p7m_not_out2 in Hx. unfold p7m_scr, SNPRINTF_K in *. lia. }
  assert (HP : forall x, ~ outside [(bv_unsigned sp - SNPRINTF_K, bv_unsigned sp);
                                    (bv_unsigned sp + 0xa0 + p7_kn ti,
                                     bv_unsigned sp + 0xa0 + p7_kn ti +
                                       Z.of_nat (length (p7_sep ti ++ p7_tok ti)) + 1)] x ->
                         bv_unsigned sp <= x -> exists b, mrd rsegs m' (wa x) = Some b).
  { intros x Hx Hx2. apply p7m_not_out2 in Hx. apply (pfc_bytes_mrd m' _ _ x HB').
    unfold pf_bytes. rewrite length_map, length_app. cbn [length]. unfold SNPRINTF_K in Hx. lia. }
  assert (ST'' : stk rsegs m' lo (bv_unsigned sp)).
  { eapply (pfc_stk_back _ m m' lo (bv_unsigned sp) SNPRINTF_K); [ | exact MU | exact WM | exact ST'
                                                             | unfold SNPRINTF_K; lia | unfold SNPRINTF_K; lia |].
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                       ltac:(unfold PARSE_FILE_FRAME; lia))).
    - intros x Hx. apply p7m_out2; unfold SNPRINTF_K in *; lia. }
  pose proof (p7m_inv_step m m' fc fc' F' Ft _ HI MU WM HW HP ST'' MI' TM' FRM HF') as HI'.
  pose proof HM as (HM60 & HM68 & HM98 & HMJ).
  assert (KEEPB : forall a bs, bytes_at rsegs m a bs -> bv_unsigned sp <= a ->
                    a + Z.of_nat (length bs) <= bv_unsigned sp + 0xa0 + p7_kn ti -> bytes_at rsegs m' a bs).
  { intros a bs B Ha1 Ha2. apply (pfc_bytes_munch _ m m' a bs B MU). intros x Hx.
    apply p7m_out2; unfold SNPRINTF_K; lia. }
  pose proof (KEEPB _ _ HM60 ltac:(lia) ltac:(rewrite length_le8; lia)) as HM60'.
  pose proof (KEEPB _ _ HM68 ltac:(lia) ltac:(rewrite length_le8; lia)) as HM68'.
  pose proof (KEEPB _ _ HM98 ltac:(lia) ltac:(rewrite length_le8; lia)) as HM98'.
  pose proof (KEEPB _ _ HMJ ltac:(lia) ltac:(unfold pf_bytes; rewrite length_map; unfold p7_kn; lia)) as HMJ'.
  assert (HJ : bytes_at rsegs m' (bv_unsigned sp + 0xa0) (pf_bytes (p7_J (S ti) ++ [0]))).
  { rewrite (p7m_J_S ti Hti), <- app_assoc. unfold pf_bytes. rewrite map_app. apply bytes_at_app. split.
    - exact HMJ'.
    - rewrite length_map. exact HB'. }
  assert (HM' : p7m_MEM m' (S ti)).
  { split; [exact HM60'|]. split; [exact HM68'|]. split; [exact HM98'|].
    pose proof HJ as HJ2. unfold pf_bytes in HJ2 |- *. rewrite map_app in HJ2. apply bytes_at_app in HJ2.
    exact (proj1 HJ2). }
  eapply K; [exact HI' | exact HM' | exact HJ].
Qed.

(** Row ti's token pointer, read from the table (tab = 0x21468 in .data.rel.ro reads as the image: pf_env's
    cat_img; fuzz_catalogue_row.row_img). *)
Lemma p7m_row : forall m fc F' ti, p7m_INV m fc F' -> (ti < 11)%nat ->
  ov_read_bytes rsegs m (wa (0x21468 + 296 * Z.of_nat ti)) 8 = Some (le8 (Z_to_bv 64 (tok_ptr ti))).
Proof.
  intros m fc F' ti HI Hti. apply p7m_ld8.
  destruct HI as ((HE & _) & _).
  pose proof HE as (_ & _ & _ & _ & _ & Hcat & _).
  pose proof (U.Prog.fuzz_catalogue_row.row_img ti Hti) as E. unfold FUZZ_CATALOGUE in E.
  apply (U.Prog.fuzz_catalogue_row.fcr_bytes_img rsegs m _ 8 _ E); [lia | lia |].
  intros a Ha. apply Hcat. cbn [sa_catalogue SA SEG_UBSAN]. unfold CAT_BYTES. lia.
Qed.

(** The join loop's head 0x159b4 after ti tokens: s9 = ti, s6 = kn, s8 = &tab[ti], s4 = tab, a2 = 240. *)
Definition p7m_HEAD (ti : nat) : Prop :=
  forall m fc F' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
    p7m_INV m fc F' -> p7m_MEM m ti ->
    a2 = Z_to_bv 64 0xf0 -> s4 = Z_to_bv 64 0x21468 -> s6 = Z_to_bv 64 (p7_kn ti) ->
    s8 = Z_to_bv 64 (0x21468 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (Z.of_nat ti) ->
    evt rsegs p7m_POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10
               (Z_to_bv 64 1) t3 t4 t5 t6)
          F' (Z_to_bv 64 0x159b4) fc None m (seg_rom rsegs)).

Ltac p7m_eqti ti Hti :=
  first [ p7m_eq | clear - Hti; p7m_cases ti ltac:(first [reflexivity | apply bv_eq; vm_compute; reflexivity]) ].

(** 0x159d0, pass ti with a3 = its separator: the four trap tests of &tab[ti], the token pointer, snprintf, then
    the exit test (ti + 1 >= ntok: the refusal) and the loop test (kn + 2 < 240: always). *)
Lemma p7m_body : forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_HEAD (S ti)) ->
  forall m fc F' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
    p7m_INV m fc F' -> p7m_MEM m ti ->
    a3 = Z_to_bv 64 (p7m_sepp ti) -> s4 = Z_to_bv 64 0x21468 -> s6 = Z_to_bv 64 (p7_kn ti) ->
    s8 = Z_to_bv 64 (0x21468 + 296 * Z.of_nat ti) -> s9 = Z_to_bv 64 (Z.of_nat ti) ->
    evt rsegs p7m_POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10
               (Z_to_bv 64 1) t3 t4 t5 t6)
          F' (Z_to_bv 64 0x159d0) fc None m (seg_rom rsegs)).
Proof.
  intros ti Hti HN m fc F' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 HI HM -> -> -> -> ->.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  pose proof (p7_kn_bound ti ltac:(lia)) as Hkn.
  pose proof HM as (HM60 & HM68 & HM98 & HMJ).
  pose proof (p7m_ld8 m _ _ HM68) as HR68.
  pose proof (p7m_ld8 m _ _ HM60) as HR60.
  pose proof (p7m_row m fc F' ti HI ltac:(lia)) as HRT.
  (* 0x159d0 a0 = 296; mul a0, s9; add a1, a0, s4; seqz a2, a1; ld a4, 0x68(sp) *)
  do 5 zstep.
  (* 0x159e4 beq a4, a2 -> trap *)
  zstep. if_cases K1; [p7m_refute K1 ti Hti|].
  (* 0x159e8 bltu a1, s4 -> trap *)
  zstep. if_cases K2; [p7m_refute K2 ti Hti|].
  (* 0x159ec a1 = 296; mulh a1, s9, a1; srai a0; xor; snez *)
  do 5 zstep.
  (* 0x15a00 bnez a0 -> trap *)
  zstep. if_cases K3; [p7m_refute K3 ti Hti|].
  (* 0x15a04 ld a0, 0x60(sp); 0x15a08 beqz a0 -> trap *)
  zstep. zstep. if_cases K4; [p7m_refute K4 ti Hti|].
  (* 0x15a0c ld a4, 0(s8); a0 = known + kn; a1 = 240 - kn; a2 = "%s%s" *)
  do 7 zstep.
  (* 0x15a28 jal snprintf *)
  zstep.
  eapply (p7m_call ti m fc F'); [exact Hti | exact HI | exact HM | p7m_eq | p7m_eq | p7m_eq | p7m_eq | p7m_eq |].
  intros m' fc' F'' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HI' HM' HJ'.
  pose proof HM' as (_ & _ & HM98' & _).
  pose proof (p7m_ld8 m' _ _ HM98') as HR98.
  (* 0x15a2c a2 = 240; ld a1, 0x98(sp); s9 = ti + 1 *)
  do 3 zstep.
  (* 0x15a38 bgeu s9, a1 -> 0x15a4c *)
  zstep. if_cases K5.
  - (* ti + 1 = ntok: the 11 tokens are joined, the refusal *)
    assert (E10 : ti = 10%nat).
    { clear - K5 Hti. revert K5. p7m_cases ti ltac:(first [intros; reflexivity | intros K; p7m_vkill K]). }
    subst ti. rewrite p7_J_11 in HJ'.
    eapply p7m_ref; [exact HI' | exact HJ'].
  - assert (Hlt : (ti < 10)%nat).
    { clear - K5 Hti. revert K5. p7m_cases ti ltac:(first [intros; lia | intros K; p7m_vkill K]). }
    pose proof (p7m_kn_S ti Hti) as KS.
    pose proof (p7_kn_bound (S ti) ltac:(lia)) as Hkn1.
    pose proof (p7m_T_len ti Hti) as HTl.
    (* 0x15a3c kn += ret; a0 = kn + 2; s8 += 296 *)
    do 3 zstep.
    (* 0x15a48 bltu a0, a2 -> 0x159b4 *)
    zstep. if_cases K6; [|p7m_refute K6 ti Hti].
    eapply (HN Hlt); [exact HI' | exact HM' | p7m_eqti ti Hti | p7m_eqti ti Hti | p7m_eqti ti Hti
                     | p7m_eqti ti Hti | p7m_eqti ti Hti].
Qed.

(** 0x159b4, the loop head: the trap on 240 < kn, then the separator ("" for row 0, "|" after). *)
Lemma p7m_head : forall ti, (ti <= 10)%nat -> ((ti < 10)%nat -> p7m_HEAD (S ti)) -> p7m_HEAD ti.
Proof.
  intros ti Hti HN. unfold p7m_HEAD.
  intros m fc F' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 HI HM -> -> -> -> ->.
  (* 0x159b4 bltu a2, s6 -> trap *)
  zstep. if_cases K1; [p7m_refute K1 ti Hti|].
  (* 0x159b8 beqz s9, 0x159c8 *)
  zstep. if_cases K2.
  - assert (E0 : ti = 0%nat).
    { clear - K2 Hti. revert K2. p7m_cases ti ltac:(first [intros; reflexivity | intros K; p7m_vkill K]). }
    subst ti.
    (* 0x159c8 auipc a0; addi a3, a0, -0x63a *)
    do 2 zstep.
    eapply (p7m_body 0%nat); [lia | exact HN | exact HI | exact HM | p7m_eq | reflexivity | reflexivity | reflexivity
                     | reflexivity].
  - assert (E0 : ti <> 0%nat).
    { clear - K2 Hti. revert K2. p7m_cases ti ltac:(first [intros; lia | intros K; p7m_vkill K]). }
    (* 0x159bc auipc a0; addi a3, a0, -0x3cc; j 0x159d0 *)
    do 3 zstep.
    eapply (p7m_body ti); [lia | exact HN | exact HI | exact HM | | reflexivity | reflexivity | reflexivity
                     | reflexivity].
    unfold p7m_sepp. replace (ti =? 0)%nat with false by (symmetry; apply Nat.eqb_neq; exact E0). p7m_eq.
Qed.

Lemma p7m_loop : forall k, (k <= 10)%nat -> p7m_HEAD (10 - k).
Proof.
  induction k as [|k IH]; intros Hk.
  - apply p7m_head; [lia | intros H; exfalso; lia].
  - apply p7m_head; [lia|]. intros _. replace (S (10 - S k)) with (10 - k)%nat by lia. apply IH. lia.
Qed.

(** 0x15974, the miss: ntok = 0, reac_box_catalogue(&ntok), the empty-table test, the loop's registers and the
    two UBSan flags, then the join loop. *)
Lemma p7m_entry : forall m fc F' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word),
  p7m_INV m fc F' ->
  evt rsegs p7m_POST
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 vp) s8 s9 s10
             (Z_to_bv 64 1) t3 t4 t5 t6)
        F' (Z_to_bv 64 0x15974) fc None m (seg_rom rsegs)).
Proof.
  intros m fc F' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 HI.
  destruct (p7m_inv_lo m fc F' HI) as (Hlo0 & Hlo & Hsp & Hap & Himg & Hsp63 & Hal).
  pose proof HI as ((HENV & _) & _).
  pose proof HENV as (_ & _ & _ & _ & (FRM & TM & _) & _ & (ST & _) & MI & _).
  destruct (pfc_dst_stk m lo (bv_unsigned sp + PARSE_FILE_FRAME) (bv_unsigned sp + 152) 8 ST
              ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia) ltac:(lia)) as (junk & SLOT).
  change (Z.to_nat 8) with 8%nat in SLOT.
  pose proof (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                       ltac:(unfold PARSE_FILE_FRAME; lia))) as STL.
  pose proof (munch_refl [(bv_unsigned sp + 152, bv_unsigned sp + 160)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (conj HI (conj ST TM)) as KEEP. clear HI HENV ST TM.
  (* 0x15974 sd zero, 0x98(sp) *)
  zstep.
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + 152) _ |- _ => rename mm into mS1; rename H into SLOT1 end.
  (* 0x15978 a0 = sp + 0x98; 0x1597c jal reac_box_catalogue *)
  do 2 zstep.
  eapply evt_cut.
  { eapply CAT with (c := bv_unsigned sp + 152); [reflexivity|].
    right. split; [Z.div_mod_to_equations; lia | exact (proj2 SLOT1)]. }
  intros ms' (a1c & m2 & Ems & POST). subst ms'.
  rewrite ret_pc_even by (try lia; reflexivity).
  assert (E0 : (bv_unsigned sp + 152 =? 0) = false) by (apply Z.eqb_neq; lia).
  rewrite E0 in POST. destruct POST as (B11 & MUc & WMc & MIc).
  destruct KEEP as (HI & STf & TM).
  assert (MU2 : munch [(bv_unsigned sp + 152, bv_unsigned sp + 160)] m m2).
  { apply (munch_trans _ m mS1 m2 MU).
    apply (munch_weaken [(bv_unsigned sp + 152, bv_unsigned sp + 152 + 8)]); [|exact MUc].
    intros x Hx. cbn [outside] in Hx |- *. destruct Hx as [Hx _]. split; [lia | exact I]. }
  pose proof (wmono_trans rsegs _ _ _ WM WMc) as WM2.
  pose proof (MIc MI) as MI2.
  assert (STL2 : stk rsegs m2 lo (bv_unsigned sp)).
  { apply (stk_transport_disjoint rsegs _ mS1 m2 lo (bv_unsigned sp) STL MUc WMc). cbn [disjoint_from].
    split; [lia | exact I]. }
  assert (TM2 : MemNorm.task_mem rsegs m2).
  { apply (pfc_task_mem_munch _ m m2 TM MU2). intros x Hx. apply p7m_not_out1 in Hx.
    destruct STf as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (b & Hb)].
    unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  assert (HI2 : p7m_INV m2 fc F').
  { apply (p7m_inv_step m m2 fc fc F' F' _ HI MU2 WM2); [ | | exact STL2 | exact MI2 | exact TM2 | exact FRM
                                                         | intros; reflexivity].
    - intros x Hx. apply p7m_not_out1 in Hx. unfold p7m_scr. lia.
    - intros x Hx _. apply p7m_not_out1 in Hx. apply (pfc_bytes_mrd m2 _ _ x B11). rewrite length_le8. lia. }
  clear MU2 WM2 MU WM MUc WMc STL SLOT1 STf TM HI MI MIc.
  pose proof HI2 as ((HENV2 & _) & _).
  pose proof HENV2 as (_ & _ & _ & _ & _ & _ & (ST2 & _) & _).
  destruct (pfc_dst_stk m2 lo (bv_unsigned sp + PARSE_FILE_FRAME) (bv_unsigned sp + 96) 16 ST2
              ltac:(lia) ltac:(unfold PARSE_FILE_FRAME; lia) ltac:(lia)) as (junk2 & SLOT2).
  change (Z.to_nat 16) with 16%nat in SLOT2.
  pose proof (p7m_ld8 m2 _ _ B11) as HR98.
  pose proof (munch_refl [(bv_unsigned sp + 96, bv_unsigned sp + 112)] m2) as MU3.
  pose proof (wmono_refl rsegs m2) as WM3.
  pose proof (conj HI2 (conj ST2 TM2)) as KEEP2. clear HI2 HENV2 ST2 TM2.
  (* 0x15980 ld a1, 0x98(sp); a2 = 240; 0x15988 beqz a1 *)
  do 3 zstep. if_cases K0; [exfalso; p7m_vkill K0|].
  (* 0x1598c .. 0x159b0: s4 = tab, s9 = 0, s6 = 0, the flags (sd at sp + 0x68 and sp + 0x60), s8 = tab *)
  do 10 zstep.
  match goal with H : rw_cells _ ?mm (bv_unsigned sp + 96) _ |- _ => rename mm into mS3; rename H into CH end.
  destruct KEEP2 as (HI2 & ST2 & TM2).
  destruct (p7m_cells2 mS3 _ _ _ CH ltac:(p7m_eq) ltac:(p7m_eq)) as [FL60 FL68].
  assert (TM3 : MemNorm.task_mem rsegs mS3).
  { apply (pfc_task_mem_munch _ m2 mS3 TM2 MU3). intros x Hx. apply p7m_not_out1 in Hx.
    destruct ST2 as (_ & _ & STa).
    destruct (STa (bv_unsigned x) ltac:(unfold PARSE_FILE_FRAME; lia)) as [_ (b & Hb)].
    unfold wa in Hb. rewrite Z_to_bv_bv_unsigned in Hb. rewrite Hb. discriminate. }
  assert (HI3 : p7m_INV mS3 fc F').
  { apply (p7m_inv_step m2 mS3 fc fc F' F' _ HI2 MU3 WM3); [ | | exact STL2 | exact MI2 | exact TM3 | exact FRM
                                                           | intros; reflexivity].
    - intros x Hx. apply p7m_not_out1 in Hx. unfold p7m_scr. lia.
    - intros x Hx _. apply p7m_not_out1 in Hx.
      destruct (Z_lt_le_dec x (bv_unsigned sp + 104)) as [Q|Q].
      + apply (pfc_bytes_mrd mS3 _ _ x FL60). rewrite length_le8. lia.
      + apply (pfc_bytes_mrd mS3 _ _ x FL68). rewrite length_le8. lia. }
  assert (HM3 : p7m_MEM mS3 0).
  { split; [exact FL60|].
    split; [replace (bv_unsigned sp + 0x68) with (bv_unsigned sp + 96 + 8) by lia; exact FL68|].
    split; [exact B11|].
    replace (pf_bytes (p7_J 0)) with (@nil byte) by reflexivity. apply bytes_at_nil. lia. }
  pose proof (p7m_loop 10 (le_n _) : p7m_HEAD 0) as H0.
  eapply H0; [exact HI3 | exact HM3 | p7m_eq | p7m_eq | p7m_eq | p7m_eq | p7m_eq].
Qed.

End P7M.

Theorem p7u_miss : snprintf_contract -> refuse_contract -> reac_box_catalogue_contract -> P7U_MISS.
Proof.
  intros SNP REF CAT. unfold P7U_MISS.
  intros n ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 F F3 fc3 m m3 lo
    v c t s rc nm o ln d gi vp val HT HCTX HST HREGS HCS HVC HVB MU WM HF.
  eapply p7m_entry; try eassumption.
  exact (conj HCTX (conj HST (conj HCS (conj HVC (conj MU (conj WM HF)))))).
Qed.
