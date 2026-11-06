(** reac-pw/fuzz_segconf, piece P5 of reac_segconf_parse_file (the key line, reac_segconf.c:215-293), UBSan build
    (image 1696d6c34ffd): KEY (0x154fc) to NEITHER, OUTS, ROLE, MODEL, IGN, KNOCK or NOKEY. Proves part of function
    reac_segconf_parse_file (its piece S_P5, lib/U/Prog/reac_segconf_parse_file_pieces_c.v).

    The walk mirrors the plain one (lib/Prog/pf_p5.v). What differs: c is read from its frame slot sp + 0x90, cur
    from sp + 0x88; the no-'=' line jumps to P3's refuse site NEITHER (0x15588 .. `j 0x15440`); unquote's tests run
    in another order (0x15534 .. 0x15610); and five branches go to the trap 0x15c7c: `beq s9, s5` (eq = -1),
    `bltu ~v, n - 1` three times and `beq s7, s5` (v = -1). Each falls through because eq and v lie in buf
    (sp + 0x1a8 ..) and sp + 0x420 < 2^63. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_p5_spine.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require pfB_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require pfB_kit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import seg_env.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strchr_c trim_c strlen_c strcasecmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import tolower_c refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Spec Require SegBridge.
Import ListNotations.
Open Scope Z_scope.

(** ** What P5 may write: the callees' stack below sp and buf [sp + 0x1a8, sp + 0x3a8). Everything else at the cut's
    entry memory m0 is kept: c, cur_name, the cur slot, the spill slots, the save area, the text. *)
Definition P5W (sp : Z) : list ivl :=
  [(sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, sp); (sp + PF_BUF, sp + PF_BUF + 512)].
Definition p5_mem (m0 m : word -> option byte) (sp lo : Z) : Prop :=
  munch (P5W sp) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m lo (sp + PARSE_FILE_FRAME).

Ltac sa_num := cbn [SA SEG_PLAIN SEG_UBSAN sa_img_end sa_img_top sa_guard sa_got_guard sa_catalogue] in *.
Ltac stack_num := unfold P5W, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, PF_BUF in *.
Ltac c_num := unfold RC_PARSE_W, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN, RSEG_SIZE, SEG_C_SIZE in *.
Ltac dj := cbn [disjoint_from]; repeat split; first [exact I | lia].

Lemma p5_mem_refl : forall m sp lo, mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
  stk rsegs m lo (sp + PARSE_FILE_FRAME) -> p5_mem m m sp lo.
Proof.
  intros m sp lo MI TM ST. split; [apply munch_refl|]. split; [apply wmono_refl|].
  split; [exact MI|]. split; [exact TM | exact ST].
Qed.

(** The numbers of pf_env this piece uses. *)
Lemma p5_env_num : forall m fc sp lo c v, pf_env m fc sp lo c v ->
  0 <= lo /\ lo + REFUSE_STACK <= sp /\ sa_img_end SA <= lo /\ sp + PARSE_FILE_FRAME < 2 ^ 63 /\
  (sp + PARSE_FILE_FRAME) mod 16 = 0 /\ c <> 0 /\ apart c SEG_C_SIZE lo (sp + PARSE_FILE_FRAME).
Proof.
  intros m fc sp lo c v (C0 & _ & AP & _ & (_ & _ & _ & IL & SPH) & _ & (ST & DEP & AL & _) & _ & SV).
  destruct ST as (LO0 & _ & _). unfold PARSE_FILE_STACK in DEP.
  pose proof (bytes_at_bound _ _ _ _ SV) as B. unfold apart, SEG_C_SIZE, PF_SAVE in *.
  split; [exact LO0|]. split; [lia|]. split; [exact IL|]. split; [exact SPH|]. split; [exact AL|].
  split; [exact C0 | exact AP].
Qed.

(** Every byte of a present stack region is a task byte (MemNorm.task_mem's condition). *)
Lemma p5_stk_task : forall m lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi ->
  forall x : word, lo <= bv_unsigned x < hi ->
  find_segment rsegs (bv_unsigned x) 1 <> None \/ bv_unsigned x < TASK_SIZE.
Proof.
  intros m lo hi T (_ & _ & S) x Hx. destruct (S _ Hx) as [_ [b Hb]].
  replace (wa (bv_unsigned x)) with x in Hb by (unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  unfold mrd in Hb. destruct (m x) as [b'|] eqn:E.
  - exact (T x b' E).
  - left. intros Nf. rewrite (MemNorm.seg_rom_unmapped rsegs x Nf) in Hb. discriminate.
Qed.

Lemma p5_task_tr : forall W m m' lo hi, MemNorm.task_mem rsegs m -> stk rsegs m lo hi -> munch W m m' ->
  (forall x : word, ~ (lo <= bv_unsigned x < hi) -> outside W (bv_unsigned x)) -> MemNorm.task_mem rsegs m'.
Proof.
  intros W m m' lo hi T ST MU H a b E.
  destruct (Z_le_gt_dec lo (bv_unsigned a)) as [L1|L1]; [destruct (Z_lt_ge_dec (bv_unsigned a) hi) as [L2|L2]|].
  - apply (p5_stk_task m lo hi T ST). lia.
  - rewrite (MU a (H a ltac:(lia))) in E. exact (T a b E).
  - rewrite (MU a (H a ltac:(lia))) in E. exact (T a b E).
Qed.

Lemma p5_stk_tr : forall W m m' lo hi, stk rsegs m lo hi -> munch W m m' -> wmono rsegs m m' ->
  (forall x, lo <= x < hi -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) -> stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (S0 & S1 & S) MU WM H. split; [exact S0|]. split; [exact S1|].
  intros a Ha. destruct (S a Ha) as [Wv [b Hb]]. split; [apply WM; exact Wv|].
  destruct (H a Ha) as [O|R]; [|exact R].
  exists b. unfold mrd in *. rewrite (MU (wa a)); [exact Hb|]. rewrite wa_unsigned by lia. exact O.
Qed.

(** After a callee whose writes W lie in P5W, with W's bytes in the frame readable afterwards. *)
Lemma p5_mem_call : forall m0 m m' sp lo W,
  p5_mem m0 m sp lo -> munch W m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp ->
  lo <= sp -> sub_fp W (P5W sp) ->
  (forall x : word, ~ (lo <= bv_unsigned x < sp + PARSE_FILE_FRAME) -> outside W (bv_unsigned x)) ->
  (forall x, sp <= x < sp + PARSE_FILE_FRAME -> outside W x \/ exists b, mrd rsegs m' (wa x) = Some b) ->
  p5_mem m0 m' sp lo.
Proof.
  intros m0 m m' sp lo W (MU & WM & MI & TM & ST) MU' WM' MI' ST' LS SUB OUT RD.
  split; [exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUB MU'))|].
  split; [exact (wmono_trans _ _ _ _ WM WM')|]. split; [exact MI'|].
  split; [exact (p5_task_tr W m m' lo (sp + PARSE_FILE_FRAME) TM ST MU' OUT)|].
  assert (LH : sp <= sp + PARSE_FILE_FRAME) by (unfold PARSE_FILE_FRAME; lia).
  destruct (stk_split rsegs m lo sp (sp + PARSE_FILE_FRAME) ST ltac:(lia)) as [_ ST2].
  apply (stk_merge rsegs m' lo sp (sp + PARSE_FILE_FRAME) ST'); [|lia].
  apply (p5_stk_tr W m m' sp (sp + PARSE_FILE_FRAME) ST2 MU' WM' RD).
Qed.

(** After a store of bs into buf. *)
Lemma p5_mem_store : forall m0 m sp lo a bs,
  p5_mem m0 m sp lo -> lo <= sp -> sp + PF_BUF <= a -> a + Z.of_nat (length bs) <= sp + PF_BUF + 512 ->
  store_ok rsegs m (wa a) (length bs) = true -> p5_mem m0 (write_to_mem m (wa a) bs) sp lo.
Proof.
  intros m0 m sp lo a bs (MU & WM & MI & TM & ST) LS H1 H2 HS.
  pose proof ST as (S0 & S1 & _).
  split; [apply munch_write; [exact MU | stack_num; lia | stack_num; lia | stack_num; cbn [inside]; right; left; lia]|].
  split; [apply wmono_write; exact WM|].
  split; [apply mem_inv_store; [exact MI | exact HS]|].
  split.
  - apply (p5_task_tr [(a, a + Z.of_nat (length bs))] m _ lo (sp + PARSE_FILE_FRAME) TM ST).
    + intros x Hx. rewrite write_to_mem_spec by (stack_num; lia).
      destruct ((a <=? bv_unsigned x) && (bv_unsigned x <? a + Z.of_nat (length bs)))%bool eqn:E;
        [|reflexivity].
      exfalso. apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. cbn [outside] in Hx.
      lia.
    + intros x Hx. cbn [outside]. stack_num. split; [lia | exact I].
  - apply stk_write; [exact ST | stack_num; lia | stack_num; lia].
Qed.

(** The cut facts at m0 hold at m. *)
Lemma p5_len_le8 : forall ws, length (concat (map le8 ws)) = (8 * length ws)%nat.
Proof.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia.
Qed.

Lemma p5_ssp_munch : forall W m m', ssp_ok m -> munch W m m' -> disjoint_from W 0 (sa_img_end SA) -> ssp_ok m'.
Proof.
  intros W m m' (G1 & g & G2) MU D. split; [|exists g].
  - eapply bytes_at_transport; [exact G1 | exact MU |]. rewrite length_le8.
    eapply p5_disjoint_sub; [exact D | sa_num; lia | sa_num; lia].
  - eapply bytes_at_transport; [exact G2 | exact MU |]. rewrite length_le8.
    eapply p5_disjoint_sub; [exact D | sa_num; lia | sa_num; lia].
Qed.

Lemma p5_cat_munch : forall W m m', cat_img rsegs m (sa_catalogue SA) -> munch W m m' ->
  disjoint_from W 0 (sa_img_end SA) -> cat_img rsegs m' (sa_catalogue SA).
Proof.
  intros W m m' CAT MU D a Ha. rewrite <- (CAT a Ha). unfold mrd.
  sa_num. unfold CAT_BYTES in Ha.
  assert (Q : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  rewrite Q. reflexivity.
Qed.

Lemma p5_ctx_mem : forall m0 fc0 m fc sp lo v c t s o ln d n,
  pf_ctx m0 fc0 sp lo v c t s o ln d n -> p5_mem m0 m sp lo -> frm0 fc -> pf_ctx m fc sp lo v c t s o ln d n.
Proof.
  intros m0 fc0 m fc sp lo v c t s o ln d n (E & T & SP & R) (MU & WM & MI & TM & ST) FRM.
  pose proof (p5_env_num m0 fc0 sp lo c v E) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  destruct E as (E1 & E2 & E3 & E4 & (_ & _ & SSP & _ & _) & CAT & (_ & E5 & E6 & E7) & _ & SV).
  assert (D0 : disjoint_from (P5W sp) 0 (sa_img_end SA)) by (stack_num; sa_num; dj).
  split; [|split; [|split; [|exact R]]].
  - split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|].
    split; [split; [exact FRM|]; split; [exact TM|]; split; [exact (p5_ssp_munch _ _ _ SSP MU D0)|];
            split; [exact IL | exact SPH]|].
    split; [exact (p5_cat_munch _ _ _ CAT MU D0)|].
    split; [split; [exact ST|]; split; [exact E5|]; split; [exact E6 | exact E7]|].
    split; [exact MI|].
    unfold saved_at in *. eapply bytes_at_transport; [exact SV | exact MU |].
    rewrite p5_len_le8. unfold sv_list. cbn [length]. unfold PF_SAVE. stack_num. dj.
  - destruct T as (T0 & CS & LS & APT & APTC). split; [exact T0|]. split; [|split; [exact LS|split; assumption]].
    eapply p5_cstr_munch; [exact CS | exact MU |]. unfold apart in APT. stack_num. dj.
  - destruct SP as (SP1 & SP2 & SP3). unfold saved_at in *.
    split; [|split].
    + eapply bytes_at_transport; [exact SP1 | exact MU |]. rewrite p5_len_le8. cbn [length]. stack_num. dj.
    + eapply bytes_at_transport; [exact SP2 | exact MU |]. rewrite p5_len_le8. cbn [length]. stack_num. dj.
    + eapply bytes_at_transport; [exact SP3 | exact MU |]. rewrite length_le8. unfold PF_CSLOT. stack_num. dj.
Qed.

Lemma p5_state_mem : forall m0 fc0 m sp lo v c rc cur nm k,
  pf_env m0 fc0 sp lo c v -> pf_state m0 sp c rc cur nm k -> p5_mem m0 m sp lo -> pf_state m sp c rc cur nm k.
Proof.
  intros m0 fc0 m sp lo v c rc cur nm k E (RC & CO & (f & NB & NE) & CN) (MU & _).
  pose proof (p5_env_num m0 fc0 sp lo c v E) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  split; [eapply p5_rconf_munch; [exact RC | exact MU |]; unfold apart in APC; stack_num; c_num; dj|].
  split; [exact CO|]. split; [|exact CN].
  exists f. split; [|exact NE]. eapply bytes_at_transport; [exact NB | exact MU |].
  destruct NE as [LF _]. rewrite LF. unfold PF_NAMEBUF. stack_num. dj.
Qed.

Lemma p5_curslot_mem : forall m0 m sp lo c cur,
  pf_curslot m0 sp c cur -> p5_mem m0 m sp lo -> pf_curslot m sp c cur.
Proof.
  intros m0 m sp lo c cur CS (MU & _). unfold pf_curslot in *.
  eapply bytes_at_transport; [exact CS | exact MU |]. rewrite length_le8. unfold PF_CURSLOT. stack_num. dj.
Qed.

(** The exit cut's post, at the exit memory, is the entry cut's post (F' equal to F off fa0). *)
Lemma p5_fin_weaken : forall v sp gp tp F F' m0 m lo c st ms,
  p5_mem m0 m (bv_unsigned sp) lo ->
  (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) ->
  pf_fin v sp gp tp F' m lo c st ms -> pf_fin v sp gp tp F m0 lo c st ms.
Proof.
  unfold pf_fin, pf_ret, ret_post_fp.
  intros v sp gp tp F F' m0 m lo c st ms (MU & WM & _) FF
    (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & F2 & fc2 & m2 &
     E & FRM & FF2 & MU2 & WM2 & REST).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, F2, fc2, m2.
  split; [exact E|]. split; [exact FRM|]. split; [intros k Hk; rewrite (FF2 k Hk); exact (FF k Hk)|].
  split; [|split; [exact (wmono_trans _ _ _ _ WM WM2) | exact REST]].
  apply (munch_trans _ m0 m m2); [|exact MU2].
  apply (munch_weaken (P5W (bv_unsigned sp))); [|exact MU].
  unfold sub_fp. intros x Hx. stack_num. cbn [outside] in *. destruct Hx as [Hx _].
  split; [lia | split; [lia | exact I]].
Qed.

(** After a callee that writes only [sp - k, sp). *)
Lemma p5_mem_call1 : forall m0 m m' sp lo k,
  p5_mem m0 m sp lo -> munch [(sp - k, sp)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp ->
  0 <= k <= REFUSE_STACK -> lo + k <= sp -> p5_mem m0 m' sp lo.
Proof.
  intros m0 m m' sp lo k PM MU WM MI ST Hk Hl.
  apply (p5_mem_call m0 m m' sp lo [(sp - k, sp)] PM MU WM MI ST); [lia | | |].
  - unfold sub_fp. intros x Hx. stack_num. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
  - intros x Hx. cbn [outside]. unfold PARSE_FILE_FRAME in Hx. split; [lia | exact I].
  - intros x Hx. left. cbn [outside]. split; [lia | exact I].
Qed.

(** ** The strcasecmp bridge (the kit's pf_lower_eq_bridge): strcasecmp_c.lower_eq on the bytes is
    SegModel.strcasecmp = 0 on NUL-free byte lists. *)
Lemma p5u_scb : forall l w, p5b l -> ~ In 0 l -> p5b w -> ~ In 0 w ->
  (lower_eq (zb l) (zb w) <-> strcasecmp l w = 0).
Proof.
  intros l w Hl Nl Hw Nw.
  exact (OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog.pfB_kit.pf_lower_eq_bridge l w Hl Hw Nl Nw).
Qed.

(** ** The literals strcasecmp compares the key with, in .rodata (the same addresses as plain). *)
Lemma p5_lit_at : forall m a w, mem_inv rsegs m -> 0 <= a -> a + Z.of_nat (length w) + 1 <= 2 ^ 64 ->
  ro_bytes_b rsegs a (zb w ++ [ZERO]) = true -> bytes_at rsegs m a (zb w ++ [ZERO]).
Proof.
  intros m a w MI H1 H2 H3. apply (ro_bytes_at rsegs m); [exact MI | exact H1 | |].
  - rewrite length_app, p5_len_zb. cbn [length]. lia.
  - apply ro_bytes_b_sound. exact H3.
Qed.
Lemma p5_ro_role : ro_bytes_b rsegs 0x10298 (zb S_role ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p5_ro_model : ro_bytes_b rsegs 0x10811 (zb S_model ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p5_ro_ignore : ro_bytes_b rsegs 0x1054f (zb S_ignore ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p5_ro_knock : ro_bytes_b rsegs 0x102a3 (zb S_knock ++ [ZERO]) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma p5_words : forall w, In w [S_role; S_model; S_ignore; S_knock] ->
  p5b w /\ ~ In 0 w /\ (length w <= 6)%nat.
Proof.
  intros w Hw. cbn [In] in Hw.
  repeat destruct Hw as [<- | Hw]; try contradiction;
    (split; [unfold p5b; repeat constructor; lia | split; [cbv; intuition discriminate | cbv; lia]]).
Qed.

(** An 8-byte load of a known word. *)
Lemma p5_ld8 : forall m a w, bytes_at rsegs m a (le8 w) -> ov_read_bytes rsegs m (wa a) 8 = Some (le8 w).
Proof.
  intros m a w B. assert (H := bytes_at_ov_read rsegs m a (le8 w) 0 (length (le8 w)) B ltac:(lia)).
  replace (a + Z.of_nat 0) with a in H by lia. cbn [skipn] in H. rewrite firstn_all, length_le8 in H. exact H.
Qed.

Section Walk.
Hypothesis STRCHR : strchr_contract.
Hypothesis TRIM : trim_contract.
Hypothesis STRLEN : strlen_contract.
Hypothesis SCMP : strcasecmp_contract.
(* trim's result (pf_pieces_spec.L_trim); pf_p5_holds discharges it with the kit's pfB_facts.L_trim_holds. *)
Hypothesis LT : L_trim.

(** strcasecmp(key, w) from the dispatch: key a C string at kp in the frame, w a literal in .rodata. *)
Lemma p5_scmp_call : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo kp : Z) (key : list Z) (la : Z) (w : list Z),
  p5_mem m0 m (bv_unsigned sp) lo -> lo + REFUSE_STACK <= bv_unsigned sp ->
  cstr_at rsegs m kp key -> bv_unsigned sp <= kp ->
  bytes_at rsegs m la (zb w ++ [ZERO]) -> p5b w -> ~ In 0 w -> la + Z.of_nat (length w) + 1 <= bv_unsigned sp - 32 ->
  a0 = Z_to_bv 64 kp -> a1 = Z_to_bv 64 la ->
  (forall (r t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     p5_mem m0 m' (bv_unsigned sp) lo -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
     (r = Z_to_bv 64 0 <-> strcasecmp key w = 0) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                    t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 STRCASECMP) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo kp key la w PM DEP CS KP LB LBb LBn LA -> -> K.
  destruct (p5_cstr_run rsegs m kp key CS) as (BK & KB & KN).
  pose proof PM as (MU & WM & MI & TM & ST).
  pose proof (bytes_at_bound _ _ _ _ BK) as BKb. pose proof (bytes_at_bound _ _ _ _ LB) as LBb'.
  rewrite length_app, p5_len_zb in BKb, LBb'. cbn [length] in BKb, LBb'.
  pose proof ST as (LO0 & _ & _). unfold REFUSE_STACK, PRINTF_K in DEP.
  eapply evt_cut.
  { apply (SCMP ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 kp) (Z_to_bv 64 la) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc m (zb key) (zb w) lo);
      rewrite ?unsigned_lit by lia.
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                      ltac:(unfold PARSE_FILE_FRAME; lia))).
    - exact BK.
    - apply p5_nz_zb; assumption.
    - exact LB.
    - apply p5_nz_zb; assumption.
    - exact MI.
    - lia.
    - right. exact KP.
    - left. rewrite p5_len_zb. lia. }
  intros ms' (r & u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
              E & MU' & WM' & MI' & ST' & _ & _ & R).
  subst ms'. apply (K r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m').
  - apply (p5_mem_call1 m0 m m' (bv_unsigned sp) lo 32 PM MU' WM' MI' ST'); unfold REFUSE_STACK, PRINTF_K; lia.
  - exact MU'.
  - rewrite R. apply p5u_scb; assumption.
Qed.

(** The post every exit of P5 reaches: r_key's. *)
Definition p5_post (v : pf_sv) (sp gp tp : word) (F : bvmap 5 word) (m0 : word -> option byte) (lo c : Z)
    (rc : rconf) (cur : option nat) (nm : list Z) (s : list Z) (o : nat) (ln : Z) : machine_state -> Prop :=
  pf_fin v sp gp tp F m0 lo c (r_lines (r_key rc cur nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))).

(** An exit cut's post at the memory m P5 has made is the post at the cut's entry memory m0. *)
Lemma p5_exit : forall v sp gp tp F m0 m lo c st ms,
  p5_mem m0 m (bv_unsigned sp) lo -> evt rsegs (pf_fin v sp gp tp F m lo c st) ms ->
  evt rsegs (pf_fin v sp gp tp F m0 lo c st) ms.
Proof.
  intros v sp gp tp F m0 m lo c st ms PM H. eapply evt_mono; [exact H|]. intros ms' HP.
  eapply p5_fin_weaken; [exact PM | intros k _; reflexivity | exact HP].
Qed.

(** The facts at every dispatch pc: the cut's entry facts at m0, P5's writes since, and the split key line at m. *)
Definition p5_D (m0 : word -> option byte) (fc : bv 32) (m : word -> option byte) (sp lo : Z) (v : pf_sv)
    (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
    (n : nat) (kp vp : Z) (key val : list Z) : Prop :=
  pf_ctx m0 fc sp lo v c t s o ln d n /\ pf_state m0 sp c rc cur nm (length (skipn o s)) /\
  pf_curslot m0 sp c cur /\ p5_mem m0 m sp lo /\ pf_kv m sp (pf_tline s o) kp vp key val.

Lemma p5_D_call1 : forall m0 fc m m' sp lo v c t s rc cur nm o ln d n kp vp key val,
  p5_D m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val -> p5_mem m0 m' sp lo ->
  munch [(sp - 32, sp)] m m' -> p5_D m0 fc m' sp lo v c t s rc cur nm o ln d n kp vp key val.
Proof.
  intros m0 fc m m' sp lo v c t s rc cur nm o ln d n kp vp key val (CX & PS & CU & PM & KV) PM' MU.
  split; [exact CX|]. split; [exact PS|]. split; [exact CU|]. split; [exact PM'|].
  destruct KV as (EI & CK & IK & CV & IV). unfold pf_inb in IK, IV. unfold PF_BUF in *.
  split; [exact EI|]. split; [eapply p5_cstr_munch; [exact CK | exact MU | dj]|]. split; [exact IK|].
  split; [eapply p5_cstr_munch; [exact CV | exact MU | dj] | exact IV].
Qed.

(** The frame facts every exit cut asks for, at the memory m P5 has made. *)
Lemma p5_D_exit : forall m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val,
  p5_D m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val ->
  pf_ctx m fc sp lo v c t s o ln d n /\ pf_state m sp c rc cur nm (length (skipn o s)) /\ pf_curslot m sp c cur.
Proof.
  intros m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val (CX & PS & CU & PM & KV).
  pose proof CX as ((_ & _ & _ & _ & (FRM & _) & _) & _).
  split; [exact (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM FRM)|].
  split; [exact (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ (proj1 CX) PS PM)|].
  exact (p5_curslot_mem _ _ _ _ _ _ CU PM).
Qed.

Lemma p5_dk : forall n, H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 -> strcasecmp key S_ignore <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15658) fc None m (seg_rom rsegs)).
Proof.
  intros n HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc gi nm o ln
    d kp vp key val D R1 R2 R3.
  pose proof D as (CX & PS & CU & PM & KV).
  pose proof (p5_env_num m0 fc (bv_unsigned sp) lo c v (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof KV as ((ei & EI & EK & EV) & CK & IK & CV & IV).
  zstep. zstep. zstep. zstep.
  pose proof PM as (_ & _ & MI & _ & _).
  destruct (p5_words S_knock ltac:(cbn; tauto)) as (WB & WN & WL).
  assert (KP : bv_unsigned sp <= kp) by (unfold pf_inb, PF_BUF in IK; lia).
  eapply p5_scmp_call with (m0 := m0) (lo := lo) (kp := kp) (key := key) (la := 0x102a3) (w := S_knock);
    [exact PM | exact DEP | exact CK | exact KP
    | apply p5_lit_at; [exact MI | lia | cbn; lia | exact p5_ro_knock]
    | exact WB | exact WN | unfold REFUSE_STACK, PRINTF_K in DEP; sa_num; cbn [length S_knock] in *; lia
    | reflexivity | reflexivity |].
  intros r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU' R.
  replace (ret_pc (Z_to_bv 64 87656)) with (Z_to_bv 64 87656) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D'.
  destruct (p5_D_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D') as (CX' & PS' & CU').
  pose proof D' as (_ & _ & _ & _ & (_ & CK' & IK' & CV' & IV')).
  zstep. if_cases K; zify_cond K.
  - assert (R4 : strcasecmp key S_knock = 0) by (apply R; apply bv_eq; rewrite K; reflexivity).
    unfold p5_post. subst key val. rewrite (p5_rkey_knock rc gi nm (ln + 1) (pf_tline s o) ei EI R1 R2 R3 R4).
    eapply p5_exit; [exact PM' |].
    eapply HK; [exact CX' | exact PS' | repeat split | exact CU' | reflexivity | exact CV' | exact IV'].
  - assert (R4 : strcasecmp key S_knock <> 0).
    { intros E. apply R in E. subst r. apply K. reflexivity. }
    pose proof CX' as (_ & _ & (_ & _ & SP3) & _).
    pose proof (p5_ld8 _ _ _ SP3) as RD. unfold PF_CSLOT in RD.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    unfold p5_post. subst key. rewrite (p5_rkey_nokey rc gi nm (ln + 1) (pf_tline s o) ei EI R1 R2 R3 R4).
    eapply p5_exit; [exact PM' |].
    eapply HN; [exact CX' | exact PS' | repeat split | exact CU' | reflexivity | reflexivity | reflexivity
               | reflexivity | reflexivity | exact CK' | exact IK'].
Qed.

(** strcasecmp(key, "ignore") at 0x15650: IGN, or on to knock. *)
Lemma p5_di : forall n, H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15644) fc None m (seg_rom rsegs)).
Proof.
  intros n HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc gi nm o
    ln d kp vp key val D R1 R2.
  pose proof D as (CX & PS & CU & PM & KV).
  pose proof (p5_env_num m0 fc (bv_unsigned sp) lo c v (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof KV as (_ & CK & IK & _ & _).
  zstep. zstep. zstep. zstep.
  pose proof PM as (_ & _ & MI & _ & _).
  destruct (p5_words S_ignore ltac:(cbn; tauto)) as (WB & WN & WL).
  assert (KP : bv_unsigned sp <= kp) by (unfold pf_inb, PF_BUF in IK; lia).
  eapply p5_scmp_call with (m0 := m0) (lo := lo) (kp := kp) (key := key) (la := 0x1054f) (w := S_ignore);
    [exact PM | exact DEP | exact CK | exact KP
    | apply p5_lit_at; [exact MI | lia | cbn; lia | exact p5_ro_ignore]
    | exact WB | exact WN | unfold REFUSE_STACK, PRINTF_K in DEP; sa_num; lia
    | reflexivity | reflexivity |].
  intros r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU' R.
  replace (ret_pc (Z_to_bv 64 87636)) with (Z_to_bv 64 87636) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D'.
  destruct (p5_D_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D') as (CX' & PS' & CU').
  pose proof D' as (_ & _ & _ & _ & KV').
  zstep. if_cases K; zify_cond K.
  - assert (R3 : strcasecmp key S_ignore = 0) by (apply R; apply bv_eq; rewrite K; reflexivity).
    unfold p5_post. eapply p5_exit; [exact PM' |].
    eapply HI; [exact CX' | exact PS' | repeat split | exact CU' | exact KV' | reflexivity | reflexivity
               | exact R1 | exact R2 | exact R3].
  - assert (R3 : strcasecmp key S_ignore <> 0).
    { intros E. apply R in E. subst r. apply K. reflexivity. }
    eapply p5_dk with (n := n); [exact HK | exact HN | exact D' | exact R1 | exact R2 | exact R3].
Qed.

(** strcasecmp(key, "model") at 0x1563c: MODEL, or on to ignore. *)
Lemma p5_dm : forall n, H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val ->
  strcasecmp key S_role <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15630) fc None m (seg_rom rsegs)).
Proof.
  intros n HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc gi nm
    o ln d kp vp key val D R1.
  pose proof D as (CX & PS & CU & PM & KV).
  pose proof (p5_env_num m0 fc (bv_unsigned sp) lo c v (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof KV as (_ & CK & IK & _ & _).
  zstep. zstep. zstep. zstep.
  pose proof PM as (_ & _ & MI & _ & _).
  destruct (p5_words S_model ltac:(cbn; tauto)) as (WB & WN & WL).
  assert (KP : bv_unsigned sp <= kp) by (unfold pf_inb, PF_BUF in IK; lia).
  eapply p5_scmp_call with (m0 := m0) (lo := lo) (kp := kp) (key := key) (la := 0x10811) (w := S_model);
    [exact PM | exact DEP | exact CK | exact KP
    | apply p5_lit_at; [exact MI | lia | cbn; lia | exact p5_ro_model]
    | exact WB | exact WN | unfold REFUSE_STACK, PRINTF_K in DEP; sa_num; lia
    | reflexivity | reflexivity |].
  intros r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU' R.
  replace (ret_pc (Z_to_bv 64 87616)) with (Z_to_bv 64 87616) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D'.
  destruct (p5_D_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D') as (CX' & PS' & CU').
  pose proof D' as (_ & _ & _ & _ & KV').
  zstep. if_cases K; zify_cond K.
  - assert (R2 : strcasecmp key S_model = 0) by (apply R; apply bv_eq; rewrite K; reflexivity).
    unfold p5_post. eapply p5_exit; [exact PM' |].
    eapply HM; [exact CX' | exact PS' | repeat split | exact CU' | exact KV' | reflexivity | reflexivity
               | exact R1 | exact R2].
  - assert (R2 : strcasecmp key S_model <> 0).
    { intros E. apply R in E. subst r. apply K. reflexivity. }
    eapply p5_di with (n := n); [exact HI | exact HK | exact HN | exact D' | exact R1 | exact R2].
Qed.

(** strcasecmp(key, "role") at 0x15628: ROLE, or on to model. *)
Lemma p5_dr : forall n, H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1561c) fc None m (seg_rom rsegs)).
Proof.
  intros n HR HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc gi
    nm o ln d kp vp key val D.
  pose proof D as (CX & PS & CU & PM & KV).
  pose proof (p5_env_num m0 fc (bv_unsigned sp) lo c v (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof KV as (_ & CK & IK & _ & _).
  zstep. zstep. zstep. zstep.
  pose proof PM as (_ & _ & MI & _ & _).
  destruct (p5_words S_role ltac:(cbn; tauto)) as (WB & WN & WL).
  assert (KP : bv_unsigned sp <= kp) by (unfold pf_inb, PF_BUF in IK; lia).
  eapply p5_scmp_call with (m0 := m0) (lo := lo) (kp := kp) (key := key) (la := 0x10298) (w := S_role);
    [exact PM | exact DEP | exact CK | exact KP
    | apply p5_lit_at; [exact MI | lia | cbn; lia | exact p5_ro_role]
    | exact WB | exact WN | unfold REFUSE_STACK, PRINTF_K in DEP; sa_num; lia
    | reflexivity | reflexivity |].
  intros r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU' R.
  replace (ret_pc (Z_to_bv 64 87596)) with (Z_to_bv 64 87596) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D'.
  destruct (p5_D_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D') as (CX' & PS' & CU').
  pose proof D' as (_ & _ & _ & _ & KV').
  zstep. if_cases K; zify_cond K.
  - assert (R1 : strcasecmp key S_role = 0) by (apply R; apply bv_eq; rewrite K; reflexivity).
    unfold p5_post. eapply p5_exit; [exact PM' |].
    eapply HR; [exact CX' | exact PS' | repeat split | exact CU' | exact KV' | reflexivity | reflexivity
               | exact R1].
  - assert (R1 : strcasecmp key S_role <> 0).
    { intros E. apply R in E. subst r. apply K. reflexivity. }
    eapply p5_dm with (n := n); [exact HM | exact HI | exact HK | exact HN | exact D' | exact R1].
Qed.

(** The cur test at 0x15614 (`ld a0, 0x88(sp); beqz a0, OUTS`), then the dispatch. *)
Lemma p5_disp : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc m (bv_unsigned sp) lo v c t s rc cur nm o ln d n kp vp key val ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15614) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc
    cur nm o ln d kp vp key val D.
  pose proof D as (CX & PS & CU & PM & KV).
  destruct (p5_D_exit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D) as (CX' & PS' & CU').
  pose proof (p5_ld8 _ _ _ CU') as RD. unfold PF_CURSLOT in RD.
  pose proof KV as ((ei & EI & EK & EV) & CK & IK & CV & IV).
  destruct cur as [gi|].
  - pose proof PS as ((bs & BC & BE) & CO & _). cbn [pf_cur_ok] in CO.
    pose proof (bytes_at_bound _ _ _ _ BC) as BB. destruct BE as (BL & SL & _).
    pose proof (proj1 (p5_env_num _ _ _ _ _ _ (proj1 CX)) ) as LO0.
    pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (_ & _ & _ & _ & _ & C0 & _).
    cbn [pf_cur_ptr] in RD. unfold rseg_addr, RSEG_SIZE in RD. unfold SEG_C_SIZE in BL.
    zstep. zstep. if_cases K; zify_cond K.
    + exfalso. rewrite ?unsigned_lit in K by lia. Z.div_mod_to_equations. lia.
    + eapply p5_dr with (n := n); [exact HR | exact HM | exact HI | exact HK | exact HN | exact D].
  - cbn [pf_cur_ptr] in RD.
    zstep. zstep.
    unfold p5_post. subst key. rewrite (p5_rkey_outs rc nm (ln + 1) (pf_tline s o) ei EI).
    eapply p5_exit; [exact PM |].
    eapply HO; [exact CX' | exact PS' | repeat split | exact CU' | reflexivity | exact CK | exact IK].
Qed.

(** The dispatch facts from the bytes of key and val in buf. *)
Lemma p5_mkD : forall m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val ei,
  pf_ctx m0 fc sp lo v c t s o ln d n -> pf_state m0 sp c rc cur nm (length (skipn o s)) ->
  pf_curslot m0 sp c cur -> p5_mem m0 m sp lo ->
  strchr (pf_tline s o) EQ = Some ei -> key = r_trim (firstn ei (pf_tline s o)) ->
  val = r_unquote (r_trim (skipn (S ei) (pf_tline s o))) ->
  bytes_at rsegs m kp (zb key ++ [ZERO]) -> p5b key -> ~ In 0 key -> pf_inb (sp + PF_BUF) kp key ->
  bytes_at rsegs m vp (zb val ++ [ZERO]) -> p5b val -> ~ In 0 val -> pf_inb (sp + PF_BUF) vp val ->
  p5_D m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val.
Proof.
  intros m0 fc m sp lo v c t s rc cur nm o ln d n kp vp key val ei CX PS CU PM EI EK EV BK KB KN IK BV VB VN IV.
  pose proof PM as (_ & _ & _ & _ & ST).
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & _ & _ & _ & _ & _).
  pose proof IK as IK0. pose proof IV as IV0.
  unfold pf_inb, PF_BUF in IK, IV. unfold REFUSE_STACK, PRINTF_K in DEP.
  split; [exact CX|]. split; [exact PS|]. split; [exact CU|]. split; [exact PM|].
  split; [exists ei; split; [exact EI | split; assumption]|].
  split; [eapply p5_cstr_stk; [exact BK | exact KB | exact KN | exact ST | lia | unfold PARSE_FILE_FRAME; lia]|].
  split; [exact IK0|].
  split; [eapply p5_cstr_stk; [exact BV | exact VB | exact VN | exact ST | lia | unfold PARSE_FILE_FRAME; lia]|].
  exact IV0.
Qed.

(** After a callee that writes nothing (strlen). *)
Lemma p5_mem_nil : forall m0 m m' sp lo, p5_mem m0 m sp lo -> lo <= sp ->
  munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> p5_mem m0 m' sp lo.
Proof.
  intros m0 m m' sp lo PM LS MU WM MI. pose proof PM as (_ & _ & _ & _ & ST).
  assert (ST' : stk rsegs m' lo sp).
  { apply (p5_stk_tr [] m m' lo sp); [| exact MU | exact WM | intros x _; left; exact I].
    exact (proj1 (stk_split rsegs m lo sp (sp + PARSE_FILE_FRAME) ST ltac:(unfold PARSE_FILE_FRAME; lia))). }
  apply (p5_mem_call m0 m m' sp lo [] PM MU WM MI ST' LS).
  - intros x _. exact I.
  - intros x _. exact I.
  - intros x _. left. exact I.
Qed.

(** A store into a present stack region. *)
Lemma p5_store_ok : forall m lo hi a (j : nat), stk rsegs m lo hi -> lo <= a -> a + Z.of_nat j <= hi ->
  store_ok rsegs m (wa a) j = true.
Proof.
  intros m lo hi a j ST H1 H2.
  pose proof (p5_stk_wr rsegs m lo hi a (Z.of_nat j) ST H1 ltac:(lia) H2) as W.
  pose proof (wr_at_store_ok rsegs m a (Z.of_nat j) 0 j W ltac:(lia) ltac:(lia)) as S.
  rewrite Z.add_0_r in S. exact S.
Qed.

(** A UBSan pointer-overflow branch to 0x15c7c that the bounds in context rule out. *)
Ltac p5_trap :=
  let KT := fresh "KT" in
  if_cases KT; zify_cond KT;
  [ exfalso; rewrite ?zb_lxor_ones in KT by lia; rewrite ?unsigned_lit in KT by lia;
    rewrite ?Z.mod_small in KT by lia; lia
  | clear KT ].

(** The unquote outcome at the cur test 0x15614: val = r_unquote V at vp, by UQ : r_unquote V = (the bytes at vp). *)
Ltac p5_keep EV UQ BVq VBq VNq IVq :=
  eapply p5_disp; [eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | ];
  eapply p5_mkD;
  [ eassumption | eassumption | eassumption | eassumption | eassumption | eassumption | reflexivity
  | eassumption | eassumption | eassumption | eassumption
  | rewrite <- EV, UQ; exact BVq | rewrite <- EV, UQ; exact VBq
  | rewrite <- EV, UQ; exact VNq | rewrite <- EV, UQ; exact IVq ].

(** strlen(v) at 0x15530 and the inlined unquote (0x15534 .. 0x15610), to the cur test at 0x15614. V = the trimmed
    value at vp0; key at kp before it. *)
Lemma p5_unq : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (ei : nat) (kp vp0 : Z) (key V : list Z),
  key = r_trim (firstn ei (pf_tline s o)) -> V = r_trim (skipn (S ei) (pf_tline s o)) ->
  pf_ctx m0 fc (bv_unsigned sp) lo v c t s o ln d n -> pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  pf_curslot m0 (bv_unsigned sp) c cur -> p5_mem m0 m (bv_unsigned sp) lo ->
  strchr (pf_tline s o) EQ = Some ei ->
  bytes_at rsegs m kp (zb key ++ [ZERO]) -> p5b key -> ~ In 0 key -> pf_inb (bv_unsigned sp + PF_BUF) kp key ->
  bytes_at rsegs m vp0 (zb V ++ [ZERO]) -> p5b V -> ~ In 0 V -> pf_inb (bv_unsigned sp + PF_BUF) vp0 V ->
  kp + Z.of_nat (length key) < vp0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) (Z_to_bv 64 vp0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 vp0) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15530) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc cur
    nm o ln d ei kp vp0 key V EK EV CX PS CU PM EI BK KB KN IK BV VB VN IV KV.
  pose proof PM as (MU & WM & MI & TM & ST).
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof IK as IK0. pose proof IV as IV0.
  unfold pf_inb, PF_BUF in IK, IV. unfold REFUSE_STACK, PRINTF_K in DEP. unfold PARSE_FILE_FRAME in SPH, ST.
  assert (CV : cstr_at rsegs m vp0 V) by (eapply p5_cstr_stk; [exact BV | exact VB | exact VN | exact ST | lia | lia]).
  destruct CV as (bs & sl & BV' & Ez & NZ & SLK).
  assert (LB : length bs = length V) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  zstep.
  eapply evt_cut.
  { eapply STRLEN with (str := bs) (slack := sl); rewrite ?unsigned_lit by lia;
      [exact BV' | apply SegBridge.nul_free_bytes; rewrite Ez; exact NZ | rewrite LB; exact SLK | exact MI]. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
              E & MU' & WM' & MI' & _).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 87348)) with (Z_to_bv 64 87348) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (PM' : p5_mem m0 m' (bv_unsigned sp) lo) by (apply (p5_mem_nil m0 m m' _ lo PM); [lia | exact MU' | exact WM' | exact MI']).
  assert (BK' : bytes_at rsegs m' kp (zb key ++ [ZERO])) by (eapply bytes_at_transport; [exact BK | exact MU' | exact I]).
  assert (BV2 : bytes_at rsegs m' vp0 (zb V ++ [ZERO])) by (eapply bytes_at_transport; [exact BV | exact MU' | exact I]).
  clear MU' WM' BK BV BV' PM MU WM MI TM ST.
  rewrite LB.
  zstep. zstep. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* |V| < 2: val = V *)
    assert (UQ : r_unquote V = V) by (apply p5_unq_short; [exact VN | lia]).
    p5_keep EV UQ BV2 VB VN IV0.
  - (* |V| >= 2: the first byte *)
    pose proof (p5_run_read rsegs m' vp0 V 0 BV2 ltac:(lia)) as RD0. replace (vp0 + Z.of_nat 0) with vp0 in RD0 by lia.
    pose proof (p5b_nth V 0 VB) as R0.
    pose proof (p5b_nth V (length V - 1) VB) as Rn.
    pose proof (p5_run_read rsegs m' vp0 V (length V - 1) BV2 ltac:(lia)) as RDn.
    replace (vp0 + Z.of_nat (length V - 1)) with (vp0 + (Z.of_nat (length V) + -1)) in RDn by lia.
    (* the unquote store and v + 1 (0x15600 .. 0x15610), from either quote *)
    assert (STRIP : forall (q : Z) (x2 x3 : word), (q = DQ \/ q = SQ) -> nth 0 V 0 = q ->
      nth (length V - 1) V 0 = q ->
      evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
        (MS (mkR (Z_to_bv 64 87348) sp gp tp u0 u1 u2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP)
                 (Z_to_bv 64 (Z.of_nat (length V) + -1)) (Z_to_bv 64 (Z.lxor vp0 18446744073709551615)) x2 x3
                 ua4 ua5 ua6 ua7 (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1))
                 s6 (Z_to_bv 64 vp0) (Z_to_bv 64 kp) s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) u3 u4 u5 u6)
            F (Z_to_bv 64 0x15600) fc None m' (seg_rom rsegs))).
    { intros q x2 x3 Hq Q0 Qn.
      assert (UQ : r_unquote V = slice 1 (length V - 1) V)
        by (apply (p5_unq_strip V q); [exact VN | lia | exact Hq | exact Q0 | exact Qn]).
      destruct (p5_slice_props V 1 (length V - 1) VB VN) as (SB & SN & SL).
      assert (HS : store_ok rsegs m' (wa (vp0 + (Z.of_nat (length V) + -1))) 1 = true).
      { pose proof PM' as (_ & _ & _ & _ & ST'). unfold PARSE_FILE_FRAME in ST'.
        apply (p5_store_ok m' lo (bv_unsigned sp + 1056)); [exact ST' | lia | lia]. }
      zstep. p5_trap.
      zstep. zstep.
      replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
      pose proof (p5_unq_run rsegs m' vp0 V ltac:(lia) BV2) as BV3.
      replace (vp0 + Z.of_nat (length V - 1)) with (vp0 + (Z.of_nat (length V) + -1)) in BV3 by lia.
      assert (PM'' := p5_mem_store m0 m' (bv_unsigned sp) lo (vp0 + (Z.of_nat (length V) + -1)) [ZERO] PM'
                        ltac:(lia) ltac:(unfold PF_BUF; lia) ltac:(cbn [length]; unfold PF_BUF; lia) HS).
      assert (BK'' : bytes_at rsegs (write_to_mem m' (wa (vp0 + (Z.of_nat (length V) + -1))) [ZERO]) kp
                       (zb key ++ [ZERO])).
      { apply bytes_at_write_other; [exact BK' | lia | cbn [length]; lia |].
        rewrite length_app, p5_len_zb. cbn [length]. lia. }
      assert (IVs : pf_inb (bv_unsigned sp + PF_BUF) (vp0 + 1) (slice 1 (length V - 1) V))
        by (unfold pf_inb, PF_BUF; lia).
      unfold wa in BV3, PM'', BK''.
      remember (write_to_mem m' (Z_to_bv 64 (vp0 + (Z.of_nat (length V) + -1))) [ZERO]) as m'' eqn:Em''.
      clear Em''.
      zstep. p5_trap.
      zstep.
      p5_keep EV UQ BV3 SB SN IVs. }
    zstep. zstep. zstep. rewrite !(p5_u8 (nth 0 V 0) R0).
    if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    + (* V[0] = SQ : 0x155e4 *)
      zstep. zstep. zstep. p5_trap.
      zstep. zstep. zstep. zstep. rewrite !(p5_u8 (nth (length V - 1) V 0) Rn).
      if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * assert (UQ : r_unquote V = V) by (apply p5_unq_keep; [exact VN | lia | lia]).
        p5_keep EV UQ BV2 VB VN IV0.
      * eapply (STRIP SQ); [right; reflexivity | exact K1 | exact K2].
    + zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * assert (UQ : r_unquote V = V) by (apply p5_unq_keep; [exact VN | lia | lia]).
        p5_keep EV UQ BV2 VB VN IV0.
      * (* V[0] = DQ : 0x15550 *)
        zstep. zstep. zstep. p5_trap.
        zstep. zstep. zstep. zstep. rewrite !(p5_u8 (nth (length V - 1) V 0) Rn).
        if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
        -- eapply (STRIP DQ); [left; reflexivity | exact K2 | exact K3].
        -- zstep.
           assert (UQ : r_unquote V = V) by (apply p5_unq_keep; [exact VN | lia | lia]).
           p5_keep EV UQ BV2 VB VN IV0.
Qed.

(** A byte of a known run reads Some. *)
Lemma p5_bytes_rd : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:E; [| apply nth_error_None in E; lia].
  exists b. rewrite <- E, <- (H _ Hi). f_equal. f_equal. lia.
Qed.

(** After trim: it writes its frame below sp and the one NUL at e in buf. *)
Lemma p5_mem_trim : forall m0 m m' sp lo e, p5_mem m0 m sp lo -> munch [(sp - 32, sp); (e, e + 1)] m m' ->
  wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo sp -> lo + 32 <= sp ->
  sp + PF_BUF <= e < sp + PF_BUF + 512 -> (exists b, mrd rsegs m' (wa e) = Some b) -> p5_mem m0 m' sp lo.
Proof.
  intros m0 m m' sp lo e PM MU WM MI ST Hl He RE.
  apply (p5_mem_call m0 m m' sp lo _ PM MU WM MI ST); [lia | | |].
  - unfold sub_fp. intros x Hx. stack_num. cbn [outside] in *. destruct Hx as [H1 [H2 _]].
    split; [lia | split; [lia | exact I]].
  - intros x Hx. cbn [outside]. stack_num. split; [lia | split; [lia | exact I]].
  - intros x Hx. destruct (Z.eq_dec x e) as [->|NE]; [right; exact RE|].
    left. cbn [outside]. split; [lia | split; [lia | exact I]].
Qed.

(** The stack trim's contract asks for, at the frame's sp. *)
Lemma p5_stack_ok32 : forall m0 fc m sp lo v c, pf_env m0 fc sp lo c v -> p5_mem m0 m sp lo ->
  stack_ok rsegs m lo sp TRIM_STACK.
Proof.
  intros m0 fc m sp lo v c E PM. pose proof (p5_env_num _ _ _ _ _ _ E) as (LO0 & DEP & _ & _ & AL & _ & _).
  pose proof E as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & NR) & _ & _).
  pose proof PM as (_ & _ & _ & _ & ST). unfold PARSE_FILE_FRAME in AL, ST. unfold REFUSE_STACK, PRINTF_K in DEP.
  unfold TRIM_STACK. split; [exact (proj1 (stk_split rsegs m lo sp (sp + 1056) ST ltac:(lia)))|].
  split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros a Ha. apply NR. unfold PARSE_FILE_FRAME. lia.
Qed.

(** `*eq = 0`, trim(line), the eq check, trim(eq + 1) (0x1550c .. 0x1552c), to strlen at 0x15530. *)
Lemma p5_trims : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (ei : nat),
  pf_ctx m0 fc (bv_unsigned sp) lo v c t s o ln d n -> pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  pf_curslot m0 (bv_unsigned sp) c cur -> p5_mem m0 m (bv_unsigned sp) lo ->
  strchr (pf_tline s o) EQ = Some ei ->
  bytes_at rsegs m lp (zb (pf_tline s o) ++ [ZERO]) -> p5b (pf_tline s o) -> ~ In 0 (pf_tline s o) ->
  pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o) ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 SEMI) (Z_to_bv 64 SP) (Z_to_bv 64 (lp + Z.of_nat ei)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) s4 (Z_to_bv 64 (-1)) s6
             (Z_to_bv 64 lp) s8 s9 (Z_to_bv 64 HASH) (Z_to_bv 64 1) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1550c) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 s9 t3 t4 t5 t6 F fc m0 m lo v c t s rc
    cur nm o ln d lp ei CX PS CU PM EI BL LB LN IL.
  destruct (p5_strchr_some _ _ _ EI) as (Hei & Hq).
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & ILo & SPH & AL & C0 & APC).
  pose proof IL as IL0. unfold pf_inb, PF_BUF in IL. unfold REFUSE_STACK, PRINTF_K in DEP.
  unfold PARSE_FILE_FRAME in SPH.
  pose proof PM as (_ & _ & _ & _ & ST). unfold PARSE_FILE_FRAME in ST.
  assert (HS : store_ok rsegs m (wa (lp + Z.of_nat ei)) 1 = true)
    by (apply (p5_store_ok m lo (bv_unsigned sp + 1056)); [exact ST | lia | lia]).
  set (K1 := firstn ei (pf_tline s o)). set (K2 := skipn (S ei) (pf_tline s o)).
  assert (LK1 : length K1 = ei) by (unfold K1; rewrite length_firstn; lia).
  assert (LK2 : length K2 = (length (pf_tline s o) - S ei)%nat) by (unfold K2; rewrite length_skipn; lia).
  assert (K1B : p5b K1) by (apply p5b_firstn; exact LB).
  assert (K2B : p5b K2) by (apply p5b_skipn; exact LB).
  assert (K1N : ~ In 0 K1) by exact (nulfree_firstn _ _ LN).
  assert (K2N : ~ In 0 K2) by exact (nulfree_skipn _ _ LN).
  destruct (p5_trim_props K1 LT K1B K1N) as (R1B & R1N & R1L).
  destruct (p5_trim_props K2 LT K2B K2N) as (R2B & R2N & R2L).
  pose proof (p5_store_run rsegs m lp (zb (pf_tline s o) ++ [ZERO]) ei ZERO BL
                ltac:(rewrite length_app, p5_len_zb; cbn [length]; lia)) as B1.
  rewrite p5_upd_eq in B1 by lia. fold K1 K2 in B1.
  apply bytes_at_app in B1 as [BK1 BV1]. rewrite length_app, p5_len_zb, LK1 in BV1. cbn [length] in BV1.
  replace (lp + Z.of_nat (ei + 1)) with (lp + Z.of_nat ei + 1) in BV1 by lia.
  assert (PM1 := p5_mem_store m0 m (bv_unsigned sp) lo (lp + Z.of_nat ei) [ZERO] PM ltac:(lia)
                   ltac:(unfold PF_BUF; lia) ltac:(cbn [length]; unfold PF_BUF; lia) HS).
  zstep. zstep.
  replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
  unfold wa in BK1, BV1, PM1.
  remember (write_to_mem m (Z_to_bv 64 (lp + Z.of_nat ei)) [ZERO]) as m1 eqn:Em1. clear Em1.
  clear BL HS PM ST.
  pose proof PM1 as (_ & _ & MI1 & _ & ST1). unfold PARSE_FILE_FRAME in ST1.
  zstep. zstep.
  (* trim(line) *)
  eapply evt_cut.
  { eapply TRIM with (lo := lo) (s := K1). unfold trim_pre. rewrite ?unsigned_lit by lia.
    split; [lia|].
    split; [eapply p5_cstr_stk; [exact BK1 | exact K1B | exact K1N | exact ST1 | lia | lia]|].
    split; [eapply p5_stk_wr; [exact ST1 | lia | lia | lia]|].
    split; [right; lia|]. split; [exact (p5_stack_ok32 _ _ _ _ _ _ _ (proj1 CX) PM1)|]. exact MI1. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m2 &
              E2 & MU2 & WM2 & MI2 & ST2 & Q2).
  rewrite !unsigned_lit in E2, MU2, Q2 by lia.
  subst ms'.
  replace (ret_pc (Z_to_bv 64 87324)) with (Z_to_bv 64 87324) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_trim_run rsegs m2 lp K1 LT K1N Q2) as BK2.
  assert (BV2 : bytes_at rsegs m2 (lp + Z.of_nat ei + 1) (zb K2 ++ [ZERO])).
  { eapply bytes_at_transport; [exact BV1 | exact MU2 |]. unfold trim_end_addr.
    rewrite length_app, p5_len_zb. cbn [length]. dj. }
  assert (PM2 : p5_mem m0 m2 (bv_unsigned sp) lo).
  { apply (p5_mem_trim m0 m1 m2 _ lo (trim_end_addr lp K1) PM1 MU2 WM2 MI2 ST2); [lia | unfold trim_end_addr, PF_BUF; lia |].
    apply (p5_bytes_rd m2 lp _ _ Q2). unfold trim_end_addr. rewrite length_app, p5_len_zb, length_firstn. cbn [length].
    lia. }
  clear MU2 WM2 MI2 ST2 Q2 BK1 BV1 PM1 MI1 ST1.
  pose proof PM2 as (_ & _ & MI2 & _ & ST2). unfold PARSE_FILE_FRAME in ST2.
  zstep. p5_trap.
  zstep. zstep. zstep.
  (* trim(eq + 1) *)
  eapply evt_cut.
  { eapply TRIM with (lo := lo) (s := K2). unfold trim_pre. rewrite ?unsigned_lit by lia.
    split; [lia|].
    split; [eapply p5_cstr_stk; [exact BV2 | exact K2B | exact K2N | exact ST2 | lia | lia]|].
    split; [eapply p5_stk_wr; [exact ST2 | lia | lia | lia]|].
    split; [right; lia|]. split; [exact (p5_stack_ok32 _ _ _ _ _ _ _ (proj1 CX) PM2)|]. exact MI2. }
  intros ms' (w0 & w1 & w2 & wa1 & wa2 & wa3 & wa4 & wa5 & wa6 & wa7 & w3 & w4 & w5 & w6 & m3 &
              E3 & MU3 & WM3 & MI3 & ST3 & Q3).
  rewrite !unsigned_lit in E3, MU3, Q3 by lia.
  subst ms'.
  replace (ret_pc (Z_to_bv 64 87340)) with (Z_to_bv 64 87340) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_trim_run rsegs m3 (lp + Z.of_nat ei + 1) K2 LT K2N Q3) as BV3.
  assert (BK3 : bytes_at rsegs m3 (lp + Z.of_nat (trim_lead K1)) (zb (r_trim K1) ++ [ZERO])).
  { eapply bytes_at_transport; [exact BK2 | exact MU3 |]. unfold trim_end_addr.
    rewrite length_app, p5_len_zb. cbn [length]. dj. }
  assert (PM3 : p5_mem m0 m3 (bv_unsigned sp) lo).
  { apply (p5_mem_trim m0 m2 m3 _ lo (trim_end_addr (lp + Z.of_nat ei + 1) K2) PM2 MU3 WM3 MI3 ST3);
      [lia | unfold trim_end_addr, PF_BUF; lia |].
    apply (p5_bytes_rd m3 (lp + Z.of_nat ei + 1) _ _ Q3). unfold trim_end_addr.
    rewrite length_app, p5_len_zb, length_firstn. cbn [length]. lia. }
  zstep.
  eapply p5_unq with (key := r_trim K1) (V := r_trim K2);
    [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | reflexivity | reflexivity
    | exact CX | exact PS | exact CU | exact PM3 | exact EI | exact BK3 | exact R1B | exact R1N
    | unfold pf_inb, PF_BUF; lia | exact BV3 | exact R2B | exact R2N | unfold pf_inb, PF_BUF; lia | lia].
Qed.

(** KEY (0x154fc): strchr(line, '='), then NEITHER or the split. *)
Lemma p5_key : forall n, H_NEITHER n -> H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  H_KEY n.
Proof.
  intros n HNE HO HR HM HI HK HN. unfold H_KEY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d lp CX PS RG CU LL HS7 CL IL H0 HB.
  destruct RG as (-> & -> & -> & -> & -> & -> & ->). subst s7.
  match goal with |- evt ?g ?P ?ms => change (evt g (p5_post v sp gp tp F m lo c rc cur nm s o ln) ms) end.
  pose proof (proj1 CX) as E.
  pose proof (p5_env_num _ _ _ _ _ _ E) as (LO0 & DEP & ILo & SPH & AL & C0 & APC).
  pose proof E as (_ & _ & _ & _ & (FRM & TM & _) & _ & (ST0 & _) & MI & _).
  pose proof (p5_mem_refl m (bv_unsigned sp) lo MI TM ST0) as PM.
  pose proof IL as IL0. unfold pf_inb, PF_BUF in IL. unfold REFUSE_STACK, PRINTF_K in DEP.
  unfold PARSE_FILE_FRAME in SPH.
  destruct (p5_cstr_run rsegs m lp _ CL) as (_ & LB & LN).
  destruct CL as (bs & sl & BL & Ez & NZ & SLK).
  assert (LBs : length bs = length (pf_tline s o)) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  assert (NZb : ~ In (Z_to_bv 8 0) bs) by (apply SegBridge.nul_free_bytes; rewrite Ez; exact NZ).
  unfold PF_PC_KEY.
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply STRCHR with (str := bs) (slack := sl) (lo := lo); rewrite ?unsigned_lit by lia.
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST0
                      ltac:(unfold PARSE_FILE_FRAME; lia))).
    - exact BL.
    - exact NZb.
    - rewrite LBs. exact SLK.
    - exact MI.
    - lia.
    - right. lia. }
  intros ms' (u0 & u1 & u2 & ub1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
              E' & MU' & WM' & MI' & ST' & BL').
  rewrite !unsigned_lit in E', BL' by lia.
  subst ms'.
  replace (ret_pc (Z_to_bv 64 87304)) with (Z_to_bv 64 87304) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  rewrite (unsigned_lit 61) by lia.
  replace (61 mod 256) with 61 by reflexivity.
  rewrite (SegBridge.bridge_strchr lp 61 bs NZb ltac:(lia)), Ez.
  assert (PM' : p5_mem m m' (bv_unsigned sp) lo)
    by (apply (p5_mem_call1 m m m' (bv_unsigned sp) lo 32 PM MU' WM' MI' ST'); unfold REFUSE_STACK, PRINTF_K; lia).
  assert (CL' : cstr_at rsegs m' lp (pf_tline s o))
    by (exists bs, sl; split; [exact BL' | split; [exact Ez | split; [exact NZ | exact SLK]]]).
  pose proof (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM' FRM) as CX'.
  pose proof (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ E PS PM') as PS'.
  pose proof (p5_curslot_mem _ _ _ _ _ _ CU PM') as CU'.
  destruct (strchr (pf_tline s o) 61) as [ei|] eqn:SE.
  - destruct (p5_strchr_some _ _ _ SE) as (Hei & _).
    zstep. if_cases K; zify_cond K.
    { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
    destruct (p5_cstr_run rsegs m' lp _ CL') as (BL2 & _ & _).
    eapply p5_trims with (ei := ei);
      [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | exact CX | exact PS | exact CU | exact PM'
      | exact SE | exact BL2 | exact LB | exact LN | exact IL0].
  - zstep. if_true.
    pose proof CX' as (_ & _ & (_ & _ & SP3) & _).
    pose proof (p5_ld8 _ _ _ SP3) as RD. unfold PF_CSLOT in RD.
    zstep. zstep. zstep. zstep. zstep. zstep.
    unfold p5_post. rewrite (p5_rkey_none rc cur nm (ln + 1) (pf_tline s o) SE).
    eapply p5_exit; [exact PM' |].
    eapply HNE; [exact CX' | exact PS' | repeat split | exact CU' | reflexivity | reflexivity | reflexivity
                | reflexivity | exact CL' | exact IL0].
Qed.

Lemma pf_p5_walk : S_P5.
Proof. intros n HNE HO HR HM HI HK HN. exact (p5_key n HNE HO HR HM HI HK HN). Qed.

End Walk.

(** Piece P5 of the UBSan build: KEY -> NEITHER, OUTS, ROLE, MODEL, IGN, KNOCK or NOKEY. *)
Theorem pf_p5_holds : strchr_contract -> trim_contract -> strlen_contract -> strcasecmp_contract -> S_P5.
Proof.
  intros STRCHR TRIM STRLEN SCMP. exact (pf_p5_walk STRCHR TRIM STRLEN SCMP pfB_facts.L_trim_holds).
Qed.
