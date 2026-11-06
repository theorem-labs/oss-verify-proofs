(** reac-pw/fuzz_segconf, plain build (image 3776ca44d75c): piece S_P5 of reac_segconf_parse_file, the key line
    (reac_segconf.c:215-293), family F3 (lib/Prog/reac_segconf_parse_file_pieces_c.v).

    Part of the proof of reac_segconf_parse_file (piece P5 only).

    pf_p5_holds : strchr_contract -> trim_contract -> strlen_contract -> refuse_contract -> strcasecmp_contract -> S_P5.
    - S9 -> TAIL (p5_s9): `li s9, 512; j TAIL`.
    - KEY -> OUTS, ROLE, MODEL, IGN, KNOCK, NOKEY or TAIL, as a chain of lemmas, one per stretch of code:
      p5_key (0x14ee0: strchr(line, '='), 0x14ee8) -> p5_nei (no '=': refuse(c, lineno, F_neither, line) at
      0x14f78, then S9) or p5_key_some (0x14ef0: `*eq = 0`, trim(line) 0x14efc, trim(eq + 1) 0x14f08) -> p5_unq
      (0x14f10: strlen(v), the quote tests and `v[n-1] = 0; v++`) -> p5_dispatch (0x14fec: cur = NULL -> OUTS;
      else the strcasecmp levels p5_dr, p5_dm, p5_di, p5_dk at 0x14ffc, 0x15010, 0x15024, 0x15038 -> ROLE, MODEL,
      IGN, KNOCK, NOKEY).
    - Memory: between the cut's entry memory m0 and the memory m of each step, P5 writes only P5W (the callees'
      stack below sp and buf): p5_mem, kept by p5_mem_call / p5_mem_store; the cut's facts transport by p5_ctx_mem /
      p5_state_mem and each exit's post weakens to the entry's by p5_fin_weaken. The key and the value are tracked
      as their bytes and NUL in buf (bytes_at), and read as C strings through the frame's presence (p5_cstr_stk).
    - Each call is one lemma with a continuation (p5_strchr_call, p5_trim_call, p5_strlen_call, p5_scmp_call).
    The build-independent lemmas are lib/Prog/pfB_p5_spine.v; the kit is lib/Prog/pfB_facts.v and
    lib/Prog/pfB_kit.v. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env pf_pieces_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_p5_spine.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import strchr_c trim_c strlen_c refuse_c strcasecmp_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_parse_file_pieces_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pfB_facts pfB_kit.
Import ListNotations.
Open Scope Z_scope.

(** ** S9 -> TAIL: `li s9, 512; j TAIL` (0x14f7c, 0x14f80). *)
Lemma p5_s9 : forall n, H_TAIL n -> H_S9 n.
Proof.
  intros n HT. unfold H_S9.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo v c t s rc cur nm o ln d HC HS HN HR H6.
  unfold PF_PC_S9. zstep. zstep.
  eapply HT; [exact HC | exact HS | exact HN | exact HR | reflexivity | exact H6].
Qed.

(** ** What P5 may write: the callees' stack below sp and buf. Everything else at the cut's entry memory m0 is
    kept: c, cur_name, the spill slots, the save area, the text. *)
Definition P5W (sp : Z) : list ivl :=
  [(sp + PARSE_FILE_FRAME - PARSE_FILE_STACK, sp); (sp + PF_BUF, sp + PF_BUF + 512)].
Definition p5_mem (m0 m : word -> option byte) (sp lo : Z) : Prop :=
  munch (P5W sp) m0 m /\ wmono rsegs m0 m /\ mem_inv rsegs m /\ MemNorm.task_mem rsegs m /\
  stk rsegs m lo (sp + PARSE_FILE_FRAME).

Ltac sa_num := cbn [SA SEG_PLAIN SEG_UBSAN sa_img_end sa_img_top sa_guard sa_got_guard sa_catalogue] in *.
Ltac stack_num := unfold P5W, PARSE_FILE_STACK, PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, PF_BUF in *.
Ltac c_num := unfold RC_PARSE_W, RC_N, RC_REFUSAL, RC_OVERFLOW, RC_READING, RC_GEN, RSEG_SIZE, SEG_C_SIZE in *.
Ltac dj := cbn [disjoint_from]; repeat split; first [exact I | lia].
(* The pc after a branch whose condition is now a constructor. *)
Ltac pc_if := try lazymatch goal with
  | |- context [if true then ?a else ?b] => change (if true then a else b) with a
  | |- context [if false then ?a else ?b] => change (if false then a else b) with b
  end.
(* Replace the branch condition by the constant v, proved by arithmetic on literals. *)
Ltac p5_cond v := lazymatch goal with |- context [if ?cnd then _ else _] =>
  replace cnd with v by (symmetry; unfold bv_ltu, bv_eqb; cbn [negb]; rewrite ?unsigned_lit by lia;
    first [apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq
          | apply Bool.negb_true_iff, Z.eqb_neq | apply Bool.negb_false_iff, Z.eqb_eq]; lia)
  end; pc_if.
Ltac p5_br := first [p5_cond true | p5_cond false].

Lemma p5_bv_eqb : forall a b : word, bv_eqb a b = true -> a = b.
Proof. intros a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

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
  - unfold pf_spill, saved_at in *. eapply bytes_at_transport; [exact SP | exact MU |].
    rewrite p5_len_le8. cbn [length]. stack_num. dj.
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

(** The literals strcasecmp compares the key with, in .rodata. *)
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

(** strcasecmp's zero test (strcasecmp_c.lower_eq on the bytes) is the spine's, on NUL-free byte strings (the kit's
    pf_lower_eq_bridge). *)
Lemma p5_scb : forall l w, p5b l -> ~ In 0 l -> p5b w -> ~ In 0 w -> (lower_eq (zb l) (zb w) <-> strcasecmp l w = 0).
Proof. intros l w Lb Ln Wb Wn. exact (pf_lower_eq_bridge l w Lb Wb Ln Wn). Qed.

Section Walk.
Hypothesis HSTRCHR : strchr_contract.
Hypothesis HTRIM : trim_contract.
Hypothesis HSTRLEN : strlen_contract.
Hypothesis HREF : refuse_contract.
Hypothesis HSCMP : strcasecmp_contract.

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
  { apply (HSCMP ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 kp) (Z_to_bv 64 la) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
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
  - rewrite R. apply p5_scb; assumption.
Qed.

(** The post every exit of the dispatch reaches: r_key's. *)
Definition p5_post (v : pf_sv) (sp gp tp : word) (F : bvmap 5 word) (m0 : word -> option byte) (lo c : Z)
    (rc : rconf) (cur : option nat) (nm : list Z) (s : list Z) (o : nat) (ln : Z) : machine_state -> Prop :=
  pf_fin v sp gp tp F m0 lo c (r_lines (r_key rc cur nm (ln + 1) (pf_tline s o)) (ln + 1) (lines (skipn (pf_next s o) s))).

(** The facts at every dispatch pc: the cut's entry facts at m0, P5's writes since, and the split key line at m. *)
Definition p5_D (m0 : word -> option byte) (fc0 : bv 32) (m : word -> option byte) (sp lo : Z) (v : pf_sv)
    (c t : Z) (s : list Z) (rc : rconf) (cur : option nat) (nm : list Z) (o : nat) (ln : Z) (d : list (list Z))
    (n : nat) (kp vp : Z) (key val : list Z) : Prop :=
  pf_ctx m0 fc0 sp lo v c t s o ln d n /\ pf_state m0 sp c rc cur nm (length (skipn o s)) /\
  p5_mem m0 m sp lo /\ pf_kv m sp (pf_tline s o) kp vp key val.

Lemma p5_D_call1 : forall m0 fc0 m m' sp lo v c t s rc cur nm o ln d n kp vp key val,
  p5_D m0 fc0 m sp lo v c t s rc cur nm o ln d n kp vp key val -> p5_mem m0 m' sp lo ->
  munch [(sp - 32, sp)] m m' -> p5_D m0 fc0 m' sp lo v c t s rc cur nm o ln d n kp vp key val.
Proof.
  intros m0 fc0 m m' sp lo v c t s rc cur nm o ln d n kp vp key val (CX & PS & PM & KV) PM' MU.
  split; [exact CX|]. split; [exact PS|]. split; [exact PM'|].
  destruct KV as (EI & CK & IK & CV & IV). unfold pf_inb in IK, IV. unfold PF_BUF in *.
  split; [exact EI|]. split; [eapply p5_cstr_munch; [exact CK | exact MU | dj]|]. split; [exact IK|].
  split; [eapply p5_cstr_munch; [exact CV | exact MU | dj] | exact IV].
Qed.

Lemma p5_dk : forall n, H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc0 m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val -> frm0 fc ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 -> strcasecmp key S_ignore <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x1502c) fc None m (seg_rom rsegs)).
Proof.
  intros n HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc gi nm o ln
    d kp vp key val D FRM R1 R2 R3.
  pose proof D as (CX & PS & PM & KV).
  pose proof (p5_env_num m0 fc0 (bv_unsigned sp) lo c v (proj1 CX)) as (LO0 & DEP & IL & SPH & AL & C0 & APC).
  pose proof KV as ((ei & SE & EK & EV) & CK & IK & CV & IV). unfold pf_inb, PF_BUF in IK, IV.
  pose proof PM as (_ & _ & MI & _ & _).
  destruct (p5_words S_knock ltac:(cbn; tauto)) as (WB & WN & WL).
  zstep. zstep. zstep. zstep.
  eapply p5_scmp_call with (la := 0x102a3) (w := S_knock) (m0 := m0) (lo := lo) (kp := kp) (key := key);
    [exact PM | exact DEP | exact CK | lia | apply p5_lit_at; [exact MI | lia | lia | exact p5_ro_knock]
    | exact WB | exact WN | sa_num; unfold REFUSE_STACK, PRINTF_K in DEP; lia | reflexivity | reflexivity |].
  intros r u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU' R.
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D'.
  replace (ret_pc (Z_to_bv 64 86076)) with (Z_to_bv 64 86076) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep.
  pose proof D' as (_ & _ & _ & (_ & CK' & _ & CV' & _)).
  destruct (bv_eqb r (Z_to_bv 64 0)) eqn:K; pc_if.
  - apply p5_bv_eqb in K. subst r. pose proof (proj1 R eq_refl) as R4.
    eapply evt_mono.
    { apply (HK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' lo v c t s rc (Some gi) nm o ln d
               vp val); unfold PF_PC_KNOCK.
      - exact (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM' FRM).
      - exact (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ (proj1 CX) PS PM').
      - repeat split.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact CV'.
      - unfold pf_inb, PF_BUF. lia. }
    intros ms PO. unfold p5_post. subst key val.
    rewrite (p5_rkey_knock rc gi nm (ln + 1) (pf_tline s o) ei SE R1 R2 R3 R4).
    eapply p5_fin_weaken; [exact PM' | intros k _; reflexivity | exact PO].
  - assert (R4 : strcasecmp key S_knock <> 0).
    { intros H. apply R in H. subst r. rewrite bv_eqb_refl in K. discriminate. }
    do 7 zstep.
    eapply evt_mono.
    { apply (HN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' lo v c t s rc (Some gi) nm o ln d
               kp key); unfold PF_PC_NOKEY.
      - exact (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM' FRM).
      - exact (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ (proj1 CX) PS PM').
      - repeat split.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - unfold PF_NAMEBUF. reflexivity.
      - reflexivity.
      - exact CK'.
      - unfold pf_inb, PF_BUF. lia. }
    intros ms PO. unfold p5_post. subst key val.
    rewrite (p5_rkey_nokey rc gi nm (ln + 1) (pf_tline s o) ei SE R1 R2 R3 R4).
    eapply p5_fin_weaken; [exact PM' | intros k _; reflexivity | exact PO].
Qed.

(* The common start of a dispatch level: the facts of D, a strcasecmp call against the literal w at la. *)
Ltac p5_level D key lit adr ro ret :=
  let CX := fresh "CX" in let PS := fresh "PS" in let PM := fresh "PM" in let KV := fresh "KV" in
  pose proof D as (CX & PS & PM & KV);
  let LO0 := fresh "LO0" in let DEP := fresh "DEP" in let IL := fresh "IL" in
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & IL & _ & _ & _ & _);
  let SE := fresh "SE" in let CK := fresh "CK" in let IK := fresh "IK" in let MI := fresh "MI" in
  pose proof KV as ((? & SE & ? & ?) & CK & IK & _ & _); unfold pf_inb, PF_BUF in IK;
  pose proof PM as (_ & _ & MI & _ & _);
  let WB := fresh "WB" in let WN := fresh "WN" in let WL := fresh "WL" in
  destruct (p5_words lit ltac:(cbn; tauto)) as (WB & WN & WL);
  zstep; zstep; zstep; zstep;
  eapply p5_scmp_call with (la := adr) (w := lit);
    [exact PM | exact DEP | exact CK | lia | apply p5_lit_at; [exact MI | lia | lia | exact ro]
    | exact WB | exact WN | sa_num; unfold REFUSE_STACK, PRINTF_K in DEP; lia | reflexivity | reflexivity |];
  let r := fresh "r" in let m' := fresh "m'" in let PM' := fresh "PM'" in let MU' := fresh "MU'" in
  let R := fresh "R" in
  intros r ? ? ? ? ? ? ? ? ? ? ? ? ? ? m' PM' MU' R;
  let D' := fresh "D'" in
  pose proof (p5_D_call1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D PM' MU') as D';
  replace (ret_pc (Z_to_bv 64 ret)) with (Z_to_bv 64 ret) by (symmetry; apply ret_pc_even; [lia | reflexivity]);
  zstep;
  let K := fresh "K" in
  destruct (bv_eqb r (Z_to_bv 64 0)) eqn:K; pc_if;
  [ apply p5_bv_eqb in K; subst r; pose proof (proj1 R eq_refl)
  | let H := fresh in assert (strcasecmp key lit <> 0) by (intros H; apply R in H; subst r; rewrite bv_eqb_refl in K;
                                                      discriminate) ].

(* A premise of an exit whose post is r_key's, at the memory m' of D'. *)
Ltac p5_same_exit D' FRM :=
  let CX := fresh "CX" in let PS := fresh "PS" in let PM := fresh "PM" in let KV := fresh "KV" in
  pose proof D' as (CX & PS & PM & KV);
  first [ exact (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM FRM)
        | exact (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ (proj1 CX) PS PM)
        | exact KV | reflexivity | solve [unfold pf_regs; repeat split] | assumption ].

Lemma p5_di : forall n, H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc0 m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val -> frm0 fc ->
  strcasecmp key S_role <> 0 -> strcasecmp key S_model <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15018) fc None m (seg_rom rsegs)).
Proof.
  intros n HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc gi nm o
    ln d kp vp key val D FRM R1 R2.
  p5_level D key S_ignore 0x1054f p5_ro_ignore 86056.
  - eapply evt_mono.
    { apply (HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' lo v c t s rc nm o ln d gi kp vp
               key val); unfold PF_PC_IGN; p5_same_exit D' FRM; assumption. }
    intros ms PO. eapply p5_fin_weaken; [exact (proj1 (proj2 (proj2 D'))) | intros k _; reflexivity | exact PO].
  - eapply p5_dk; [exact HK | exact HN | exact D' | exact FRM | exact R1 | exact R2 | assumption].
Qed.

Lemma p5_dm : forall n, H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc0 m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val -> frm0 fc ->
  strcasecmp key S_role <> 0 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x15004) fc None m (seg_rom rsegs)).
Proof.
  intros n HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc gi nm
    o ln d kp vp key val D FRM R1.
  p5_level D key S_model 0x10811 p5_ro_model 86036.
  - eapply evt_mono.
    { apply (HM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' lo v c t s rc nm o ln d gi kp vp
               key val); unfold PF_PC_MODEL; p5_same_exit D' FRM; assumption. }
    intros ms PO. eapply p5_fin_weaken; [exact (proj1 (proj2 (proj2 D'))) | intros k _; reflexivity | exact PO].
  - eapply p5_di; [exact HI | exact HK | exact HN | exact D' | exact FRM | exact R1 | assumption].
Qed.

Lemma p5_dr : forall n, H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (gi : nat) (nm : list Z)
    (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc0 m (bv_unsigned sp) lo v c t s rc (Some gi) nm o ln d n kp vp key val -> frm0 fc ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc (Some gi) nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (rseg_addr c gi)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ff0) fc None m (seg_rom rsegs)).
Proof.
  intros n HR HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc gi
    nm o ln d kp vp key val D FRM.
  p5_level D key S_role 0x10298 p5_ro_role 86016.
  - eapply evt_mono.
    { apply (HR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m' lo v c t s rc nm o ln d gi kp vp
               key val); unfold PF_PC_ROLE; p5_same_exit D' FRM; assumption. }
    intros ms PO. eapply p5_fin_weaken; [exact (proj1 (proj2 (proj2 D'))) | intros k _; reflexivity | exact PO].
  - eapply p5_dm; [exact HM | exact HI | exact HK | exact HN | exact D' | exact FRM | assumption].
Qed.

(** The dispatch from 0x14fec: cur = NULL -> OUTS; else the four strcasecmp levels. *)
Lemma p5_dispatch : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (kp vp : Z) (key val : list Z),
  p5_D m0 fc0 m (bv_unsigned sp) lo v c t s rc cur nm o ln d n kp vp key val -> frm0 fc ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (pf_cur_ptr c cur)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14fec) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc
    cur nm o ln d kp vp key val D FRM.
  pose proof D as (CX & PS & PM & KV).
  destruct cur as [gi|].
  - pose proof PS as ((bs & BC & EC) & CO & _ & _). cbn [pf_cur_ok] in CO.
    pose proof (bytes_at_bound _ _ _ _ BC) as BCb. destruct EC as (LBS & L32 & _).
    pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (_ & _ & _ & _ & _ & C0 & _).
    unfold SEG_C_SIZE in LBS. cbn [pf_cur_ptr]. unfold rseg_addr, RSEG_SIZE.
    zstep.
    destruct (bv_eqb (Z_to_bv 64 (c + 356 * Z.of_nat gi)) (Z_to_bv 64 0)) eqn:K; pc_if.
    { exfalso. apply p5_bv_eqb in K. apply (f_equal (@bv_unsigned 64)) in K.
      rewrite !unsigned_lit in K by lia. lia. }
    eapply p5_dr; [exact HR | exact HM | exact HI | exact HK | exact HN | exact D | exact FRM].
  - cbn [pf_cur_ptr]. zstep. rewrite bv_eqb_refl. pc_if. do 6 zstep.
    pose proof KV as ((ei & SE & EK & EV) & CK & IK & _ & _).
    eapply evt_mono.
    { apply (HO _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m lo v c t s rc nm o ln d kp key);
        unfold PF_PC_OUTS.
      - exact (p5_ctx_mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ CX PM FRM).
      - exact (p5_state_mem _ _ _ _ _ _ _ _ _ _ _ (proj1 CX) PS PM).
      - repeat split.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - exact CK.
      - exact IK. }
    intros ms PO. unfold p5_post. subst key val.
    rewrite (p5_rkey_outs rc nm (ln + 1) (pf_tline s o) ei SE).
    eapply p5_fin_weaken; [exact PM | intros k _; reflexivity | exact PO].
Qed.

(** The dispatch's facts from the bytes of the key and the value in buf. *)
Lemma p5_mkD : forall m0 fc0 m sp lo v c t s rc cur nm o ln d n ei kp vp key val,
  pf_ctx m0 fc0 sp lo v c t s o ln d n -> pf_state m0 sp c rc cur nm (length (skipn o s)) -> p5_mem m0 m sp lo ->
  strchr (pf_tline s o) EQ = Some ei -> key = r_trim (firstn ei (pf_tline s o)) ->
  val = r_unquote (r_trim (skipn (S ei) (pf_tline s o))) ->
  bytes_at rsegs m kp (zb key ++ [ZERO]) -> p5b key -> ~ In 0 key ->
  sp + PF_BUF <= kp -> kp + Z.of_nat (length key) < sp + PF_BUF + 512 ->
  bytes_at rsegs m vp (zb val ++ [ZERO]) -> p5b val -> ~ In 0 val ->
  sp + PF_BUF <= vp -> vp + Z.of_nat (length val) < sp + PF_BUF + 512 ->
  p5_D m0 fc0 m sp lo v c t s rc cur nm o ln d n kp vp key val.
Proof.
  intros m0 fc0 m sp lo v c t s rc cur nm o ln d n ei kp vp key val CX PS PM SE EK EV BK KB KN K1 K2 BV VB VN V1 V2.
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & _ & _ & _ & _ & _).
  pose proof PM as (_ & _ & _ & _ & ST). unfold PF_BUF, REFUSE_STACK, PRINTF_K in *.
  split; [exact CX|]. split; [exact PS|]. split; [exact PM|].
  split; [exists ei; split; [exact SE | split; [exact EK | exact EV]]|].
  split; [apply (p5_cstr_stk rsegs m lo (sp + PARSE_FILE_FRAME)); try assumption; unfold PARSE_FILE_FRAME; lia|].
  split; [unfold pf_inb, PF_BUF; lia|].
  split; [apply (p5_cstr_stk rsegs m lo (sp + PARSE_FILE_FRAME)); try assumption; unfold PARSE_FILE_FRAME; lia|].
  unfold pf_inb, PF_BUF; lia.
Qed.

(** strlen(v) on a C string v in the frame. *)
Lemma p5_strlen_call : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo vp : Z) (V : list Z),
  p5_mem m0 m (bv_unsigned sp) lo -> lo <= bv_unsigned sp -> cstr_at rsegs m vp V -> a0 = Z_to_bv 64 vp ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     p5_mem m0 m' (bv_unsigned sp) lo -> munch [] m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length V))) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo vp V PM LS CS -> K.
  pose proof CS as (bs & sl & B & Ez & Nz & SL).
  pose proof PM as (MU & WM & MI & TM & ST).
  pose proof (bytes_at_bound _ _ _ _ B) as Bb. rewrite length_app in Bb. cbn [length] in Bb.
  assert (LB : length bs = length V) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  eapply evt_cut.
  { apply (HSTRLEN ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 vp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m bs sl); rewrite ?unsigned_lit by lia.
    - exact B.
    - subst V. apply p5_nz_zb in Nz; [rewrite p5_zb_zs in Nz; exact Nz | apply p5b_zs].
    - rewrite LB. exact SL.
    - exact MI. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' & E & MU' & WM' & MI' & _).
  subst ms'. rewrite LB. apply (K u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m'); [|exact MU'].
  destruct (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
              ltac:(unfold PARSE_FILE_FRAME; lia)) as [ST1 _].
  apply (p5_mem_call m0 m m' (bv_unsigned sp) lo [] PM MU' WM' MI'); [| exact LS | | |].
  - apply (p5_stk_tr [] m m' lo (bv_unsigned sp) ST1 MU' WM'). intros x _. left. exact I.
  - intros x _. exact I.
  - intros x _. exact I.
  - intros x _. left. exact I.
Qed.

Lemma p5_bveqb_ne : forall x y, x <> y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof. intros x y H Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. apply Z.eqb_neq. exact H. Qed.

(** unquote from 0x14f10 (strlen(v), the quote tests, v[n-1] = 0, v + 1) to the dispatch at 0x14fec. *)
Lemma p5_unq : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (ei : nat) (kp vp : Z),
  pf_ctx m0 fc0 (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  p5_mem m0 m (bv_unsigned sp) lo -> frm0 fc ->
  p5b (pf_tline s o) -> ~ In 0 (pf_tline s o) -> strchr (pf_tline s o) EQ = Some ei ->
  bytes_at rsegs m kp (zb (r_trim (firstn ei (pf_tline s o))) ++ [ZERO]) ->
  bytes_at rsegs m vp (zb (r_trim (skipn (S ei) (pf_tline s o))) ++ [ZERO]) ->
  bv_unsigned sp + PF_BUF <= kp -> kp + Z.of_nat (length (r_trim (firstn ei (pf_tline s o)))) < vp ->
  vp + Z.of_nat (length (r_trim (skipn (S ei) (pf_tline s o)))) < bv_unsigned sp + PF_BUF + 512 ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) (Z_to_bv 64 vp) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (pf_cur_ptr c cur)) (Z_to_bv 64 vp) (Z_to_bv 64 kp) s9 (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14f10) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s9 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc
    cur nm o ln d ei kp vp CX PS PM FRM LB LN SE BK BV K1 K2 V2.
  set (L := pf_tline s o) in *.
  pose proof (p5_strchr_some L 61 ei SE) as (EIL & _).
  destruct (p5_trim_props (firstn ei L) L_trim_holds (p5b_firstn ei L LB) (nulfree_firstn _ _ LN)) as (KB & KN & _).
  destruct (p5_trim_props (skipn (S ei) L) L_trim_holds (p5b_skipn (S ei) L LB) (nulfree_skipn _ _ LN)) as (VB & VN & _).
  set (key := r_trim (firstn ei L)) in *. set (V := r_trim (skipn (S ei) L)) in *.
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & IL & SPH & _ & _ & _).
  pose proof PM as (_ & _ & _ & _ & ST). unfold PF_BUF, REFUSE_STACK, PRINTF_K, PARSE_FILE_FRAME in *.
  assert (CV : cstr_at rsegs m vp V)
    by (apply (p5_cstr_stk rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME)); try assumption; unfold PARSE_FILE_FRAME;
        lia).
  zstep.
  eapply p5_strlen_call with (m0 := m0) (lo := lo) (vp := vp) (V := V);
    [exact PM | lia | exact CV | reflexivity |].
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m' PM' MU'.
  assert (BK' : bytes_at rsegs m' kp (zb key ++ [ZERO])) by (eapply bytes_at_transport; [exact BK | exact MU' | exact I]).
  assert (BV' : bytes_at rsegs m' vp (zb V ++ [ZERO])) by (eapply bytes_at_transport; [exact BV | exact MU' | exact I]).
  clear BK BV MU' CV.
  replace (ret_pc (Z_to_bv 64 0x14f14)) with (Z_to_bv 64 0x14f14) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  zstep. zstep.
  assert (MKD : forall m'' vq val, p5_mem m0 m'' (bv_unsigned sp) lo -> val = r_unquote V ->
            bytes_at rsegs m'' kp (zb key ++ [ZERO]) -> bytes_at rsegs m'' vq (zb val ++ [ZERO]) -> p5b val ->
            ~ In 0 val -> vp <= vq -> vq + Z.of_nat (length val) <= vp + Z.of_nat (length V) ->
            p5_D m0 fc0 m'' (bv_unsigned sp) lo v c t s rc cur nm o ln d n kp vq key val).
  { intros m'' vq val PM'' EV B1 B2 B3 B4 B5 B6.
    apply (p5_mkD m0 fc0 m'' (bv_unsigned sp) lo v c t s rc cur nm o ln d n ei kp vq key val CX PS PM'' SE eq_refl EV
             B1 KB KN); unfold PF_BUF; try assumption; lia. }
  destruct (Nat.lt_ge_cases (length V) 2) as [S2|S2].
  { p5_cond true. zstep. zstep.
    eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
    apply (MKD m' vp V PM'); [symmetry; apply p5_unq_short; assumption | exact BK' | exact BV' | exact VB | exact VN
                             | lia | lia]. }
  p5_cond false.
  assert (HR0 : ov_read_bytes rsegs m' (wa vp) 1 = Some [Z_to_bv 8 (nth 0 V 0)]).
  { pose proof (p5_run_read rsegs m' vp V 0 BV' ltac:(lia)) as H. rewrite Z.add_0_r in H. exact H. }
  assert (Q0R : 0 <= nth 0 V 0 < 256) by (apply p5b_nth; exact VB).
  assert (QLR : 0 <= nth (length V - 1) V 0 < 256) by (apply p5b_nth; exact VB).
  assert (HRL : ov_read_bytes rsegs m' (wa (vp + Z.of_nat (length V - 1))) 1
                = Some [Z_to_bv 8 (nth (length V - 1) V 0)]) by (apply (p5_run_read rsegs m' vp V); [exact BV' | lia]).
  assert (HS : store_ok rsegs m' (wa (vp + Z.of_nat (length V - 1))) 1 = true).
  { pose proof PM' as (_ & _ & _ & _ & ST').
    apply (wr_at_store_ok rsegs m' vp (Z.of_nat (length V)) (Z.of_nat (length V - 1)) 1); [|lia|lia].
    apply (p5_stk_wr rsegs m' lo (bv_unsigned sp + PARSE_FILE_FRAME)); [exact ST' | lia | lia | unfold PARSE_FILE_FRAME; lia]. }
  zstep. cbv beta. rewrite (p5_u8 (nth 0 V 0) Q0R). zstep. zstep.
  destruct (Z.eq_dec (nth 0 V 0) 39) as [Q0|Q0].
  - p5_br. zstep. zstep. cbv beta. rewrite (p5_u8 _ QLR). zstep. zstep. zstep.
    destruct (Z.eq_dec (nth (length V - 1) V 0) 39) as [QL|QL].
    + p5_br. zstep. zstep.
      replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
      assert (PM'' := p5_mem_store m0 m' (bv_unsigned sp) lo (vp + Z.of_nat (length V - 1)) [ZERO] PM' ltac:(lia)
                        ltac:(unfold PF_BUF; cbn [length]; lia)
                        ltac:(unfold PF_BUF; cbn [length]; lia) HS).
      pose proof (p5_unq_run rsegs m' vp V S2 BV') as BV''.
      assert (BK'' := bytes_at_write_other rsegs m' (vp + Z.of_nat (length V - 1)) [ZERO] kp _ BK' ltac:(lia)
                        ltac:(cbn [length]; lia) ltac:(rewrite length_app, p5_len_zb; cbn [length]; lia)).
      destruct (p5_slice_props V 1 (length V - 1) VB VN) as (SB & SN & SL).
      zstep.
      eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
      apply (MKD _ (vp + 1) (slice 1 (length V - 1) V) PM''); try assumption; [|lia|lia].
      symmetry. apply (p5_unq_strip V 39 VN S2 (or_intror eq_refl) Q0 QL).
    + p5_br.
      eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
      apply (MKD m' vp V PM'); [| exact BK' | exact BV' | exact VB | exact VN | lia | lia].
      symmetry. apply p5_unq_keep; [exact VN | exact S2 | lia].
  - p5_br. zstep. zstep. zstep.
    destruct (Z.eq_dec (nth 0 V 0) 34) as [Q1|Q1].
    + p5_br. zstep. zstep. cbv beta. rewrite (p5_u8 _ QLR). zstep.
      destruct (Z.eq_dec (nth (length V - 1) V 0) 34) as [QL|QL].
      * p5_br. zstep. zstep.
        replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
        assert (PM'' := p5_mem_store m0 m' (bv_unsigned sp) lo (vp + Z.of_nat (length V - 1)) [ZERO] PM' ltac:(lia)
                        ltac:(unfold PF_BUF; cbn [length]; lia)
                          ltac:(unfold PF_BUF; cbn [length]; lia) HS).
        pose proof (p5_unq_run rsegs m' vp V S2 BV') as BV''.
        assert (BK'' := bytes_at_write_other rsegs m' (vp + Z.of_nat (length V - 1)) [ZERO] kp _ BK' ltac:(lia)
                          ltac:(cbn [length]; lia) ltac:(rewrite length_app, p5_len_zb; cbn [length]; lia)).
        destruct (p5_slice_props V 1 (length V - 1) VB VN) as (SB & SN & SL).
        zstep.
        eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
        apply (MKD _ (vp + 1) (slice 1 (length V - 1) V) PM''); try assumption; [|lia|lia].
        symmetry. apply (p5_unq_strip V 34 VN S2 (or_introl eq_refl) Q1 QL).
      * p5_br. zstep.
        eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
        apply (MKD m' vp V PM'); [| exact BK' | exact BV' | exact VB | exact VN | lia | lia].
        symmetry. apply p5_unq_keep; [exact VN | exact S2 | lia].
    + p5_br.
      eapply p5_dispatch; [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | | exact FRM].
      apply (MKD m' vp V PM'); [| exact BK' | exact BV' | exact VB | exact VN | lia | lia].
      symmetry. apply p5_unq_keep; [exact VN | exact S2 | lia].
Qed.

(** strchr(line, '=') on the trimmed line at lp in buf. *)
Lemma p5_strchr_call : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo lp : Z) (L : list Z),
  p5_mem m0 m (bv_unsigned sp) lo -> lo + REFUSE_STACK <= bv_unsigned sp -> cstr_at rsegs m lp L ->
  bv_unsigned sp <= lp -> a0 = Z_to_bv 64 lp -> a1 = Z_to_bv 64 61 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     p5_mem m0 m' (bv_unsigned sp) lo -> munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                    (Z_to_bv 64 (match strchr L 61 with Some i => lp + Z.of_nat i | None => 0 end))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 STRCHR) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo lp L PM DEP CS LP -> -> K.
  pose proof CS as (bs & sl & B & Ez & Nz & SL).
  pose proof PM as (MU & WM & MI & TM & ST).
  pose proof (bytes_at_bound _ _ _ _ B) as Bb. rewrite length_app in Bb. cbn [length] in Bb.
  assert (LB : length bs = length L) by (rewrite <- Ez; unfold zs; symmetry; apply length_map).
  assert (NZ : ~ In (Z_to_bv 8 0) bs) by (subst L; apply p5_nz_zb in Nz; [rewrite p5_zb_zs in Nz; exact Nz | apply p5b_zs]).
  pose proof ST as (LO0 & _ & _). unfold REFUSE_STACK, PRINTF_K in DEP.
  eapply evt_cut.
  { apply (HSTRCHR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 lp) (Z_to_bv 64 61) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc m bs sl lo); rewrite ?unsigned_lit by lia.
    - exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                      ltac:(unfold PARSE_FILE_FRAME; lia))).
    - exact B.
    - exact NZ.
    - rewrite LB. exact SL.
    - exact MI.
    - lia.
    - right. exact LP. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
              E & MU' & WM' & MI' & ST' & _).
  subst ms'. rewrite ?unsigned_lit in * by lia.
  rewrite (SegBridge.bridge_strchr lp (61 mod 256) bs NZ ltac:(cbv; split; reflexivity)), Ez.
  change (61 mod 256) with 61.
  apply (K u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m'); [|exact MU'].
  apply (p5_mem_call1 m0 m m' (bv_unsigned sp) lo 32 PM MU' WM' MI' ST'); unfold REFUSE_STACK, PRINTF_K; lia.
Qed.

(** trim(p) on the C string K at p in buf. *)
Lemma p5_trim_call : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lo p : Z) (K : list Z),
  p5_mem m0 m (bv_unsigned sp) lo -> lo + REFUSE_STACK <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
  (forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None) ->
  bytes_at rsegs m p (zb K ++ [ZERO]) -> p5b K -> ~ In 0 K ->
  bv_unsigned sp + PF_BUF <= p -> p + Z.of_nat (length K) < bv_unsigned sp + PF_BUF + 512 -> a0 = Z_to_bv 64 p ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
     p5_mem m0 m' (bv_unsigned sp) lo ->
     munch [(bv_unsigned sp - 16, bv_unsigned sp); (trim_end_addr p K, trim_end_addr p K + 1)] m m' ->
     bytes_at rsegs m' p (zb (firstn (trim_lead K + length (r_trim K)) K) ++ [ZERO]) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (p + Z.of_nat (trim_lead K)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                   F (ret_pc ra) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 TRIM) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    lo p K PM DEP AL RO BK KB KN P1 P2 -> CONT.
  pose proof PM as (MU & WM & MI & TM & ST).
  pose proof ST as (LO0 & HI0 & _). unfold REFUSE_STACK, PRINTF_K, PF_BUF, PARSE_FILE_FRAME in *.
  destruct (L_trim_holds K KN) as (TL & _ & _).
  eapply evt_cut.
  { apply (HTRIM ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6 F fc m lo K).
    unfold trim_pre. rewrite ?unsigned_lit by lia.
    split; [lia|]. split.
    { apply (p5_cstr_stk rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME)); try assumption; unfold PARSE_FILE_FRAME; lia. }
    split; [apply (p5_stk_wr rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME)); [exact ST | lia | lia | unfold PARSE_FILE_FRAME; lia]|].
    split; [unfold apart; right; lia|]. split; [|exact MI].
    split; [exact (proj1 (stk_split rsegs m lo (bv_unsigned sp) (bv_unsigned sp + PARSE_FILE_FRAME) ST
                            ltac:(unfold PARSE_FILE_FRAME; lia)))|].
    unfold TRIM_STACK. split; [lia|]. split; [exact AL | exact RO]. }
  intros ms' (u0 & u1 & u2 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & m' &
              E & MU' & WM' & MI' & ST' & BQ).
  subst ms'. rewrite ?unsigned_lit in * by lia. unfold TRIM_STACK in MU'.
  apply (CONT u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m'); [|exact MU' | exact BQ].
  apply (p5_mem_call m0 m m' (bv_unsigned sp) lo _ PM MU' WM' MI' ST'); [lia | | | ].
  - unfold sub_fp, trim_end_addr. intros x Hx. stack_num. cbn [outside] in *. destruct Hx as [Hx1 [Hx2 _]].
    split; [lia | split; [lia | exact I]].
  - intros x Hx. unfold trim_end_addr. cbn [outside]. unfold PARSE_FILE_FRAME in Hx.
    split; [lia | split; [lia | exact I]].
  - intros x Hx. destruct (Z.eq_dec x (trim_end_addr p K)) as [->|NE].
    + right. exists ZERO. destruct BQ as (_ & _ & BQi). unfold trim_end_addr.
      assert (LF : length (zb (firstn (trim_lead K + length (r_trim K)) K)) = (trim_lead K + length (r_trim K))%nat)
        by (rewrite p5_len_zb, length_firstn; lia).
      rewrite (BQi (trim_lead K + length (r_trim K))%nat ltac:(rewrite length_app, LF; cbn [length]; lia)).
      rewrite nth_error_app2 by lia. rewrite LF, Nat.sub_diag. reflexivity.
    + left. cbn [outside]. unfold trim_end_addr in *. split; [lia | split; [lia | exact I]].
Qed.

Lemma p5_mem_refl : forall m fc sp lo c v, pf_env m fc sp lo c v -> p5_mem m m sp lo.
Proof.
  intros m fc sp lo c v (_ & _ & _ & _ & (_ & TM & _) & _ & (ST & _) & MI & _).
  split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact TM | exact ST].
Qed.

(** The C strings from 0x14ef0 to 0x14f10: the line split at the '=' at ei, key and value trimmed in place. *)
Lemma p5_key_some : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n ->
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (lp : Z) (ei : nat),
  pf_ctx m0 fc0 (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  p5_mem m0 m (bv_unsigned sp) lo -> frm0 fc ->
  p5b (pf_tline s o) -> ~ In 0 (pf_tline s o) -> strchr (pf_tline s o) EQ = Some ei ->
  bytes_at rsegs m lp (zb (pf_tline s o) ++ [ZERO]) ->
  pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o) ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) (Z_to_bv 64 (lp + Z.of_nat ei)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (pf_cur_ptr c cur)) (Z_to_bv 64 lp) s8 s9 (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ef0) fc None m (seg_rom rsegs)).
Proof.
  intros n HO HR HM HI HK HN ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 s9 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc
    cur nm o ln d lp ei CX PS PM FRM LB LN SE BL IL.
  set (L := pf_tline s o) in *.
  pose proof (p5_strchr_some L 61 ei SE) as (EIL & _).
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & ILO & SPH & AL & _ & _).
  unfold REFUSE_STACK, PRINTF_K in DEP. unfold PARSE_FILE_FRAME in SPH.
  pose proof (proj1 CX) as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & RO) & _).
  assert (RO' : forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None)
    by (intros a Ha; apply RO; unfold PARSE_FILE_FRAME; lia).
  assert (AL' : bv_unsigned sp mod 16 = 0)
    by (unfold PARSE_FILE_FRAME in AL; replace (bv_unsigned sp) with (bv_unsigned sp + 976 - 61 * 16) by lia;
        rewrite Zminus_mod, AL; reflexivity).
  unfold pf_inb, PF_BUF in IL.
  pose proof PM as (_ & _ & _ & _ & ST).
  set (K0 := firstn ei L) in *. set (K1 := skipn (S ei) L) in *.
  assert (LK0 : length K0 = ei) by (unfold K0; rewrite length_firstn; lia).
  assert (LK1 : length K1 = (length L - S ei)%nat) by (unfold K1; rewrite length_skipn; lia).
  assert (K0B : p5b K0) by (apply p5b_firstn; exact LB). assert (K0N : ~ In 0 K0) by (apply nulfree_firstn; exact LN).
  assert (K1B : p5b K1) by (apply p5b_skipn; exact LB). assert (K1N : ~ In 0 K1) by (apply nulfree_skipn; exact LN).
  destruct (p5_trim_props K0 L_trim_holds K0B K0N) as (KB & KN & KL).
  destruct (p5_trim_props K1 L_trim_holds K1B K1N) as (VB & VN & VL).
  (* `mv s9, a0; sb zero, 0(a0)`: *eq = 0 *)
  zstep.
  assert (HS : store_ok rsegs m (wa (lp + Z.of_nat ei)) 1 = true).
  { apply (wr_at_store_ok rsegs m lp (Z.of_nat (length L) + 1) (Z.of_nat ei) 1); [|lia|lia].
    apply (p5_stk_wr rsegs m lo (bv_unsigned sp + PARSE_FILE_FRAME)); [exact ST | unfold REFUSE_STACK, PRINTF_K in DEP; lia
                                                                     | lia | unfold PARSE_FILE_FRAME; lia]. }
  zstep. replace (le1 (Z_to_bv 64 0)) with [ZERO] by reflexivity.
  pose proof (p5_mem_store m0 m (bv_unsigned sp) lo (lp + Z.of_nat ei) [ZERO] PM
                ltac:(unfold REFUSE_STACK, PRINTF_K in DEP; lia) ltac:(unfold PF_BUF; lia)
                ltac:(unfold PF_BUF; cbn [length]; lia) HS) as PM1.
  pose proof (p5_store_run rsegs m lp (zb L ++ [ZERO]) ei ZERO BL
                ltac:(rewrite length_app, p5_len_zb; cbn [length]; lia)) as B1.
  rewrite p5_upd_eq in B1 by exact EIL. fold K0 K1 in B1.
  apply bytes_at_app in B1 as [B1a B1b]. rewrite length_app, p5_len_zb, LK0 in B1b. cbn [length] in B1b.
  change (write_to_mem m (Z_to_bv 64 (lp + Z.of_nat ei)) [ZERO]) with (write_to_mem m (wa (lp + Z.of_nat ei)) [ZERO]).
  set (m1 := write_to_mem m (wa (lp + Z.of_nat ei)) [ZERO]) in *.
  clearbody m1. clear HS BL.
  (* trim(line) -> key *)
  zstep. zstep.
  eapply p5_trim_call with (m0 := m0) (lo := lo) (p := lp) (K := K0);
    [exact PM1 | exact DEP | exact AL' | exact RO' | exact B1a | exact K0B | exact K0N | unfold PF_BUF; lia | unfold PF_BUF; lia | reflexivity |].
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m2 PM2 MU2 BQ2.
  replace (ret_pc (Z_to_bv 64 0x14f00)) with (Z_to_bv 64 0x14f00) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_trim_run rsegs m2 lp K0 L_trim_holds K0N BQ2) as BK2.
  assert (B2b : bytes_at rsegs m2 (lp + Z.of_nat (ei + 1)) (zb K1 ++ [ZERO])).
  { eapply bytes_at_transport; [exact B1b | exact MU2 |]. unfold trim_end_addr. rewrite length_app, p5_len_zb.
    cbn [length]. unfold REFUSE_STACK, PRINTF_K in DEP. dj. }
  clear BQ2 MU2 B1a B1b PM1.
  (* trim(eq + 1) -> v *)
  zstep. zstep. zstep.
  eapply p5_trim_call with (m0 := m0) (lo := lo) (p := lp + Z.of_nat (ei + 1)) (K := K1);
    [exact PM2 | exact DEP | exact AL' | exact RO' | exact B2b | exact K1B | exact K1N | unfold PF_BUF; lia | unfold PF_BUF; lia | |].
  { apply bv_eq. rewrite !unsigned_lit by lia. lia. }
  intros w0 w1 w2 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 m3 PM3 MU3 BQ3.
  replace (ret_pc (Z_to_bv 64 0x14f0c)) with (Z_to_bv 64 0x14f0c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (p5_trim_run rsegs m3 (lp + Z.of_nat (ei + 1)) K1 L_trim_holds K1N BQ3) as BV3.
  assert (BK3 : bytes_at rsegs m3 (lp + Z.of_nat (trim_lead K0)) (zb (r_trim K0) ++ [ZERO])).
  { eapply bytes_at_transport; [exact BK2 | exact MU3 |]. unfold trim_end_addr. rewrite length_app, p5_len_zb.
    cbn [length]. unfold REFUSE_STACK, PRINTF_K in DEP. dj. }
  zstep.
  eapply p5_unq with (ei := ei); [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | exact CX | exact PS
    | exact PM3 | exact FRM | exact LB | exact LN | exact SE | exact BK3 | | unfold PF_BUF; lia | unfold K0, K1, L in *; lia | unfold PF_BUF, K0, K1, L in *; lia].
  exact BV3.
Qed.

(** The no-'=' branch from 0x14eec (strchr gave NULL): refuse(c, lineno, F_neither, line), then S9 -> TAIL. *)
Definition p5_nei_stmt (n : nat) : Prop :=
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc fc0 : bv 32)
    (m0 m : word -> option byte) (lo : Z) (v : pf_sv) (c t : Z) (s : list Z) (rc : rconf) (cur : option nat)
    (nm : list Z) (o : nat) (ln : Z) (d : list (list Z)) (lp : Z),
  pf_ctx m0 fc0 (bv_unsigned sp) lo v c t s o ln d n ->
  pf_state m0 (bv_unsigned sp) c rc cur nm (length (skipn o s)) ->
  p5_mem m0 m (bv_unsigned sp) lo -> frm0 fc ->
  strchr (pf_tline s o) EQ = None ->
  cstr_at rsegs m lp (pf_tline s o) -> pf_inb (bv_unsigned sp + PF_BUF) lp (pf_tline s o) ->
  evt rsegs (p5_post v sp gp tp F m0 lo c rc cur nm s o ln)
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 HASH) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (t + Z.of_nat (pf_next s o))) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 SEMI) s5
             (Z_to_bv 64 (pf_cur_ptr c cur)) (Z_to_bv 64 lp) s8 (Z_to_bv 64 512) (Z_to_bv 64 SP)
             (Z_to_bv 64 TAB) t3 t4 t5 t6)
        F (Z_to_bv 64 0x14eec) fc None m (seg_rom rsegs)).

(** KEY (0x14ee0): strchr(line, '='), then the no-'=' branch or the split line. *)
Lemma p5_key : forall n, H_OUTS n -> H_ROLE n -> H_MODEL n -> H_IGN n -> H_KNOCK n -> H_NOKEY n -> p5_nei_stmt n ->
  H_KEY n.
Proof.
  intros n HO HR HM HI HK HN NEI. unfold H_KEY.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v c t
    s rc cur nm o ln d lp CX PS HRg H9 H6 HL H7 CL IL H0 HB.
  destruct HRg as (E0 & E2 & E3 & E1 & E4 & E10 & E11). subst s0 s2 s3 s1 s4 s10 s11 s9 s6 s7.
  pose proof (p5_mem_refl m fc _ _ _ _ (proj1 CX)) as PM.
  pose proof (proj1 CX) as (_ & _ & _ & _ & (FRM & _) & _).
  pose proof (p5_env_num _ _ _ _ _ _ (proj1 CX)) as (LO0 & DEP & _ & SPH & _ & _ & _).
  unfold REFUSE_STACK, PRINTF_K in DEP. unfold PARSE_FILE_FRAME in SPH.
  pose proof IL as IL'. unfold pf_inb, PF_BUF in IL'.
  destruct (p5_cstr_run rsegs m lp _ CL) as (BL & LB & LN).
  fold (p5_post v sp gp tp F m lo c rc cur nm s o ln).
  unfold PF_PC_KEY. zstep. zstep. zstep.
  eapply p5_strchr_call with (m0 := m) (lo := lo) (lp := lp) (L := pf_tline s o);
    [exact PM | exact DEP | exact CL | lia | reflexivity | reflexivity |].
  intros u0 u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 ua7 u3 u4 u5 u6 m1 PM1 MU1.
  replace (ret_pc (Z_to_bv 64 0x14eec)) with (Z_to_bv 64 0x14eec) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (BL1 : bytes_at rsegs m1 lp (zb (pf_tline s o) ++ [ZERO])).
  { eapply bytes_at_transport; [exact BL | exact MU1 |]. rewrite length_app, p5_len_zb. cbn [length].
    unfold REFUSE_STACK, PRINTF_K in DEP. dj. }
  assert (CL1 : cstr_at rsegs m1 lp (pf_tline s o)).
  { eapply p5_cstr_munch; [exact CL | exact MU1 |]. dj. }
  destruct (strchr (pf_tline s o) 61) as [ei|] eqn:SE.
  - pose proof (p5_strchr_some _ _ _ SE) as (EIL & _).
    pose proof (bytes_at_bound _ _ _ _ BL) as BLb. rewrite length_app, p5_len_zb in BLb. cbn [length] in BLb.
    zstep. p5_br.
    eapply p5_key_some with (ei := ei); [exact HO | exact HR | exact HM | exact HI | exact HK | exact HN | exact CX
      | exact PS | exact PM1 | exact FRM | exact LB | exact LN | exact SE | exact BL1 | exact IL].
  - eapply NEI; [exact CX | exact PS | exact PM1 | exact FRM | exact SE | exact CL1 | exact IL].
Qed.

Lemma p5_P5W_Wp : forall sp c, sub_fp (P5W sp) (pf_Wp sp c).
Proof.
  intros sp c. unfold sub_fp, P5W, pf_Wp, PF_LO, PF_SCRATCH, PF_BUF, PF_NAMEBUF. intros x Hx.
  cbn [outside] in *. destruct Hx as (H1 & H2 & _). split; [exact H1 | split; [lia | exact I]].
Qed.

Lemma p5_pf_mem : forall m0 m fc sp lo c v rc,
  pf_env m0 fc sp lo c v -> rconf_at rsegs m0 c rc -> p5_mem m0 m sp lo -> pf_mem m0 m sp lo c.
Proof.
  intros m0 m fc sp lo c v rc E RC (MU & WM & MI & TM & ST).
  pose proof (pf_mem_refl m0 fc sp lo c v rc E RC) as (WOK & _).
  split; [exact WOK|]. split; [exact (munch_weaken _ _ _ _ (p5_P5W_Wp sp c) MU)|].
  split; [exact WM|]. split; [exact MI|]. split; [exact TM | exact ST].
Qed.

Lemma p5_refuse_W_Wp : forall sp c rc, (length (rc_refusal rc) <= 8)%nat ->
  sub_fp (refuse_W sp c rc) (pf_Wp sp c).
Proof.
  intros sp c rc H8. unfold sub_fp, refuse_W. intros x Hx.
  destruct (length (rc_refusal rc) <? 8)%nat eqn:E8.
  - apply Nat.ltb_lt in E8. revert Hx. pf_goal. intros Hx.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [exact I | lia].
  - revert Hx. pf_goal. rewrite app_nil_r. cbn [outside]. intros Hx.
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat split; first [exact I | lia].
Qed.

Lemma p5_nei : forall n, H_TAIL n -> p5_nei_stmt n.
Proof.
  intros n HT. unfold p5_nei_stmt.
  intros ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s8 t3 t4 t5 t6 F fc fc0 m0 m lo v c t s rc cur nm o ln d lp
    CX PS PM FRM SE CL IL.
  pose proof PS as (RC0 & CO & NM0 & CN).
  pose proof RC0 as (bs0 & BC0 & (LB0 & _ & _ & _ & L8 & _)).
  pose proof (bytes_at_bound _ _ _ _ BC0) as BCb. unfold SEG_C_SIZE in LB0.
  pose proof (p5_pf_mem m0 m fc0 _ lo c v rc (proj1 CX) RC0 PM) as PFM.
  pose proof (pf_mem_wok _ _ _ _ _ PFM) as WOK.
  destruct (pf_wok_nums _ _ _ WOK) as (N1 & N2 & N3 & N4 & N5).
  pose proof CX as (ENV & (T0 & TCS & TL & TAP & TAPC) & SPL & Ho & Hn & (LC1 & LC2 & LC3 & LC4)).
  assert (RC : rconf_at rsegs m c rc).
  { eapply p5_rconf_munch; [exact RC0 | exact (proj1 PM) |]. revert N4. unfold P5W, PARSE_FILE_STACK,
      PARSE_FILE_FRAME, REFUSE_STACK, PRINTF_K, PF_BUF, SEG_C_SIZE. intros N4'. dj. }
  pose proof (pf_env_mem m0 m0 fc0 fc _ lo c v ENV (pf_mem_refl m0 fc0 _ lo c v rc ENV RC0) FRM) as ENVfc.
  unfold pf_inb, PF_BUF in IL.
  pose proof (pf_lo_callee _ _ _ WOK) as (LOc & LOe & LOn).
  assert (TLz : Z.of_nat (length s) <= 65535).
  { apply Nat2Z.inj_le in TL. assert (E : Z.of_nat 65535 = 65535) by reflexivity. rewrite E in TL. exact TL. }
  assert (LN1 : 0 <= ln + 1 < 2 ^ 31) by (clear - LC1 TLz LC3 LC4; lia).
  zstep. rewrite bv_eqb_refl. pc_if.
  do 6 zstep.
  eapply evt_cut.
  { apply (HREF _ _ _ _ _ _ _ _ _ (Z_to_bv 64 c) (Z_to_bv 64 (ln + 1)) (Z_to_bv 64 PF_STR_NEITHER) (Z_to_bv 64 lp)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (PF_LO (bv_unsigned sp)) (ln + 1) rc F_neither
             [AS (pf_tline s o)]).
    rewrite !unsigned_lit by (unfold PF_STR_NEITHER; lia).
    apply (pf_refuse_pre m0 m fc (bv_unsigned sp) lo c v rc (ln + 1) F_neither PF_STR_NEITHER
             (length (skipn o s))); try assumption.
    - unfold PF_FMTS. cbn [In]. do 8 right. left. reflexivity.
    - reflexivity.
    - cbn [va_args_ok]. split; [|exact I].
      pose proof PM as (_ & _ & _ & _ & (_ & HI0 & _)). unfold PARSE_FILE_FRAME in HI0.
      apply (pf_va_frame m _ lo c rc); try assumption; rewrite unsigned_lit by lia; [exact CL | lia | ].
      unfold PARSE_FILE_FRAME. lia. }
  intros ms' (u0 & u1 & u2 & ua0 & ua1 & ua2 & ua3 & ua4 & ua5 & ua6 & ua7 & u3 & u4 & u5 & u6 & F' & fc' & m' &
              E & FRM' & FF' & MU' & WM' & MI' & TM' & ST' & RC').
  subst ms'. rewrite unsigned_lit in MU', RC' by lia.
  replace (ret_pc (Z_to_bv 64 0x14f7c)) with (Z_to_bv 64 0x14f7c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  pose proof (pf_mem_call m0 m m' _ lo c _ PFM (p5_refuse_W_Wp _ c rc L8) MU' WM' MI') as PFM'.
  destruct (pf_tail_ctx m0 m' fc0 fc' _ lo v c t s o ln d n CX PFM' FRM') as (HC & HN).
  destruct (p5_refuse_rec rc (ln + 1) F_neither [AS (pf_tline s o)]) as (RS & RR & RO).
  eapply evt_mono.
  { apply (p5_s9 n HT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' lo v c t s
             (refuse rc (ln + 1) F_neither [AS (pf_tline s o)]) cur nm (pf_next s o) (ln + 1) d); unfold PF_PC_S9.
    - exact HC.
    - split; [exact RC'|]. split; [destruct cur; cbn [pf_cur_ok] in *; [rewrite RS; exact CO | exact I]|].
      split; [exact (pf_nm_at_mem m0 m' _ lo c nm NM0 PFM')|].
      apply (pfb_cnt_next rc _ s o Ho CN); lia.
    - exact HN.
    - repeat split.
    - reflexivity. }
  intros ms PO. unfold p5_post. rewrite (p5_rkey_none rc cur nm (ln + 1) (pf_tline s o) SE).
  eapply pf_fin_weaken; [exact FF' | exact PFM' | exact PO].
Qed.

End Walk.

(** ** The piece *)
Theorem pf_p5_holds : strchr_contract -> trim_contract -> strlen_contract -> refuse_contract -> strcasecmp_contract ->
  S_P5.
Proof.
  intros STR TR SL RF SC n. split.
  - intros HO HR HM HI HK HN HT.
    apply (p5_key STR TR SL SC n HO HR HM HI HK HN (p5_nei RF n HT)).
  - apply p5_s9.
Qed.
