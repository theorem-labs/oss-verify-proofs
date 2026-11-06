(* The slot's entry, first part (arm `en`, prefix LE): 0x1384c .. 0x138c8, i.e. the prologue, the
   size test, the memset of the fake kernel, and the constants interfaces() runs on.  It ends
   either at the head of the 64-name loop (0x138cc, LEDefs' `L_IF_HEAD`) with
   `le_if_mem0 G 0 (g_ps 0) (g_ixs 0)`, or -- when the size does not fit 26 bits -- at the
   epilogue 0x1414c (LEDefs' `le_free2r`), from which LEX's `le_EXc` returns 0. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import
  PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Img0 MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import memset_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LEDefs.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   Facts the walk needs about the image and about task_mem
   ========================================================================== *)

(* Every address of the image is below TASK_SIZE (lib/Reusable/YL0i.v lib_pre_x_sp puts the slot's
   own stack pointer, about 1.4e14, below it), so a callee that writes only inside the image keeps
   `task_mem`, which memset's Post does not state. *)
Lemma task_mem_img : forall (m m' : word -> option byte) (lo hi : Z),
  MemNorm.task_mem rsegs m -> munch [(lo, hi)] m m' -> 0 <= lo -> hi <= 0x960e0 ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros m m' lo hi TM MU Hlo Hhi a b E.
  destruct (Z.le_gt_cases lo (bv_unsigned a)) as [L|L].
  - destruct (Z.lt_ge_cases (bv_unsigned a) hi) as [H|H].
    + right. unfold TASK_SIZE. lia.
    + rewrite (MU a ltac:(cbn [outside]; split; [lia | exact I])) in E. exact (TM a b E).
  - rewrite (MU a ltac:(cbn [outside]; split; [lia | exact I])) in E. exact (TM a b E).
Qed.

(* the size test at 0x1388c: `srli a1, a1, 0x1a` then `bnez a1` *)
Lemma shr26_zero : forall u, 0 <= u < 2 ^ 26 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = true.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_small by lia.
  unfold bv_eqb. apply Z.eqb_refl.
Qed.

Lemma shr26_nonzero : forall u, 2 ^ 26 <= u < 2 ^ 32 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (Hq : 1 <= u / 2 ^ 26 < 2 ^ 6) by (Z.div_mod_to_equations; lia).
  unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.mod_small by lia.
  apply Z.eqb_neq. lia.
Qed.

(* the g_nl block is one of the image's writable segments, so a byte list of its size exists *)
Lemma nlk_of_cells : forall (m : word -> option byte) (j : list byte),
  rw_cells rsegs m A_G_NL [CB (Z.to_nat NK_SIZE) j] ->
  (exists kb, Z.of_nat (length kb) = NK_SIZE /\ bytes_at rsegs m A_G_NL kb) /\
  wr_at rsegs m A_G_NL NK_SIZE.
Proof.
  intros m j [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw.
  split; [exists j; split; [rewrite HL; unfold NK_SIZE; lia | exact Hb]|].
  replace NK_SIZE with (Z.of_nat (Z.to_nat NK_SIZE)) by (unfold NK_SIZE; lia). exact Hw.
Qed.

(* splitting a cell list at a boundary *)
Lemma rw_cells_app_split : forall m A pre post,
  rw_cells rsegs m A (pre ++ post) ->
  rw_cells rsegs m A pre /\ rw_cells rsegs m (A + Z.of_nat (cells_size pre)) post.
Proof.
  intros m A pre post [[Hwf Hb] Hw].
  apply cells_wf_app in Hwf. destruct Hwf as [Hp Hq].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb1 Hb2].
  rewrite (cells_bytes_length pre Hp) in Hb2.
  rewrite cells_size_app, Nat2Z.inj_add in Hw.
  destruct Hw as (Hw0 & Hw1 & Hw2).
  split; split.
  - split; [exact Hp | exact Hb1].
  - split; [lia|]. split; [lia|]. intros i Hi. apply Hw2. lia.
  - split; [exact Hq | exact Hb2].
  - split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat (cells_size pre) + i) with (A + (Z.of_nat (cells_size pre) + i)) by lia.
    apply Hw2. lia.
Qed.

(* the 104 saved bytes, from the 13 cells the prologue wrote *)
Lemma cells_lr : forall m A (R : lregs),
  rw_cells rsegs m A [C8 (r_s11 R); C8 (r_s10 R); C8 (r_s9 R); C8 (r_s8 R); C8 (r_s7 R);
                      C8 (r_s6 R); C8 (r_s5 R); C8 (r_s4 R); C8 (r_s3 R); C8 (r_s2 R);
                      C8 (r_s1 R); C8 (r_s0 R); C8 (r_ra R)] ->
  bytes_at rsegs m A (lr_bytes R) /\ wr_at rsegs m A 104.
Proof.
  intros m A R [[_ Hb] Hw]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize] in Hw. split; [exact Hb | exact Hw].
Qed.

(* a 32-bit and a 64-bit zero out of a run of zero bytes *)
Lemma le4_zero : le4 (wz 0) = repeat (zb 0) 4.
Proof. vm_compute. reflexivity. Qed.
Lemma le8_zero : le8 (wz 0) = repeat (zb 0) 8.
Proof. vm_compute. reflexivity. Qed.

Lemma rep_slice : forall m A n off k,
  bytes_at rsegs m A (repeat (zb 0) n) -> 0 <= off -> 0 <= k -> off + k <= Z.of_nat n ->
  bytes_at rsegs m (A + off) (repeat (zb 0) (Z.to_nat k)).
Proof.
  intros m A n off k HB Hoff Hk Hn.
  destruct (bytes_at_split m A (repeat (zb 0) n) (Z.to_nat off) HB) as [_ HB1].
  rewrite firstn_length, repeat_length in HB1.
  replace (Nat.min (Z.to_nat off) n) with (Z.to_nat off) in HB1 by lia.
  replace (A + Z.of_nat (Z.to_nat off)) with (A + off) in HB1 by lia.
  rewrite skipn_rep in HB1.
  destruct (bytes_at_split m (A + off) (repeat (zb 0) (n - Z.to_nat off)) (Z.to_nat k) HB1)
    as [HB2 _].
  rewrite firstn_rep in HB2.
  replace (Nat.min (Z.to_nat k) (n - Z.to_nat off)) with (Z.to_nat k) in HB2 by lia.
  exact HB2.
Qed.

Lemma u32_zero_of_rep : forall m A n off,
  bytes_at rsegs m A (repeat (zb 0) n) -> 0 <= off -> off + 4 <= Z.of_nat n ->
  u32_at m (A + off) 0.
Proof.
  intros m A n off HB Hoff Hn. unfold u32_at. rewrite le4_zero.
  exact (rep_slice m A n off 4 HB Hoff ltac:(lia) ltac:(lia)).
Qed.

(* ==========================================================================
   Carrying the entry's views across a window the callee wrote
   ========================================================================== *)

(* every address of [lo, hi) is outside the window W *)
Definition outs (W : list ivl) (lo hi : Z) : Prop := forall x, lo <= x < hi -> outside W x.

Lemma outs_sub : forall W lo hi lo' hi', outs W lo hi -> lo <= lo' -> hi' <= hi ->
  outs W lo' hi'.
Proof. intros W lo hi lo' hi' H L1 L2 x Hx. apply H. lia. Qed.

Lemma bytes_at_pt : forall W m m' A bs,
  bytes_at rsegs m A bs -> munch W m m' ->
  outs W A (A + Z.of_nat (length bs)) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs (H1 & H2 & H3) MU HO. split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite <- (H3 i Hi). unfold mrd.
  rewrite (MU (wa (A + Z.of_nat i)) ltac:(unfold wa; rewrite unsigned_lit by lia; apply HO; lia)).
  reflexivity.
Qed.

Lemma rw_cells_pt : forall W m m' A cs,
  rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  outs W A (A + Z.of_nat (cells_size cs)) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU WM HO. split; [split; [exact Hwf|]|].
  - apply (bytes_at_pt W m m' A _ Hb MU).
    rewrite (cells_bytes_length cs Hwf). exact HO.
  - exact (wr_at_transport rsegs m m' A _ Hw WM).
Qed.

Lemma u64_at_pt : forall W m m' A v,
  u64_at m A v -> munch W m m' -> outs W A (A + 8) -> u64_at m' A v.
Proof.
  intros W m m' A v H MU HO. unfold u64_at in *.
  apply (bytes_at_pt W m m' A _ H MU). rewrite length_le8. exact HO.
Qed.

Lemma u32_at_pt : forall W m m' A v,
  u32_at m A v -> munch W m m' -> outs W A (A + 4) -> u32_at m' A v.
Proof.
  intros W m m' A v H MU HO. unfold u32_at in *.
  apply (bytes_at_pt W m m' A _ H MU). rewrite length_le4. exact HO.
Qed.

Lemma cstr_at_pt : forall W m m' A s,
  cstr_at m A s -> munch W m m' ->
  outs W A (A + Z.of_nat (length s) + 1) -> cstr_at m' A s.
Proof.
  intros W m m' A s [HB HN] MU HO. split; [|exact HN].
  apply (bytes_at_pt W m m' A _ HB MU). rewrite app_length. cbn [length].
  eapply outs_sub; [exact HO | lia | lia].
Qed.

(* The image facts the entry keeps live below g_nl (the policy strings in .rodata, the two pointer
   tables and the GOT guard slot in .data.rel.ro) and at the stack guard word, so they survive a
   window that covers g_nl and g_names. *)
Lemma le_img_pt : forall W m m', le_img m -> munch W m m' ->
  outs W 0x10000 A_G_NL -> outs W A_GUARD_S (A_GUARD_S + 8) -> le_img m'.
Proof.
  intros W m m' (OD & TX & PO & GU) MU HO HG.
  assert (SUB : forall lo hi, 0x10000 <= lo -> hi <= A_G_NL -> outs W lo hi)
    by (intros lo hi L1 L2; eapply outs_sub; [exact HO | lia | lia]).
  split; [|split; [|split]].
  - intros i Hi. destruct (OD i Hi) as [HU HC]. split.
    + apply (u64_at_pt W m m' _ _ HU MU). apply SUB; unfold A_ODD, A_G_NL; lia.
    + apply (cstr_at_pt W m m' _ _ HC MU).
      assert (HB : 0x10000 <= nth i odd_ptrs 0 /\
                   nth i odd_ptrs 0 + Z.of_nat (length (nth i odd_strs [])) + 1 <= A_G_NL).
      { unfold A_G_NL. destruct i as [|[|[|[|[|[|i]]]]]]; cbn [nth odd_ptrs odd_strs];
          cbn [length S_ENP S_ETH0 S_WLAN0 S_VETH S_GONE0 map]; lia. }
      apply SUB; lia.
  - intros i Hi. apply (u64_at_pt W m m' _ _ (TX i Hi) MU).
    apply SUB; unfold A_TEXTS, A_G_NL; lia.
  - destruct PO as (P1 & P2 & P3 & P4). split; [|split; [|split]];
      [ apply (cstr_at_pt W m m' _ _ P1 MU) | apply (cstr_at_pt W m m' _ _ P2 MU)
      | apply (cstr_at_pt W m m' _ _ P3 MU) | apply (cstr_at_pt W m m' _ _ P4 MU) ];
      apply SUB; unfold A_PREFIX, A_SERVED, A_VLAN, A_EMPTY, A_G_NL, S_PREFIX, S_SERVED, S_VLAN;
      cbn [length map]; lia.
  - destruct GU as (G1 & (c & G2)). split.
    + apply (bytes_at_pt W m m' _ _ G1 MU). rewrite length_le8.
      apply SUB; unfold A_GOT_GUARD_S, A_G_NL; lia.
    + exists c. apply (bytes_at_pt W m m' _ _ G2 MU). rewrite length_le8.
      eapply outs_sub; [exact HG | lia | lia].
Qed.

Lemma la_ok_pt : forall W m m', la_ok m -> munch W m m' -> wmono rsegs m m' ->
  outs W A_LONG_ALIAS (A_LONG_ALIAS + 304) -> la_ok m'.
Proof.
  intros W m m' (la & sl & HC & HB & HL) MU WM HO. exists la, sl.
  split; [apply (rw_cells_pt W m m' _ _ HC MU WM);
            cbn [cells_size csize]; eapply outs_sub; [exact HO | lia | lia]|].
  split; [|exact HL].
  apply (bytes_at_pt W m m' _ _ HB MU). rewrite HL.
  eapply outs_sub; [exact HO | unfold LONG_ALIAS_SIZE; lia | unfold LONG_ALIAS_SIZE; lia].
Qed.

Lemma le_base_pt : forall (G : lent) W m m',
  le_base G m -> munch W m m' -> wmono rsegs m m' ->
  mem_inv rsegs m' -> MemNorm.task_mem rsegs m' ->
  outs W 0x10000 A_G_NL -> outs W A_GUARD_S (A_GUARD_S + 8) ->
  outs W A_LONG_ALIAS (A_LONG_ALIAS + 304) ->
  le_place G ->
  (forall x, 0 <= x < 0x10000 -> outside W x) ->
  (forall x, 0x97000 <= x < n_S G - SLOT_STACK_Z -> outside W x) ->
  le_base G m'.
Proof.
  intros G W m m' (IMG & LA & PAY & ER & MI & TM) MU WM MI' TM' HO HG HL PL PLO PHI.
  split; [exact (le_img_pt W m m' IMG MU HO HG)|].
  split; [exact (la_ok_pt W m m' LA MU WM HL)|].
  split; [exact (pay_keep G W m m' PL PAY MU PLO PHI)|].
  split; [exact (wr_at_transport rsegs m m' _ _ ER WM)|].
  split; [exact MI' | exact TM'].
Qed.

(* a callee that writes only below TASK_SIZE keeps task_mem, which memset's Post does not state *)
Lemma task_mem_pt : forall (m m' : word -> option byte) (W : list ivl),
  MemNorm.task_mem rsegs m -> munch W m m' ->
  (forall x : word, outside W (bv_unsigned x) \/ bv_unsigned x < 2 ^ 47) ->
  MemNorm.task_mem rsegs m'.
Proof.
  intros m m' W TM MU HW a b E. destruct (HW a) as [HO|HB].
  - rewrite (MU a HO) in E. exact (TM a b E).
  - right. unfold TASK_SIZE. lia.
Qed.

(* ==========================================================================
   The walk 0x1384c -> 0x138cc, or the early return at 0x1414c
   ========================================================================== *)

Section E0a.
Hypothesis MEMSET : memset_contract.

Lemma le_E0a : forall (G : lent) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  le_place G -> frm0 fc -> le_entry_mem G m ->
  evt rsegs
    (fun ms' =>
       ((exists (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                (m' : word -> option byte),
           ms' = MS (mkR ra' (wz (n_S G - SLOT_FRAME)) (n_gp G) (wz A_TP) t0' t1' t2'
                         (wz A_G_NAMES) (wz A_FMT_NL) a0' a1' a2' a3' a4' a5' a6' a7'
                         (wz (n_len G)) (wz A_G_NL) (r_s4 (n_R G)) (wz GNL_OFF) (wz 2) (wz 15)
                         (wz 0x42) (wz GNL42) (r_s10 (n_R G)) (r_s11 (n_R G)) t3' t4' t5' t6')
                    F (wz L_IF_HEAD) fc None m' (seg_rom rsegs) /\
           n_len G < 2 ^ 26 /\ le_if_mem0 G 0 (g_ps 0) (g_ixs 0) m')
        \/ le_free2r (n_S G) (n_gp G) (n_R G) ms') /\
       munch (le_W0 G) m (ms_mem ms') /\ wmono rsegs m (ms_mem ms'))
    (MS (mkR (r_ra (n_R G)) (wz (n_S G)) (n_gp G) (wz A_TP) t0 t1 t2 (r_s0 (n_R G)) (r_s1 (n_R G))
             (wz (n_p0 G)) (wz (n_len G)) a2 a3 a4 a5 a6 a7
             (r_s2 (n_R G)) (r_s3 (n_R G)) (r_s4 (n_R G)) (r_s5 (n_R G)) (r_s6 (n_R G))
             (r_s7 (n_R G)) (r_s8 (n_R G)) (r_s9 (n_R G)) (r_s10 (n_R G)) (r_s11 (n_R G))
             t3 t4 t5 t6)
        F (wz L_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros G t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m PL FC EM.
  assert (ST : stk rsegs m (n_S G - SLOT_STACK_Z) (n_S G))
    by (destruct EM as (_ & _ & _ & H); exact H).
  assert (MI : mem_inv rsegs m)
    by (destruct EM as ((_ & _ & _ & _ & H & _) & _); exact H).
  assert (TM : MemNorm.task_mem rsegs m)
    by (destruct EM as ((_ & _ & _ & _ & _ & H) & _); exact H).
  pose proof PL as PL'.
  destruct PL' as (HS1 & HS2 & HS16 & HPD & HLEN).
  pose proof (Nat2Z.is_nonneg (length (n_pl G))) as HN0.
  unfold n_len in *.
  unfold wz, L_ENTRY, L_IF_HEAD, SLOT_STACK_Z, SLOT_FRAME in *.
  pose proof (munch_refl [(n_S G - 65536, n_S G)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 480%nat ST.
  do 16 step.
  rewrite (unsigned_lit (Z.of_nat (length (n_pl G)))) by lia.
  assert (OW : forall lo hi, 0 <= lo -> (hi <= 203648 \/ (476152 <= lo /\
                 hi <= n_S G - 65536) \/ n_S G <= lo) -> outs (le_W0 G) lo hi).
  { intros lo hi Hl Hd x Hx. unfold le_W0, SLOT_STACK_Z; cbn [outside].
    unfold A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE in *.
    split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (GNL0 : exists jk, rw_cells rsegs m0 A_G_NL [CB (Z.to_nat NK_SIZE) jk]).
  { destruct EM as (_ & (jk & H) & _). exists jk.
    apply (rw_cells_pt _ m m0 _ _ H MU WM). cbn [cells_size csize].
    intros x Hx; cbn [outside]; split; [unfold A_G_NL, NK_SIZE in *; lia | exact I]. }
  assert (GN0 : exists jg, rw_cells rsegs m0 A_G_NAMES [CB (Z.to_nat G_NAMES_SIZE) jg]).
  { destruct EM as (_ & _ & (jg & H) & _). exists jg.
    apply (rw_cells_pt _ m m0 _ _ H MU WM). cbn [cells_size csize].
    intros x Hx; cbn [outside]; split; [unfold A_G_NAMES, G_NAMES_SIZE in *; lia | exact I]. }
  destruct GNL0 as (jk & GNLc). destruct GN0 as (jg & GNc).
  unfold A_G_NL, NK_SIZE in GNLc. unfold A_G_NAMES, G_NAMES_SIZE in GNc.
  assert (BASE : forall mm, mem_inv rsegs mm -> munch (le_W0 G) m mm ->
                   wmono rsegs m mm -> MemNorm.task_mem rsegs mm /\ le_base G mm).
  { intros mm MIx MUx WMx.
    assert (TMx : MemNorm.task_mem rsegs mm).
    { apply (task_mem_pt m mm (le_W0 G) TM MUx).
      intros x. destruct (Z.lt_ge_cases (bv_unsigned x) (2 ^ 47)) as [Hx|Hx]; [right; exact Hx|].
      left. unfold le_W0, SLOT_STACK_Z, A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE; cbn [outside].
      split; [lia|]. split; [lia|]. split; [lia | exact I]. }
    split; [exact TMx|].
    destruct EM as (B & _). apply (le_base_pt G _ m mm B MUx WMx MIx TMx).
    - unfold A_G_NL. apply OW; lia.
    - unfold A_GUARD_S. apply OW; lia.
    - unfold A_LONG_ALIAS. apply OW; lia.
    - exact PL.
    - apply (OW 0 0x10000); lia.
    - unfold SLOT_STACK_Z. apply (OW 0x97000 (n_S G - 65536)); lia. }
  clear EM TM.
  step. if_cases HC; zify_cond HC.
  - (* the size does not fit 26 bits: 0x1414c, the epilogue *)
    assert (MUW : munch (le_W0 G) m m0).
    { apply (munch_weaken [(n_S G - 65536, n_S G)] (le_W0 G) m m0); [|exact MU].
      unfold sub_fp, le_W0, SLOT_STACK_Z; cbn [outside]; intros x (H1 & H2 & H3 & _).
      split; [lia | exact I]. }
    destruct (BASE m0 MI MUW WM) as [TM0 BASE0].
    match type of FR with
    | rw_cells _ _ _ (?c :: ?rest) =>
        destruct (rw_cells_app_split m0 (n_S G + -480) [c] rest FR) as [FRpre FRsv]
    end.
    cbn [cells_size csize Nat.add] in FRsv, FRpre.
    replace (n_S G + -480 + Z.of_nat 376) with (n_S G - 104) in FRsv by lia.
    destruct (cells_lr m0 (n_S G - 104) (n_R G) FRsv) as [SB SW].
    apply evt_done. split; [right|].
    + unfold le_free2r, le_tail_mem, wz, SLOT_FRAME, SLOT_STACK_Z.
      do 28 eexists. exists F, fc, m0.
      replace (n_S G - 480) with (n_S G + -480) by lia.
      split; [reflexivity|]. split; [exact FC|].
      split; [match type of FRpre with rw_cells _ _ _ [CB _ ?j] => exists j end; exact FRpre|].
      split; [exact SB|]. split; [exact SW|].
      destruct BASE0 as (IMG0 & LA0 & _ & ER0 & _ & _).
      split; [exact ER0|]. split; [exact (proj2 (proj2 (proj2 IMG0)))|].
      split; [exact LA0|]. split; [exact MI|]. split; [exact TM0|]. exact ST.
    + cbn [ms_mem]. split; [exact MUW | exact WM].
  - (* the size fits: the memset of the fake kernel, then the constants *)
    assert (HSMALL : Z.of_nat (length (n_pl G)) < 2 ^ 26).
    { clear - HC HN0 HLEN. rewrite Z.shiftr_div_pow2 in HC by lia.
      Z.div_mod_to_equations; lia. }
    rewrite HC.
    do 7 step.
    eapply evt_cut.
    { eapply MEMSET.
      - rewrite !unsigned_lit by lia. exact GNLc.
      - exact MI. }
    intros ms' PO.
    destruct PO as (u0 & u1 & u2 & ua1 & ua2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & m2
                    & EQ & MU1 & WM1 & MI2 & GNLz).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 80044)) with (Z_to_bv 64 80044)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]).
    rewrite !unsigned_lit in MU1, GNLz by lia.
    replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0) mod 256)) with (zb 0) in GNLz
      by reflexivity.
    (* the fake kernel is now 271992 zero bytes; carry the rest across that window *)
    assert (OG : forall lo hi, (hi <= 203648 \/ 475640 <= lo) -> 0 <= lo ->
                   outs [(203648, 475640)] lo hi)
      by (intros lo hi Hd Hl x Hx; cbn [outside]; split; [lia | exact I]).
    assert (MU2 : munch (le_W0 G) m m2).
    { eapply munch_trans;
        [ apply (munch_weaken [(n_S G - 65536, n_S G)] (le_W0 G) m m1); [|exact MU];
          unfold sub_fp, le_W0, SLOT_STACK_Z; cbn [outside]; intros x (H1 & H2 & H3 & _);
          split; [lia | exact I] |].
      apply (munch_weaken [(203648, 475640)] (le_W0 G) m1 m2); [|exact MU1].
      unfold sub_fp, le_W0, SLOT_STACK_Z, A_G_NL, NK_SIZE, A_G_NAMES, G_NAMES_SIZE;
        cbn [outside]; intros x (H1 & H2 & H3 & _). split; [lia | exact I]. }
    assert (WM2 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM1]).
    destruct (BASE m2 MI2 MU2 WM2) as [TM2 BASE2].
    match type of FR with
    | rw_cells _ _ _ ?cs =>
        assert (FR2 : rw_cells rsegs m2 (n_S G + -480) cs)
          by (apply (rw_cells_pt _ m1 m2 _ _ FR MU1 WM1);
              cbn [cells_size csize Nat.add]; apply OG; lia)
    end.
    assert (ST2 : stk rsegs m2 (n_S G - 65536) (n_S G + -480)).
    { eapply stk_transport_disjoint; [exact ST | exact MU1 | exact WM1 |].
      cbn [disjoint_from]. split; [lia | exact I]. }
    match type of FR2 with
    | rw_cells _ _ _ (?c1 :: ?c2 :: ?c3 :: ?rest) =>
        destruct (rw_cells_app_split m2 (n_S G + -480) [c1; c2; c3] rest FR2) as [FRpre FRsv]
    end.
    cbn [cells_size csize Nat.add] in FRsv.
    replace (n_S G + -480 + Z.of_nat 376) with (n_S G - 104) in FRsv by lia.
    destruct (cells_lr m2 (n_S G - 104) (n_R G) FRsv) as [SB2 SW2].
    do 8 step.
    apply evt_done. split; [left|].
    + do 17 eexists.
      replace (A_G_NAMES + 8 * Z.of_nat 0) with A_G_NAMES by (unfold A_G_NAMES; lia).
      split; [reflexivity|]. split; [exact HSMALL|].
      unfold le_if_mem0, le_nlk, le_tabl, le_zfields, le_gnames, fr_cells0,
             SLOT_FRAME, SLOT_STACK_Z.
      destruct GNLz as [[GZwf GZb] GZw]. cbn [cells_bytes cbytes cells_size csize] in GZb, GZw.
      rewrite app_nil_r in GZb.
      replace (n_S G - 480) with (n_S G + -480) by lia.
      split; [exact BASE2|]. split; [split; [|split; [|split]]|].
      * exists (repeat (zb 0) (Z.to_nat 271992)).
        split; [rewrite repeat_length; unfold NK_SIZE; lia|].
        unfold A_G_NL. exact GZb.
      * unfold A_G_NL, NK_SIZE.
        replace 271992 with (Z.of_nat (Z.to_nat 271992)) by lia. exact GZw.
      * unfold A_G_NL, NK_N_CHUNKS, NK_NEXT, NK_END_ERRNO, NK_SOCKET_ERRNO, NK_SEND_ERRNO,
               NK_OPEN, NK_OPENED, NK_CLOSED, NK_MISUSE, NK_N_SENT.
        repeat split;
          (eapply u32_zero_of_rep; [exact GZb | lia | lia]).
      * unfold g_ps, g_ixs. cbn [kept map length Z.of_nat].
        split; [reflexivity|]. split.
        -- unfold A_G_NL, NK_N_IF.
           eapply u32_zero_of_rep; [exact GZb | lia | lia].
        -- intros i Hi. exfalso. cbn [length] in Hi. lia.
      * split.
        -- split; [intros j Hj; exfalso; lia|].
           exists jg.
           replace (A_G_NAMES + 8 * Z.of_nat 0) with 475640 by (unfold A_G_NAMES; lia).
           replace (Z.to_nat (G_NAMES_SIZE - 8 * Z.of_nat 0)) with (Z.to_nat 512)
             by (unfold G_NAMES_SIZE; f_equal; lia).
           apply (rw_cells_pt _ m1 m2 _ _ GNc MU1 WM1). cbn [cells_size csize].
           apply OG; lia.
        -- split;
             [match type of FRpre with
              | rw_cells _ _ _ [CB _ ?a; C8 _; CB _ ?b] => exists a, b end; exact FRpre|].
           split; [exact SB2|]. split; [exact SW2 | exact ST2].
    + cbn [ms_mem]. split; [exact MU2 | exact WM2].
Qed.

End E0a.
