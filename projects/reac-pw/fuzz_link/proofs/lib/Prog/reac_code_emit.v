(* reac_code_emit (reac_code.h:103-108, plain 0x16640, 29 instructions), PLAIN build: the walk of its
   contract (lib/Prog/reac_code_emit_c.v) on the plain image (link/ct/dis/plain/reac_code_emit.s).
   - +0x00..+0x24: the 64-byte frame: ra, s0, s1 at sp+0x18/+0x10/+0x8, s0 = fmt, s1 = f, and a4..a7
     at sp+0x20..+0x38 (the va_list slots);
   - +0x28..+0x44: fprintf(f, "%s: %s " (0x10558), "reac-pw" (0x10520), "E_NOT_MARKED" (0x103a8)),
     through lib/Prog/fprintf_c.v; the format and the two strings are the image's bytes
     (lib/Prog/link_msgs_fit.v `fmt_emit_ok`, `s_reacpw_ok`, `s_enm_ok`); the 22 bytes go after the
     k pending ones;
   - +0x48..+0x5c: ap = sp+0x20 stored at 0(sp), vfprintf(f, fmt, ap), through lib/Prog/vfprintf_c.v,
     with the four slots as its arguments (`va_of_frame`) and the FILE as fprintf left it;
   - +0x60..+0x70: ra, s0, s1 back, the frame released, ret.
   The FILE (`memfile_k`, `mf_dyn`, the pending bytes) and the caller's format and arguments are carried
   from the entry memory across the frame's stores and the two calls with the facts of
   lib/Prog/reac_code_emit_aux.v; the Post's k and T are the Pre's (`memfile_k_unique`,
   `emit_fmt_unique`). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import
  link_mem mk_leaf mk_leaf_fp mk_call mk_str memfile_c printf_facts_c vfprintf_c fprintf_c link_msgs_fit
  reac_code_emit_c reac_code_emit_aux.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require MemFile.
Local Open Scope Z_scope.

Definition emit_pre (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  exists fmt ps args T k,
    arg regs 0 <> 0 /\ arg regs 3 <> 0
    /\ emit_fmt m regs (arg regs 3) fmt ps args T
    /\ memfile_k m (arg regs 0) k
    /\ k + EMIT_HEAD + Z.of_nat (length T) <= MemFile.MF_BUFSIZ
    /\ arg regs 0 + FILE_BLOCK <= spZ regs - 6112.
Definition emit_wr (regs : bvmap 5 word) (m : word -> option byte) : list ivl := [mf_block (arg regs 0)].
Definition emit_post (regs : bvmap 5 word) (m : word -> option byte)
    (regs' : bvmap 5 word) (m' : word -> option byte) : Prop :=
  forall fmt ps args T k,
    emit_fmt m regs (arg regs 3) fmt ps args T -> memfile_k m (arg regs 0) k ->
    memfile_k m' (arg regs 0) (k + EMIT_HEAD + Z.of_nat (length T)).

Lemma emit_contract_eq : reac_code_emit_contract = leaf_fp REAC_CODE_EMIT 6112 emit_pre emit_wr emit_post.
Proof. reflexivity. Qed.

Theorem reac_code_emit_walk : fprintf_contract -> vfprintf_contract ->
  leaf_fp_walk REAC_CODE_EMIT 6112 emit_pre emit_wr emit_post.
Proof.
  intros HFP HVF. unfold leaf_fp_walk, REAC_CODE_EMIT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros PRE MI TM ST LO SP FRM ITOP GG GQ.
  destruct PRE as (fmt & ps & args & T & k & A0 & A3 & EF & MK & FIT & FB).
  rewrite mkR_a0 in A0, MK, FB. rewrite mkR_a3 in A3. rewrite mkR_sp in FB.
  unfold FILE_BLOCK in FB. unfold EMIT_HEAD in FIT.
  pose proof (memfile_k_place m _ k MK) as PL.
  pose proof (memfile_k_range m _ k MK) as RK.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  assert (Hf64 : bv_unsigned a0 + MemFile.MF_BLOCK < 2 ^ 64) by (unfold MemFile.MF_BLOCK; lia).
  destruct (mf_dyn_of_k m _ k MK Hf64) as (fl & om & wend & wpos & wbase & pos & len & MD).
  destruct (mf_pend_of_k m _ k MK) as (pb & MP & LP).
  assert (GW : guard_words m) by exact (conj GG GQ). clear GG GQ.
  assert (WV : forall x, lo <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; exact (proj1 (proj2 (proj2 ST) x Hx))).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 64%nat ST.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
  pose proof (memfile_k_at m _ k MK) as (F0 & _).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64)
    by (apply unsigned_lit; lia).
  assert (TM1 : task_mem rsegs m1) by (apply (task_mem_frame m m1 _ _ TM MU); intros x Hx; apply WV; lia).
  assert (OUT1 : forall z, bv_unsigned a0 <= z < bv_unsigned a0 + MemFile.MF_BLOCK ->
                           outside [(bv_unsigned sp + -64, bv_unsigned sp)] z)
    by (intros z Hz; cbn [outside]; unfold MemFile.MF_BLOCK in *; split; [lia | exact I]).
  pose proof (memfile_k_munch _ m m1 _ k MK MU WM OUT1) as MK1.
  pose proof (mf_dyn_munch _ m m1 _ _ _ _ _ _ _ _ MD MU ltac:(lia) ltac:(unfold MemFile.MF_BLOCK in *; lia) OUT1)
    as MD1.
  pose proof (mf_pend_munch _ m m1 _ pb MP MU ltac:(unfold MemFile.MF_BUFSIZ in *; lia) OUT1) as MP1.
  pose proof (guard_munch _ m m1 GW MU
                ltac:(intros z Hz; cbn [outside]; unfold GOT_GUARD, A_IMG_TOP in *; split; [lia | exact I])
                ltac:(intros z Hz; cbn [outside]; unfold GUARD, A_IMG_TOP in *; split; [lia | exact I])) as GW1.
  eapply (leaf_fp_call _ _ _ _ _
            (HFP (bv_unsigned a0) k fl om wend wpos wbase pos len pb FMT_EMIT PS_EMIT [APtr S_REACPW; APtr S_ENM] T_EMIT)
            (pf_post_ext (bv_unsigned a0) k pb T_EMIT fl om wend pos len)).
  { apply leaf_fp_q_ext. intros q1 q2 m' _ H. exact H. }
  { cbv beta. apply emit_head_pre; try reflexivity; try assumption.
    - unfold MemFile.MF_BUFSIZ in *. lia.
    - rewrite mkR_sp, ESP. unfold FPRINTF_K, MemFile.MF_BLOCK. lia.
    - rewrite mkR_sp, ESP. unfold FPRINTF_K, IMG_TOP, A_IMG_TOP in *. lia. }
  { exact MI. }
  { exact TM1. }
  { rewrite ESP. exact ST. }
  { rewrite ESP. unfold FPRINTF_K. lia. }
  { rewrite ESP. lia. }
  { exact FRM. }
  { exact ITOP. }
  { exact (proj1 GW1). }
  { exact (proj2 GW1). }
  intros ra1 t01 t11 t21 a01 a11 a21 a31 a41 a51 a61 a71 t31 t41 t51 t61 Ft1 fc1 m2 FRM1 FK1 MU1 WM1 MI1 TM2 ST1 PO1.
  cbv beta in MU1, PO1. destruct PO1 as [_ (MK2 & MD2 & MP2)].
  rewrite ESP in MU1, ST1.
  rewrite ret_pc_even by (lia || reflexivity).
  pose proof (rw_cells_transport rsegs _ m1 m2 _ _ FR MU1 WM1
                ltac:(cbn [disjoint_from cells_size csize mf_block fst snd Nat.add];
                      unfold FPRINTF_K, MemFile.MF_BLOCK in *; repeat split; lia)) as FR1.
  clear FR. rename FR1 into FR.
  assert (MUc : munch [(bv_unsigned sp - 6112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 1304)] m m2).
  { apply (munch_trans _ m m1 m2).
    - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in Hx |- *. split; [lia | exact I].
    - eapply munch_weaken; [|exact MU1]. intros x Hx. cbn [outside mf_block fst snd] in Hx |- *.
      unfold MemFile.MF_BLOCK, FPRINTF_K. split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs m m1 m2 WM WM1) as WMc.
  clear MU MU1 WM WM1 MK1 MD1 MP1 GW1 TM1 TM.
  rename MUc into MU, WMc into WM.
  assert (WV2 : forall x, bv_unsigned sp + -64 <= x < bv_unsigned sp -> wview rsegs m2 (wa x) <> None).
  { intros x Hx. destruct FR as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
    specialize (W (x - (bv_unsigned sp + -64)) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
    replace (bv_unsigned sp + -64 + (x - (bv_unsigned sp + -64))) with x in W by lia. exact W. }
  pose proof (munch_refl [(bv_unsigned sp + -64, bv_unsigned sp)] m2) as MU2.
  pose proof (wmono_refl rsegs m2) as WM2.
  zstep. zstep. zstep. zstep. zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
  clear MI ST.
  assert (TM3 : task_mem rsegs m3) by (apply (task_mem_frame m2 m3 _ _ TM2 MU2); exact WV2).
  assert (LT : Z.of_nat (length T_EMIT) = 22) by reflexivity.
  assert (LP2 : Z.of_nat (length (pb ++ pf_bytes T_EMIT)) = k + Z.of_nat (length T_EMIT))
    by (rewrite length_app; unfold pf_bytes; rewrite length_map; lia).
  pose proof (memfile_k_munch _ m2 m3 _ _ MK2 MU2 WM2 OUT1) as MK3.
  pose proof (mf_dyn_munch _ m2 m3 _ _ _ _ _ _ _ _ MD2 MU2 ltac:(lia) ltac:(unfold MemFile.MF_BLOCK in *; lia) OUT1)
    as MD3.
  pose proof (mf_pend_munch _ m2 m3 _ _ MP2 MU2 ltac:(rewrite LP2, LT; unfold MemFile.MF_BUFSIZ in *; lia) OUT1)
    as MP3.
  pose proof PL as PL'. unfold mf_place_ok, IMG_LO, IMG_TOP, MemFile.MF_BLOCK in PL'.
  pose proof (guard_munch _ m m3 GW MU
                ltac:(intros z Hz; cbn [outside]; unfold GOT_GUARD, A_IMG_TOP in *; split; [lia | split; [lia | exact I]])
                ltac:(intros z Hz; cbn [outside]; unfold GUARD, A_IMG_TOP in *; split; [lia | split; [lia | exact I]]))
    as GW3.
  assert (IT0 : IMG_TOP <= bv_unsigned sp - 6112) by (unfold IMG_TOP, A_IMG_TOP in *; lia).
  assert (L1 : bv_unsigned sp - 6112 <= bv_unsigned sp + -64 - VFPRINTF_K) by (unfold VFPRINTF_K; lia).
  assert (L2 : bv_unsigned sp + -64 <= bv_unsigned sp) by lia.
  destruct (emit_fmt_munch m m3 _ _ _ _ _ _ (bv_unsigned a0) (bv_unsigned sp + -64)
              (bv_unsigned sp + -64 - VFPRINTF_K) EF eq_refl PL MU IT0 L1 L2) as [FB3 PA3].
  pose proof EF as (_ & R1 & R2 & EP & ET & _).
  pose proof (va_of_frame _ _ _ _ _ _ _ _ _ _ FR) as VA.
  assert (ESP32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
    by (apply unsigned_lit; lia).
  eapply (leaf_fp_call _ _ _ _ _
            (HVF (bv_unsigned a0) (k + Z.of_nat (length T_EMIT)) fl (if wend =? 0 then YI14.U32M1 else om)
                 (bv_unsigned a0 + MemFile.MF_BUF + MemFile.MF_BUFSIZ)
                 (bv_unsigned a0 + MemFile.MF_BUF + k + Z.of_nat (length T_EMIT))
                 (bv_unsigned a0 + MemFile.MF_BUF) pos len (pb ++ pf_bytes T_EMIT) fmt ps args T [a4; a5; a6; a7])
            (pf_post_ext (bv_unsigned a0) (k + Z.of_nat (length T_EMIT)) (pb ++ pf_bytes T_EMIT) T fl
                 (if wend =? 0 then YI14.U32M1 else om) (bv_unsigned a0 + MemFile.MF_BUF + MemFile.MF_BUFSIZ) pos len)).
  { apply leaf_fp_q_ext. intros q1 q2 m' _ H. exact H. }
  { cbv beta.
    split; [reflexivity|].
    split; [exact MK3|]. split; [exact MD3|]. split; [exact MP3|]. split; [exact LP2|].
    split; [exact FB3|]. split; [exact R1|]. split; [exact R2|]. split; [exact EP|]. split; [exact ET|].
    split; [rewrite mkR_a2, ESP32; replace (bv_unsigned sp + -32) with (bv_unsigned sp + -64 + 32) by lia;
            exact VA|].
    split; [rewrite mkR_sp, mkR_a2, ESP, ESP32; lia|].
    split; [rewrite mkR_a2, ESP32; change (Z.of_nat (length [a4; a5; a6; a7])) with 4; lia|].
    split; [rewrite mkR_sp, ESP; exact PA3|].
    split; [rewrite LT; unfold MemFile.MF_BUFSIZ in *; lia|].
    split; [rewrite mkR_sp, ESP; unfold VFPRINTF_K, MemFile.MF_BLOCK; lia|].
    split; [rewrite mkR_sp, ESP; unfold VFPRINTF_K, IMG_TOP, A_IMG_TOP in *; lia|].
    exact GW3. }
  { exact MI1. }
  { exact TM3. }
  { rewrite ESP. exact ST1. }
  { rewrite ESP. unfold VFPRINTF_K. lia. }
  { rewrite ESP. lia. }
  { exact FRM1. }
  { exact ITOP. }
  { exact (proj1 GW3). }
  { exact (proj2 GW3). }
  intros ra2 t02 t12 t22 a02 a12 a22 a32 a42 a52 a62 a72 t32 t42 t52 t62 Ft2 fc2 m4 FRM2 FK2 MU3 WM3 MI4 TM4 ST4 PO2.
  cbv beta in MU3, PO2. destruct PO2 as [_ (MK4 & _ & _)].
  rewrite ESP in MU3, ST4.
  rewrite ret_pc_even by (lia || reflexivity).
  pose proof (rw_cells_transport rsegs _ m3 m4 _ _ FR MU3 WM3
                ltac:(cbn [disjoint_from cells_size csize mf_block fst snd Nat.add];
                      unfold VFPRINTF_K, MemFile.MF_BLOCK in *; repeat split; lia)) as FR1.
  clear FR. rename FR1 into FR.
  assert (MUc : munch [(bv_unsigned sp - 6112, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 1304)] m m4).
  { apply (munch_trans _ m m3 m4); [exact MU|].
    eapply munch_weaken; [|exact MU3]. intros x Hx. cbn [outside mf_block fst snd] in Hx |- *.
    unfold MemFile.MF_BLOCK, VFPRINTF_K. split; [lia | split; [lia | exact I]]. }
  pose proof (wmono_trans rsegs m m3 m4 WM WM3) as WMc.
  clear MU MU2 MU3 WM WM2 WM3 MK2 MD2 MP2 MK3 MD3 MP3 TM2 TM3 MI1 ST1 GW3 FB3 PA3 VA.
  rename MUc into MU, WMc into WM.
  zstep. zstep. zstep. zstep.
  release_frame FR ST4 (bv_unsigned sp).
  zstep.
  apply evt_done. do 3 eexists. exists m4. split; [reflexivity|].
  split; [exact FRM2|].
  split; [intros r Hr; rewrite (FK2 r Hr); exact (FK1 r Hr)|].
  split; [eapply regs_preserved_mkR|].
  split; [exact MU|].
  split; [exact WM|]. split; [exact MI4|]. split; [exact TM4|]. split; [exact ST4|].
  intros fmt' ps' args' T' k' EF' MK'.
  change (arg _ 0) with (bv_unsigned a0) in MK' |- *.
  assert (Ek : k' = k) by exact (memfile_k_unique m _ k' k MK' MK Hf64).
  assert (ET' : T' = T) by exact (emit_fmt_unique _ _ _ _ _ _ _ _ _ _ _ EF' EF).
  subst k' T'. unfold EMIT_HEAD. rewrite <- LT. exact MK4.
Qed.

Lemma emit_pre_ext : pre_ext emit_pre.
Proof. intros r1 r2 m E H. unfold emit_pre, emit_fmt, arg, spZ in *. rewrite <- !E. exact H. Qed.

Lemma emit_wr_ext : wr_ext emit_wr.
Proof. intros r1 r2 m E. unfold emit_wr, arg. rewrite E. reflexivity. Qed.

Lemma emit_post_ext : post_ext emit_post.
Proof. intros r1 r2 m q1 q2 m' E1 _ H. unfold emit_post, emit_fmt, arg, spZ in *. rewrite <- !E1. exact H. Qed.

(* the callees fprintf and vfprintf (the printf lane's contracts, lib/Prog/fprintf_c.v and
   vfprintf_c.v) are hypotheses: no closed proof of either is on the branch *)
Theorem reac_code_emit_holds : fprintf_contract -> vfprintf_contract -> reac_code_emit_contract.
Proof.
  intros HFP HVF. rewrite emit_contract_eq. apply leaf_fp_intro.
  - exact emit_pre_ext.
  - exact emit_wr_ext.
  - exact emit_post_ext.
  - exact (reac_code_emit_walk HFP HVF).
Qed.
