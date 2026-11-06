(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v; 1022 of its 1119 lines of code are new or changed and 738 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths and module names changed; 183 of its 219 lines of code are new or changed and 1083 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 186 of its 232 lines of code are new or changed and 173 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma fp_kept_trans : forall fx1 fx2 fx3, CF.RecKindB.fp_kept fx1 fx2 -> CF.RecKindB.fp_kept fx2 fx3 -> CF.RecKindB.fp_kept fx1 fx3.
Proof.
  intros fx1 fx2 fx3 (_ & H1) (Z3 & H2). split; [exact Z3|]. intros r Hr. rewrite (H2 r Hr). exact (H1 r Hr).
Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation fx0 := (s_fx S).
Local Notation L0 := (s_L S).
Local Notation A0 := (s_A S).
Local Notation rg0 := (s_regs S).
Local Notation m0 := (s_mem S).
Local Notation md0 := (s_md S).
Local Notation b0 := (s_b S).
Local Notation O0 := (s_O S).
Local Notation spf := (s_spf S).
Local Notation VS f := (@vr_state f _ B API S).

Definition ans_post (K : Z) (L : layout) (A : astate) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (b : sbound) (sizes : list Z) (Rt : rstate * list byte) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' rg' mem' md' O' q,
    c' = mkCfg (@mkst fx' rg' (getr rg 1) mem' (seg_rom rsegs)) md' /\
    CF.RecKindB.fp_kept fx fx' /\
    CF.RecKindB.call_post_rec B MR K L A rg mem md CF.RecKindB.rec_area (fun a => In a (map fst O)) L' A' rg' mem' md' /\
    getr rg' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' (fst Rt) O' /\ CF.RecKindB.owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length (snd Rt)) + 1)) /\
    In (q, Z.of_nat (length (snd Rt)) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length (snd Rt)) + 1) /\
    ~ In q (map fst O') /\
    bytes_at (ms_segs B) mem' q (snd Rt ++ [Z_to_bv 8 0]) /\
    CF.RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length (snd Rt)) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (CF.RecKindB.sb_mallocs b sizes).

Lemma frame_keep : forall K rg mem1 mem' L1 A1 L' A' md1 md' (E : Z -> Prop),
  MR L1 A1 mem1 md1 -> MR L' A' mem' md' -> spZ rg = spf -> (forall a, E a -> a < alloc_ceiling) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a -> ~ owned B L' A' a ->
     ~ scratch_k B K rg a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem' a)) ->
  forall a, spf <= a < spf + 608 ->
    mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a).
Proof using HF HS.
  intros K rg mem1 mem' L1 A1 L' A' md1 md' E HM1 HM' SPR HE HFR a Ha.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (aa_laws API) as LAWS. rewrite <- SEGS.
  apply HFR.
  - left. unfold s_spf, VR_K in *. lia.
  - intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ a HM1 Ho). unfold s_spf, VR_K in *. lia.
  - intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ a HM' Ho). unfold s_spf, VR_K in *. lia.
  - unfold scratch_k. rewrite SPR, ERR. unfold s_spf, VR_K in *. lia.
  - intros He. pose proof (HE a He). unfold s_spf, VR_K in *. lia.
Qed.

Lemma gq_keep : forall K rg mem1 mem' L1 A1 L' A' md1 md' (E : Z -> Prop),
  MR L1 A1 mem1 md1 -> MR L' A' mem' md' -> spZ rg = spf -> 0 <= K <= 14336 -> (forall i, 0 <= i < 4 -> ~ E (G_QUIT + i)) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L1 A1 a -> ~ owned B L' A' a ->
     ~ scratch_k B K rg a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem1 a /\
     (writable_at (ms_segs B) mem1 a <-> writable_at (ms_segs B) mem' a)) ->
  forall i, 0 <= i < 4 ->
    mbyte rsegs mem' (G_QUIT + i) = mbyte rsegs mem1 (G_QUIT + i) /\
    (writable_at rsegs mem1 (G_QUIT + i) <-> writable_at rsegs mem' (G_QUIT + i)).
Proof using HF HS.
  intros K rg mem1 mem' L1 A1 L' A' md1 md' E HM1 HM' SPR HK HE HFR i Hi.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  rewrite <- SEGS. pose proof (gq_glob i Hi) as HG.
  apply HFR.
  - right. exact (proj1 (vf_globs B API HF _ HG)).
  - exact (vf_globo B API HF L1 A1 mem1 md1 _ HM1 HG).
  - exact (vf_globo B API HF L' A' mem' md' _ HM' HG).
  - unfold scratch_k. rewrite SPR, ERR. unfold G_QUIT, s_spf, VR_K in *. lia.
  - exact (HE i Hi).
Qed.

Lemma length_concat_le8 : forall ps : list word, length (concat (map le8 ps)) = (8 * length ps)%nat.
Proof. induction ps as [|p ps IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, length_le8, IH. lia. Qed.

Lemma vfr_keep : forall mem1 mem' jk,
  (forall a, spf <= a < spf + 608 ->
     mbyte rsegs mem' a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem' a)) ->
  vfr S mem1 jk -> vfr S mem' jk.
Proof using HS.
  intros mem1 mem' jk KP (F1 & (junk & F2) & F3).
  split; [|split; [exists junk|]].
  - apply (rw_cells_transfer rsegs mem1); [exact F1|]. intros i Hi. cbn in Hi.
    destruct (KP (spf + 520 + i) ltac:(lia)) as [E W]. split; [exact E | apply W].
  - apply (rw_cells_transfer rsegs mem1); [exact F2|]. intros i Hi. cbn in Hi.
    destruct (KP (spf + i) ltac:(lia)) as [E W]. split; [exact E | apply W].
  - apply (bytes_at_transfer rsegs mem1); [exact F3|]. intros i Hi.
    destruct F2 as [_ (Ha & Hn & _)]. cbn in Hn.
    assert (L : Z.of_nat (length (concat (map le8 (s_ps S)))) <= 512).
    { rewrite length_concat_le8. pose proof (ok_psl B API S HS). lia. }
    exact (proj1 (KP (spf + 8 + i) ltac:(lia))).
Qed.

Lemma vregs_pres : forall rg rg', vregs S rg -> regs_preserved rg rg' -> vregs S rg'.
Proof.
  intros rg rg' (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27) HP.
  assert (P : forall r, callee_saved r -> getr rg' (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r)) by exact HP.
  split; [exact (eq_trans (P 2 ltac:(unfold callee_saved; lia)) V2)|].
  split; [exact (eq_trans (P 3 ltac:(unfold callee_saved; lia)) V3)|].
  split; [exact (eq_trans (P 4 ltac:(unfold callee_saved; lia)) V4)|].
  split; [exact (eq_trans (P 8 ltac:(unfold callee_saved; lia)) V8)|].
  split; [exact (eq_trans (P 9 ltac:(unfold callee_saved; lia)) V9)|].
  split; [exact (eq_trans (P 25 ltac:(unfold callee_saved; lia)) V25)|].
  split; [exact (eq_trans (P 26 ltac:(unfold callee_saved; lia)) V26)|].
  exact (eq_trans (P 27 ltac:(unfold callee_saved; lia)) V27).
Qed.

Lemma vregs_sp : forall rg, vregs S rg -> spZ rg = spf.
Proof using HS.
  intros rg (V2 & _). pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val.
  unfold spZ. rewrite V2. apply unsigned_lit. unfold s_spf, VR_K in *. lia.
Qed.

Lemma rec_area_low : forall a, CF.RecKindB.rec_area a -> a < alloc_ceiling.
Proof. intros a Ha. pose proof alloc_ceiling_val. unfold CF.RecKindB.rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Ha. lia. Qed.

Lemma rec_area_gq : forall i, 0 <= i < 4 -> ~ CF.RecKindB.rec_area (G_QUIT + i).
Proof. intros i Hi Ha. unfold CF.RecKindB.rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_QUIT in Ha. lia. Qed.

Lemma gq_transfer : forall mem1 mem' qv,
  (forall i, 0 <= i < 4 ->
    mbyte rsegs mem' (G_QUIT + i) = mbyte rsegs mem1 (G_QUIT + i) /\
    (writable_at rsegs mem1 (G_QUIT + i) <-> writable_at rsegs mem' (G_QUIT + i))) ->
  bytes_at rsegs mem1 G_QUIT (le4 (Z_to_bv 64 qv)) -> (forall i, 0 <= i < 4 -> writable_at rsegs mem1 (G_QUIT + i)) ->
  bytes_at rsegs mem' G_QUIT (le4 (Z_to_bv 64 qv)) /\ (forall i, 0 <= i < 4 -> writable_at rsegs mem' (G_QUIT + i)).
Proof.
  intros mem1 mem' qv K Hb Hw. split.
  - apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi. rewrite length_le4 in Hi. exact (proj1 (K i Hi)).
  - intros i Hi. apply (proj2 (K i Hi)). exact (Hw i Hi).
Qed.

Lemma call_ans : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv jk c K ret sizes (Rt : rstate * list byte) P,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  getr rg 1 = Z_to_bv 64 ret -> 0 <= K <= 14336 ->
  (k1 + length sizes <= 32)%nat -> Forall (fun n => 0 <= n <= 8194) sizes ->
  SR rsegs c (ans_post K L1 A1 rg mem1 md1 O1 (sb_n b0 k1) sizes Rt) ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' q c',
     VS fx' rg' ret mem' md' L' A' (fst Rt) O' (k1 + length sizes) qv
       (Some (q, Z.of_nat (length (snd Rt)) + 1, snd Rt)) jk c' ->
     getr rg' 10 = Z_to_bv 64 q -> regs_preserved rg rg' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv jk c K ret sizes Rt P HST E1 HK HKS HSZ HSR KONT.
  pose proof (vf_segs B API HF) as SEGS.
  eapply SR_bind; [exact HSR|].
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & q & -> & FPK & POST & A0' & REC & OWN & BLK & INB & FRESH & NOQ
    & BQ & OK & APART & RO & INIT & RLEN & RES).
  pose proof HST as (_ & FPK0 & VR & H & FR & GQ & GW).
  pose proof POST as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _).
  pose proof (vregs_sp rg VR) as SPR.
  pose proof (frame_keep K rg mem1 mem' L1 A1 L' A' md1 md' CF.RecKindB.rec_area HM1 HM' SPR rec_area_low HFR) as KP.
  pose proof (gq_keep K rg mem1 mem' L1 A1 L' A' md1 md' CF.RecKindB.rec_area HM1 HM' SPR HK rec_area_gq HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  apply (KONT fx' rg' mem' md' L' A' O' q); [| exact A0' | exact HPR].
  split; [rewrite E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres rg rg' VR HPR)|].
  split.
  { apply (heap_step_stub B API HF S HS rg mem1 md1 L1 A1 R1 O1 k1 None K L' A' rg' mem' md' (fst Rt) O'
      [(q, Z.of_nat (length (snd Rt)) + 1)] (Some (q, Z.of_nat (length (snd Rt)) + 1, snd Rt)) (k1 + length sizes)
      H SPR HK POST REC OWN).
    - intros pn Hin. destruct (BLK pn Hin) as [X|[X|X]]; [left; exact X | right; left; exact X | right; right; left; symmetry; exact X].
    - exact OK.
    - exact RO.
    - exact INIT.
    - exact RLEN.
    - exact (st_res B API S HS A' k1 sizes HKS HSZ RES).
    - exact HKS.
    - reflexivity.
    - intros pn [<-|[]]. split; [exact INB|]. split; [exact NOQ|]. split; [cbn [snd]; lia|].
      intros pn' Hin' Hno'.
      assert (AP : forall p k, In (p, k) (user_blocks A1) -> ~ In (ptr_addr L1 p, k) O1 ->
                     ptr_addr L1 p + k <= q \/ q + (Z.of_nat (length (snd Rt)) + 1) <= ptr_addr L1 p)
        by (intros p k X1 X2; destruct (APART p k X1 X2); lia).
      destruct (user_apart L1 A1 O1 q _ AP pn' Hin' Hno'); cbn [fst snd]; lia.
    - constructor; [intros []|constructor].
    - rewrite SEGS in BQ. split; [exact BQ | lia]. }
  split; [exact (vfr_keep mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

Lemma vs_pre : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> 0 <= K <= 14336 ->
  call_pre_t B API K L1 A1 rg mem1 md1 /\ spZ rg = spf /\ frm_zero (@fp_csr fx) /\
  CF.RecKindB.f18_words (ms_segs B) mem1 /\ ro_agree (ms_segs B) mem1 /\ g_rec_rep (ms_segs B) L1 A1 mem1 R1 O1 /\
  MR L1 A1 mem1 md1 /\
  Mem.bytes_at (ms_segs B) mem1 rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret HST E1 RET HK.
  destruct (st_pre B API HF S HS rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret HST E1 RET HK) as (PRE & TS & SPR).
  pose proof HST as (_ & (FZ & _) & VR & H & FR & GQ & GW).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  split; [exact (conj PRE TS)|]. split; [exact SPR|]. split; [exact FZ|].
  split; [exact (proj1 (st_f18 B API HF _ _ _ _ HM1))|].
  split; [exact (h_ro B API S _ _ _ _ _ _ _ _ H)|].
  split; [exact (h_rec B API S _ _ _ _ _ _ _ _ H)|].
  split; [exact HM1|].
  pose proof (ok_shp B API S HS) as SH.
  apply (bytes_at_transfer _ (s_mem S)); [exact SH|]. intros i Hi.
  apply (st_relro B API HF S HS _ _ _ _ _ REL). exists 0x226b0, 1680. split; [left; reflexivity|].
  rewrite rec_shape_of.g_shapes_length in Hi. unfold rec_shape_of_c.G_SHAPES. lia.
Qed.

End C.
