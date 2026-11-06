(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module names changed; 495 of its 534 lines of code are new or changed and 176 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since verbs_receive_rel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply verbs_receive_route.
Import ListNotations.
Local Open Scope Z_scope.

Section F.
Context {rc : YM05.RunCeil}.

Record vframe (B : malloc_syms) (API : AllocAPI B) : Prop := {
  vf_segs : ms_segs B = rsegs;
  vf_errno : errno_addr B = 0x3441c;
  vf_guard : ms_guard B = 0x54730;
  vf_gotg : ms_got_guard B = 0x22d40;
  vf_free : ms_free B = 0x18ad0;
  vf_globs : forall a, in_globals FrameAPI.frame_G a -> in_img B a /\ ~ static_owned B a /\
    ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4);
  vf_globo : forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_G a -> ~ owned B L A a;
  vf_relro : forall L A mem md a, aa_MR API L A mem md -> in_globals FrameAPI.frame_RELRO a ->
    in_img B a /\ ~ owned B L A a;
  vf_ax : AllocExtra B (aa_MR API);
  vf_ctxo : ctx_owned B API;
  vf_bslack : block_slack_present B API;
  vf_bwr : blocks_writable B API }.

Record vstart := VS {
  s_fx : YK11.FPState;
  s_L : layout; s_A : astate; s_regs : bvmap 5 word; s_mem : word -> option byte; s_md : Model; s_b : sbound;
  s_R : rstate; s_O : list (Z * Z); s_msg : Z; s_fd : Z; s_data : Z; s_n : Z; s_q0 : Z; s_D : list byte;
  s_can : word; s_lb : Z; s_cb : Z; s_ps : list word }.

Definition s_nlb (S : vstart) : Z := Z.of_nat (length (upto0 (s_D S))) + 1.
Definition s_ncb (S : vstart) : Z := Z.of_nat (length (line (s_D S))) + 1.
Definition s_sp (S : vstart) : Z := spZ (s_regs S).
Definition s_spf (S : vstart) : Z := spZ (s_regs S) - 608.

Record vok (B : malloc_syms) (API : AllocAPI B) (S : vstart) : Prop := {
  ok_pre : call_pre_k B (aa_MR API) VR_K (s_L S) (s_A S) (s_regs S) (s_mem S) (s_md S);
  ok_ts : spZ (s_regs S) <= TASK_SIZE;
  ok_ro : ro_agree (ms_segs B) (s_mem S);
  ok_fz : @frm_zero (@fp_csr (s_fx S));
  ok_a0 : getr (s_regs S) 10 = Z_to_bv 64 (s_msg S);
  ok_m8 : s_msg S mod 8 = 0;
  ok_m4k : 4096 <= s_msg S;
  ok_m63 : s_msg S + 24 <= 2 ^ 63;
  ok_spm : bv_unsigned (getr (s_regs S) 2) <= s_msg S;
  ok_eimg : in_img B (errno_addr B);
  ok_fd : le_at B (s_mem S) (s_msg S) (Mem.le4 (Z_to_bv 64 (s_fd S)));
  ok_mdat : le_at B (s_mem S) (s_msg S + 8) (Mem.le8 (Z_to_bv 64 (s_data S)));
  ok_mn : le_at B (s_mem S) (s_msg S + 16) (Mem.le8 (Z_to_bv 64 (s_n S)));
  ok_mout : outside B (s_L S) (s_A S) VR_K (s_regs S) (s_msg S) 24;
  ok_mnw : forall i, 0 <= i < 24 -> ~ vr_writes (s_msg S + i);
  ok_db : In (s_data S, Z.max (s_n S) 1) (blocks (s_L S) (s_A S));
  ok_dno : ~ In (s_data S, Z.max (s_n S) 1) (s_O S);
  ok_D : le_at B (s_mem S) (s_data S) (s_D S);
  ok_nD : Z.of_nat (length (s_D S)) = s_n S;
  ok_n8 : s_n S <= 8192;
  ok_rec : g_rec_rep (ms_segs B) (s_L S) (s_A S) (s_mem S) (s_R S) (s_O S);
  ok_calls : r_calls (s_R S) = [];
  ok_ans : r_answer (s_R S) = None;
  ok_rep : r_reply (s_R S) = None;
  ok_nrep : r_nreplies (s_R S) = 0;
  ok_decl : r_refuse (s_R S) <> 0 -> declared (r_code (s_R S)) = true;
  ok_q : le_at B (s_mem S) G_QUIT (Mem.le4 (Z_to_bv 64 (s_q0 S)));
  ok_qw : forall i, 0 <= i < 4 -> writable_at (ms_segs B) (s_mem S) (G_QUIT + i);
  ok_qout : outside B (s_L S) (s_A S) VR_K (s_regs S) G_QUIT 4;
  ok_tab : vr_tables B (s_mem S) (s_can S);
  ok_shp : Mem.bytes_at (ms_segs B) (s_mem S) rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes;
  ok_res : res_ok_slots (s_A S) (s_b S);
  ok_room : room_slots (SB (sb_live (s_b S) + 32) (sb_bytes (s_b S) + 262208) (sb_cap (s_b S))) VR_REQ;
  ok_lbf : fresh_block B (s_lb S) (s_nlb S);
  ok_cbf : fresh_block B (s_cb S) (s_ncb S);
  ok_lbap : forall pn, In pn (blocks (s_L S) (s_A S)) -> fst pn + snd pn <= s_lb S \/ s_lb S + s_nlb S <= fst pn;
  ok_cbap : forall pn, In pn (blocks (s_L S) (s_A S)) -> fst pn + snd pn <= s_cb S \/ s_cb S + s_ncb S <= fst pn;
  ok_lbcb : s_lb S + s_nlb S <= s_cb S \/ s_cb S + s_ncb S <= s_lb S;
  ok_psl : (length (s_ps S) <= 64)%nat }.

End F.

Lemma Forall2_nth : forall {X Y : Type} (P : X -> Y -> Prop) l1 l2 i x y,
  Forall2 P l1 l2 -> nth_error l1 i = Some x -> nth_error l2 i = Some y -> P x y.
Proof.
  intros X Y P l1 l2 i. revert l1 l2. induction i as [|i IH]; intros l1 l2 x y HF E1 E2;
    destruct HF as [|a b l1' l2' Hab HF']; try discriminate; cbn in E1, E2.
  - injection E1 as <-. injection E2 as <-. exact Hab.
  - exact (IH _ _ _ _ HF' E1 E2).
Qed.

Lemma sb_mallocs_fields : forall ns b,
  sb_live (RecKindB.sb_mallocs b ns) = sb_live b + Z.of_nat (length ns) /\
  sb_bytes (RecKindB.sb_mallocs b ns) = sb_bytes b + fold_right Z.add 0 ns /\
  sb_cap (RecKindB.sb_mallocs b ns) = sb_cap b.
Proof.
  induction ns as [|x ns IH]; intros b; cbn [RecKindB.sb_mallocs fold_left length fold_right]; [lia|].
  unfold RecKindB.sb_mallocs in IH. destruct (IH (sb_malloc b x)) as (E1 & E2 & E3).
  unfold RecKindB.sb_mallocs. rewrite E1, E2, E3. unfold sb_malloc. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Lemma sum_bound : forall ns, Forall (fun n => 0 <= n <= 8194) ns ->
  0 <= fold_right Z.add 0 ns <= 8194 * Z.of_nat (length ns).
Proof.
  induction ns as [|x ns IH]; intros H; cbn [fold_right length]; [lia|].
  inversion H as [|y l Hx Hl]; subst. specialize (IH Hl). lia.
Qed.

Lemma repeat_snoc0 : forall k, repeat (Z_to_bv 8 0) k ++ [Z_to_bv 8 0] = Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) k.
Proof. induction k as [|k IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Section St.
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
Local Notation R0 := (s_R S).
Local Notation O0 := (s_O S).
Local Notation D := (s_D S).
Local Notation lb := (s_lb S).
Local Notation cb := (s_cb S).
Local Notation ps := (s_ps S).
Local Notation nlb := (s_nlb S).
Local Notation ncb := (s_ncb S).
Local Notation spf := (s_spf S).

Definition xbl (xq : option (Z * Z * list byte)) : list (Z * Z) :=
  (lb, nlb) :: (cb, ncb) :: match xq with Some (q, nq, _) => [(q, nq)] | None => [] end.

Record vtail (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) (R1 : rstate)
    (O1 : list (Z * Z)) (k1 : nat) (X : list (Z * Z)) : Prop := {
  t_rel : vr_rel B API O0 L0 A0 rg0 m0 md0 L1 A1 mem1 md1;
  t_rec : g_rec_rep (ms_segs B) L1 A1 mem1 R1 O1;
  t_ro : ro_agree (ms_segs B) mem1;
  t_init : st_init_done A1 = true;
  t_res : res_ok_slots A1 (sb_n b0 k1) /\ (k1 <= 32)%nat;
  t_old : forall pn, In pn (blocks L0 A0) -> ~ In pn O0 -> In pn (blocks L1 A1) /\ ~ In pn O1;
  t_sub : forall pn, In pn (blocks L1 A1) -> (In pn (blocks L0 A0) /\ ~ In pn O0) \/ In pn O1 \/ In pn X;
  t_x : forall pn, In pn X -> In pn (blocks L1 A1) /\ ~ In (fst pn) (map fst O1);
  t_xap : forall pn, In pn X -> forall pn', In pn' (blocks L0 A0) -> ~ In pn' O0 ->
    fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn;
  t_xnd : List.NoDup (map fst X);
  t_xsz : forall pn, In pn X -> 1 <= snd pn }.

Record vheap (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) (R1 : rstate)
    (O1 : list (Z * Z)) (k1 : nat) (xq : option (Z * Z * list byte)) : Prop := {
  h_t : vtail L1 A1 mem1 md1 R1 O1 k1 (xbl xq);
  h_lb : bytes_at rsegs mem1 lb (line D ++ repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D)) ++ [Z_to_bv 8 0]);
  h_tok : Forall2 (fun p w => VerbsMem.cstr0_at mem1 (bv_unsigned p) w /\ cb <= bv_unsigned p /\
                              bv_unsigned p + Z.of_nat (length w) + 1 <= cb + ncb) ps (toks D);
  h_q : match xq with
        | Some (q, nq, t) => bytes_at rsegs mem1 q (t ++ [Z_to_bv 8 0]) /\ Z.of_nat (length t) + 1 <= nq
        | None => True
        end }.

Section Proj.
Variables (L1 : layout) (A1 : astate) (mem1 : word -> option byte) (md1 : Model) (R1 : rstate)
  (O1 : list (Z * Z)) (k1 : nat) (xq : option (Z * Z * list byte)).
Lemma h_rel : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> vr_rel B API O0 L0 A0 rg0 m0 md0 L1 A1 mem1 md1.
Proof. intros H. exact (t_rel _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_rec : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> g_rec_rep (ms_segs B) L1 A1 mem1 R1 O1.
Proof. intros H. exact (t_rec _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_ro : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> ro_agree (ms_segs B) mem1.
Proof. intros H. exact (t_ro _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_init : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> st_init_done A1 = true.
Proof. intros H. exact (t_init _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_res : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> res_ok_slots A1 (sb_n b0 k1) /\ (k1 <= 32)%nat.
Proof. intros H. exact (t_res _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_old : vheap L1 A1 mem1 md1 R1 O1 k1 xq ->
  forall pn, In pn (blocks L0 A0) -> ~ In pn O0 -> In pn (blocks L1 A1) /\ ~ In pn O1.
Proof. intros H. exact (t_old _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_sub : vheap L1 A1 mem1 md1 R1 O1 k1 xq ->
  forall pn, In pn (blocks L1 A1) -> (In pn (blocks L0 A0) /\ ~ In pn O0) \/ In pn O1 \/ In pn (xbl xq).
Proof. intros H. exact (t_sub _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_x : vheap L1 A1 mem1 md1 R1 O1 k1 xq ->
  forall pn, In pn (xbl xq) -> In pn (blocks L1 A1) /\ ~ In (fst pn) (map fst O1).
Proof. intros H. exact (t_x _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_xap : vheap L1 A1 mem1 md1 R1 O1 k1 xq ->
  forall pn, In pn (xbl xq) -> forall pn', In pn' (blocks L0 A0) -> ~ In pn' O0 ->
    fst pn + snd pn <= fst pn' \/ fst pn' + snd pn' <= fst pn.
Proof. intros H. exact (t_xap _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_xnd : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> List.NoDup (map fst (xbl xq)).
Proof. intros H. exact (t_xnd _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
Lemma h_xsz : vheap L1 A1 mem1 md1 R1 O1 k1 xq -> forall pn, In pn (xbl xq) -> 1 <= snd pn.
Proof. intros H. exact (t_xsz _ _ _ _ _ _ _ _ (h_t _ _ _ _ _ _ _ _ H)). Qed.
End Proj.

Definition vregs (rg : bvmap 5 word) : Prop :=
  getr rg 2 = Z_to_bv 64 spf /\ getr rg 3 = getr rg0 3 /\ getr rg 4 = getr rg0 4 /\
  getr rg 8 = Z_to_bv 64 lb /\ getr rg 9 = Z_to_bv 64 cb /\
  getr rg 25 = getr rg0 25 /\ getr rg 26 = getr rg0 26 /\ getr rg 27 = getr rg0 27.

Definition vsaved : list cell :=
  [C8 (getr rg0 24); C8 (getr rg0 23); C8 (getr rg0 22); C8 (getr rg0 21); C8 (getr rg0 20);
   C8 (getr rg0 19); C8 (getr rg0 18); C8 (getr rg0 9); C8 (getr rg0 8); C8 (getr rg0 1)].

Definition vfr (mem1 : word -> option byte) (jk : list byte) : Prop :=
  rw_cells rsegs mem1 (spf + 520) (CB 8 jk :: vsaved) /\
  (exists junk, rw_cells rsegs mem1 spf [CB 520 junk]) /\
  bytes_at rsegs mem1 (spf + 8) (concat (map le8 ps)).

Definition vr_state (rg : bvmap 5 word) (pc : Z) (mem1 : word -> option byte) (md1 : Model) (L1 : layout)
    (A1 : astate) (R1 : rstate) (O1 : list (Z * Z)) (k1 : nat) (qv : Z) (xq : option (Z * Z * list byte))
    (jk : list byte) (c : config) : Prop :=
  c = mkCfg (mkst rg (Z_to_bv 64 pc) mem1 (seg_rom rsegs)) md1 /\
  RecKindB.fp_kept fx0 fx /\ vregs rg /\ vheap L1 A1 mem1 md1 R1 O1 k1 xq /\ vfr mem1 jk /\
  bytes_at rsegs mem1 G_QUIT (le4 (Z_to_bv 64 qv)) /\ (forall i, 0 <= i < 4 -> writable_at rsegs mem1 (G_QUIT + i)).

Lemma sp_facts : alloc_ceiling + VR_K <= spZ rg0 /\ spZ rg0 < 2 ^ 63 /\ spZ rg0 mod 16 = 0 /\
  spf = spZ rg0 - 608.
Proof using HS.
  pose proof (ok_pre B API S HS) as (_ & _ & _ & _ & HAL & HC & H63 & _). unfold s_spf. lia.
Qed.

Lemma gq_glob : forall i, 0 <= i < 4 -> in_globals FrameAPI.frame_G (G_QUIT + i).
Proof. intros i Hi. exists 0x33ff0, 1020. split; [left; reflexivity|]. unfold G_QUIT. lia. Qed.

Lemma rec_glob : forall a, G_REC <= a < G_REC + REC_SIZE \/ REC_SC <= a < REC_SC + SC_SIZE ->
  in_globals FrameAPI.frame_G a.
Proof.
  intros a Ha. exists 0x33ff0, 1020. split; [left; reflexivity|].
  unfold G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha. lia.
Qed.

Lemma blk_low : forall L1 A1 mem1 md1 a k i, MR L1 A1 mem1 md1 -> In (a, k) (blocks L1 A1) -> 0 <= i < k ->
  4096 <= a /\ a + k <= alloc_ceiling /\ ~ in_img B (a + i) /\ present mem1 (a + i).
Proof using HF.
  intros L1 A1 mem1 md1 a k i HM Hin Hi. pose proof (aa_laws API) as LAWS.
  destruct (block_facts B _ LAWS _ _ _ _ _ _ i HM Hin Hi) as (Hp & H4 & Hc & _).
  split; [exact H4|]. split; [exact Hc|]. split; [|exact Hp].
  unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hpk). cbn in E. injection E as <- <-.
  exact (ax_blocks_img (vf_ax B API HF) L1 A1 mem1 md1 p k' i HM Hpk Hi).
Qed.

Lemma line_le_upto : (length (line D) <= length (upto0 D))%nat.
Proof.
  unfold line, trim. rewrite length_rev. pose proof (verbs_receive_route.dropw_len is_trail (rev (upto0 D))) as H.
  rewrite length_rev in H. exact H.
Qed.

Lemma tail_mem : forall L1 A1 mem1 md1 R1 O1 k1 X mem2,
  vtail L1 A1 mem1 md1 R1 O1 k1 X ->
  MR L1 A1 mem2 md1 -> ro_agree (ms_segs B) mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= a < spZ rg0) -> ~ (G_QUIT <= a < G_QUIT + 4) ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  (forall a, spZ rg0 - VR_K <= a < spZ rg0 -> writable_at rsegs mem1 a -> writable_at rsegs mem2 a) ->
  vtail L1 A1 mem2 md1 R1 O1 k1 X /\
  (forall a k s bs, In (a, k) (blocks L1 A1) -> a <= s -> s + Z.of_nat (length bs) <= a + k ->
     bytes_at rsegs mem1 s bs -> bytes_at rsegs mem2 s bs).
Proof using HF HS.
  intros L1 A1 mem1 md1 R1 O1 k1 X mem2 H HM2 RO2 OUT SW.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof sp_facts as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (aa_laws API) as LAWS.
  pose proof (t_rel _ _ _ _ _ _ _ _ H) as REL.
  pose proof REL as (HM1 & _).
  assert (GQI : forall i, 0 <= i < 4 -> in_img B (G_QUIT + i)) by (intros i Hi; exact (proj1 (vf_globs B API HF _ (gq_glob i Hi)))).
  assert (KH : forall a k i, In (a, k) (blocks L1 A1) -> 0 <= i < k ->
             mbyte rsegs mem2 (a + i) = mbyte rsegs mem1 (a + i)).
  { intros a k i Hin Hi. destruct (blk_low _ _ _ _ a k i HM1 Hin Hi) as (H4 & Hc & Hni & _).
    apply OUT; [lia | lia |]. intros Hq. apply Hni.
    replace (a + i) with (G_QUIT + (a + i - G_QUIT)) by ring. apply GQI. lia. }
  split.
  2:{ intros a k s bs Hin H1 H2 Hb. apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi.
      replace (s + i) with (a + (s - a + i)) by ring. apply (KH a k); [exact Hin | lia]. }
  constructor.
  - eapply (rel_mem B API); [exact REL | exact HM2 | | | ].
    + intros a Dm N1 Ns Nw. rewrite SEGS.
      assert (Ra : 0 <= a < 2 ^ 64).
      { destruct Dm as [Dm|Dm]; [lia|]. pose proof (in_img_low B SEGS a Dm). lia. }
      apply OUT; [exact Ra | |].
      * intros Hw. apply Ns. left. exact Hw.
      * intros Hq. apply Nw. unfold vr_writes. right. right. exact Hq.
    + intros a k i Hin Hx Hi.
      assert (Hno : ~ In (a, k) O0) by (intros Ho; apply Hx; apply in_map_iff; exists (a, k); split; [reflexivity | exact Ho]).
      destruct (t_old _ _ _ _ _ _ _ _ H (a, k) Hin Hno) as [Hin1 _].
      rewrite SEGS. exact (KH a k i Hin1 Hi).
    + intros a Ha W. rewrite SEGS in *. destruct Ha as [Ha|Ha]; [exact (SW a Ha W)|].
      rewrite ERR in Ha. apply (OUT a); [lia | lia | unfold G_QUIT; lia | exact W].
  - apply (rec_rep_frame (ms_segs B) G_REC REC_SC L1 A1 mem1 R1 O1 L1 A1 mem2 (t_rec _ _ _ _ _ _ _ _ H)).
    + intros a Ha. destruct (vf_globs B API HF a (rec_glob a Ha)) as (Hi & _).
      pose proof (in_img_low B SEGS a Hi) as Hlo. rewrite SEGS.
      destruct (OUT a) as [E W]; [lia | lia | unfold G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in *; lia |].
      split; [exact E | apply W].
    + intros p n i Hin Hi. destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec _ _ _ _ _ _ _ _ H) (p, n) Hin) as [Hb _].
      rewrite SEGS. exact (KH p n i Hb Hi).
    + intros pn Hin. exact (proj1 (reply.rec_rep_O _ _ _ _ _ _ _ _ (t_rec _ _ _ _ _ _ _ _ H) pn Hin)).
  - exact RO2.
  - exact (t_init _ _ _ _ _ _ _ _ H).
  - exact (t_res _ _ _ _ _ _ _ _ H).
  - exact (t_old _ _ _ _ _ _ _ _ H).
  - exact (t_sub _ _ _ _ _ _ _ _ H).
  - exact (t_x _ _ _ _ _ _ _ _ H).
  - exact (t_xap _ _ _ _ _ _ _ _ H).
  - exact (t_xnd _ _ _ _ _ _ _ _ H).
  - exact (t_xsz _ _ _ _ _ _ _ _ H).
Qed.

Lemma heap_mem : forall L1 A1 mem1 md1 R1 O1 k1 xq mem2,
  vheap L1 A1 mem1 md1 R1 O1 k1 xq ->
  MR L1 A1 mem2 md1 -> ro_agree (ms_segs B) mem2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= a < spZ rg0) -> ~ (G_QUIT <= a < G_QUIT + 4) ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  (forall a, spZ rg0 - VR_K <= a < spZ rg0 -> writable_at rsegs mem1 a -> writable_at rsegs mem2 a) ->
  vheap L1 A1 mem2 md1 R1 O1 k1 xq.
Proof using HF HS.
  intros L1 A1 mem1 md1 R1 O1 k1 xq mem2 H HM2 RO2 OUT SW.
  destruct (tail_mem L1 A1 mem1 md1 R1 O1 k1 (xbl xq) mem2 (h_t _ _ _ _ _ _ _ _ H) HM2 RO2 OUT SW) as [T KB].
  pose proof (h_x _ _ _ _ _ _ _ _ H) as HX.
  constructor.
  - exact T.
  - apply (KB lb nlb); [exact (proj1 (HX (lb, nlb) (or_introl eq_refl))) | lia | | exact (h_lb _ _ _ _ _ _ _ _ H)].
    rewrite !length_app, repeat_length. cbn [length]. pose proof line_le_upto. unfold s_nlb. lia.
  - eapply Forall2_impl; [|exact (h_tok _ _ _ _ _ _ _ _ H)]. intros p w ((Hb & Hnz) & H1 & H2).
    split; [split; [|exact Hnz]|split; assumption].
    apply (KB cb ncb); [exact (proj1 (HX (cb, ncb) (or_intror (or_introl eq_refl)))) | exact H1 | | exact Hb].
    rewrite length_app. cbn [length]. lia.
  - pose proof (h_q _ _ _ _ _ _ _ _ H) as HQ. destruct xq as [[[q nq] t]|]; [|exact I].
    destruct HQ as [Hb Hl]. split; [|exact Hl].
    apply (KB q nq); [exact (proj1 (HX (q, nq) (or_intror (or_intror (or_introl eq_refl))))) | lia | | exact Hb].
    rewrite length_app. cbn [length]. lia.
Qed.

Lemma ka_bridge : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  vr_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ rg0 - VR_K <= x < spZ rg0) -> ~ (G_QUIT <= x < G_QUIT + 4) ->
     Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' mem2 rg', QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     mem_rel rsegs mem2 m' -> munch W mem1 mem2 -> wmono rsegs mem1 mem2 ->
     vheap L1 A1 mem2 md1 R1 O1 k1 xq ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P (-> & FPK & VR & H & FR & GQ & GW) WO EVT K.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof sp_facts as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  pose proof (h_rel _ _ _ _ _ _ _ _ H) as REL. pose proof REL as (HM1 & _).
  pose proof (h_ro _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (aa_laws API) as LAWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HM1) as (Hh & Hl & Hmat).
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO1 | exact EVT]. }
  intros ms5 (can5 & (s5 & (Q5 & R' & pc' & m' & E5 & MU' & WM') & REL5 & ROS5) & EQ5).
  subst s5.
  destruct (ms_rel_MS _ _ _ _ _ _ _ _ _ REL5) as [CAN5 HR5].
  remember (ms_mem can5) as mem2 eqn:Em2. subst can5. clear Em2.
  assert (RN1 : mem_rel rsegs mem1 (normalize rsegs mem1)) by (apply mem_rel_normalize; exact RO1).
  pose proof (munch_rel rsegs _ _ _ _ _ RN1 HR5 ROS5 MU') as MU.
  pose proof (wmono_rel rsegs _ _ _ _ RN1 HR5 ROS5 WM') as WM.
  pose proof (ro_agree_same rsegs _ _ RO1 ROS5) as RO2.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ5 eq_refl eq_refl) as (rg' & -> & X5).
  apply (K R' pc' m' mem2 rg' Q5 X5 HR5 MU WM).
  assert (NOQ : forall a, owned B L1 A1 a -> ~ (G_QUIT <= a < G_QUIT + 4)).
  { intros a Ho Hq. apply (vf_globo B API HF L1 A1 mem1 md1 a HM1); [|exact Ho].
    replace a with (G_QUIT + (a - G_QUIT)) by ring. apply gq_glob. lia. }
  apply (heap_mem L1 A1 mem1 md1 R1 O1 k1 xq mem2 H).
  - eapply (mr_frame B _ LAWS L1 A1 mem1 mem2 md1 md1 HM1).
    + intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
      rewrite SEGS. eapply munch_mbyte; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho)]].
    + intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HM1 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU | lia | apply WO; [lia | lia | exact (NOQ a Ho)] | exact Hp].
    + intros p k i Hin Hi. destruct (mr_blocks B _ LAWS L1 A1 mem1 md1 p k i HM1 Hin Hi) as (Hp & H4 & Hc & Hno).
      assert (Hni : ~ in_img B (ptr_addr L1 p + i)) by exact (ax_blocks_img (vf_ax B API HF) L1 A1 mem1 md1 p k i HM1 Hin Hi).
      eapply munch_present; [exact MU | lia | apply WO; [lia | lia | ] | exact Hp].
      intros Hq. apply Hni. replace (ptr_addr L1 p + i) with (G_QUIT + (ptr_addr L1 p + i - G_QUIT)) by ring.
      exact (proj1 (vf_globs B API HF _ (gq_glob (ptr_addr L1 p + i - G_QUIT) ltac:(lia)))).
    + reflexivity.
    + exact Hh.
    + exact Hl.
    + exact Hmat.
  - rewrite SEGS. exact RO2.
  - intros a Ra Hs Hq. split; [eapply munch_mbyte | eapply munch_writable]; (exact MU || exact Ra || (apply WO; assumption)).
  - intros a _ W1. apply WM. exact W1.
Qed.

Lemma st_pre : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret,
  vr_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) -> 0 <= K <= 14336 ->
  call_pre_k B MR K L1 A1 rg mem1 md1 /\ spZ rg <= TASK_SIZE /\ spZ rg = spf.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret (-> & FPK & VR & H & FR & GQ & GW) E1 RET HK.
  pose proof sp_facts as (SPC & SP63 & SP16 & _). pose proof alloc_ceiling_val as ACV.
  pose proof (ok_ts B API S HS) as TS.
  pose proof (ok_pre B API S HS) as (_ & _ & _ & _ & _ & _ & _ & _ & TP0 & _).
  pose proof (h_rel _ _ _ _ _ _ _ _ H) as (HM1 & HW1 & HB1 & _ & _ & _ & _ & _ & HS1).
  destruct VR as (V2 & V3 & V4 & _).
  assert (SPR : spZ rg = spf).
  { unfold spZ. rewrite V2. apply unsigned_lit. unfold s_spf, VR_K in *. lia. }
  split; [|split; [unfold s_spf in *; lia | exact SPR]].
  split; [exact HM1|]. split; [exact HW1|]. split; [exact HB1|].
  split; [rewrite E1; exact RET|].
  split; [rewrite SPR; unfold s_spf; replace (spZ rg0 - 608) with (spZ rg0 + (-38) * 16) by ring;
          rewrite Z.mod_add by lia; exact SP16|].
  split; [rewrite SPR; unfold s_spf, VR_K in *; lia|].
  split; [rewrite SPR; unfold s_spf in *; lia|].
  split; [intros a Ha; apply HS1; left; rewrite SPR in Ha; unfold s_spf, VR_K in *; lia|].
  split; [rewrite V4; exact TP0|].
  split; [intros a Ha; apply HS1; right; exact Ha|].
  intros HI. rewrite (h_init _ _ _ _ _ _ _ _ H) in HI. discriminate.
Qed.


Lemma blk_str_arg : forall L1 A1 mem1 md1 O1 a k p x sp K,
  MR L1 A1 mem1 md1 -> In (a, k) (blocks L1 A1) -> ~ In a (map fst O1) ->
  a <= p -> p + Z.of_nat (length x) + 1 <= a + k ->
  bytes_at rsegs mem1 p (x ++ [Z_to_bv 8 0]) -> no0 x -> Z.of_nat (length x) <= LMAX ->
  alloc_ceiling <= sp - K ->
  RecKindB.str_arg B L1 A1 O1 sp K mem1 p (Some x).
Proof using HF.
  intros L1 A1 mem1 md1 O1 a k p x sp K HM Hin Hno Hap Hpk Hb Hnz Hlen HK.
  pose proof (vf_segs B API HF) as SEGS. pose proof alloc_ceiling_value as (ACV & AC4).
  destruct (blk_low _ _ _ _ a k 0 HM Hin ltac:(lia)) as (H4 & Hc & _ & _).
  set (y := p + Z.of_nat (length x) + 1) in *.
  set (s := (- y) mod 8).
  assert (Hs : 0 <= s < 8) by (unfold s; apply Z.mod_pos_bound; lia).
  assert (RU : y + s <= 8 * ((a + k + 7) / 8)) by (unfold s; Z.div_mod_to_equations; lia).
  assert (RC : 8 * ((a + k + 7) / 8) <= alloc_ceiling) by (Z.div_mod_to_equations; lia).
  destruct (present_rw_cells rsegs mem1 y (Z.to_nat s)) as [slk HSLK]; [lia | lia | |].
  { intros i Hi. destruct (Z_lt_ge_dec (y + i) (a + k)) as [Hl|Hl].
    - replace (y + i) with (a + (y + i - a)) by ring.
      exact (proj2 (proj2 (proj2 (blk_low _ _ _ _ a k (y + i - a) HM Hin ltac:(lia))))).
    - eapply (vf_bslack B API HF); [exact HM | exact Hin | lia]. }
  destruct HSLK as [[HSW HSB] _]. cbn [cells_bytes cbytes] in HSB. rewrite app_nil_r in HSB.
  cbn [cells_wf cell_wf] in HSW. destruct HSW as [HSL _].
  assert (LS : Z.of_nat (length slk) = s) by lia.
  assert (LT : Z.of_nat (length (x ++ Z_to_bv 8 0 :: slk)) = Z.of_nat (length x) + 1 + s)
    by (rewrite length_app; cbn [length]; lia).
  split; [lia|]. split; [exact Hnz|]. split; [exact Hlen|].
  exists slk. rewrite SEGS.
  split.
  { replace (x ++ Z_to_bv 8 0 :: slk) with ((x ++ [Z_to_bv 8 0]) ++ slk) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact Hb|]. rewrite length_app. cbn [length].
    replace (p + Z.of_nat (length x + 1)) with y by (unfold y; lia). exact HSB. }
  split; [unfold y in *; lia|].
  split; [left; rewrite LT; unfold y in *; lia|].
  split; [right; left; exists a, k; split; [exact Hin|]; split; [exact Hno|]; unfold y in *; lia|].
  intros z Hz Hr. rewrite LT in Hz.
  assert (Rz : 0x33ff0 <= z < 0x343e8) by (unfold RecKindB.rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE in Hr; lia).
  assert (Hw : exists j, 0 <= j < k /\ 0x33ff0 <= a + j < 0x343e8).
  { destruct (Z_lt_ge_dec z (a + k)) as [Hl|Hl]; [exists (z - a); lia|].
    exists (k - 1). assert (0x33ff0 < a + k) by (Z.div_mod_to_equations; lia). unfold y in *. lia. }
  destruct Hw as (j & Hj & Hr2).
  destruct (blk_low _ _ _ _ a k j HM Hin Hj) as (_ & _ & Hni & _). apply Hni.
  apply (vf_globs B API HF). exists 0x33ff0, 1020. split; [left; reflexivity | lia].
Qed.

Lemma st_tok_arg : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K i p w,
  vr_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c -> 0 <= K <= 14336 ->
  nth_error ps i = Some p -> nth_error (toks D) i = Some w ->
  RecKindB.str_arg B L1 A1 O1 spf K mem1 (bv_unsigned p) (Some w).
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K i p w (_ & _ & _ & H & _) HK Ep Ew.
  pose proof sp_facts as (SPC & _ & _ & _).
  destruct (Forall2_nth _ _ _ _ _ _ (h_tok _ _ _ _ _ _ _ _ H) Ep Ew) as ((Hb & Hnz) & H1 & H2).
  destruct (h_x _ _ _ _ _ _ _ _ H (cb, ncb) (or_intror (or_introl eq_refl))) as [Hin Hno].
  pose proof (verbs_receive_route.toks_len D w (nth_error_In _ _ Ew)) as LW.
  pose proof (ok_nD B API S HS) as ND. pose proof (ok_n8 B API S HS) as N8.
  apply (blk_str_arg L1 A1 mem1 md1 O1 cb ncb); try assumption.
  - exact (proj1 (h_rel _ _ _ _ _ _ _ _ H)).
  - apply no0_forall. exact Hnz.
  - unfold LMAX. lia.
  - unfold s_spf, VR_K in *. lia.
Qed.

Lemma st_line_arg : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K,
  vr_state rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c -> 0 <= K <= 14336 ->
  RecKindB.str_arg B L1 A1 O1 spf K mem1 lb (Some (line D)).
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K (_ & _ & _ & H & _) HK.
  pose proof sp_facts as (SPC & _ & _ & _).
  destruct (h_x _ _ _ _ _ _ _ _ H (lb, nlb) (or_introl eq_refl)) as [Hin Hno].
  pose proof (h_lb _ _ _ _ _ _ _ _ H) as HLB.
  rewrite repeat_snoc0 in HLB.
  replace (line D ++ Z_to_bv 8 0 :: repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D)))
    with ((line D ++ [Z_to_bv 8 0]) ++ repeat (Z_to_bv 8 0) (length (upto0 D) - length (line D))) in HLB
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in HLB. destruct HLB as [HLB _].
  pose proof (verbs_receive_route.line_len D) as LL. pose proof line_le_upto as LU.
  pose proof (ok_nD B API S HS) as ND. pose proof (ok_n8 B API S HS) as N8.
  apply (blk_str_arg L1 A1 mem1 md1 O1 lb nlb); try assumption.
  - exact (proj1 (h_rel _ _ _ _ _ _ _ _ H)).
  - lia.
  - unfold s_nlb. lia.
  - apply no0_forall. rewrite Forall_forall. intros c0 Hc. exact (line_nonul D c0 Hc).
  - unfold LMAX. lia.
  - unfold s_spf, VR_K in *. lia.
Qed.

Lemma st_f18 : forall L1 A1 mem1 md1, MR L1 A1 mem1 md1 ->
  RecKindB.f18_words (ms_segs B) mem1 /\ exists cn, ssp_b B mem1 cn.
Proof using HF.
  intros L1 A1 mem1 md1 HM. pose proof (vf_segs B API HF) as SEGS.
  destruct (ax_statics (vf_ax B API HF) L1 A1 mem1 md1 HM) as (WG & (g & Hg & WGD) & _).
  pose proof (reply.word_le_at B mem1 _ _ WG ltac:(rewrite (vf_guard B API HF); lia)) as L1'.
  pose proof (reply.word_le_at B mem1 _ _ WGD Hg) as L2'.
  rewrite (vf_gotg B API HF), (vf_guard B API HF) in L1'. rewrite (vf_guard B API HF) in L2'.
  split.
  - rewrite SEGS. apply (reply.f18_of_le mem1 (Z_to_bv 64 g)); intros i Hi.
    + unfold le_at, blk_data in L1'. rewrite SEGS in L1'. apply L1'. rewrite length_le8. lia.
    + unfold le_at, blk_data in L2'. rewrite SEGS in L2'. apply L2'. rewrite length_le8. lia.
  - exists (Z_to_bv 64 g). unfold ssp_b, SSP_GOT_B, SSP_GUARD_B. split; assumption.
Qed.

Lemma st_relro : forall L1 A1 mem1 md1 a, vr_rel B API O0 L0 A0 rg0 m0 md0 L1 A1 mem1 md1 ->
  in_globals FrameAPI.frame_RELRO a -> mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) m0 a.
Proof using HF HS.
  intros L1 A1 mem1 md1 a (HM1 & _ & _ & _ & _ & _ & HF1 & _) Hg.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  pose proof (ok_pre B API S HS) as (HM0 & _).
  pose proof sp_facts as (SPC & _ & _ & _). pose proof alloc_ceiling_val as ACV.
  destruct (vf_relro B API HF L0 A0 m0 md0 a HM0 Hg) as [Hi N0].
  destruct (vf_relro B API HF L1 A1 mem1 md1 a HM1 Hg) as [_ N1].
  pose proof (in_img_low B SEGS a Hi) as Hlo.
  assert (Ha : 0x226b0 <= a < 0x22d58) by (destruct Hg as (lo & len & Hin & Hr); destruct Hin as [E|[E|[]]];
    injection E as <- <-; lia).
  apply (HF1 a (or_intror Hi) N0 N1).
  - unfold scratch_k. rewrite ERR. lia.
  - unfold vr_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT. lia.
Qed.

Lemma st_room : forall k1 ns REQ, (k1 + length ns <= 32)%nat -> Forall (fun n => 0 <= n <= 8194) ns ->
  0 <= REQ <= 8194 -> room_slots (RecKindB.sb_mallocs (sb_n b0 k1) ns) REQ.
Proof using HS.
  intros k1 ns REQ Hk Hns HR. pose proof (ok_room B API S HS) as ROOM.
  pose proof (sum_bound ns Hns) as SB. destruct (sb_mallocs_fields ns (sb_n b0 k1)) as (E1 & E2 & E3).
  refine (RecKindB.room_slots_mono _ _ REQ VR_REQ _ _ ROOM); [| unfold VR_REQ; lia].
  unfold RecKindB.sb_le. rewrite E1, E2, E3. unfold sb_n, SB_REQ. cbn [sb_live sb_bytes sb_cap]. lia.
Qed.

Lemma st_res : forall A1 k1 ns, (k1 + length ns <= 32)%nat -> Forall (fun n => 0 <= n <= 8194) ns ->
  res_ok_slots A1 (RecKindB.sb_mallocs (sb_n b0 k1) ns) -> res_ok_slots A1 (sb_n b0 (k1 + length ns)).
Proof using HS.
  intros A1 k1 ns Hk Hns H. pose proof (ok_room B API S HS) as (_ & RC & _).
  pose proof (sum_bound ns Hns) as SB. destruct (sb_mallocs_fields ns (sb_n b0 k1)) as (E1 & E2 & E3).
  apply (RecKindB.res_ok_slots_le A1 (RecKindB.sb_mallocs (sb_n b0 k1) ns) _); [| | exact H]; cbn [sb_live sb_cap] in RC;
    unfold RecKindB.sb_le; try rewrite E1, E2, E3; unfold sb_n, SB_REQ; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Lemma st_le : forall A1 b1 k1, RecKindB.sb_le b1 (sb_n b0 k1) -> (k1 <= 32)%nat ->
  res_ok_slots A1 b1 -> res_ok_slots A1 (sb_n b0 k1).
Proof using HS.
  intros A1 b1 k1 Hle Hk H. pose proof (ok_room B API S HS) as (_ & RC & _).
  apply (RecKindB.res_ok_slots_le A1 b1); [exact Hle | | exact H]. cbn [sb_live sb_cap] in RC.
  unfold sb_n. cbn [sb_live sb_cap]. lia.
Qed.

End St.
