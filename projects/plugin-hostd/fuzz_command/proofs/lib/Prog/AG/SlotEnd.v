(* lib/Prog/SlotEnd.v with the agreement room cap CAP_AG (lib/SlotAgree.v) for CAPMAX. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP
  SlotSpec SlotGlue SlotRuns rec_calls_free_c rec_clear_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.AG Require Slot SlotRec SlotInv SlotIter.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require RecAns.
Import ListNotations.
Local Open Scope Z_scope.

(* The end of the slot (LLVMFuzzerTestOneInput, plain 0x14048): from the entry of the last rec_clear (pc 0x1559c,
   SlotIter.exit_at) to the return, with the slot's post lib_post_g and GI (S j). *)

Lemma se_g_of : forall a, 0x33d10 <= a < 0x3410c -> in_globals SlotInv.G_cmd a.
Proof. intros a Ha. exists 0x33d10, 1020. split; [left; reflexivity | lia]. Qed.

Lemma se_g_iv : forall a, in_globals SlotInv.G_cmd a -> 0x33d10 <= a < 0x3410c.
Proof.
  intros a (lo & len & Hin & Hb). unfold SlotInv.G_cmd, frame_G in Hin. destruct Hin as [E|[]].
  injection E as <- <-. lia.
Qed.

Lemma se_relro_iv : forall a, in_globals frame_RELRO a -> 0x224a8 <= a < 0x23000.
Proof.
  intros a (lo & len & Hin & Hb). unfold frame_RELRO in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia.
Qed.

Lemma se_rcw_G : forall n a, (n <= 16)%nat -> rec_clear_writes n a -> in_globals SlotInv.G_cmd a.
Proof.
  intros n a Hn H. apply se_g_of. unfold rec_clear_writes, nargs_field in H.
  unfold G_REC, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE in H.
  destruct H as [H|[(i & Hi & H)|[H|H]]]; lia.
Qed.

Lemma se_rec_empty : forall segs L A mem R O, g_rec_rep segs L A mem R O -> r_calls R = [] -> r_answer R = None ->
  r_reply R = None -> r_spill R = (0, []) -> forall pn, ~ In pn O.
Proof.
  intros segs L A mem R O (Q & HR & HO) Hc Ha Hr Hs pn Hin. apply HO in Hin.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite Hc in C2. cbn [length] in C2.
  rewrite Hs in C5. destruct C5 as (_ & _ & C5 & _). cbn [snd length] in C5.
  unfold answer_at in HA. rewrite Ha in HA.
  unfold reply_at in HP. rewrite Hr in HP.
  unfold lay_blocks in Hin.
  destruct (l_answer Q); [destruct HA|]. destruct (l_reply Q); [destruct HP|].
  destruct (l_calls Q); [|cbn in C2; discriminate].
  destruct (l_spill Q); [|cbn in C5; discriminate].
  cbn in Hin. exact Hin.
Qed.

Lemma se_rfree_cap : forall F b, sb_cap (rfree_b b F) = sb_cap b.
Proof. unfold rfree_b. induction F as [|pn F IH]; intros b; cbn [fold_left]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Definition se_rochk (a : Z) : bool := negb (ro_addr rsegs (Z_to_bv 64 a)).

Lemma se_g_rochk : forallb (fun i => se_rochk (0x33d10 + i)) (map Z.of_nat (seq 0 1020)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma se_g_not_ro : forall a, 0x33d10 <= a < 0x3410c -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (Slot.zseq_forall _ 1020 se_g_rochk (a - 0x33d10) ltac:(lia)) as H. unfold se_rochk in H.
  replace (0x33d10 + (a - 0x33d10)) with a in H by lia.
  destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate | reflexivity].
Qed.

Lemma se_ret_pc : forall z, z mod 2 = 0 -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z H. pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 z)) as R. unfold bv_modulus in R. cbn in R.
  pose proof (ret_pc_even (bv_unsigned (Z_to_bv 64 z)) R) as E. rewrite Z_to_bv_bv_unsigned in E. apply E.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite KindBGlue.kb_mod2_land. exact H.
Qed.

Lemma se_fds_vm : forall vm md, m_fds (with_vmmaps vm md) = m_fds md.
Proof. intros vm [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma se_img_iv : forall (B : malloc_syms) lo len a, ms_segs B = rsegs ->
  existsb (fun s => (bv_unsigned (fst s) <=? lo) && (lo + len <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
    (segments_reserved rsegs) = true -> lo <= a < lo + len -> in_img B a.
Proof.
  intros B lo len a SEGS H Ha. apply existsb_exists in H as (sg & Hs & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  split; [rewrite SEGS; discriminate|]. exists sg. rewrite SEGS. split; [exact Hs | lia].
Qed.


Lemma se_rep_gi4 : forall L A mem R O, g_rec_rep rsegs L A mem R O -> r_calls R = [] -> r_answer R = None ->
  r_reply R = None -> r_nreplies R = 0 -> r_spill R = (0, []) ->
  Slot.zero_at mem (Slot.G_REC_A + 8) 4 /\ Slot.zero_at mem (Slot.G_REC_A + 912) 12 /\
  Slot.zero_at mem (Slot.G_REC_A + 928) 16 /\ Slot.zero_at mem Slot.G_SPILL 8.
Proof.
  intros L A mem R O (Q & HR & HO) Hc Ha Hr Hn Hs.
  destruct HR as (HS & HC & HA & HP & HX & HW).
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6).
  rewrite Hc in C3. cbn [length] in C3. change (Z.of_nat 0) with 0 in C3.
  rewrite Hs in C5. destruct C5 as (_ & _ & _ & S1 & S2 & _). cbn [fst snd length] in S1, S2.
  change (Z.of_nat 0) with 0 in S2.
  unfold answer_at in HA. rewrite Ha in HA. destruct (l_answer Q) as [pn|]; [destruct HA|].
  unfold reply_at in HP. rewrite Hr in HP. destruct (l_reply Q) as [pn|]; [destruct HP|].
  destruct HP as [P1 P2].
  destruct HX as (_ & _ & X3 & _). rewrite Hn in X3.
  unfold Slot.G_REC_A, Slot.G_SPILL.
  unfold G_REC, REC_SC, OFF_NCALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE, CALL_OFF_FN,
    CALL_OFF_NARGS in *.
  split; [|split; [|split]].
  - exact (SlotRec.bytes_zero_le4 _ _ C3).
  - change 12 with (8 + 4). apply SlotRec.zero_at_join; [exact (SlotRec.bytes_zero_le8 _ _ HA) | exact (SlotRec.bytes_zero_le4 _ _ X3)].
  - change 16 with (8 + 8). apply SlotRec.zero_at_join; [exact (SlotRec.bytes_zero_le8 _ _ P1) | exact (SlotRec.bytes_zero_le8 _ _ P2)].
  - change 8 with (4 + 4). apply SlotRec.zero_at_join.
    + rewrite Z.add_0_r in S1. exact (SlotRec.bytes_zero_le4 _ _ S1).
    + exact (SlotRec.bytes_zero_le4 _ _ S2).
Qed.

(* g_rec.state := 0 and g_rec.host_settings := 0 when the recorder owns no block and only G's bytes below
   g_rec.state are known to be kept. *)
Lemma se_rep_set_sh : forall L A mem mem' R O,
  g_rec_rep rsegs L A mem R O -> (forall pn, ~ In pn O) ->
  Mem.bytes_at rsegs mem' (0x33d48 + 944) (Mem.le8 (Z_to_bv 64 0) ++ Mem.le8 (Z_to_bv 64 0)) ->
  (forall a, 0x33d10 <= a < 0x33d48 + 944 -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  g_rec_rep rsegs L A mem' (set_host (set_state R 0) 0) O.
Proof.
  intros L A mem mem' R O (Q & HR & HO) HE B K.
  exists Q. split; [|exact HO].
  assert (HR' := HR). destruct HR' as (_ & _ & _ & _ & (X1 & X2 & X3 & X4 & X5 & X6) & (_ & HW)).
  apply Mem.bytes_at_app in B as [B1 B2]. rewrite Mem.length_le8 in B2.
  apply (SlotRec.rep_at_move rsegs (blocks L A) mem mem' G_REC REC_SC R _ Q HR).
  - apply SlotRec.g_wr_at; unfold G_REC, REC_SIZE; lia.
  - apply SlotRec.g_wr_at; unfold REC_SC, SC_SIZE; lia.
  - intros a Ha. apply K. unfold G_REC, REC_SC, SC_SIZE in Ha. lia.
  - intros pn i Hpn Hi. exfalso. exact (HE pn (proj2 (HO pn) Hpn)).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold g1_scalars. cbn [set_host set_state r_refuse r_code r_nreplies r_state r_host].
    unfold G_REC, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    refine (conj _ (conj _ (conj _ (conj B1 (conj _ _))))).
    + apply (bytes_at_keep_in rsegs mem mem' 0x33d48 (0x33d48 + 944)); [exact X1 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' 0x33d48 (0x33d48 + 944)); [exact X2 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + apply (bytes_at_keep_in rsegs mem mem' 0x33d48 (0x33d48 + 944)); [exact X3 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K. lia.
    + replace (0x33d48 + 952) with (0x33d48 + 944 + Z.of_nat 8) by reflexivity. exact B2.
    + destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). repeat split; lia.
Qed.

Ltac fg_destruct FG :=
  destruct FG as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16 & F17 &
    F18 & F18v & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27 & F28 & F29 & F30).

Section End.
Context {rc : RunCeil} {fxs : FPState}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head) (SK : sink_syms)
  (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (L0 : layout) (A0 : astate)
  (p0 n0 : Z) (pl : list byte) (b : sbound) (j : nat).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.
Hypothesis RCLEAR : forall fx : FPState, @rec_clear_contract fx rc B (API rc).
Hypothesis DBL : ms_debruijn_len B = 32.

Lemma se_SEGS : ms_segs B = rsegs.
Proof. fg_destruct FG. exact F0. Qed.

Lemma se_ERRNO : errno_addr B + 4 <= alloc_ceiling.
Proof. fg_destruct FG. exact (F6 rc). Qed.

Lemma se_FA : @frame_allocator rc fxs B (API rc).
Proof. fg_destruct FG. exact (F30 rc fxs). Qed.

Lemma se_AX : AllocExtra B (aa_MR (API rc)).
Proof. destruct se_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma se_GNOWN : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals SlotInv.G_cmd a -> ~ owned B L A a.
Proof. destruct se_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma se_RNOWN : forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals frame_RELRO a -> ~ owned B L A a.
Proof. destruct se_FA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Lemma se_NODUP : forall L A mem md, aa_MR (API rc) L A mem md -> List.NoDup (blocks L A).
Proof.
  intros L A mem md HM. destruct se_FA as (_ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (SlotInv.blocks_nodup_list L A (H L A mem md HM)).
Qed.

Lemma se_GFREE : forall a, in_globals SlotInv.G_cmd a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. fg_destruct FG. exact F25. Qed.

Lemma se_RFREE : forall a, in_globals frame_RELRO a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. fg_destruct FG. exact F26. Qed.

Lemma se_HS : alloc_ceiling + SLOT_STACK <= S < 2 ^ 63.
Proof.
  destruct PRE as ((_ & _ & _ & _ & _ & _ & H6 & H7 & _) & _). rewrite <- RG2. split; assumption.
Qed.

Lemma se_S16 : S mod 16 = 0.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & H5 & _) & _). rewrite <- RG2. exact H5. Qed.

Lemma se_errno_v : errno_addr B = 0x3413c.
Proof. fg_destruct FG. unfold errno_addr. rewrite F16, F17. reflexivity. Qed.

(* The sink words keep their values when the image outside the allocator's bytes, the errno word and G is kept. *)
Lemma se_sink_keep : forall mem mem' md md',
  (forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals SlotInv.G_cmd a -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  m_fds md' = m_fds md ->
  sink_none (SH := SH) (SK := SK) B mem md -> sink_none (SH := SH) (SK := SK) B mem' md'.
Proof.
  intros mem mem' md md' K Hf ((T & Lk) & Hd & Fd).
  pose proof se_errno_v as EV. pose proof FG as FG'. fg_destruct FG'.
  assert (NS : forall a, (a = 0x54471 \/ 0x54898 <= a < 0x548a8) -> ~ static_owned B a).
  { intros a Ha. unfold static_owned, vml_lo, vml_len. rewrite F7, F8, F10, F11, F12, F13, F14, F15, F18v, DBL. lia. }
  assert (NC : forall a, (a = 0x54471 \/ 0x54898 <= a < 0x548a8) -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE)).
  { intros a Ha. rewrite F9. unfold CTX_SIZE. lia. }
  assert (NE : forall a, (a = 0x54471 \/ 0x54898 <= a < 0x548a8) -> ~ (errno_addr B <= a < errno_addr B + 4)).
  { intros a Ha. rewrite EV. lia. }
  assert (NG : forall a, (a = 0x54471 \/ 0x54898 <= a < 0x548a8) -> ~ in_globals SlotInv.G_cmd a).
  { intros a Ha Hg. pose proof (se_g_iv a Hg). lia. }
  rewrite F0 in *.
  unfold sink_none, closed_stdio_env, val_mem, word_mem in *. rewrite F0 in *.
  split; [split|split].
  - intros k Hk. rewrite <- (T k Hk). rewrite F21 in *. assert (k = 0%nat) by lia. subst k.
    apply K; [apply (se_img_iv B 0x54471 1); [exact F0 | vm_compute; reflexivity | lia] | apply NS | apply NC | apply NE
      | apply NG]; lia.
  - intros k Hk. rewrite <- (Lk k Hk). rewrite F20 in *.
    apply K; [apply (se_img_iv B 0x54898 4); [exact F0 | vm_compute; reflexivity | lia] | apply NS | apply NC | apply NE
      | apply NG]; lia.
  - intros k Hk. rewrite <- (Hd k Hk). rewrite F19 in *.
    apply K; [apply (se_img_iv B 0x548a0 8); [exact F0 | vm_compute; reflexivity | lia] | apply NS | apply NC | apply NE
      | apply NG]; lia.
  - rewrite Hf. exact Fd.
Qed.

(* A call of rec_clear at the slot's frame base (pc 0x1559c), with the facts the walk keeps. *)
Lemma se_rc_step : forall fx L A regs mem md R O (Q : config -> Prop),
  SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 fx L A regs mem md ->
  g_rec_rep rsegs L A mem R O -> r_spill R = (0, []) -> SlotInv.rcap A ->
  (forall a k, In (a, k) (blocks L0 A0) -> ~ In a (map fst O)) ->
  (forall pn, In pn (blocks L A) -> In pn (blocks L0 A0) \/ In pn O) ->
  YK0s.ret_ok (getr regs 1) ->
  (forall L1 A1 regs1 mem1 md1 O1,
     SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 fx L1 A1 regs1 mem1 md1 ->
     g_rec_rep rsegs L1 A1 mem1 (rec_clear R) O1 -> (forall pn, ~ In pn O1) ->
     (forall pn, In pn (blocks L1 A1) -> In pn (blocks L0 A0)) -> SlotInv.rcap A1 ->
     regs_preserved regs regs1 ->
     (forall a, in_globals frame_G a -> ~ rec_clear_writes (length (r_calls R)) a ->
        mbyte rsegs mem1 a = mbyte rsegs mem a) ->
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (SlotInv.FB S - RCL_K <= a < SlotInv.FB S) ->
        mbyte rsegs mem1 a = mbyte rsegs mem a /\ (writable_at rsegs mem a <-> writable_at rsegs mem1 a)) ->
     SR rsegs (mkCfg (@mkst fx regs1 (getr regs 1) mem1 (seg_rom rsegs)) md1) Q) ->
  SR rsegs (mkCfg (@mkst fx regs (Z_to_bv 64 0x1559c) mem (seg_rom rsegs)) md) Q.
Proof.
  intros fx L A regs mem md R O Q HCF REP SPILL HRC ENO BLK HRA KC.
  pose proof se_SEGS as SEGS. pose proof se_ERRNO as ERRNO. pose proof se_AX as AX. pose proof se_HS as HS.
  pose proof se_S16 as S16. pose proof se_errno_v as EV. pose proof alloc_ceiling_val as AC.
  pose proof PRE as ((P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14) &
    X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  assert (SP : spZ regs = SlotInv.FB S)
    by (unfold spZ; rewrite R2; apply unsigned_lit; unfold SlotInv.FB, SLOT_STACK in *; lia).
  assert (NC : (length (r_calls R) <= 16)%nat) by (destruct REP as (Q0 & (_ & (C1 & _) & _) & _); exact C1).
  assert (PREK : call_pre_k B (aa_MR (API rc)) RCL_K L A regs mem md).
  { unfold call_pre_k. rewrite SP. rewrite SEGS.
    refine (conj M (conj Wf (conj Bd (conj HRA (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    - unfold SlotInv.FB. clear -S16. Z.div_mod_to_equations. lia.
    - unfold SlotInv.FB, RCL_K, RCF_K, ALLOC_STACK, SLOT_STACK in *. lia.
    - unfold SlotInv.FB, SLOT_STACK in *. lia.
    - intros a Ha. apply SW. unfold lib_scratch. left. rewrite RG2.
      unfold SlotInv.FB, RCL_K, RCF_K, ALLOC_STACK, SLOT_STACK in *. lia.
    - rewrite R4. exact P9.
    - intros a Ha. apply SW. unfold lib_scratch. right. exact Ha.
    - intros E. rewrite I in E. discriminate. }
  pose proof (RCLEAR fx L A regs mem md R O (SlotInv.tb A) PREK ltac:(rewrite SEGS; exact RO)
     ltac:(rewrite SEGS; exact REP) (SlotInv.res_tb L A Wf HRC)) as HRCL.
  rewrite SEGS in HRCL. unfold REC_CLEAR in HRCL.
  eapply SR_bind; [exact HRCL|].
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & O1 & D & -> & POST & REP1 & O1O & DD & PERM & BLK1 & KEPT & UB1 & UB1'
    & GDK & RO1 & GK1 & INIT1 & REG1 & RES1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  assert (GI1 : G_img_c B frame_RELRO mem1).
  { intros a Ha. pose proof (se_relro_iv a Ha) as Hr. destruct (se_RFREE a Ha) as (Hi & Hs & Hc & He).
    destruct (FRAME a (or_intror Hi)) as [E1 _].
    - exact (se_RNOWN L A mem md a M Ha).
    - exact (se_RNOWN L1 A1 mem1 md1 a M1 Ha).
    - intros Hx. unfold scratch_k in Hx. rewrite SP in Hx.
      unfold SlotInv.FB, SLOT_STACK, RCL_K, RCF_K, ALLOC_STACK in *. destruct Hx as [Hx|Hx]; [lia | exact (He Hx)].
    - intros Hw. pose proof (se_g_iv a (se_rcw_G _ a NC Hw)). lia.
    - rewrite E1. exact (GIm a Ha). }
  assert (EB1 : SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk].
    assert (ND : ~ In a (map fst D)).
    { intros Hd. apply in_map_iff in Hd as ([a' k'] & Ea & Hd). cbn in Ea. subst a'.
      apply (ENO a k Hin). apply in_map_iff. exists (a, k'). split; [reflexivity | exact (proj1 (proj1 (DD _) Hd))]. }
    split.
    - assert (Hp : In (a, k) (blocks L1 A1 ++ D)) by exact (Permutation_in _ PERM Hb).
      apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [exact Hp|].
      exfalso. apply ND. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hp].
    - intros i Hi. rewrite <- (Hk i Hi). rewrite <- SEGS. exact (KEPT a k i Hb ND Hi). }
  assert (CF1 : SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 fx L1 A1 regs1 mem1 md1).
  { apply (SlotInv.cf_call B (API rc) S rg mem0 md0 L0 A0 SEGS ERRNO AX HS RG2 fx fx RCL_K L A regs mem md
             (rec_clear_writes (length (r_calls R))) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT1 I) PRES
             (ex_intro _ vm1 Hmd1) FRAME SCRW).
    - unfold SlotInv.FB, SLOT_STACK, RCL_K, RCF_K, ALLOC_STACK. lia.
    - unfold RCL_K, RCF_K, ALLOC_STACK. lia.
    - intros a Ha. left. exact (se_rcw_G _ a NC Ha).
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ.
    - intros r. reflexivity. }
  assert (HE1 : forall pn, ~ In pn O1) by exact (se_rec_empty _ _ _ _ _ _ REP1 eq_refl eq_refl eq_refl SPILL).
  apply (KC L1 A1 regs1 mem1 md1 O1 CF1 REP1 HE1).
  - intros pn Hp. destruct (BLK1 pn Hp) as [[Hp1 Hn1]|Hp1].
    + destruct (BLK pn Hp1) as [H|H]; [exact H | contradiction].
    + exfalso. exact (HE1 pn Hp1).
  - exists (rfree_b (SlotInv.tb A) D). split; [exact RES1 | rewrite se_rfree_cap; reflexivity].
  - exact PRES.
  - intros a Ha Hw. exact (proj1 (GDK a Ha Hw)).
  - intros a Ha Hs. rewrite <- SEGS. apply (FRAME a (or_introl Ha)).
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L A mem md a M Ho). lia.
    + intros Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L1 A1 mem1 md1 a M1 Ho). lia.
    + intros Hx. unfold scratch_k in Hx. rewrite SP in Hx. rewrite EV in Hx. destruct Hx as [Hx|Hx]; [exact (Hs Hx) | lia].
    + intros Hw. pose proof (se_g_iv a (se_rcw_G _ a NC Hw)). lia.
Qed.

(* From the entry of the last rec_clear to the return: rec_clear, then 0x14324 (g_quitting := 0, the saved
   registers back, ret). *)
Lemma end_ok : forall c, SlotIter.exit_at B (API rc) S rg mem0 md0 L0 A0 c ->
  SR rsegs c (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
     c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom rsegs)) md' /\ frm_zero (@fp_csr fx') /\
     lib_post_g (LS := LS) (SH := SH) (SK := SK) B (API rc) Slot.G_cmd SLOT_STACK L0 A0 rg mem0 md0 p0 n0 b
       (LL 0 (m_fs md0) []) L' A' regs' mem' md' /\ Slot.GI_cmd (Datatypes.S j) mem').
Proof.
  intros c (fx & L & A & regs & mem & md & R & O & q & -> & HCF & HRF & HRC & HR1).
  pose proof se_SEGS as SEGS. pose proof se_ERRNO as ERRNO. pose proof se_AX as AX. pose proof se_HS as HS.
  pose proof se_S16 as S16. pose proof se_errno_v as EV. pose proof alloc_ceiling_val as AC.
  pose proof PRE as ((P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14) &
    X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  pose proof FG as FG'. fg_destruct FG'.
  pose proof HCF as (M & Wf & Bd & I & (vm & Hmd) & R2 & R3 & R4 & SV & SW & SF & RO & GIm & EB & FZ).
  pose proof HRF as (REP & SPILL & QB & Hq & ENO & BLK).
  assert (SP : spZ regs = SlotInv.FB S)
    by (unfold spZ; rewrite R2; apply unsigned_lit; unfold SlotInv.FB, SLOT_STACK in *; lia).
  assert (NC : (length (r_calls R) <= 16)%nat) by (destruct REP as (Q0 & (_ & (C1 & _) & _) & _); exact C1).
  assert (PREK : call_pre_k B (aa_MR (API rc)) RCL_K L A regs mem md).
  { unfold call_pre_k. rewrite SP. rewrite SEGS.
    refine (conj M (conj Wf (conj Bd (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    - rewrite HR1. apply bv_eq. vm_compute. reflexivity.
    - unfold SlotInv.FB. clear -S16. Z.div_mod_to_equations. lia.
    - unfold SlotInv.FB, RCL_K, RCF_K, ALLOC_STACK, SLOT_STACK in *. lia.
    - unfold SlotInv.FB, SLOT_STACK in *. lia.
    - intros a Ha. apply SW. unfold lib_scratch. left. rewrite RG2.
      unfold SlotInv.FB, RCL_K, RCF_K, ALLOC_STACK, SLOT_STACK in *. lia.
    - rewrite R4. exact P9.
    - intros a Ha. apply SW. unfold lib_scratch. right. exact Ha.
    - intros E. rewrite I in E. discriminate. }
  pose proof (RCLEAR fx L A regs mem md R O (SlotInv.tb A) PREK ltac:(rewrite SEGS; exact RO)
     ltac:(rewrite SEGS; exact REP) (SlotInv.res_tb L A Wf HRC)) as HRCL.
  rewrite SEGS in HRCL. unfold REC_CLEAR in HRCL.
  eapply SR_bind; [exact HRCL|].
  intros c1 (L1 & A1 & regs1 & mem1 & md1 & O1 & D & -> & POST & REP1 & O1O & DD & PERM & BLK1 & KEPT & UB1 & UB1'
    & GDK & RO1 & GK1 & INIT1 & REG1 & RES1).
  destruct POST as (M1 & W1 & Bd1 & LLE1 & PA1 & PRES & (vm1 & Hmd1) & FRAME & BYTES & SCRW).
  assert (GI1 : G_img_c B frame_RELRO mem1).
  { intros a Ha. pose proof (se_relro_iv a Ha) as Hr. destruct (se_RFREE a Ha) as (Hi & Hs & Hc & He).
    destruct (FRAME a (or_intror Hi)) as [E1 _].
    - exact (se_RNOWN L A mem md a M Ha).
    - exact (se_RNOWN L1 A1 mem1 md1 a M1 Ha).
    - intros Hx. unfold scratch_k in Hx. rewrite SP in Hx.
      unfold SlotInv.FB, SLOT_STACK, RCL_K, RCF_K, ALLOC_STACK in *. destruct Hx as [Hx|Hx]; [lia | exact (He Hx)].
    - intros Hw. pose proof (se_g_iv a (se_rcw_G _ a NC Hw)). lia.
    - rewrite E1. exact (GIm a Ha). }
  assert (EB1 : SlotInv.eblocks mem0 L0 A0 L1 A1 mem1).
  { intros a k Hin. destruct (EB a k Hin) as [Hb Hk].
    assert (ND : ~ In a (map fst D)).
    { intros Hd. apply in_map_iff in Hd as ([a' k'] & Ea & Hd). cbn in Ea. subst a'.
      apply (ENO a k Hin). apply in_map_iff. exists (a, k'). split; [reflexivity | exact (proj1 (proj1 (DD _) Hd))]. }
    split.
    - assert (Hp : In (a, k) (blocks L1 A1 ++ D)) by exact (Permutation_in _ PERM Hb).
      apply in_app_or in Hp. destruct Hp as [Hp|Hp]; [exact Hp|].
      exfalso. apply ND. apply in_map_iff. exists (a, k). split; [reflexivity | exact Hp].
    - intros i Hi. rewrite <- (Hk i Hi). rewrite <- SEGS. exact (KEPT a k i Hb ND Hi). }
  assert (CF1 : SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 fx L1 A1 regs1 mem1 md1).
  { apply (SlotInv.cf_call B (API rc) S rg mem0 md0 L0 A0 SEGS ERRNO AX HS RG2 fx fx RCL_K L A regs mem md
             (rec_clear_writes (length (r_calls R))) L1 A1 regs1 mem1 md1 regs1 HCF M1 W1 Bd1 (INIT1 I) PRES
             (ex_intro _ vm1 Hmd1) FRAME SCRW).
    - unfold SlotInv.FB, SLOT_STACK, RCL_K, RCF_K, ALLOC_STACK. lia.
    - unfold RCL_K, RCF_K, ALLOC_STACK. lia.
    - intros a Ha. left. exact (se_rcw_G _ a NC Ha).
    - exact RO1.
    - exact GI1.
    - exact EB1.
    - exact FZ.
    - intros r. reflexivity. }
  pose proof CF1 as (M1' & W1' & Bd1' & I1 & (vmx & Hmdx) & R2' & R3' & R4' & SV1 & SW1 & SF1 & RO1' & GIm1 & EB1' & FZ1).
  pose proof SF1 as [SF1a SF1b].
  assert (BLK1' : forall pn, In pn (blocks L1 A1) -> In pn (blocks L0 A0)).
  { intros pn Hp. destruct (BLK1 pn Hp) as [[Hp1 Hn1]|Hp1].
    - destruct (BLK pn Hp1) as [H|H]; [exact H | contradiction].
    - exfalso. exact (se_rec_empty _ _ _ _ _ _ REP1 eq_refl eq_refl eq_refl SPILL pn Hp1). }
  assert (RCAP1 : SlotInv.rcap A1)
    by (exists (rfree_b (SlotInv.tb A) D); split; [exact RES1 | rewrite se_rfree_cap; reflexivity]).
  assert (SP1 : bv_unsigned (reg_get regs1 2) = SlotInv.FB S).
  { change (reg_get regs1 2) with (getr regs1 2). rewrite R2'. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  destruct (mr_model B _ (aa_laws (API rc)) _ _ _ _ M1) as (Hh1 & Hl1 & Hmt1).
  assert (NWQ : forall i, 0 <= i < 4 -> ~ rec_clear_writes (length (r_calls R)) (0x34108 + i)).
  { intros i Hi Hw. unfold rec_clear_writes, nargs_field in Hw.
    unfold G_REC, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE in Hw.
    destruct Hw as [H|[(k & Hk & H)|[H|H]]]; lia. }
  assert (QB1 : bytes_at rsegs mem1 0x34108 (le4 (Z_to_bv 64 q))).
  { apply (KindB.bytes_at_transfer rsegs mem). { exact QB. }
    intros i Hi. rewrite length_le4 in Hi.
    exact (proj1 (GDK (0x34108 + i) (se_g_of (0x34108 + i) ltac:(lia)) (NWQ i ltac:(lia)))). }
  assert (QRW : rw_cells rsegs mem1 0x34108 [CB 4 (le4 (Z_to_bv 64 q))]).
  { split; [split|].
    - split; [exact (length_le4 (Z_to_bv 64 q)) | exact Logic.I].
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact QB1.
    - cbn [cells_size csize]. apply SlotRec.g_wr_at; lia. }
  apply (KindB.rw_cells_normalize rsegs _ _ _ RO1) in QRW;
    [| intros i Hi; cbn in Hi; apply se_g_not_ro; lia].
  assert (GQn : bytes_at rsegs (normalize rsegs mem1) 0x22a38 (le8 (Z_to_bv 64 0x34108))).
  { apply bytes_at_normalize; [exact RO1|].
    assert (H : forall a, in_globals frame_RELRO a -> mbyte rsegs mem1 a = seg_rom rsegs (Z_to_bv 64 a))
      by (intros a Ha; rewrite <- SEGS; exact (GIm1 a Ha)).
    exact (proj1 (proj2 (proj2 (proj2 (SlotRec.relro_img mem1 H))))). }
  pose proof SV1 as SV1n.
  apply (KindB.rw_cells_normalize rsegs _ _ _ RO1) in SV1n;
    [| intros i Hi; apply ro_addr_hi; unfold SlotInv.savecells, SAVE in Hi; cbn in Hi;
       unfold SlotInv.FB, SLOT_STACK in *; lia].
  unfold SlotInv.savecells in SV1n.
  rewrite HR1.
  eapply (sr_run regs1 (Z_to_bv 64 0x14324) mem1 md1 _ _ Hh1 Hl1 RO1).
  { unfold Regs6ss.mkR_of. eapply run_epi_ok.
    - apply mem_inv_normalize.
    - rewrite SP1. unfold SlotInv.FB, SLOT_STACK, CommandModel.IMG_END in *. lia.
    - rewrite SP1. unfold SlotInv.FB in *. lia.
    - exact GQn.
    - exact QRW.
    - rewrite SP1. exact SV1n. }
  { intros s0 (a0' & m' & -> & _). do 5 eexists. reflexivity. }
  intros R0 F' pc' fc' m0' regs2 mem2 (a0' & m' & E & Ha0 & MU & WM & MI & QC) REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R0 F' pc' fc' m0' a0'.
  apply SR_ret.
  assert (MU2 : munch [(0x34108, 0x34108 + 4)] mem1 mem2)
    by exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem1 RO1) REL ROS MU).
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (0x34108 <= a < 0x34108 + 4) ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
  { intros a Ha Hx. assert (Ho : outside [(0x34108, 0x34108 + 4)] a) by (cbn; split; [exact Hx | exact Logic.I]).
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU2 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU2 Ha Ho)]. }
  assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (0x34108 <= a < 0x34108 + 4) -> present mem1 a -> present mem2 a).
  { intros a Ha Hx. apply (KindB.munch_present _ _ _ a MU2 Ha). cbn; split; [exact Hx | exact Logic.I]. }
  pose proof (ro_agree_same rsegs _ _ RO1 ROS) as RO2.
  assert (M2 : aa_MR (API rc) L1 A1 mem2 md1).
  { apply (mr_frame B _ (aa_laws (API rc)) L1 A1 mem1 mem2 md1 md1 M1).
    - intros a Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L1 A1 mem1 md1 a M1 Ho) as Hl.
      assert (NQ : ~ (0x34108 <= a < 0x34108 + 4))
        by (intros Hx; exact (se_GNOWN L1 A1 mem1 md1 a M1 (se_g_of a ltac:(lia)) Ho)).
      rewrite SEGS. exact (proj1 (K2 a ltac:(lia) NQ)).
    - intros a Ho Hp. pose proof (mr_owned_low B _ (aa_laws (API rc)) L1 A1 mem1 md1 a M1 Ho) as Hl.
      assert (NQ : ~ (0x34108 <= a < 0x34108 + 4))
        by (intros Hx; exact (se_GNOWN L1 A1 mem1 md1 a M1 (se_g_of a ltac:(lia)) Ho)).
      exact (KP2 a ltac:(lia) NQ Hp).
    - intros p n i Hin Hi. destruct (mr_blocks B _ (aa_laws (API rc)) L1 A1 mem1 md1 p n i M1 Hin Hi) as (Hp & H4 & Hc & _).
      apply KP2; [lia | | exact Hp].
      intros Hx. apply (ax_blocks_img AX L1 A1 mem1 md1 p n i M1 Hin Hi).
      exact (proj1 (se_GFREE _ (se_g_of (ptr_addr L1 p + i) ltac:(lia)))).
    - reflexivity.
    - exact Hh1.
    - exact Hl1.
    - exact Hmt1. }
  assert (KEEPB : forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k ->
     mbyte rsegs mem2 (ptr_addr L0 q + i) = mbyte rsegs mem0 (ptr_addr L0 q + i)).
  { intros q0 k i Hq0 Hi.
    assert (Hb : In (ptr_addr L0 q0, k) (blocks L0 A0))
      by (unfold blocks; apply in_map_iff; exists (q0, k); split; [reflexivity | exact Hq0]).
    destruct (EB1' _ _ Hb) as [_ Hk1].
    destruct (mr_blocks B _ (aa_laws (API rc)) L0 A0 mem0 md0 q0 k i P0 Hq0 Hi) as (_ & H4 & Hc & _).
    assert (NQ : ~ (0x34108 <= ptr_addr L0 q0 + i < 0x34108 + 4)).
    { intros Hx. apply (ax_blocks_img AX L0 A0 mem0 md0 q0 k i P0 Hq0 Hi).
      exact (proj1 (se_GFREE _ (se_g_of (ptr_addr L0 q0 + i) ltac:(lia)))). }
    rewrite (proj1 (K2 (ptr_addr L0 q0 + i) ltac:(lia) NQ)). exact (Hk1 i Hi). }
  assert (IMGK : forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
     ~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals SlotInv.G_cmd a ->
     mbyte rsegs mem2 a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem2 a)).
  { intros a Hi Hs Hc He Hg. destruct (SF1b a Hi Hs Hc He Hg) as [E1 W1x].
    pose proof (KindB.in_img_low B SEGS a Hi) as Hl.
    destruct (K2 a ltac:(lia)) as [E2 W2]; [intros Hx; apply Hg; apply se_g_of; lia|].
    split; [congruence | tauto]. }
  do 6 eexists. split.
  { rewrite P4, (se_ret_pc ra F1). reflexivity. }
  split; [exact FZ1|].
  split.
  - split; [exact M2|]. split; [exact W1'|]. split; [exact Bd1'|]. split; [exact I1|].
    split; [rewrite GR; reflexivity|].
    split.
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [C|C].
      { subst r. transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs1 2) + 176)); [rewrite GR; reflexivity|].
        rewrite SP1. apply bv_eq. rewrite unsigned_lit by (unfold SlotInv.FB, SLOT_STACK in *; lia).
        change (bv_unsigned (getr rg (Z_to_bv 5 2))) with (spZ rg). rewrite RG2. unfold SlotInv.FB. lia. }
      destruct C as [C|C]; [subst r; transitivity (reg_get regs1 3); [rewrite GR; reflexivity | exact R3'] |].
      destruct C as [C|C]; [subst r; transitivity (reg_get regs1 4); [rewrite GR; reflexivity | exact R4'] |].
      repeat (destruct C as [C|C]; [subst r; rewrite GR; reflexivity|]). subst r; rewrite GR; reflexivity. }
    split.
    { exists vmx, (m_fds md0), (m_statpins md0). split; [rewrite Hmdx; exact (with_vmmaps_os_upd vmx md0) |].
      intros k; reflexivity. }
    split.
    { intros q0 k Hq0.
      assert (Hb : In (ptr_addr L0 q0, k) (blocks L0 A0))
        by (unfold blocks; apply in_map_iff; exists (q0, k); split; [reflexivity | exact Hq0]).
      destruct (EB1' _ _ Hb) as [Hb1 _]. unfold blocks in Hb1. apply in_map_iff in Hb1 as ([q' k'] & Eq & Hq').
      cbn in Eq. injection Eq as E1 E2. subst k'. exists q'. split; [exact Hq' | exact E1]. }
    split.
    { intros a Ha Hs. destruct (SF1a a Ha Hs) as [E1 W1x].
      destruct (K2 a ltac:(lia) ltac:(lia)) as [E2 W2]. rewrite SEGS. split; [congruence | tauto]. }
    split.
    { intros a Hi Hs Hc He Hg. rewrite SEGS. exact (IMGK a Hi Hs Hc He Hg). }
    split.
    { intros a Hg. pose proof (se_g_iv a Hg) as Hr. rewrite SEGS. split; intros _; apply SlotRec.g_writable; lia. }
    split.
    { intros q0 k i Hq0 _ Hi. rewrite SEGS. exact (KEEPB q0 k i Hq0 Hi). }
    split.
    { intros a Ha. rewrite SEGS. pose proof (SW1 a Ha) as Wa.
      unfold lib_scratch in Ha. rewrite RG2, EV in Ha. unfold SLOT_STACK in *.
      exact (proj1 (proj2 (K2 a ltac:(lia) ltac:(lia))) Wa). }
    split; [reflexivity|]. split; [reflexivity|]. split; [exact X7|].
    split.
    { apply (se_sink_keep mem0 mem2 md0 md1).
      - intros a Hi Hs Hc He Hg. exact (proj1 (IMGK a Hi Hs Hc He Hg)).
      - rewrite Hmdx. apply se_fds_vm.
      - exact X5. }
    split; [rewrite SEGS; exact RO2|].
    split.
    { rewrite F28. apply (SlotInv.res_end L1 A1 L0 A0 b W1' RCAP1 (se_NODUP L1 A1 mem2 md1 M2) (se_NODUP L0 A0 mem0 md0 P0)).
      - intros pn. split; [apply BLK1' | intros Hp; destruct pn as [a k]; exact (proj1 (EB1' a k Hp))].
      - exact X3.
      - exact (proj2 (proj2 (F29 b n0 X4))). }
    { intros i Hi. rewrite SEGS. destruct P13 as [[Hn Hp]|[Hn (q0 & Hq0 & Hp0)]]; [lia|].
      rewrite <- Hp0. exact (KEEPB q0 n0 i Hq0 Hi). }
  - destruct (se_rep_gi4 L1 A1 mem1 (rec_clear R) O1 REP1 eq_refl eq_refl eq_refl eq_refl SPILL) as (Z1 & Z2 & Z3 & Z4).
    unfold Slot.GI_cmd, Slot.zero_at, Slot.G_REC_A, Slot.G_SPILL, Slot.G_QUIT_A in *.
    split; [|split; [|split; [|split]]].
    { intros i Hi. rewrite (proj1 (K2 (0x33d48 + 8 + i) ltac:(lia) ltac:(lia))). apply Z1. lia. }
    { intros i Hi. rewrite (proj1 (K2 (0x33d48 + 912 + i) ltac:(lia) ltac:(lia))). apply Z2. lia. }
    { intros i Hi. rewrite (proj1 (K2 (0x33d48 + 928 + i) ltac:(lia) ltac:(lia))). apply Z3. lia. }
    { intros i Hi. rewrite (proj1 (K2 (0x33d10 + i) ltac:(lia) ltac:(lia))). apply Z4. lia. }
    intros i Hi. pose proof (KindB.rw_cells_of_rel rsegs mem2 m' _ _ REL QC) as QC2.
    destruct QC2 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
    exact (SlotRec.bytes_zero_le4 _ _ Hb i Hi).
Qed.

Hypothesis GI0 : Slot.GI_cmd j mem0.
Hypothesis GIMG0 : G_img_c B frame_RELRO mem0.
Hypothesis RO0 : ro_agree rsegs mem0.
Hypothesis FZ0 : frm_zero (@fp_csr fxs).

Definition se_final (c' : config) : Prop :=
  exists (fx' : FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom rsegs)) md' /\ frm_zero (@fp_csr fx') /\
    lib_post_g (LS := LS) (SH := SH) (SK := SK) B (API rc) Slot.G_cmd SLOT_STACK L0 A0 rg mem0 md0 p0 n0 b
      (LL 0 (m_fs md0) []) L' A' regs' mem' md' /\ Slot.GI_cmd (Datatypes.S j) mem'.

(* From the slot's entry (0x14048): the size refusal returns at once; otherwise the prologue, the first rec_clear
   and the initialisation lead to the loop head of message 0 or (no input) to the last rec_clear. *)
Lemma start_ok :
  SR rsegs (mkCfg (@mkst fxs rg (Z_to_bv 64 ENTRY) mem0 (seg_rom rsegs)) md0)
    (fun c' => se_final c' \/ SlotIter.head_at B (API rc) S rg mem0 md0 L0 A0 p0 n0 0 c' \/
               SlotIter.exit_at B (API rc) S rg mem0 md0 L0 A0 c').
Proof.
  pose proof se_SEGS as SEGS. pose proof se_ERRNO as ERRNO. pose proof se_AX as AX. pose proof se_HS as HS.
  pose proof se_S16 as S16. pose proof se_errno_v as EV. pose proof alloc_ceiling_val as AC.
  pose proof alloc_ceiling_lt as ACL.
  pose proof PRE as ((P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14) &
    X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8).
  pose proof FG as FG'. fg_destruct FG'.
  destruct (mr_model B _ (aa_laws (API rc)) _ _ _ _ P0) as (Hh0 & Hl0 & Hmt0).
  assert (SPR : bv_unsigned (reg_get rg 2) = S) by exact RG2.
  assert (HN0 : 0 <= n0 < 2 ^ 47).
  { destruct P13 as [[-> _]|[Hn (q0 & Hq0 & Hp0)]]; [lia|].
    destruct (mr_blocks_range B _ (aa_laws (API rc)) L0 A0 mem0 md0 q0 n0 P0 Hq0) as [H4 Hc]. lia. }
  assert (A11 : bv_unsigned (reg_get rg 11) = n0).
  { change (reg_get rg 11) with (getr rg 11). rewrite P12. apply unsigned_lit. lia. }
  assert (STK0 : stk rsegs (normalize rsegs mem0) (S - SLOT_STACK) S).
  { apply RecAns.stk_normalize; [unfold SLOT_STACK in *; lia | lia |].
    intros a Ha. rewrite <- SEGS. apply P8. rewrite RG2. exact Ha. }
  assert (W0 : forall a, lib_scratch B SLOT_STACK rg a -> writable_at rsegs mem0 a).
  { intros a Ha. rewrite <- SEGS. destruct Ha as [Ha|Ha]; [apply P8; exact Ha | apply P10; exact Ha]. }
  assert (LOW : forall a, 0 <= a < alloc_ceiling -> ~ (S - 176 <= a < S)) by (intros a Ha; unfold SLOT_STACK in *; lia).
  unfold ENTRY.
  destruct (Z_lt_ge_dec n0 (2 ^ 26)) as [HSM|HBG].
  2:{
    eapply (sr_run rg (Z_to_bv 64 0x14048) mem0 md0 _ _ Hh0 Hl0 RO0).
    { unfold Regs6ss.mkR_of. eapply run_big_ok with (lo := S - SLOT_STACK).
      - apply mem_inv_normalize.
      - rewrite SPR. exact STK0.
      - rewrite SPR. unfold SLOT_STACK in *. lia.
      - unfold CommandModel.IMG_END, SLOT_STACK in *. lia.
      - rewrite A11. lia. }
    { intros s0 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
      do 5 eexists. reflexivity. }
    intros R0 F' pc' fc' m0' regs2 mem2
      (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI)
      REL ROS GR.
    injection E as ER EF Epc Efc Em. subst R0 F' pc' fc' m0'.
    apply SR_ret. left.
    rewrite SPR in MU.
    assert (MU2 : munch [(S - 176, S)] mem0 mem2)
      by exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem0 RO0) REL ROS MU).
    assert (WM2 : wmono rsegs mem0 mem2)
      by exact (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem0 RO0) REL ROS WM).
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 176 <= a < S) ->
       mbyte rsegs mem2 a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem2 a)).
    { intros a Ha Hx. assert (Ho : outside [(S - 176, S)] a) by (cbn; split; [exact Hx | exact Logic.I]).
      split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU2 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU2 Ha Ho)]. }
    assert (KP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 176 <= a < S) -> present mem0 a -> present mem2 a).
    { intros a Ha Hx. apply (KindB.munch_present _ _ _ a MU2 Ha). cbn; split; [exact Hx | exact Logic.I]. }
    pose proof (ro_agree_same rsegs _ _ RO0 ROS) as RO2.
    assert (M2 : aa_MR (API rc) L0 A0 mem2 md0).
    { apply (mr_frame B _ (aa_laws (API rc)) L0 A0 mem0 mem2 md0 md0 P0).
      - intros a Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L0 A0 mem0 md0 a P0 Ho) as Hl.
        rewrite SEGS. exact (proj1 (K2 a ltac:(lia) (LOW a Hl))).
      - intros a Ho Hp. pose proof (mr_owned_low B _ (aa_laws (API rc)) L0 A0 mem0 md0 a P0 Ho) as Hl.
        exact (KP2 a ltac:(lia) (LOW a Hl) Hp).
      - intros p n i Hin Hi. destruct (mr_blocks B _ (aa_laws (API rc)) L0 A0 mem0 md0 p n i P0 Hin Hi) as (Hp & H4 & Hc & _).
        exact (KP2 (ptr_addr L0 p + i) ltac:(lia) (LOW (ptr_addr L0 p + i) ltac:(lia)) Hp).
      - reflexivity.
      - exact Hh0.
      - exact Hl0.
      - exact Hmt0. }
    assert (KEEPB : forall q k i, In (q, k) (user_blocks A0) -> 0 <= i < k ->
       mbyte rsegs mem2 (ptr_addr L0 q + i) = mbyte rsegs mem0 (ptr_addr L0 q + i)).
    { intros q0 k i Hq0 Hi.
      destruct (mr_blocks B _ (aa_laws (API rc)) L0 A0 mem0 md0 q0 k i P0 Hq0 Hi) as (_ & H4 & Hc & _).
      exact (proj1 (K2 (ptr_addr L0 q0 + i) ltac:(lia) (LOW (ptr_addr L0 q0 + i) ltac:(lia)))). }
    assert (IMGK : forall a, in_img B a -> mbyte rsegs mem2 a = mbyte rsegs mem0 a /\
       (writable_at rsegs mem0 a <-> writable_at rsegs mem2 a)).
    { intros a Hi. pose proof (KindB.in_img_low B SEGS a Hi) as Hl. exact (K2 a ltac:(lia) (LOW a ltac:(lia))). }
    do 6 eexists. split.
    { change (reg_get rg 1) with (getr rg 1). rewrite P4, (se_ret_pc ra F1). reflexivity. }
    split; [exact FZ0|].
    split.
    - split; [exact M2|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
      split; [rewrite GR; reflexivity|].
      split.
      { intros r Hr. rewrite GR. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r; reflexivity. }
      split.
      { exists (m_vmmaps md0), (m_fds md0), (m_statpins md0). split; [exact (os_upd_self md0) | intros k; reflexivity]. }
      split.
      { intros q0 k Hq0. exists q0. split; [exact Hq0 | reflexivity]. }
      split.
      { intros a Ha Hs. unfold lib_scratch in Hs. rewrite RG2 in Hs. rewrite SEGS.
        apply (K2 a ltac:(lia)). intros Hx. apply Hs. left. unfold SLOT_STACK. lia. }
      split.
      { intros a Hi Hs Hc He Hg. rewrite SEGS. exact (IMGK a Hi). }
      split.
      { intros a Hg. pose proof (se_g_iv a Hg) as Hr. rewrite SEGS. split; intros _; apply SlotRec.g_writable; lia. }
      split.
      { intros q0 k i Hq0 _ Hi. rewrite SEGS. exact (KEEPB q0 k i Hq0 Hi). }
      split.
      { intros a Ha. rewrite SEGS. apply WM2. exact (W0 a Ha). }
      split; [reflexivity|]. split; [reflexivity|]. split; [exact X7|].
      split.
      { apply (se_sink_keep mem0 mem2 md0 md0).
        - intros a Hi Hs Hc He Hg. exact (proj1 (IMGK a Hi)).
        - reflexivity.
        - exact X5. }
      split; [rewrite SEGS; exact RO2|].
      split; [rewrite F28; exact X3|].
      { intros i Hi. rewrite SEGS. destruct P13 as [[Hn Hp]|[Hn (q0 & Hq0 & Hp0)]]; [lia|].
        rewrite <- Hp0. exact (KEEPB q0 n0 i Hq0 Hi). }
    - assert (KG : forall a, in_globals Slot.G_cmd a -> mbyte (ms_segs B) mem2 a = mbyte (ms_segs B) mem0 a).
      { intros a Ha. pose proof (se_g_iv a Ha). rewrite SEGS. exact (proj1 (K2 a ltac:(lia) (LOW a ltac:(lia)))). }
      exact (Slot.GI_cmd_local B SEGS j mem0 mem2 KG GI0). }
  eapply (sr_run rg (Z_to_bv 64 0x14048) mem0 md0 _ _ Hh0 Hl0 RO0).
  { unfold Regs6ss.mkR_of. eapply run_pro_ok with (lo := S - SLOT_STACK).
    - apply mem_inv_normalize.
    - rewrite SPR. exact STK0.
    - rewrite SPR. unfold SLOT_STACK in *. lia.
    - unfold CommandModel.IMG_END, SLOT_STACK in *. lia.
    - rewrite A11. exact HSM. }
  { intros s0 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & jl & -> & _).
    do 5 eexists. reflexivity. }
  intros R0 F' pc' fc' m0' regs1 mem1
    (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & jl & E & MU & WM & MI
     & JL & SVc) REL ROS GR.
  injection E as ER EF Epc Efc Em. subst R0 F' pc' fc' m0'.
  rewrite SPR in MU, JL, SVc.
  assert (MU1 : munch [(S - 176, S)] mem0 mem1)
    by exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem0 RO0) REL ROS MU).
  assert (WM1 : wmono rsegs mem0 mem1)
    by exact (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem0 RO0) REL ROS WM).
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 176 <= a < S) ->
     mbyte rsegs mem1 a = mbyte rsegs mem0 a /\ (writable_at rsegs mem0 a <-> writable_at rsegs mem1 a)).
  { intros a Ha Hx. assert (Ho : outside [(S - 176, S)] a) by (cbn; split; [exact Hx | exact Logic.I]).
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU1 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU1 Ha Ho)]. }
  assert (KP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (S - 176 <= a < S) -> present mem0 a -> present mem1 a).
  { intros a Ha Hx. apply (KindB.munch_present _ _ _ a MU1 Ha). cbn; split; [exact Hx | exact Logic.I]. }
  pose proof (ro_agree_same rsegs _ _ RO0 ROS) as RO1.
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ REL JL) as JL1.
  pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ REL SVc) as SV1.
  assert (M1 : aa_MR (API rc) L0 A0 mem1 md0).
  { apply (mr_frame B _ (aa_laws (API rc)) L0 A0 mem0 mem1 md0 md0 P0).
    - intros a Ho. pose proof (mr_owned_low B _ (aa_laws (API rc)) L0 A0 mem0 md0 a P0 Ho) as Hl.
      rewrite SEGS. exact (proj1 (K1 a ltac:(lia) (LOW a Hl))).
    - intros a Ho Hp. pose proof (mr_owned_low B _ (aa_laws (API rc)) L0 A0 mem0 md0 a P0 Ho) as Hl.
      exact (KP1 a ltac:(lia) (LOW a Hl) Hp).
    - intros p n i Hin Hi. destruct (mr_blocks B _ (aa_laws (API rc)) L0 A0 mem0 md0 p n i P0 Hin Hi) as (Hp & H4 & Hc & _).
      exact (KP1 (ptr_addr L0 p + i) ltac:(lia) (LOW (ptr_addr L0 p + i) ltac:(lia)) Hp).
    - reflexivity.
    - exact Hh0.
    - exact Hl0.
    - exact Hmt0. }
  assert (CF0 : SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 (mkFP (@fp_regs fxs) (@fp_csr fxs)) L0 A0 regs1 mem1 md0).
  { split; [exact M1|]. split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exists (m_vmmaps md0); symmetry; apply KindBGlue.kb_vm_id|].
    split.
    { rewrite GR. transitivity (Z_to_bv 64 (bv_unsigned (reg_get rg 2) - 176)); [reflexivity|]. rewrite SPR. reflexivity. }
    split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
    split.
    { replace (SlotInv.FB S + 72) with (S - 104) by (unfold SlotInv.FB; lia). exact SV1. }
    split.
    { intros a Ha. apply WM1. exact (W0 a Ha). }
    split.
    { split.
      - intros a Ha Hs. unfold lib_scratch in Hs. rewrite RG2 in Hs.
        apply (K1 a ltac:(lia)). intros Hx. apply Hs. left. unfold SLOT_STACK. lia.
      - intros a Hi Hs Hc He Hg. pose proof (KindB.in_img_low B SEGS a Hi) as Hl.
        exact (K1 a ltac:(lia) (LOW a ltac:(lia))). }
    split; [exact RO1|].
    split.
    { intros a Ha. pose proof (se_relro_iv a Ha). rewrite <- (GIMG0 a Ha). rewrite SEGS.
      exact (proj1 (K1 a ltac:(lia) (LOW a ltac:(lia)))). }
    split.
    { intros a k Hin. split; [exact Hin|]. intros i Hi.
      unfold blocks in Hin. apply in_map_iff in Hin as ([q k'] & Eq & Hq). cbn in Eq. injection Eq as <- <-.
      destruct (mr_blocks B _ (aa_laws (API rc)) L0 A0 mem0 md0 q k' i P0 Hq Hi) as (_ & H4 & Hc & _).
      exact (proj1 (K1 (ptr_addr L0 q + i) ltac:(lia) (LOW (ptr_addr L0 q + i) ltac:(lia)))). }
    exact FZ0. }
  assert (GI1 : Slot.GI_cmd j mem1).
  { assert (KG : forall a, in_globals Slot.G_cmd a -> mbyte (ms_segs B) mem1 a = mbyte (ms_segs B) mem0 a).
    { intros a Ha. pose proof (se_g_iv a Ha). rewrite SEGS. exact (proj1 (K1 a ltac:(lia) (LOW a ltac:(lia)))). }
    exact (Slot.GI_cmd_local B SEGS j mem0 mem1 KG GI0). }
  destruct (SlotRec.gi_rep j L0 A0 mem1 GI1) as (Rr & REP0 & C0 & AN0 & RP0 & NR0 & SP0).
  assert (QB1 : bytes_at rsegs mem1 0x34108 (le4 (Z_to_bv 64 0))).
  { rewrite SlotRec.le4_0. destruct GI1 as (_ & _ & _ & _ & Z5). unfold Slot.G_QUIT_A in Z5.
    apply (SlotRec.zero_bytes mem1 0x34108 4 0x34108 4 Z5); lia. }
  assert (R1a : getr regs1 1 = Z_to_bv 64 0x14094) by (rewrite GR; reflexivity).
  apply (se_rc_step (mkFP (@fp_regs fxs) (@fp_csr fxs)) L0 A0 regs1 mem1 md0 Rr [] _ CF0 REP0 SP0).
  { exists b. split; [exact X3 | exact (proj2 (proj2 (F29 b n0 X4)))]. }
  { intros a k _ []. }
  { intros pn Hp. left. exact Hp. }
  { rewrite R1a. apply bv_eq. vm_compute. reflexivity. }
  intros L1 A1 regs2 mem2 md1 O1 CF1 REP1 HE1 BLK1' RCAP1 PRES GDK HIF.
  rewrite R1a.
  pose proof CF1 as (M2 & W2 & Bd2 & I2 & (vm2 & Hmd2) & R22 & R32 & R42 & SV2 & SW2 & SF2 & RO2 & GIm2 & EB2 & FZ2).
  destruct (mr_model B _ (aa_laws (API rc)) _ _ _ _ M2) as (Hh2 & Hl2 & Hmt2).
  assert (SP2 : bv_unsigned (reg_get regs2 2) = SlotInv.FB S).
  { change (reg_get regs2 2) with (getr regs2 2). rewrite R22. apply unsigned_lit.
    unfold SlotInv.FB, SLOT_STACK in *. lia. }
  assert (JL2 : rw_cells rsegs mem2 (SlotInv.FB S) [CB 72 jl]).
  { apply (KindB.rw_cells_transfer rsegs mem1). { replace (SlotInv.FB S) with (S - 176) by reflexivity. exact JL1. }
    intros i Hi. cbn in Hi. destruct (HIF (SlotInv.FB S + i)) as [E1 W1x].
    - unfold SlotInv.FB, SLOT_STACK in *. lia.
    - unfold SlotInv.FB, SLOT_STACK, RCL_K, RCF_K, ALLOC_STACK in *. lia.
    - split; [exact E1 | exact (proj1 W1x)]. }
  apply (rw_cells_split_CB rsegs mem2 (SlotInv.FB S) [] 72 jl [] [40; 32]%nat) in JL2; [| reflexivity].
  cbn [mk_CB_cells app] in JL2.
  destruct (sr_app_split mem2 (SlotInv.FB S) [CB 40 (firstn 40 jl)] [CB 32 (firstn 32 (skipn 40 jl))] JL2) as [JLa JLb].
  cbn [cells_size csize] in JLb.
  assert (SHB : bytes_at rsegs mem2 (0x33d48 + 944) (le8 (Z_to_bv 64 (r_state Rr)) ++ le8 (Z_to_bv 64 (r_host Rr)))).
  { destruct REP1 as (Q1 & (_ & _ & _ & _ & (_ & _ & _ & Y4 & Y5 & _) & _) & _).
    unfold G_REC, OFF_STATE, OFF_HOST in Y4, Y5.
    apply Mem.bytes_at_app. split; [exact Y4|]. rewrite Mem.length_le8. exact Y5. }
  assert (SHR : rw_cells rsegs mem2 (0x33d48 + 944) [CB 16 (le8 (Z_to_bv 64 (r_state Rr)) ++ le8 (Z_to_bv 64 (r_host Rr)))]).
  { split; [split|].
    - split; [| exact Logic.I].
      change (length (le8 (Z_to_bv 64 (r_state Rr)) ++ le8 (Z_to_bv 64 (r_host Rr))) = 16%nat).
      rewrite length_app, !Mem.length_le8. reflexivity.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact SHB.
    - cbn [cells_size csize]. apply SlotRec.g_wr_at; lia. }
  apply (KindB.rw_cells_normalize rsegs _ _ _ RO2) in SHR; [| intros i Hi; cbn in Hi; apply se_g_not_ro; lia].
  pose proof JLa as JLan.
  apply (KindB.rw_cells_normalize rsegs _ _ _ RO2) in JLan;
    [| intros i Hi; cbn in Hi; apply ro_addr_hi; unfold SlotInv.FB, SLOT_STACK in *; lia].
  assert (H : forall a, in_globals frame_RELRO a -> mbyte rsegs mem2 a = seg_rom rsegs (Z_to_bv 64 a))
    by (intros a Ha; rewrite <- SEGS; exact (GIm2 a Ha)).
  destruct (SlotRec.relro_img mem2 H) as (G1 & G2 & G3 & _).
  apply (bytes_at_normalize rsegs mem2) in G1; [|exact RO2].
  apply (bytes_at_normalize rsegs mem2) in G2; [|exact RO2].
  apply (bytes_at_normalize rsegs mem2) in G3; [|exact RO2].
  eapply (sr_run regs2 (Z_to_bv 64 0x14094) mem2 md1 _ _ Hh2 Hl2 RO2).
  { unfold Regs6ss.mkR_of. eapply run_init_ok.
    - apply mem_inv_normalize.
    - rewrite SP2. unfold SlotInv.FB, SLOT_STACK, CommandModel.IMG_END in *. lia.
    - rewrite SP2. unfold SlotInv.FB in *. lia.
    - exact G1.
    - exact G2.
    - exact G3.
    - exact SHR.
    - rewrite SP2. exact JLan. }
  { intros s0 (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3' & jl' & jsv
      & _ & _ & _ & _ & _ & [[_ ->]|[_ [_ ->]]]); do 5 eexists; reflexivity. }
  intros R0 F' pc' fc' m0' regs3 mem3
    (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m3' & jl' & jsv
     & MUi & WMi & MIi & GS & JLx & BR) RELi ROSi GR3.
  assert (Em0 : m0' = m3') by (destruct BR as [[_ E]|[_ [_ E]]]; injection E; intros; assumption).
  subst m0'.
  rewrite SP2 in MUi, JLx.
  assert (MU3 : munch [(SlotInv.FB S, SlotInv.FB S + 24); (G_REC + 944, G_REC + 960)] mem2 mem3).
  { exact (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs mem2 RO2) RELi ROSi MUi). }
  assert (WM3 : wmono rsegs mem2 mem3)
    by exact (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs mem2 RO2) RELi ROSi WMi).
  pose proof (ro_agree_same rsegs _ _ RO2 ROSi) as RO3.
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (SlotInv.FB S <= a < SlotInv.FB S + 24) ->
     ~ (0x33d48 + 944 <= a < 0x33d48 + 960) ->
     mbyte rsegs mem3 a = mbyte rsegs mem2 a /\ (writable_at rsegs mem2 a <-> writable_at rsegs mem3 a)).
  { intros a Ha Hx Hy. assert (Ho : outside [(SlotInv.FB S, SlotInv.FB S + 24); (G_REC + 944, G_REC + 960)] a)
      by (cbn; unfold G_REC; split; [exact Hx | split; [exact Hy | exact Logic.I]]).
    split; [exact (KindB.munch_mbyte rsegs _ _ _ a MU3 Ha Ho) | exact (KindB.munch_writable rsegs _ _ _ a MU3 Ha Ho)]. }
  assert (CF3 : forall fx' regs', frm_zero (@fp_csr fx') ->
     getr regs' 2 = getr regs2 2 -> getr regs' 3 = getr regs2 3 -> getr regs' 4 = getr regs2 4 ->
     SlotInv.CF B (API rc) S rg mem0 md0 L0 A0 fx' L1 A1 regs' mem3 md1).
  { intros fx' regs' FZ' E2 E3 E4.
    apply (SlotInv.cf_run B (API rc) S rg mem0 md0 L0 A0 SEGS ERRNO AX HS RG2 se_GFREE se_GNOWN
             (mkFP (@fp_regs fxs) (@fp_csr fxs)) fx' L1 A1 regs2 mem2 md1 _ mem3 regs' CF1 MU3 WM3 RO3).
    - intros a Ha Ho. cbn in Ho. unfold G_REC, SlotInv.FB, SLOT_STACK in *.
      destruct (Z_lt_ge_dec a 0x40000) as [Hs|Hs]; [right; left; apply se_g_of; lia | left; lia].
    - intros p n i Hin Hi Hno. exfalso.
      destruct (mr_blocks B _ (aa_laws (API rc)) L1 A1 mem2 md1 p n i M2 Hin Hi) as (_ & H4 & Hc & _).
      apply Hno. cbn [outside]. unfold G_REC. split; [unfold SlotInv.FB, SLOT_STACK in *; lia|]. split; [|exact Logic.I].
      intros Hx. apply (ax_blocks_img AX L1 A1 mem2 md1 p n i M2 Hin Hi).
      exact (proj1 (se_GFREE _ (se_g_of (ptr_addr L1 p + i) ltac:(lia)))).
    - exact FZ'.
    - exact E2.
    - exact E3.
    - exact E4. }
  assert (GS3 : bytes_at rsegs mem3 (0x33d48 + 944) (le8 (Z_to_bv 64 0) ++ le8 (Z_to_bv 64 0))).
  { pose proof (KindB.rw_cells_of_rel rsegs _ _ _ _ RELi GS) as GS1. destruct GS1 as [[_ Hb] _].
    cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (REP3 : g_rec_rep rsegs L1 A1 mem3 (set_host (set_state (rec_clear Rr) 0) 0) O1).
  { apply (se_rep_set_sh L1 A1 mem2 mem3 (rec_clear Rr) O1 REP1 HE1 GS3).
    intros a Ha. exact (proj1 (K3 a ltac:(lia) ltac:(unfold SlotInv.FB, SLOT_STACK in *; lia) ltac:(lia))). }
  assert (QB3 : bytes_at rsegs mem3 0x34108 (le4 (Z_to_bv 64 0))).
  { apply (KindB.bytes_at_transfer rsegs mem2).
    - apply (KindB.bytes_at_transfer rsegs mem1). { exact QB1. }
      intros i Hi. rewrite Mem.length_le4 in Hi. apply GDK; [exact (se_g_of (0x34108 + i) ltac:(lia))|].
      intros Hw. unfold rec_clear_writes, nargs_field in Hw.
      unfold G_REC, OFF_NCALLS, OFF_CALLS, OFF_ANSWER, OFF_NREPLIES, OFF_REPLY, OFF_REPLY_SIZE in Hw.
      destruct Hw as [Hw|[(k & Hk & Hw)|[Hw|Hw]]]; lia.
    - intros i Hi. rewrite Mem.length_le4 in Hi.
      exact (proj1 (K3 (0x34108 + i) ltac:(lia) ltac:(unfold SlotInv.FB, SLOT_STACK in *; lia) ltac:(lia))). }
  assert (RF3 : SlotInv.RF L0 A0 L1 A1 mem3 (set_host (set_state (rec_clear Rr) 0) 0) O1 0).
  { split; [exact REP3|]. split; [exact SP0|]. split; [exact QB3|]. split; [lia|].
    split; [intros a k _ Ha; apply in_map_iff in Ha as (xo & _ & Hxo); exact (HE1 xo Hxo)|].
    intros pn Hp. left. exact (BLK1' pn Hp). }
  assert (R23 : reg_get regs2 23 = Z_to_bv 64 n0)
    by exact (eq_trans (PRES 23 ltac:(unfold callee_saved; lia)) (eq_trans (GR (Z_to_bv 5 23)) P12)).
  assert (R18 : reg_get regs2 18 = Z_to_bv 64 p0)
    by exact (eq_trans (PRES 18 ltac:(unfold callee_saved; lia)) (eq_trans (GR (Z_to_bv 5 18)) P11)).
  destruct BR as [[Hs7 E]|[Hs7 [LC E]]];
    injection E as ER EF Epc Efc; subst R0 F' pc' fc'; apply SR_ret; right.
  - right. do 9 eexists. split; [reflexivity|].
    split; [apply CF3; [exact FZ2 | rewrite GR3; reflexivity | rewrite GR3; reflexivity | rewrite GR3; reflexivity]|].
    split; [exact RF3|]. split; [exact RCAP1|]. rewrite GR3. reflexivity.
  - left. do 11 eexists. split; [reflexivity|].
    rewrite R23, unsigned_lit in Hs7 by lia.
    split; [apply CF3; [exact FZ2 | rewrite GR3; reflexivity | rewrite GR3; reflexivity | rewrite GR3; reflexivity]|].
    split; [exact RF3|]. split; [exact RCAP1|].
    split; [destruct O1 as [|xo O1']; [cbn; unfold SlotInv.O_MAX; lia | exfalso; exact (HE1 xo (or_introl eq_refl))]|].
    split; [rewrite GR3; reflexivity|].
    split; [rewrite GR3; exact R18|]. split; [rewrite GR3; exact R23|].
    split; [rewrite GR3; reflexivity|]. split; [rewrite GR3; reflexivity|].
    split.
    { exists jsv, (firstn 32 (skipn 40 jl)). split.
      - rewrite SP2 in LC. exact (KindB.rw_cells_of_rel rsegs _ _ _ _ RELi LC).
      - apply (KindB.rw_cells_transfer rsegs mem2). { exact JLb. }
        intros i Hi. cbn in Hi. destruct (K3 (SlotInv.FB S + Z.of_nat 40 + i)) as [E1 W1x].
        + unfold SlotInv.FB, SLOT_STACK in *. lia.
        + lia.
        + unfold SlotInv.FB, SLOT_STACK in *. lia.
        + split; [exact E1 | exact (proj1 W1x)]. }
    lia.
Qed.

End End.
