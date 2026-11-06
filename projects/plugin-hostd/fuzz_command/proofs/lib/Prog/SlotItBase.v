From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes MState.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05 YL0i YL0g YL01 YL00 YI14 YI16 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Contract FrameAPI MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require KindBGlue BlocksNodup.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import KindB RecFacts RecModel RecInv RecInvP
  SlotSpec SlotGlue HarnessProps SlotCallees SlotIter SlotEnd.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Slot SlotInv SlotRec RecAns RecAnsB send_message.
Import ListNotations.
Local Open Scope Z_scope.

(* The context of one iteration of the message loop of the entry function (plain 0x14048): the premises of
   SlotIter.iter_spec, the SR lift of a Kind A run on the memory normalized to the task's addresses, and the
   call premises that the walk invariant CF gives at the frame base. *)

Section Bridge.
Context {fx : FPState}.

Lemma sr_cj : forall regs pc mem md (P : config -> Prop) (Q : machine_state -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize_cj rsegs mem) (seg_rom rsegs)) ->
  (forall s0, Q s0 -> exists R F' pc' fc' m0, s0 = MS R F' pc' fc' None m0 (seg_rom rsegs)) ->
  (forall R F' pc' fc' m0 regs' mem',
     Q (MS R F' pc' fc' None m0 (seg_rom rsegs)) -> mem_rel_cj rsegs mem' m0 -> cj_same rsegs mem mem' ->
     (forall r, getr regs' r = getr R r) ->
     SR rsegs (mkCfg (@mkst (mkFP F' fc') regs' pc' mem' (seg_rom rsegs)) md) P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md P Q Hh Hl RO EV SHAPE K.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RO | exact EV]. }
  intros ms' (can & (s0 & Q0 & REL & ROS) & EQ).
  destruct (SHAPE s0 Q0) as (R & F' & pc' & fc' & m0 & ->).
  destruct (RecAns.ms_rel_cj_MS _ _ _ _ _ _ _ _ REL) as [CAN HR].
  remember (ms_mem can) as mc eqn:Emc. subst can. clear Emc.
  destruct (RecAnsB.eqv_mkst_fx R F' pc' fc' mc (seg_rom rsegs) ms' EQ) as (R' & -> & X).
  apply (K R F' pc' fc' m0 R' mc Q0 HR ROS).
  intros r. exact (KindBGlue.kb_getr_eqv R R' X r).
Qed.

End Bridge.

Section It.
Context {rc : RunCeil}.
Variables (B : malloc_syms) (API : forall rc : RunCeil, AllocAPI B) (LS : lib_shape) (SH : sink_head)
  (SK : sink_syms) (ra empty : Z) (S : Z) (rg : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (L0 : layout) (A0 : astate) (p0 n0 : Z) (pl : list byte) (b : sbound).
Hypothesis FG : Slot.frame_given B API LS SH SK ra empty.
Hypothesis PRE : lib_pre_x (LS := LS) (SH := SH) (SK := SK) B (API rc) SLOT_STACK empty L0 A0 rg mem0 md0 ra p0 n0 pl b.
Hypothesis RG2 : spZ rg = S.

Notation CF := (SlotInv.CF B (API rc) S rg mem0 md0 L0 A0).
Notation FB := (SlotInv.FB S).

Lemma it_SEGS : ms_segs B = rsegs.
Proof. fg_destruct FG. exact F0. Qed.

Lemma it_HS : alloc_ceiling + SLOT_STACK <= S < 2 ^ 63.
Proof.
  destruct PRE as ((_ & _ & _ & _ & _ & _ & H6 & H7 & _) & _). rewrite <- RG2. split; assumption.
Qed.

Lemma it_S16 : S mod 16 = 0.
Proof. destruct PRE as ((_ & _ & _ & _ & _ & H5 & _) & _). rewrite <- RG2. exact H5. Qed.

Lemma it_TS : S <= TASK_SIZE.
Proof. rewrite <- RG2. exact (lib_pre_x_sp B (API rc) _ _ _ _ _ _ _ _ _ _ _ _ PRE). Qed.

Lemma it_tp : getr rg 4 = Z_to_bv 64 (ms_tp B).
Proof. destruct PRE as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & H & _) & _). exact H. Qed.

Lemma it_errno : errno_addr B = 0x3413c.
Proof. eapply se_errno_v; eassumption. Qed.

Lemma it_FA : forall fx : FPState, @frame_allocator rc fx B (API rc).
Proof. intros fx. eapply se_FA; eassumption. Qed.

Lemma it_spz : forall regs, getr regs 2 = Z_to_bv 64 FB -> spZ regs = FB.
Proof.
  intros regs H. pose proof it_HS. pose proof alloc_ceiling_val. unfold spZ. rewrite H. apply unsigned_lit.
  unfold SlotInv.FB, SLOT_STACK in *. lia.
Qed.

Lemma it_model : forall fx L A regs mem md, CF fx L A regs mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros fx L A regs mem md (HM & _). destruct (mr_model _ _ (aa_laws (API rc)) _ _ _ _ HM) as (Hh & Hl & _).
  split; assumption.
Qed.

(* A call made at the frame base with a stack need K at most the slot's stack below the frame. *)
Lemma it_pre : forall fx L A regs mem md K, CF fx L A regs mem md -> YK0s.ret_ok (getr regs 1) ->
  0 <= K <= SLOT_STACK - 176 -> call_pre_k B (aa_MR (API rc)) K L A regs mem md.
Proof.
  intros fx L A regs mem md K (HM & HW & HB & HI & _ & H2 & _ & H4 & _ & HS & _) Hr HK.
  pose proof it_HS as HSS. pose proof it_S16 as H16. pose proof (it_spz regs H2) as SP.
  pose proof alloc_ceiling_val as AC. pose proof it_SEGS as SEGS.
  unfold SlotInv.FB, SLOT_STACK in *.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact Hr|].
  rewrite SP. split; [replace (S - 176) with (S + (-11) * 16) by ring; rewrite Z.mod_add by lia; exact H16|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; rewrite SEGS; apply HS; left; rewrite RG2; lia|].
  split; [rewrite H4; exact it_tp|].
  split; [intros a Ha; rewrite SEGS; apply HS; right; exact Ha|].
  intros HF. rewrite HI in HF. discriminate.
Qed.

Lemma it_AX : forall fx : FPState, AllocExtra B (aa_MR (API rc)).
Proof. intros fx. destruct (it_FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma it_GNOWN : forall fx : FPState, forall L A mem md a, aa_MR (API rc) L A mem md -> in_globals SlotInv.G_cmd a ->
  ~ owned B L A a.
Proof. intros fx. destruct (it_FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma it_NODUP : forall fx : FPState, forall L A mem md, aa_MR (API rc) L A mem md -> List.NoDup (blocks L A).
Proof.
  intros fx L A mem md HM. destruct (it_FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & H & _).
  exact (SlotInv.blocks_nodup_list L A (H L A mem md HM)).
Qed.

Lemma it_GFREE : forall a, in_globals SlotInv.G_cmd a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Proof. eapply se_GFREE; eassumption. Qed.

Lemma it_ERRNO : errno_addr B + 4 <= alloc_ceiling.
Proof. eapply se_ERRNO; eassumption. Qed.

Lemma it_cf_run : forall fx fx' L A regs mem md W mem' regs',
  CF fx L A regs mem md -> munch W mem mem' -> wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a ->
     (S - SLOT_STACK <= a < FB + 72) \/ in_globals SlotInv.G_cmd a \/
     (a < alloc_ceiling /\ ~ in_img B a /\ ~ owned B L A a /\
      forall a0 k, In (a0, k) (blocks L0 A0) -> ~ (a0 <= a < a0 + k))) ->
  (forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ~ outside W (ptr_addr L p + i) ->
     present mem' (ptr_addr L p + i)) ->
  frm_zero (@fp_csr fx') ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  CF fx' L A regs' mem' md.
Proof.
  intros fx fx' L A regs mem md W mem' regs' HCF HMU HWM HRO HW HP HFZ H2 H3 H4.
  eapply SlotInv.cf_run with (fx := fx) (regs := regs) (mem := mem) (W := W).
  all: first [ exact HCF | exact HMU | exact HWM | exact HRO | exact HW | exact HP | exact HFZ | exact H2 | exact H3
             | exact H4 | exact it_SEGS | exact it_ERRNO | exact (it_AX fx) | exact it_HS | exact RG2 | exact it_GFREE
             | exact (it_GNOWN fx) | match goal with |- ?G => idtac "ITREM:" G; fail end ].
Qed.

Lemma it_cf_call : forall fx fx' K L A regs mem md (E : Z -> Prop) L' A' regs' mem' md' regs'',
  CF fx L A regs mem md ->
  aa_MR (API rc) L' A' mem' md' -> WF A' -> bounded A' -> st_init_done A' = true ->
  regs_preserved regs regs' -> (exists vm', md' = with_vmmaps vm' md) ->
  (forall a, (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a ->
     ~ scratch_k B K regs a -> ~ E a ->
     mbyte (ms_segs B) mem' a = mbyte (ms_segs B) mem a /\
     (writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) mem' a)) ->
  (forall a, scratch_k B K regs a -> writable_at (ms_segs B) mem' a) ->
  S - SLOT_STACK <= FB - K -> 0 <= K ->
  (forall a, E a -> in_globals SlotInv.G_cmd a \/ (a < alloc_ceiling /\ ~ in_img B a)) ->
  ro_agree rsegs mem' -> G_img_c B frame_RELRO mem' -> SlotInv.eblocks mem0 L0 A0 L' A' mem' ->
  frm_zero (@fp_csr fx') ->
  (forall r, getr regs'' r = getr regs' r) ->
  CF fx' L' A' regs'' mem' md'.
Proof.
  intros fx fx' K L A regs mem md E L' A' regs' mem' md' regs'' HCF HM HW HB HI HPR HVM HF HSC HK1 HK2 HE HRO HGI HEB
    HFZ HRR.
  eapply SlotInv.cf_call with (fx := fx) (K := K) (regs := regs) (mem := mem) (E := E) (regs' := regs').
  all: first [ exact HCF | exact HM | exact HW | exact HB | exact HI | exact HPR | exact HVM | exact HF | exact HSC
             | exact HK1 | exact HK2 | exact HE | exact HRO | exact HGI | exact HEB | exact HFZ | exact HRR
             | exact it_SEGS | exact it_ERRNO | exact (it_AX fx) | exact it_HS | exact RG2 | exact it_GFREE
             | exact (it_GNOWN fx) | match goal with |- ?G => idtac "ITREM2:" G; fail end ].
Qed.

(* The recorder's scalars and storage, and its blocks: live, at most LMAX + 2 bytes each. *)
Lemma it_rep_parts : forall L A mem R O, g_rec_rep rsegs L A mem R O ->
  g1_storage rsegs mem G_REC REC_SC /\ g1_scalars rsegs mem G_REC R.
Proof. intros L A mem R O (Q & (H1 & _ & _ & _ & H5 & _) & _). split; assumption. Qed.

Lemma it_rec_blk : forall segs L A mem R O pn, g_rec_rep segs L A mem R O -> In pn O ->
  In pn (blocks L A) /\ 0 < snd pn <= LMAX + 2.
Proof.
  intros segs L A mem R O pn (Q & HR & HO) Hin. apply HO in Hin.
  destruct HR as (_ & HC & HA & HP & _ & _). destruct HC as (_ & C2 & _ & C4 & C5 & _).
  assert (CP : forall a c P, call_at segs (blocks L A) mem a c P -> In pn P ->
                 In pn (blocks L A) /\ 0 < snd pn <= LMAX + 2).
  { intros a c P (_ & _ & Hl & _ & _ & _ & Hk) Hp.
    destruct (In_nth_error P pn Hp) as [k Ek].
    assert (Hk' : (k < length (snd c))%nat) by (rewrite <- Hl; apply nth_error_Some; rewrite Ek; discriminate).
    destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (Hk k s pn Es Ek) as (_ & _ & Hb & Hs & _). split; [exact Hb | lia]. }
  unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin|Hin].
  - apply in_concat in Hin as (P & HP0 & Hpn).
    destruct (In_nth_error _ _ HP0) as [i Ei].
    assert (Hi : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Ei; discriminate).
    destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
    exact (CP _ _ _ (proj1 (C4 i c P Ec Ei)) Hpn).
  - apply in_app_or in Hin as [Hin|Hin]; [exact (CP _ _ _ C5 Hin)|].
    apply in_app_or in Hin as [Hin|Hin].
    + revert HA Hin. unfold answer_at.
      destruct (r_answer R) as [t|]; destruct (l_answer Q) as [pn'|]; intros HA Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HA as (_ & _ & H3 & H4 & _). split; [exact H3 | lia].
    + revert HP Hin. unfold reply_at.
      destruct (r_reply R) as [y|]; destruct (l_reply Q) as [pn'|]; intros HP Hin; cbn [oblk In] in Hin;
        try contradiction.
      destruct Hin as [<-|[]]. destruct HP as (_ & _ & _ & H4 & H5 & H6 & _).
      destruct y as [|y0 y']; [exfalso; exact (H4 eq_refl)|]. cbn [length] in H6. split; [exact H5 | lia].
Qed.

(* g_rec.refuse and g_rec.code set, the rest of the memory kept (SlotRec.rep_set_rc with the kept range bounded). *)
Lemma it_set_rc : forall L A mem mem' R O rf cd,
  g_rec_rep rsegs L A mem R O -> -2^31 <= rf < 2^31 -> -2^31 <= cd < 2^31 ->
  Mem.bytes_at rsegs mem' 0x33d48 (Mem.le4 (Z_to_bv 64 rf)) ->
  Mem.bytes_at rsegs mem' (0x33d48 + 4) (Mem.le4 (Z_to_bv 64 cd)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (0x33d48 <= a < 0x33d48 + 8) -> mbyte rsegs mem' a = mbyte rsegs mem a) ->
  (forall pn, In pn O -> 0 <= fst pn /\ fst pn + snd pn <= 2 ^ 64) ->
  g_rec_rep rsegs L A mem'
    (RState rf cd (r_calls R) (r_spill R) (r_answer R) (r_nreplies R) (r_reply R) (r_state R) (r_host R)) O.
Proof.
  intros L A mem mem' R O rf cd (Q & HR & HO) Hrf Hcd B1 B2 K HB.
  exists Q. split; [|exact HO].
  assert (HR' := HR). destruct HR' as (_ & _ & _ & _ & (X1 & X2 & X3 & X4 & X5 & X6) & (_ & HW)).
  apply (SlotRec.rep_at_move rsegs (blocks L A) mem mem' G_REC REC_SC R _ Q HR).
  - apply SlotRec.g_wr_at; unfold G_REC, REC_SIZE; lia.
  - apply SlotRec.g_wr_at; unfold REC_SC, SC_SIZE; lia.
  - intros a Ha. apply K; unfold G_REC, REC_SC, SC_SIZE in Ha; lia.
  - intros pn i Hpn Hi. destruct (HB pn (proj2 (HO pn) Hpn)) as [Hb1 Hb2].
    apply K; [lia|]. destruct (HW pn Hpn) as [Ha _]. unfold iv_apart, G_REC, REC_SIZE in Ha. lia.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold g1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host].
    unfold G_REC, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
    refine (conj _ (conj B2 (conj _ (conj _ (conj _ _))))).
    + rewrite Z.add_0_r. exact B1.
    + apply (bytes_at_keep_in rsegs mem mem' (0x33d48 + 8) (0x33d48 + 960)); [exact X3 | lia | rewrite Mem.length_le4; lia |].
      intros x Hx. apply K; lia.
    + apply (bytes_at_keep_in rsegs mem mem' (0x33d48 + 8) (0x33d48 + 960)); [exact X4 | lia | rewrite Mem.length_le8; lia |].
      intros x Hx. apply K; lia.
    + apply (bytes_at_keep_in rsegs mem mem' (0x33d48 + 8) (0x33d48 + 960)); [exact X5 | lia | rewrite Mem.length_le8; lia |].
      intros x Hx. apply K; lia.
    + destruct X6 as (Y1 & Y2 & Y3 & Y4 & Y5). repeat split; lia.
Qed.

(* The tables verbs_receive reads: the GNU_RELRO image bytes and the guard words the allocator keeps. *)
Lemma it_vrt : forall fx : FPState, forall L A mem md, aa_MR (API rc) L A mem md -> G_img_c B frame_RELRO mem ->
  exists can, VerbsB.vr_tables B mem can.
Proof.
  intros fx L A mem md HM GI. pose proof it_SEGS as SEGS.
  destruct (ax_statics (it_AX fx) L A mem md HM) as (Hgot & (g & Hg & Hguard) & _).
  assert (GI' : forall x, in_globals frame_RELRO x -> mbyte rsegs mem x = seg_rom rsegs (Z_to_bv 64 x)).
  { intros x Hx. rewrite <- SEGS. exact (GI x Hx). }
  fg_destruct FG. rewrite SEGS, F8, F7 in Hgot. rewrite SEGS, F7 in Hguard.
  exists (Z_to_bv 64 g). unfold VerbsB.vr_tables.
  split; [|split; [|split]].
  - apply (send_message.sm_le_of_bytes B mem _ _ SEGS).
    apply (SlotRec.relro_bytes mem _ _ GI'); [unfold VerbsB.IV_TABLE_B; lia | vm_compute; congruence | vm_compute; reflexivity].
  - apply (send_message.sm_le_of_bytes B mem _ _ SEGS).
    apply (SlotRec.relro_bytes mem _ _ GI'); [unfold VerbsB.INFO_TABLE; lia | vm_compute; congruence | vm_compute; reflexivity].
  - apply (send_message.sm_le_of_bytes B mem _ _ SEGS). unfold VerbsB.SSP_GOT_B, VerbsB.SSP_GUARD_B.
    apply (KindBGlue.word_mem_le8 rsegs mem 0x22a68 0x54450 Hgot); lia.
  - apply (send_message.sm_le_of_bytes B mem _ _ SEGS). unfold VerbsB.SSP_GUARD_B.
    apply (KindBGlue.word_mem_le8 rsegs mem 0x54450 g Hguard); lia.
Qed.

End It.
