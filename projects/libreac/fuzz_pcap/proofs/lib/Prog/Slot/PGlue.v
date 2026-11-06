From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Cells.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import Img0 Contract FrameAPI OutForm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import StdioModel.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PInv PTac PSROcf.
Import ListNotations.
Open Scope Z_scope.

Lemma sg_bytes_nth : forall segs (m : word -> option byte) a bs, bytes_at segs m a bs ->
  forall i, (i < length bs)%nat -> mbyte segs m (a + Z.of_nat i) = nth_error bs i.
Proof. intros segs m a bs (_ & _ & H) i Hi. exact (H i Hi). Qed.

Section Glue.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.
Local Abbreviation API := (APIf rc).
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR (APIf rc)).

Lemma sg_segs : ms_segs B = rsegs.
Proof. destruct FF as (H & _). exact H. Qed.

Lemma sg_md : forall L A mem md, MR L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof. intros L A mem md H. exact (KindBGlue.kb_md B API L A mem md H). Qed.

(* A cut at pc with remaining output o. *)
Lemma cut_open : forall g pc km hb P c o (Q : config -> Prop),
  CUTST B APIf ra empty g pc km hb P c ->
  (forall (fx' : FPState) L A regs mem md, frm_zero (@fp_csr fx') ->
     FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     SRO segs (mkCfg (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) o Q) ->
  SRO segs c o Q.
Proof.
  intros g pc km hb P c o Q (fx' & L & A & regs & mem & md & -> & Hf & H1 & H2 & H3) K.
  exact (K fx' L A regs mem md Hf H1 H2 H3).
Qed.

Lemma cut_close : forall (fx' : FPState) g pc km hb (P : bvmap 5 word -> (word -> option byte) -> Prop)
    L A regs mem md,
  frm_zero (@fp_csr fx') ->
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
  CUTST B APIf ra empty g pc km hb P (mkCfg (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md).
Proof.
  intros fx' g pc km hb P L A regs mem md Hf H1 H2 H3. exists fx', L, A, regs, mem, md. split; [reflexivity|].
  split; [exact Hf|]. split; [exact H1|]. split; [exact H2 | exact H3].
Qed.

Lemma FR_MR : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md -> MR L A mem md.
Proof. intros g km hb L A regs mem md (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma sg_GV_S : forall g, GV B empty g -> spZ (g_regs g) = g_S g /\ alloc_ceiling + SLOT_K <= g_S g <= 2 ^ 47.
Proof.
  intros g (_ & _ & _ & _ & H1 & H2 & _ & H3 & _). unfold spZ. rewrite H3.
  pose proof alloc_ceiling_value. unfold SLOT_K, SLOT_STACK in *. rewrite unsigned_lit by lia. lia.
Qed.

(* A stretch of the slot's own code from a frame record to the states of X (typically a cut, by cut_close). *)
Lemma run_to : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) o (X P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md -> X (mkCfg (mkst regs' pc' m' (seg_rom segs)) md)) ->
  (forall c', X c' -> SRO segs c' o P) ->
  SRO segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md pc Q o X P HFR HP HE Hform HX HK.
  apply (ss_mid_o B APIf ra empty FF g km hb L A regs mem md pc Q o P HFR HP HE Hform).
  intros R pc' m0' regs' m' HQ Hx Hrel HF'. apply HK. exact (HX R pc' m0' regs' m' HQ Hx Hrel HF').
Qed.

(* The image bytes that sink_none reads besides the open-file head: none of them is written by the run. *)
Lemma sg_img_kept : forall a, (a = @sk_threaded SK \/ @sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4) /\ ~ img_w a.
Proof.
  intros a Ha. pose proof (ss_errno B APIf ra empty FF) as Er.
  pose proof FF as (SEG & RA2 & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR
    & TP & EOFF & REP & OFH & OFL & THR & EMP & EMPR & CTXRO & GLOB & RELRO & ALLOC & VML & DBL).
  rewrite THR, OFL in Ha.
  split; [apply (ss_img_rng B APIf ra empty FF A_LIBC A_OFL_HEAD); [vm_compute; reflexivity | unfold A_LIBC, A_OFL_HEAD; lia]|].
  split; [unfold static_owned, vml_lo, vml_len; rewrite LCK, LIBC, GOT, GUA, DBR, SCL, SMC, MDC, VML, DBL; lia|].
  split; [rewrite CTX; unfold CTX_SIZE; lia|].
  split; [rewrite Er; lia|].
  intros Hw. pose proof (img_w_range a Hw) as R. unfold A_STDERR, A_OFL_HEAD in R. lia.
Qed.

(* After the reader is closed the open-file head holds 0 again, as at the entry. *)
Lemma ofl_back : forall g mem, GV B empty g -> ofl_empty mem ->
  forall a, A_OFL_HEAD <= a < A_OFL_HEAD + 8 -> mbyte segs mem a = mbyte segs (g_mem g) a.
Proof.
  intros g mem HGV HO a Ha.
  pose proof HGV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HgSn & _).
  destruct HgSn as (_ & Hh & _). destruct (ss_sink B APIf ra empty FF) as (E1 & _ & _). rewrite E1 in Hh.
  pose proof (KindBGlue.word_mem_le8 segs (g_mem g) _ 0 Hh ltac:(lia) ltac:(lia) ltac:(lia)) as HB0.
  pose proof (ss_cells_bytes mem A_OFL_HEAD _ HO) as HB1.
  cbn [Cells.cells_bytes Cells.cbytes] in HB1. rewrite app_nil_r in HB1. unfold wz in HB1.
  assert (Ea : a = A_OFL_HEAD + Z.of_nat (Z.to_nat (a - A_OFL_HEAD))) by lia.
  assert (Hi : (Z.to_nat (a - A_OFL_HEAD) < length (le8 (Z_to_bv 64 0)))%nat)
    by (rewrite length_le8; unfold A_OFL_HEAD in *; lia).
  rewrite Ea. rewrite sg_segs.
  rewrite (sg_bytes_nth rsegs mem _ _ HB1 _ Hi).
  rewrite sg_segs in HB0. unfold A_OFL_HEAD in *.
  rewrite (sg_bytes_nth rsegs (g_mem g) _ _ HB0 _ Hi). reflexivity.
Qed.

(* The return: from the frame record with no blocks of its own left, the open-file head back at its entry value
   and the output invariant, the state at ra satisfies the slot's post. *)
Lemma post_FR : forall g km L A regs0 regs mem md (fx' : FPState),
  FR B APIf ra empty g km [] L A regs0 mem md ->
  Permutation (blocks L A) ([] ++ blocks (g_L g) (g_A g)) ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (g_regs g) regs ->
  (forall a, A_OFL_HEAD <= a < A_OFL_HEAD + 8 -> mbyte segs mem a = mbyte segs (g_mem g) a) ->
  GI 0 mem -> frm_zero (@fp_csr fx') ->
  Post_o B APIf ra g (mkCfg (@mkst fx' regs (Z_to_bv 64 ra) mem (seg_rom segs)) md).
Proof.
  intros g km L A regs0 regs mem md fx' HF HP H10 HRP HOFL HGI Hfrm.
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & Hrel & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & HB0
    & Her & HRES & Hwin).
  pose proof HGV as (Hn & Hnp & Hblk & HS16 & HSc & HS47 & Hroom & HgS & HgT & HgR & HgSn & HgFs & HgFd).
  destruct (sg_GV_S g HGV) as [HSP HS].
  exists fx', L, A, regs, mem, md. split; [reflexivity|]. split; [exact Hfrm|].
  split; [|exact HGI].
  unfold lib_post_g.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
  split; [exact H10|]. split; [exact HRP|].
  split.
  { destruct Hmd as (vm & ->). exists vm, (m_fds (g_md g)), (m_statpins (g_md g)). cbn [ll_fs].
    split; [apply with_vmmaps_os_upd | intros k; reflexivity]. }
  split.
  { intros q k Hq. pose proof (ss_blocks_in (g_L g) (g_A g) q k Hq) as Hb.
    apply (Permutation_in _ (Permutation_sym HP)) in Hb.
    destruct (ss_blk_of L A _ _ Hb) as (q' & Hq' & E). exists q'. split; [exact Hq' | exact E]. }
  split.
  { intros a Ha Hn'. unfold lib_scratch in Hn'. rewrite HSP in Hn'.
    assert (N1 : ~ (g_S g - SLOT_K <= a < g_S g)) by (unfold SLOT_K; tauto).
    assert (N2 : ~ (errno_addr B <= a < errno_addr B + 4)) by tauto.
    destruct (Hhi a Ha N1 N2) as [E1 E2]. split; [exact E1 | tauto]. }
  split.
  { intros a H1 H2 H3 H4 HG. destruct (Himg a H1 H2 H3 H4) as [E1 E2].
    split; [|tauto].
    destruct (img_w_dec a) as [Hw|Hw]; [|exact (E1 Hw)].
    destruct (img_w_range a Hw) as [R|[R|R]].
    - assert (HR : in_globals frame_RELRO a).
      { unfold A_STDERR in R.
        assert (D : A_STDERR <= a < (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) \/ (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) <= a < (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) + 4 \/ (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) + 4 <= a < A_STDERR + 232)
          by (unfold A_STDERR; lia).
        destruct D as [D|[D|D]].
        - exists A_STDERR, 136. split; [unfold frame_RELRO, A_STDERR; cbn [In]; right; right; left; reflexivity|].
          unfold A_STDERR in *; lia.
        - exfalso. apply HG. exists (symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z), 4. split; [unfold frame_G; cbn [In]; left; reflexivity | lia].
        - exists ((symaddr (Symbols.Plain.s___stderr_FILE + 0x88)%Z) + 4), 92. split; [unfold frame_RELRO; cbn [In]; right; right; right; left; reflexivity|].
          unfold A_STDERR in *; lia. }
      rewrite (Hrel a HR), (HgR a HR). reflexivity.
    - exfalso. apply HG. exists (symaddr Symbols.Plain.s_g_file_len), 16. split; [unfold frame_G; cbn [In]; right; left; reflexivity | exact R].
    - exact (HOFL a R). }
  split.
  { intros a HG. destruct (ss_glob_img B APIf ra empty FF a HG) as (Hi & Hs & Hc & He).
    destruct (Himg a Hi Hs Hc He) as [_ E2]. tauto. }
  split.
  { intros q k i Hq _ Hi. apply (HB0 (ptr_addr (g_L g) q) k i); [apply ss_blocks_in; exact Hq | exact Hi]. }
  split.
  { intros a [Ha|Ha]; [apply Hwin; rewrite HSP in Ha; unfold SLOT_K; exact Ha | apply Her; exact Ha]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HgFs|].
  split.
  { destruct HgSn as ((Ht & Hl) & Hh & Hnf). destruct (ss_sink B APIf ra empty FF) as (E1 & E2 & E3).
    assert (KM : forall a, (a = @sk_threaded SK \/ @sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) ->
                 mbyte segs mem a = mbyte segs (g_mem g) a).
    { intros a Ha. destruct (sg_img_kept a Ha) as (Hi & Hs & Hc & He & Hw). exact (proj1 (Himg a Hi Hs Hc He) Hw). }
    split; [split|split].
    - eapply val_mem_frame; [|exact Ht]. intros x Hx. apply KM. cbn in Hx. lia.
    - eapply val_mem_frame; [|exact Hl]. intros x Hx. apply KM. cbn in Hx. lia.
    - apply (val_mem_word_mem segs). apply (val_mem_word_mem segs) in Hh.
      eapply val_mem_frame; [|exact Hh]. intros x Hx. rewrite E1 in Hx. cbn in Hx. apply HOFL.
      unfold A_OFL_HEAD. lia.
    - destruct Hmd as (vm & ->). exact Hnf. }
  split; [exact HMI|].
  split; [exact (resb_end (g_b g) km A HRES)|].
  intros i Hi. destruct Hnp as [[Hn0 _]|[_ Hp]]; [lia|]. exact (HB0 (g_p g) (g_n g) i Hp Hi).
Qed.


(* Cut-free twins (SROcf) of cut_open and run_to. *)
Lemma cut_open_cf : forall g pc km hb P c o (Q : config -> Prop),
  CUTST B APIf ra empty g pc km hb P c ->
  (forall (fx' : FPState) L A regs mem md, frm_zero (@fp_csr fx') ->
     FR B APIf ra empty g km hb L A regs mem md ->
     Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) -> P regs mem ->
     SROcf segs (mkCfg (@mkst fx' regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) o Q) ->
  SROcf segs c o Q.
Proof.
  intros g pc km hb P c o Q (fx' & L & A & regs & mem & md & -> & Hf & H1 & H2 & H3) K.
  exact (K fx' L A regs mem md Hf H1 H2 H3).
Qed.

Lemma run_to_cf : forall g km hb L A regs mem md pc (Q : machine_state -> Prop) o (X P : config -> Prop),
  FR B APIf ra empty g km hb L A regs mem md ->
  Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  Exec.evt rsegs Q (MState.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> exists R pc' m', ms = MState.MS R fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
     (exists W, Frame.munch W (normalize rsegs mem) m' /\ Frame.wmono rsegs (normalize rsegs mem) m' /\
        (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
           (g_S g - SLOT_K <= x < g_S g - 104) \/ (img_w x /\ ~ in_globals frame_RELRO x))) /\
     getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4) ->
  (forall R pc' m0' regs' m', Q (MState.MS R fp_regs pc' fp_csr None m0' (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R regs' -> mem_rel rsegs m' m0' ->
     FR B APIf ra empty g km hb L A regs' m' md -> X (mkCfg (mkst regs' pc' m' (seg_rom segs)) md)) ->
  (forall c', X c' -> SROcf segs c' o P) ->
  SROcf segs (mkCfg (mkst regs pc mem (seg_rom segs)) md) o P.
Proof.
  intros g km hb L A regs mem md pc Q o X P HFR HP HE Hform HX HK.
  apply (ss_mid_o_cf B APIf ra empty FF g km hb L A regs mem md pc Q o P HFR HP HE Hform).
  intros R pc' m0' regs' m' HQ Hx Hrel HF'. apply HK. exact (HX R pc' m0' regs' m' HQ Hx Hrel HF').
Qed.

End Glue.
