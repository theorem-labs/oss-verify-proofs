From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Contract Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Mem Frame MState Regs6ss Step.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import Cells.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require snprintf_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_fr.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Definition LLVM_TOP : Z := 0x12d30.
Definition LLVM_JOIN : Z := 0x13314.
Definition LLVM_EXIT : Z := 0x13408.

Definition llvm_case_pc (k : Z) : Z :=
  if k =? 0 then 0x12d6c else if k =? 1 then 0x12dd8 else if k =? 2 then 0x12da8 else 0x12e08.

Definition llvm_saved_cells (regs0 : bvmap 5 word) : list cell :=
  [C8 (getr regs0 27); C8 (getr regs0 26); C8 (getr regs0 25); C8 (getr regs0 24); C8 (getr regs0 23);
   C8 (getr regs0 22); C8 (getr regs0 21); C8 (getr regs0 20); C8 (getr regs0 19); C8 (getr regs0 18);
   C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)].

Definition llvm_kept (bs bs' : list byte) (ren : Z) : Prop :=
  forall j, 0 <= j < bx_n bs ->
    bx_base bs' j = bx_base bs j /\ bx_nch bs' j = bx_nch bs j /\ bx_pinned bs' j = bx_pinned bs j /\
    (bx_mac bs j = zero6 \/ bx_mac bs' j = bx_mac bs j) /\ (j = ren \/ bx_name bs' j = bx_name bs j).

Lemma llvm_ov_read1 : forall (m : word -> option byte) a v, 0 <= a < 2 ^ 64 ->
  mbyte rsegs m a = Some v -> ov_read_bytes rsegs m (Z_to_bv 64 a) 1 = Some [v].
Proof.
  intros m a v Ha H. unfold mbyte, seg_rom in H. cbn [ov_read_bytes].
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E.
  - injection H as ->. reflexivity.
  - destruct (memory_read rsegs (Z_to_bv 64 a) 1) as [[|x l]|]; try discriminate. injection H as ->. reflexivity.
Qed.

Section I.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Definition llvm_ctx (stk empty : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (ra p n : Z) (b : sbound) : Prop :=
  llvm_binds B API /\ LLVM_K <= stk /\ YK0s.ret_ok (Z_to_bv 64 ra) /\
  lib_pre B API stk empty L0 A0 regs0 mem0 md0 ra p n /\ sink_none B mem0 md0 /\ spZ regs0 <= 2 ^ 47 /\
  res_ok_slots A0 b /\ llvm_room b /\
  ro_agree rsegs mem0 /\ G_img_c B llvm_RELRO mem0 /\ frm_zero (@fp_csr fx) /\ n < 2 ^ 26.

Definition llvm_blocks_above_image : Prop :=
  forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) -> snprintf_c.IMG_END <= q.

Definition llvm_regs_base (regs0 regs : bvmap 5 word) (r fab i : Z) : Prop :=
  getr regs 2 = Z_to_bv 64 (spZ regs0 - 448) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  getr regs 8 = Z_to_bv 64 r /\ getr regs 24 = Z_to_bv 64 i /\
  getr regs 25 = Z_to_bv 64 (spZ regs0 - 448 + 326) /\ getr regs 26 = Z_to_bv 64 (spZ regs0 - 448 + 32) /\
  getr regs 27 = Z_to_bv 64 fab.

Definition llvm_alloc (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (b : sbound) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (r : Z) (k : nat) : Prop :=
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md /\ lf_mine L0 A0 L A r 288 /\
  res_ok_slots A (sb_malloc b LLVM_REQ).

Definition llvm_J (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (p n : Z) (b : sbound) (i : Z) (k : nat) (c : config) : Prop :=
  exists (fx' : FPState) regs mem md L A r fab ip inn bs j0 j1 j2,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 LLVM_TOP) mem (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    llvm_regs_base regs0 regs r fab i /\ getr regs 21 = Z_to_bv 64 inn /\
    Step.rw_cells rsegs mem (spZ regs0 - 448)
      (CB 8 j0 :: C8 (Z_to_bv 64 fab) :: CB 312 j1 :: C8 (Z_to_bv 64 ip) :: CB 8 j2 :: llvm_saved_cells regs0) /\
    0 <= i <= 63 /\ 1 <= inn /\ p <= ip /\ ip + inn = p + n /\
    Step.rw_cells rsegs mem r [CB 288 bs] /\ boxreg_inv bs /\ bx_fabric bs = fab /\
    llvm_alloc stk L0 A0 regs0 mem0 md0 b L A mem md r k /\ (k <= 1 + Z.to_nat i)%nat.

Definition llvm_T (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (p n : Z) (b : sbound) (i : Z) (k : nat) (c : config) : Prop :=
  exists (fx' : FPState) regs mem md L A r fab ip inn bs op j0 j1 jm,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 (llvm_case_pc (Z.land op 3))) mem (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    llvm_regs_base regs0 regs r fab i /\
    getr regs 9 = Z_to_bv 64 ip /\ getr regs 18 = Z_to_bv 64 (inn - 1) /\ getr regs 19 = Z_to_bv 64 (ip + 1) /\
    getr regs 21 = Z_to_bv 64 inn /\ getr regs 22 = Z_to_bv 64 op /\ getr regs 23 = Z_to_bv 64 (bx_n bs) /\
    Step.rw_cells rsegs mem (spZ regs0 - 448)
      (CB 8 j0 :: C8 (Z_to_bv 64 fab) :: CB 16 j1 :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 (ip + 1)) ::
       C8 (Z_to_bv 64 (inn - 1)) :: llvm_saved_cells regs0) /\
    0 <= i <= 63 /\ 1 <= inn /\ p <= ip /\ ip + inn = p + n /\ 0 <= op < 256 /\
    Step.rw_cells rsegs mem r [CB 288 bs] /\ boxreg_inv bs /\ bx_fabric bs = fab /\
    llvm_alloc stk L0 A0 regs0 mem0 md0 b L A mem md r k /\ (k <= 1 + Z.to_nat i)%nat.

Definition llvm_K (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (p n : Z) (b : sbound) (i : Z) (k : nat) (c : config) : Prop :=
  exists (fx' : FPState) regs mem md L A r fab ip inn bs bs' ren j0 j1 jm,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 LLVM_JOIN) mem (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    llvm_regs_base regs0 regs r fab i /\ getr regs 19 = Z_to_bv 64 (ren mod 2 ^ 32) /\
    Step.rw_cells rsegs mem (spZ regs0 - 448)
      (CB 8 j0 :: C8 (Z_to_bv 64 fab) :: CB 16 j1 :: CB 288 bs :: CB 8 jm :: C8 (Z_to_bv 64 ip) ::
       C8 (Z_to_bv 64 inn) :: llvm_saved_cells regs0) /\
    0 <= i <= 63 /\ 0 <= inn /\ p <= ip /\ ip + inn = p + n /\ -1 <= ren < bx_n bs /\
    boxreg_inv bs /\ bx_fabric bs = fab /\
    Step.rw_cells rsegs mem r [CB 288 bs'] /\ boxreg_inv bs' /\ bx_fabric bs' = fab /\ llvm_kept bs bs' ren /\
    llvm_alloc stk L0 A0 regs0 mem0 md0 b L A mem md r k /\ (k <= 2 + Z.to_nat i)%nat.

Definition llvm_X (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (b : sbound) (k : nat) (c : config) : Prop :=
  exists (fx' : FPState) regs mem md L A r jx,
    c = mkCfg (@mkst fx' regs (Z_to_bv 64 LLVM_EXIT) mem (seg_rom (ms_segs B))) md /\
    frm_zero (@fp_csr fx') /\
    getr regs 2 = Z_to_bv 64 (spZ regs0 - 448) /\ getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
    getr regs 8 = Z_to_bv 64 r /\
    Step.rw_cells rsegs mem (spZ regs0 - 448) (CB 344 jx :: llvm_saved_cells regs0) /\
    llvm_alloc stk L0 A0 regs0 mem0 md0 b L A mem md r k /\ (k <= 65)%nat.

Definition llvm_top_ok : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_J stk L0 A0 regs0 mem0 md0 p n b i k c ->
    SR (ms_segs B) c (llvm_T stk L0 A0 regs0 mem0 md0 p n b i k).

Definition llvm_case_ok (op3 : Z) : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_T stk L0 A0 regs0 mem0 md0 p n b i k c ->
    (exists ms md, c = mkCfg ms md /\ ms_pc_val ms = Z_to_bv 64 (llvm_case_pc op3)) ->
    SR (ms_segs B) c (fun c' => exists k', llvm_K stk L0 A0 regs0 mem0 md0 p n b i k' c').

Definition llvm_join_ok : Prop :=
  forall stk empty L0 A0 regs0 mem0 md0 ra p n b i k c,
    llvm_ctx stk empty L0 A0 regs0 mem0 md0 ra p n b ->
    llvm_K stk L0 A0 regs0 mem0 md0 p n b i k c ->
    SR (ms_segs B) c (fun c' => llvm_J stk L0 A0 regs0 mem0 md0 p n b (i + 1) k c' \/
                                llvm_X stk L0 A0 regs0 mem0 md0 b k c').

Hypothesis SINK : lf_sink_env B.

Lemma llvm_ctx_segs : forall stk empty L0 A0 regs0 mem0 md0 ra p n b,
  llvm_ctx stk empty L0 A0 regs0 mem0 md0 ra p n b -> ms_segs B = rsegs.
Proof. intros stk empty L0 A0 regs0 mem0 md0 ra p n b ((H & _) & _). exact H. Qed.

Lemma llvm_md_ok : forall stk S L0 A0 mem0 md0 L A mem md,
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> m_halted md = None /\ m_vm_lazy md = [].
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md (HM & _).
  destruct (mr_model B _ (aa_laws API) _ _ _ _ HM) as (H1 & H2 & _). auto.
Qed.

Lemma llvm_payload_read : forall stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x,
  llvm_ctx stk empty L0 A0 regs0 mem0 md0 ra p n b ->
  lf_fr B API stk (spZ regs0) L0 A0 mem0 md0 L A mem md -> p <= x < p + n ->
  exists v, ov_read_bytes rsegs mem (Z_to_bv 64 x) 1 = Some [v].
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n b L A mem md x
    ((SEGS & _) & _ & _ & (HM0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpl & _) & _) FR Hx.
  destruct FR as (_ & _ & _ & _ & _ & _ & _ & _ & Hbyt & _).
  destruct Hpl as [[E _] | [Hn (q & Hq & Hqp)]]; [lia|].
  assert (Hb : In (p, n) (blocks L0 A0)) by (apply blocks_In; exists q; auto).
  destruct (mr_blocks B _ (aa_laws API) L0 A0 mem0 md0 q n (x - p) HM0 Hq ltac:(lia)) as ((v & Hv) & H1 & H2 & _).
  rewrite Hqp in H1, H2, Hv. replace (p + (x - p)) with x in Hv by lia.
  pose proof YM05.alloc_ceiling_value as Hac.
  exists v. apply llvm_ov_read1; [lia|].
  pose proof (Hbyt p n (x - p) Hb ltac:(lia)) as E. replace (p + (x - p)) with x in E by lia.
  rewrite <- SEGS. rewrite E. unfold mbyte. rewrite Hv. reflexivity.
Qed.

Lemma llvm_stk_below : forall stk S L0 A0 mem0 md0 L A mem md lo hi,
  lf_fr B API stk S L0 A0 mem0 md0 L A mem md -> ms_segs B = rsegs ->
  alloc_ceiling + stk <= S -> S <= 2 ^ 64 -> S - stk <= lo -> hi <= S ->
  Frame.stk rsegs mem lo hi.
Proof.
  intros stk S L0 A0 mem0 md0 L A mem md lo hi FR SEGS Hc HS Hlo Hhi.
  pose proof YM05.alloc_ceiling_value as Hac. pose proof lf_ceiling as Hrt.
  destruct FR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hstw & _).
  apply lf_stk; [lia | lia |]. intros a Ha. rewrite <- SEGS. apply Hstw. lia.
Qed.

End I.
