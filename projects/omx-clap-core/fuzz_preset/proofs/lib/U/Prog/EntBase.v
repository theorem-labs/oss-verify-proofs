From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01 YL0g YI14 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract KindBGlue Img0 FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes EntC1_Defs EntC1_Glue LLVMFuzzerTestOneInput_c EntryDefs EntrySR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require fuzz_alloc_ran_out_c.
Import ListNotations.

Module EMem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module EFrame := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Frame.
Module EMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.MState.
Module EExec := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Exec.
Local Open Scope Z_scope.

Lemma ent_stk_sub : forall s m lo hi lo' hi', EFrame.stk s m lo hi -> lo <= lo' -> hi' <= hi -> lo' <= hi' ->
  EFrame.stk s m lo' hi'.
Proof. intros s m lo hi lo' hi' (H1 & H2 & H) Hl Hh Hlh. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma ent_slot : forall s m x y v, x = y -> EMem.bytes_at s m x (EMem.le8 v) -> EMem.bytes_at s m y (EMem.le8 v).
Proof. intros s m x y v -> H. exact H. Qed.

Ltac ent_inj E R pc m :=
  let ER := fresh "ER" in let EP := fresh "EP" in let EM := fresh "EM" in
  pose proof (f_equal ms_regs E) as ER; pose proof (f_equal ms_pc_val E) as EP;
  pose proof (f_equal ms_mem E) as EM; cbn [ms_regs ms_pc_val ms_mem EMS.MS] in ER, EP, EM;
  subst R pc m; clear E.

(* The image bytes that the entry's frame lets its own steps and its callees write: the alloc statics, g_ran_out (one
   byte; fuzz_alloc_ran_out_reset at 0x13750), and since #102 g_own_ran_out (one byte; `sb zero` at 0x1374c) and g_most
   (eight bytes; fuzz_alloc_most at 0x13760). G_RAN_OUT is fuzz_alloc_ran_out_c's (= LedgerCells.GL_RAN_OUT);
   GL_OWN_RAN_OUT and GL_MOST are LedgerCells' names, re-exported by Ledger. *)
Definition ent_W (a : Z) : Prop :=
  alloc_statics a \/ fuzz_alloc_ran_out_c.G_RAN_OUT <= a < fuzz_alloc_ran_out_c.G_RAN_OUT + 1 \/
  GL_OWN_RAN_OUT <= a < GL_OWN_RAN_OUT + 1 \/ GL_MOST <= a < GL_MOST + 8.

(* out_of_memory() = 0 (fuzz_preset.c:79-82 of #102): both flag bytes 0. The entry has them from 0x1374c / 0x13750 on;
   each callee that can note memory running out keeps them 0 under its room premises (its contract says so). *)
Definition ent_flags (segs : list Segment) (mem : word -> option byte) : Prop :=
  EMem.bytes_at segs mem fuzz_alloc_ran_out_c.G_RAN_OUT (EMem.le1 (Z_to_bv 64 0)) /\
  EMem.bytes_at segs mem GL_OWN_RAN_OUT (EMem.le1 (Z_to_bv 64 0)).

Section P.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.
Let MR := aa_MR API.
Hypothesis HSEG : ms_segs B = rsegs.
Hypothesis FA : forall fx' : YK11.FPState, @frame_allocator rc fx' B API.

Lemma ent_AX : AllocExtra B (aa_MR API).
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ent_FG : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Proof. destruct (FA fx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma ent_img_low : KindBGlue.img_low B.
Proof.
  apply (KindBGlue.img_low_of_check B CEIL_MIN); [unfold KindBGlue.img_check; rewrite HSEG; vm_compute; reflexivity |].
  pose proof alloc_ceiling_val. lia.
Qed.

Definition ent_pre (stk empty : Z) (j : nat) (L : layout) (A : astate) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (ra p n : Z) (pl : list byte) (peak cnt : Z) (b0 : rf_R F) : Prop :=
  lib_pre_w B API stk empty L A regs mem md ra p n pl /\
  slot_syms B /\ slot_sinks B /\ ra mod 2 = 0 /\ SLOT_K <= stk /\
  ro_agree segs mem /\ spZ regs <= TASK_SIZE /\ frm_zero fp_csr /\
  ledger B L A mem [] peak cnt (2 ^ 64 - 1) /\ cnt <= Z.of_nat j * 2 ^ 60 /\ (j < 4)%nat /\
  rf_ok F A b0.

Definition ent_cpost (stk : Z) (j : nat) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ra p n : Z) (bres : rf_R F) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md',
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    EntrySR.ent_post B API stk L A regs mem md p n (LL 0 (m_fs md) []) L' A' regs' mem' md' /\
    omx_GI B (S j) mem' /\
    rf_ok F A' bres.

Definition ent_sr_post (stk : Z) (j : nat) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (ra p n : Z) (pl : list byte) (cnt : Z) (b0 : rf_R F) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' E1 E2 E3 Dp cset b4 trs Ds Df,
    c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
    frm_zero (@fp_csr fx') /\
    EntrySR.ent_post B API stk L A regs mem md p n (LL 0 (m_fs md) []) L' A' regs' mem' md' /\
    omx_GI B (S j) mem' /\
    entry_wit F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df /\
    rf_ok F A' (entry_fold F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df).

Lemma ent_sr_of_cpost : forall stk j L A regs mem md ra p n pl cnt b0 E1 E2 E3 Dp cset b4 trs Ds Df c',
  entry_wit F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df ->
  ent_cpost stk j L A regs mem md ra p n (entry_fold F b0 cnt pl E1 E2 E3 Dp cset b4 trs Ds Df) c' ->
  ent_sr_post stk j L A regs mem md ra p n pl cnt b0 c'.
Proof.
  intros stk j L A regs mem md ra p n pl cnt b0 E1 E2 E3 Dp cset b4 trs Ds Df c' HW
    (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hp & Hg & Hr).
  exists fx', L', A', regs', mem', md', E1, E2, E3, Dp, cset, b4, trs, Ds, Df.
  split; [exact Hc|]. split; [exact Hf|]. split; [exact Hp|]. split; [exact Hg|]. split; [exact HW | exact Hr].
Qed.

Lemma entry_fold_big : forall b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df,
  0x300000 < ent_n x -> entry_fold F b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df = b0.
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df H. unfold entry_fold.
  rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
Qed.

Lemma entry_wit_big : forall b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df,
  0x300000 < ent_n x -> entry_wit F b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df.
Proof. intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df H H'. lia. Qed.

Definition ent_inv (stk : Z) (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte)
    (md0 : Model) (p n : Z)
    (fx' : YK11.FPState) (L : layout) (A : astate) (mem : word -> option byte) (md : Model)
    (Lam : list (Z * Z)) (peak cnt : Z) (bnd : rf_R F) : Prop :=
  rstep B API stk (spZ regs0) ent_W (fun _ => False) L0 A0 mem0 md0 L A mem md /\
  (forall a k, In (a, k) (blocks L0 A0) -> k <= 0 -> In (a, k) (blocks L A)) /\
  st_init_done A = true /\ rd_cells B mem /\
  frm_zero (@fp_csr fx') /\
  ledger B L A mem Lam peak cnt (2 ^ 64 - 1) /\
  rf_ok F A bnd /\
  (forall i, 0 <= i < n -> mbyte segs mem (p + i) = mbyte segs mem0 (p + i)) /\
  EMem.bytes_at segs mem (spZ regs0 - 8) (EMem.le8 (getr regs0 1)) /\
  EMem.bytes_at segs mem (spZ regs0 - 16) (EMem.le8 (getr regs0 8)) /\
  EMem.bytes_at segs mem (spZ regs0 - 24) (EMem.le8 (getr regs0 9)) /\
  EMem.bytes_at segs mem (spZ regs0 - 32) (EMem.le8 (getr regs0 18)) /\
  EMem.bytes_at segs mem (spZ regs0 - 40) (EMem.le8 (getr regs0 19)) /\
  EMem.bytes_at segs mem (spZ regs0 - 48) (EMem.le8 (getr regs0 20)) /\
  EMem.bytes_at segs mem (spZ regs0 - 56) (EMem.le8 (getr regs0 21)) /\
  EMem.wr_at segs mem (spZ regs0 - 56) 56.

Lemma ent_kA : forall (fx1 : YK11.FPState) regs1 pc mem1 md1 (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md1 = None -> m_vm_lazy md1 = [] ->
  EExec.evt rsegs Q (EMS.MS (rmk regs1) (@fp_regs fx1) pc (@fp_csr fx1) None mem1 (seg_rom rsegs)) ->
  (forall ms', Q ms' -> exists R pc' m', ms' = EMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None m' (seg_rom rsegs)) ->
  (forall R pc' mem' regs', Q (EMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs)) ->
     (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs' pc' mem' (seg_rom (ms_segs B))) md1) P) ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom (ms_segs B))) md1) P.
Proof.
  intros fx1 regs1 pc mem1 md1 Q P Hh Hz HE HS HK.
  apply (@kb_run fx1 B regs1 pc mem1 md1
    (fun R pc' mem' => Q (EMS.MS R (@fp_regs fx1) pc' (@fp_csr fx1) None mem' (seg_rom rsegs))) P Hh Hz).
  - rewrite HSEG. eapply EExec.evt_mono; [exact HE|]. intros ms' HQ. destruct (HS ms' HQ) as (R & pc' & m' & E).
    exists R, pc', m'. split; [exact E | rewrite <- E; exact HQ].
  - exact HK.
Qed.

Lemma ent_ro_munch : forall m m' lo hi, ro_agree (ms_segs B) m -> EFrame.munch [(lo, hi)] m m' ->
  alloc_ceiling <= lo -> ro_agree (ms_segs B) m'.
Proof.
  intros m m' lo hi Hro HM Hlo a Ha.
  assert (Hlt : bv_unsigned a < alloc_ceiling).
  { unfold EMem.ro_addr in Ha.
    destruct (find_segment (ms_segs B) (bv_unsigned a) 1) as [seg|] eqn:Ef; [|discriminate].
    destruct ent_img_low as [_ HI]. exact (proj2 (HI _ _ Ef)). }
  assert (E : EMem.mrd (ms_segs B) m' a = EMem.mrd (ms_segs B) m a).
  { unfold EMem.mrd. rewrite (HM a); [reflexivity|]. apply outside_one. lia. }
  rewrite E. exact (Hro a Ha).
Qed.

Lemma ent_bytes : forall m m' x bs, EMem.bytes_at segs m x bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte segs m' (x + i) = mbyte segs m (x + i)) ->
  EMem.bytes_at segs m' x bs.
Proof.
  intros m m' x bs (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  rewrite <- (H3 i Hi). exact (HE (Z.of_nat i) ltac:(lia)).
Qed.

Lemma ent_wr : forall m m' x n, EMem.wr_at segs m x n ->
  (forall i, 0 <= i < n -> (writable_at segs m (x + i) <-> writable_at segs m' (x + i))) ->
  EMem.wr_at segs m' x n.
Proof.
  intros m m' x n (H1 & H2 & H3) HE. split; [exact H1|]. split; [exact H2|]. intros i Hi.
  exact (proj1 (HE i Hi) (H3 i Hi)).
Qed.

Lemma ent_errno : slot_syms B -> errno_addr B = strtod_c.STRTOD_ERRNO.
Proof. intros (_ & _ & _ & _ & _ & _ & Ht & He). unfold errno_addr. rewrite Ht, He. reflexivity. Qed.

Lemma ent_statics_lo : forall a, alloc_statics a -> a < alloc_ceiling.
Proof.
  intros a Ha. pose proof alloc_ceiling_val as HCV.
  unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Ha. lia.
Qed.

Lemma ent_W_lo : forall a, ent_W a -> a < alloc_ceiling.
Proof.
  intros a [Ha|Ha]; [exact (ent_statics_lo a Ha)|].
  pose proof alloc_ceiling_val as HCV. unfold fuzz_alloc_ran_out_c.G_RAN_OUT, GL_OWN_RAN_OUT, GL_MOST in Ha. lia.
Qed.

Lemma ent_W_img : forall a, ent_W a -> in_img B a.
Proof.
  intros a [Ha|[Ha|[Ha|Ha]]]; [exact (proj1 (statics_img B API HSEG ent_AX ent_FG a Ha))| | |].
  - apply (rg_img_range B API HSEG ent_AX ent_FG fuzz_alloc_ran_out_c.G_RAN_OUT (fuzz_alloc_ran_out_c.G_RAN_OUT + 1));
      [vm_compute; reflexivity | exact Ha].
  - apply (rg_img_range B API HSEG ent_AX ent_FG GL_OWN_RAN_OUT (GL_OWN_RAN_OUT + 1)); [vm_compute; reflexivity | exact Ha].
  - apply (rg_img_range B API HSEG ent_AX ent_FG GL_MOST (GL_MOST + 8)); [vm_compute; reflexivity | exact Ha].
Qed.

Lemma ent_ret_ok : forall stk empty j L A regs mem md ra p n pl peak cnt b0,
  ent_pre stk empty j L A regs mem md ra p n pl peak cnt b0 -> YK0s.ret_ok (getr regs 1).
Proof.
  intros stk empty j L A regs mem md ra p n pl peak cnt b0
    (((_ & _ & _ & _ & RA0 & _) & _) & _ & _ & RAE & _).
  rewrite RA0. apply YK0s.ret_ok_even. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite kb_mod2_land. exact RAE.
Qed.

Lemma ent_blk : forall K Sp E L0 A0 mem0 md0 L A mem md q k i,
  MR L0 A0 mem0 md0 ->
  rstep B API K Sp E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  (forall x, E x -> alloc_statics x) ->
  In (q, k) (user_blocks A0) -> 0 <= i < k ->
  mbyte segs mem (ptr_addr L0 q + i) = mbyte segs mem0 (ptr_addr L0 q + i).
Proof.
  intros K Sp E L0 A0 mem0 md0 L A mem md q k i HM RS HE Hq Hi.
  destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & BK & _).
  apply (BK (ptr_addr L0 q) k i (rg_blk_of B API HSEG ent_AX ent_FG L0 A0 q k Hq) (fun h => h) Hi).
  intros He. destruct (statics_img B API HSEG ent_AX ent_FG _ (HE _ He)) as [Hin _].
  exact (ax_blocks_img ent_AX L0 A0 mem0 md0 q k i HM Hq Hi Hin).
Qed.

Lemma ent_pay : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl K Sp E L A mem md,
  lib_pre_w B API stk empty L0 A0 regs0 mem0 md0 ra p n pl ->
  rstep B API K Sp E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  (forall x, E x -> alloc_statics x) ->
  forall i, 0 <= i < n -> mbyte segs mem (p + i) = mbyte segs mem0 (p + i).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl K Sp E L A mem md (PRE & _) RS HE i Hi.
  destruct PRE as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
  destruct PAY as [(Hn & _)|(_ & q & Hq & <-)]; [lia|].
  exact (ent_blk K Sp E L0 A0 mem0 md0 L A mem md q n i HM RS HE Hq Hi).
Qed.

Lemma ent_blk_W : forall K Sp E L0 A0 mem0 md0 L A mem md q k i,
  MR L0 A0 mem0 md0 ->
  rstep B API K Sp E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  (forall x, E x -> ent_W x) ->
  In (q, k) (user_blocks A0) -> 0 <= i < k ->
  mbyte segs mem (ptr_addr L0 q + i) = mbyte segs mem0 (ptr_addr L0 q + i).
Proof.
  intros K Sp E L0 A0 mem0 md0 L A mem md q k i HM RS HE Hq Hi.
  destruct RS as (_ & _ & _ & _ & _ & _ & _ & _ & BK & _).
  apply (BK (ptr_addr L0 q) k i (rg_blk_of B API HSEG ent_AX ent_FG L0 A0 q k Hq) (fun h => h) Hi).
  intros He. pose proof (ent_W_img _ (HE _ He)) as Hin.
  exact (ax_blocks_img ent_AX L0 A0 mem0 md0 q k i HM Hq Hi Hin).
Qed.

Lemma ent_pay_W : forall stk empty L0 A0 regs0 mem0 md0 ra p n pl K Sp E L A mem md,
  lib_pre_w B API stk empty L0 A0 regs0 mem0 md0 ra p n pl ->
  rstep B API K Sp E (fun _ => False) L0 A0 mem0 md0 L A mem md ->
  (forall x, E x -> ent_W x) ->
  forall i, 0 <= i < n -> mbyte segs mem (p + i) = mbyte segs mem0 (p + i).
Proof.
  intros stk empty L0 A0 regs0 mem0 md0 ra p n pl K Sp E L A mem md (PRE & _) RS HE i Hi.
  destruct PRE as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PAY & _).
  destruct PAY as [(Hn & _)|(_ & q & Hq & <-)]; [lia|].
  exact (ent_blk_W K Sp E L0 A0 mem0 md0 L A mem md q n i HM RS HE Hq Hi).
Qed.

Lemma ent_after : forall stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0
    (fx1 : YK11.FPState) L A mem md Lam peak cnt bnd Kc Ec gc (fx2 : YK11.FPState) L' A' mem' md' Lam' peak' cnt' bnd',
  ent_pre stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 ->
  ent_inv stk L0 A0 regs0 mem0 md0 p n fx1 L A mem md Lam peak cnt bnd ->
  rstep B API Kc (spZ regs0 - 112) Ec gc L A mem md L' A' mem' md' ->
  0 <= Kc -> 112 + Kc <= stk ->
  (forall a, Ec a -> ent_W a \/ (spZ regs0 - 112 <= a < spZ regs0 - 56) \/
     (0 <= a < alloc_ceiling /\ ~ in_img B a /\ forall b k, In (b, k) (blocks L A) -> ~ gc b -> ~ (b <= a < b + k))) ->
  (forall a, spZ regs0 - 112 <= a < spZ regs0 - 56 -> Ec a -> writable_at segs mem' a) ->
  (forall a k, In (a, k) (blocks L0 A0) -> 0 < k -> ~ gc a) ->
  (forall a k, In (a, k) (blocks L A) -> k <= 0 -> In (a, k) (blocks L' A')) ->
  ro_agree segs mem' ->
  frm_zero (@fp_csr fx2) ->
  ledger B L' A' mem' Lam' peak' cnt' (2 ^ 64 - 1) ->
  rf_ok F A' bnd' ->
  ent_inv stk L0 A0 regs0 mem0 md0 p n fx2 L' A' mem' md' Lam' peak' cnt' bnd'.
Proof.
  intros stk empty j L0 A0 regs0 mem0 md0 ra p n pl peak0 cnt0 b0 fx1 L A mem md Lam peak cnt bnd
    Kc Ec gc fx2 L' A' mem' md' Lam' peak' cnt' bnd'
    ENT INV STEP HK0 HK1 HEC HECW HG HZ RA' FRM' LED' RES'.
  pose proof ENT as (PREW & SYMS & _).
  pose proof PREW as (PRE & _).
  pose proof PRE as (MR0 & WF0 & BD0 & _ & _ & SP16 & SPC & SP63 & _).
  pose proof (ent_errno SYMS) as ERRB.
  destruct INV as (RS & Z0 & INIT & RD & FRM & LED & RES & PAY0 &
                   SL8 & SL16 & SL24 & SL32 & SL40 & SL48 & SL56 & WR56).
  pose proof RS as (MRc & WFc & BDc & INc & PSc & MDc & ACc & IMc & BKc & WRc).
  pose proof STEP as (MR' & WF' & BD' & IN' & PS' & MD' & AC' & IM' & BK' & WR').
  pose proof alloc_ceiling_val as HCV.
  assert (HERR : forall a, errno_addr B <= a < errno_addr B + 4 -> a < alloc_ceiling).
  { intros a Ha. rewrite ERRB in Ha. unfold strtod_c.STRTOD_ERRNO in Ha. lia. }
  set (SP := spZ regs0) in *.
  assert (STW : rstep B API stk SP Ec gc L A mem md L' A' mem' md').
  { apply (rstep_widen B API HSEG ent_AX ent_FG Kc (SP - 112) stk SP Ec gc L A mem md L' A' mem' md' STEP);
      [lia | lia | lia | lia | exact WRc |].
    intros a Ha Hn He. destruct (HEC a He) as [Hs | [Hw | (Hlo & _ & _)]].
    - pose proof (ent_W_lo a Hs). lia.
    - apply HECW; [lia | exact He].
    - lia. }
  assert (STD : rstep B API stk SP ent_W gc L A mem md L' A' mem' md').
  { apply (rstep_E_drop B API HSEG ent_AX ent_FG stk SP Ec ent_W gc L A mem md L' A' mem' md' STW MRc);
      [lia | exact ERRB |].
    intros a He. destruct (HEC a He) as [Hs | [Hw | Hb]].
    - left. exact Hs.
    - right. left. unfold rwin. left. lia.
    - right. right. exact Hb. }
  assert (STQ : rstep B API stk SP ent_W (fun _ => False) L0 A0 mem0 md0 L' A' mem' md').
  { eapply (rstep_E B API HSEG ent_AX ent_FG).
    - eapply (rstep_seq B API HSEG ent_AX ent_FG); [exact RS | exact STD |].
      intros a k Hin Hk _. exact (HG a k Hin Hk).
    - intros a [H|H]; exact H.
    - intros a H; exact H. }
  assert (KEEP : forall a, SP - 56 <= a < 2 ^ 64 ->
      mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)).
  { intros a Ha. apply AC'; [lia | |].
    - unfold rwin. intros [Hr|Hr]; [lia | pose proof (HERR a Hr); lia].
    - intros He. destruct (HEC a He) as [Hs | [Hw | (Hlo & _ & _)]]; [pose proof (ent_W_lo a Hs) | |]; lia. }
  assert (HB : forall x bs, SP - 56 <= x -> x + Z.of_nat (length bs) <= SP -> EMem.bytes_at segs mem x bs ->
      EMem.bytes_at segs mem' x bs).
  { intros x bs H1 H2 Hb. apply (ent_bytes mem); [exact Hb|]. intros i Hi. apply KEEP. lia. }
  unfold ent_inv. fold SP.
  split; [exact STQ|].
  split; [intros a k Hin Hk; apply HZ; [apply Z0; assumption | exact Hk]|].
  split; [apply IN'; exact INIT|].
  split; [exact (rd_cells_of_MR B API HSEG ent_AX ent_FG L' A' mem' md' MR' RA')|].
  split; [exact FRM'|].
  split; [exact LED'|].
  split; [exact RES'|].
  split; [exact (ent_pay_W stk empty L0 A0 regs0 mem0 md0 ra p n pl stk SP ent_W L' A' mem' md' PREW STQ
                   (fun x h => h))|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL8]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL16]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL24]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL32]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL40]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL48]|].
  split; [apply HB; [lia | rewrite EMem.length_le8; lia | exact SL56]|].
  apply (ent_wr mem); [exact WR56|]. intros i Hi. apply KEEP. lia.
Qed.

End P.
