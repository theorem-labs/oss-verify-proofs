From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require FrameAPI.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import Regs6ss.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import Ledger ManifestB names_c as_ruled_c KindB.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import printf_facts_c snprintf_c plain_c strlen_c check_round_trip_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import crt_lib crt_inv crt_aux crt_text crt_ka0 crt_snp crt_whole crt_ka1 crt_ka2 crt_ka3.
Import ListNotations.
Local Open Scope Z_scope.


Lemma rel_shape_cj : forall s R F pc fc rv m0 ro, ms_rel_cj rsegs s (MS R F pc fc rv m0 ro) ->
  s = MS R F pc fc rv (ms_mem s) ro /\ mem_rel_cj rsegs (ms_mem s) m0.
Proof.
  intros [R' F' pc' svc' rv' fc' m' ro'] R F pc fc rv m0 ro (E1 & E2 & E3 & E4 & E5 & E6 & E7 & HR).
  cbn in *. subst. split; [reflexivity | exact HR].
Qed.

Lemma mem_inv_normalize : forall m, mem_inv rsegs (normalize_cj rsegs m).
Proof. intros m. exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs m)). Qed.

Lemma task_mem_normalize : forall m, task_mem rsegs (normalize_cj rsegs m).
Proof. intros m. exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs m)). Qed.

Lemma cj_keep_low : forall x, 0 <= x < TASK_SIZE -> (x < 65536 \/ 122880 <= x) -> cj_drop rsegs (wa x) = false.
Proof.
  intros x Hx Hr. apply cj_drop_false_intro.
  - destruct (ro_addr rsegs (wa x)) eqn:E; [|reflexivity].
    pose proof (ro_low _ E) as R. rewrite wa_unsigned in R by (unfold TASK_SIZE in *; lia). lia.
  - right. rewrite wa_unsigned by (unfold TASK_SIZE in *; lia). lia.
Qed.

Lemma stk_normalize : forall m lo hi, stk rsegs m lo hi -> 122880 <= lo /\ hi <= TASK_SIZE ->
  stk rsegs (normalize_cj rsegs m) lo hi.
Proof.
  intros m lo hi (H1 & H2 & H) [Hlo Hhi]. split; [lia|]. split; [lia|]. intros a Ha.
  pose proof (cj_keep_low a ltac:(lia) ltac:(lia)) as E. destruct (H a Ha) as [Hw Hr].
  unfold wview, mrd, normalize_cj in *. rewrite E. split; [exact Hw | exact Hr].
Qed.

Lemma bytes_at_norm : forall m a bs, ro_agree rsegs m -> bytes_at rsegs m a bs ->
  a + Z.of_nat (length bs) <= TASK_SIZE -> bytes_at rsegs (normalize_cj rsegs m) a bs.
Proof. intros m a bs RA H L. exact (bytes_at_normalize_cj_low rsegs m a bs RA L H). Qed.

Lemma cstr_normalize : forall m a bs sl, ro_agree rsegs m -> cstr_at m a bs sl ->
  a + Z.of_nat (length bs + 1 + length sl) <= TASK_SIZE -> cstr_at (normalize_cj rsegs m) a bs sl.
Proof.
  intros m a bs sl RA (Hb & Hn & Hs) L. split; [|split; assumption].
  apply bytes_at_norm; [exact RA | exact Hb |]. rewrite length_app. cbn [length]. lia.
Qed.

Lemma ka_step : forall {fx1 : FPState} {rc : RunCeil} (segs : list Segment) (P : machine_state -> Prop) regs1 pc mem1 md1 Q',
  segs = rsegs -> ro_agree rsegs mem1 -> m_halted md1 = None -> m_vm_lazy md1 = [] ->
  evt rsegs P (MS (mkR_of regs1) (@fp_regs fx1) pc (@fp_csr fx1) None (normalize_cj rsegs mem1) (seg_rom rsegs)) ->
  (forall s s0, P s0 -> ms_rel_cj rsegs s s0 -> cj_same rsegs mem1 (ms_mem s) -> forall ms', ms_eqv s ms' ->
     SR segs (mkCfg ms' md1) Q') ->
  SR segs (mkCfg (@mkst fx1 regs1 pc mem1 (seg_rom segs)) md1) Q'.
Proof.
  intros fx1 rc segs P regs1 pc mem1 md1 Q' SEG RA Hh Hl EV K. subst segs.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. apply (evt_normalize_cj rsegs); [exact FrameAPI.wx_apart_rsegs | exact RA | exact EV]. }
  intros ms' (s & (s0 & HP & HR & HO) & EQ). exact (K s s0 HP HR HO ms' EQ).
Qed.

Lemma rel_post : forall m m1 m0 W, ro_agree rsegs m -> mem_rel_cj rsegs m1 m0 -> cj_same rsegs m m1 ->
  munch W (normalize_cj rsegs m) m0 -> wmono rsegs (normalize_cj rsegs m) m0 ->
  munch W m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1.
Proof.
  intros m m1 m0 W RA HR HO MU WM.
  pose proof (mem_rel_cj_normalize rsegs m RA) as R0.
  split; [exact (munch_rel_cj rsegs W m _ m1 m0 R0 HR HO MU)|].
  split; [exact (wmono_rel_cj rsegs m _ m1 m0 R0 HR HO WM)|].
  exact (ro_agree_same_cj rsegs m m1 RA HO).
Qed.

Lemma Zmax_idem : forall p x, Z.max (Z.max p x) x = Z.max p x.
Proof. intros p x. lia. Qed.

Lemma ka_post : forall s R F pc fc m0 ms' mem1 W, ms_rel_cj rsegs s (MS R F pc fc None m0 (seg_rom rsegs)) ->
  cj_same rsegs mem1 (ms_mem s) -> ms_eqv s ms' -> ro_agree rsegs mem1 ->
  munch W (normalize_cj rsegs mem1) m0 -> wmono rsegs (normalize_cj rsegs mem1) m0 ->
  exists R2, ms' = @mkst (mkFP F fc) R2 pc (ms_mem s) (seg_rom rsegs) /\ xregs_eqv R R2 /\
    mem_rel_cj rsegs (ms_mem s) m0 /\ munch W mem1 (ms_mem s) /\ wmono rsegs mem1 (ms_mem s) /\ ro_agree rsegs (ms_mem s).
Proof.
  intros s R F pc fc m0 ms' mem1 W REL ROS EQV RA MU WM.
  destruct (rel_shape_cj _ _ _ _ _ _ _ _ REL) as [Es MR2].
  rewrite Es in EQV.
  change (ms_eqv (MS R (@fp_regs (mkFP F fc)) pc (@fp_csr (mkFP F fc)) None (ms_mem s) (seg_rom rsegs)) ms') in EQV.
  destruct (eqv_shape (mkFP F fc) R pc (ms_mem s) (seg_rom rsegs) ms' EQV) as [E2 XR].
  destruct (rel_post mem1 (ms_mem s) m0 W RA MR2 ROS MU WM) as (MU1 & WM1 & RA1).
  exists (ms_regs ms'). exact (conj E2 (conj XR (conj MR2 (conj MU1 (conj WM1 RA1))))).
Qed.

Lemma ro_false_out : forall x, 0 <= x < 2 ^ 64 -> (x < 65536 \/ 122880 <= x) -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx Hr. destruct (ro_addr rsegs (wa x)) eqn:E; [|reflexivity].
  pose proof (ro_low _ E) as R. rewrite wa_unsigned in R by lia. lia.
Qed.

Lemma rw_cells_normalize : forall m A cs, ro_agree rsegs m -> rw_cells rsegs m A cs ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> x < 65536 \/ 122880 <= x < TASK_SIZE) ->
  rw_cells rsegs (normalize_cj rsegs m) A cs.
Proof.
  intros m A cs RA [[Hwf Hb] Hw] Ho. pose proof (bytes_at_bound _ _ _ _ Hb) as BB.
  rewrite cells_bytes_length in BB by exact Hwf.
  split; [split; [exact Hwf|]|].
  - destruct (Nat.eq_dec (cells_size cs) 0) as [E0|E0].
    + destruct (cells_bytes cs) eqn:Ec; [apply bytes_at_nil; lia|].
      pose proof (cells_bytes_length cs Hwf) as L. rewrite Ec, E0 in L. discriminate.
    + apply bytes_at_norm; [exact RA | exact Hb |]. rewrite cells_bytes_length by exact Hwf.
      pose proof (Ho (A + Z.of_nat (cells_size cs) - 1) ltac:(lia)). unfold TASK_SIZE in *. lia.
  - apply (wr_at_norm_cj rsegs m); [apply mem_rel_cj_normalize; exact RA | exact Hw |].
    intros i Hi. destruct (Ho (A + i) ltac:(lia)) as [H1|H1]; apply cj_keep_low; unfold TASK_SIZE in *; lia.
Qed.

Lemma rw_cells_rel : forall m m0 A cs, mem_rel_cj rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR [[Hwf Hb] Hw]. split; [split; [exact Hwf|]|].
  - exact (bytes_at_rel_cj rsegs m m0 A _ HR Hb).
  - exact (wr_at_rel_cj rsegs m m0 A _ HR Hw).
Qed.

Lemma cstr_rel : forall m m0 a bs sl, mem_rel_cj rsegs m m0 -> cstr_at m0 a bs sl -> cstr_at m a bs sl.
Proof.
  intros m m0 a bs sl HR (Hb & Hn & Ha). split; [|split; assumption].
  exact (bytes_at_rel_cj rsegs m m0 a _ HR Hb).
Qed.

Lemma rt_used_le : forall (zu : list Z) f k, (rt_used zu k f <= length zu - k)%nat.
Proof.
  intros zu f. induction f as [|f IH]; intros k; cbn [rt_used]; [lia|].
  destruct ((k <? length zu)%nat && negb (byte_at zu (k - 1) =? 62)) eqn:E; [|lia].
  apply andb_true_iff in E as [E _]. apply Nat.ltb_lt in E.
  specialize (IH (S k)). destruct (plain_name (skipn k zu)); lia.
Qed.

Lemma rsegs_first : exists s0 rest, rsegs = s0 :: rest /\ Z.of_N (seg_base s0) = 65536 /\
  Z.of_N (seg_size s0) = 8192 /\ seg_writable s0 = false.
Proof.
  destruct rsegs as [|s0 rest] eqn:E.
  - exfalso. pose proof (f_equal (@length Segment) E) as L. vm_compute in L. discriminate L.
  - exists s0, rest. split; [reflexivity|].
    pose proof (f_equal (fun l : list Segment => match l with s :: _ => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s) | [] => (0, 0, true) end) E) as F.
    vm_compute in F. injection F as F1 F2 F3. auto.
Qed.

Lemma ro_first : forall x, 65536 <= x < 73728 -> ro_addr rsegs (wa x) = true.
Proof.
  intros x Hx. destruct rsegs_first as (s0 & rest & E & B0 & S0 & W0).
  unfold ro_addr. rewrite wa_unsigned by lia. rewrite E. cbn [find_segment].
  rewrite B0, S0. replace ((65536 <=? x) && (x + 1 <=? 65536 + 8192)) with true by (symmetry; apply andb_true_iff; split; apply Z.leb_le; lia).
  rewrite W0. reflexivity.
Qed.

Lemma crt_strings_keep : forall m m', ro_agree rsegs m -> ro_agree rsegs m' -> crt_strings m -> crt_strings m'.
Proof.
  intros m m' H H' (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  unfold crt_strings.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); (eapply bytes_ro; [exact H | exact H' | | eassumption]); intros i Hi; vm_compute in Hi; apply ro_first;
    unfold EMPTY_STR, FMT_TW, FMT_TX, FMT_T1, FMT_T2, FMT_T3, FMT_T1X; lia.
Qed.

Lemma crt_strings_norm : forall m, ro_agree rsegs m -> crt_strings m -> crt_strings (normalize_cj rsegs m).
Proof.
  intros m H (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))); (apply bytes_at_norm; [exact H | assumption | apply Z.leb_le; vm_compute; reflexivity]).
Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis NAMES : forall fx', @names_contract fx' rc B API.
Hypothesis ASR : forall fx', @as_ruled_contract fx' rc B API.
Hypothesis MAL : forall fx', @malloc_contract fx' rc B API.
Hypothesis FRE : forall fx', @free_contract fx' rc B API.
Hypothesis SFA : statics_facts B.
Hypothesis SF : statics_free B MR.
Hypothesis ERR : errno_low B.
Hypothesis CTX : ManifestB.ctx_owned B MR.
Hypothesis GS : guard_syms B.
Hypothesis SNE : statics_noerrno B.
Hypothesis MSO : malloc_syms_omx B.
Hypothesis AX : YL01.AllocExtra B MR.
Hypothesis BSP : block_slack_present B API.

Variables (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (b : sbound) (u us : list byte) (Lam : list (Z * Z)) (peak cnt fail ua uk : Z).
Hypothesis SEG : ms_segs B = rsegs.
Hypothesis PRE : call_pre_k B MR CRT_K L A regs mem md.
Hypothesis RA0 : ro_agree rsegs mem.
Hypothesis CU0 : cstr_at mem (bv_unsigned (getr regs 10)) u us.
Hypothesis UB : In (ua, uk) (blocks L A).
Hypothesis UL : ua <= bv_unsigned (getr regs 10).
Hypothesis UR : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 <= ua + uk.
Hypothesis LEN : (length u <= 255)%nat.
Hypothesis IMG : img_strings mem.
Hypothesis LG : ledger B L A mem Lam peak cnt fail.
Hypothesis QT : quiet cnt fail 1019.
Hypothesis CS0 : crt_strings mem.
Hypothesis SNP : snprintf_contract.
Hypothesis STRL : strlen_contract.
Hypothesis PLN : plain_contract.
Hypothesis CAP0 : sb_live b + 2 <= sb_cap b <= CAPMAX.
Hypothesis BY0 : 0 <= sb_bytes b.
Hypothesis BYU : sb_bytes b + (4 * Z.of_nat (length u) + 83) <= 2 ^ 40.
Hypothesis RES0 : res_ok_slots A b.
Hypothesis FRM0 : frm_zero (@fp_csr fx).
Hypothesis INIT0 : st_init_done A = true.
Hypothesis SPT : spZ regs <= TASK_SIZE.

Definition nm_pk (pk : Z) : Z := match u with [] => pk | _ :: _ => Z.max pk (lsum Lam + Z.of_nat (length u) + 3) end.
Definition nm_c (c : Z) : Z := match u with [] => c | _ :: _ => c + 1 end.
Definition nroom (b1 : sbound) : Prop :=
  sb_live b1 + 1 <= sb_cap b1 <= CAPMAX /\ 0 <= sb_bytes b1 /\ sb_bytes b1 + (Z.of_nat (length u) + 19) <= 2 ^ 40.

Lemma crtk_val : CRT_K = 8560. Proof. reflexivity. Qed.
Lemma namesk_val : NAMES_K = 8416. Proof. reflexivity. Qed.
Lemma asrk_val : AS_RULED_K = 8448. Proof. reflexivity. Qed.

Lemma pre_facts : alloc_ceiling + 8560 <= spZ regs /\ spZ regs < 2 ^ 63 /\ spZ regs mod 16 = 0 /\
  YK0s.ret_ok (getr regs 1) /\ getr regs 4 = Z_to_bv 64 (ms_tp B) /\ MR L A mem md.
Proof.
  pose proof PRE as (HM & HWF & HBD & HRA & H16 & HAC & H63 & HWS & HTP & HER & _).
  rewrite crtk_val in HAC. exact (conj HAC (conj H63 (conj H16 (conj HRA (conj HTP HM))))).
Qed.

Lemma u_home : forall blk L1 A1 mem1 md1, crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  In (ua, uk) (blocks L1 A1).
Proof.
  intros blk L1 A1 mem1 md1 (_ & _ & _ & _ & _ & (b1 & b2 & E1 & E0) & _).
  rewrite E1. apply in_mid. rewrite <- E0. exact UB.
Qed.

Lemma u_bounds : 4096 <= ua /\ ua + uk <= alloc_ceiling.
Proof.
  destruct (pre_facts) as (_ & _ & _ & _ & _ & HM).
  destruct (in_blocks L A ua uk UB) as (p & Hp & E).
  pose proof (mr_blocks_range _ _ (aa_laws API) L A mem md p uk HM Hp) as R. rewrite <- E in R. exact R.
Qed.

Lemma u_cstr : forall blk L1 A1 mem1 md1, crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  exists us1, cstr_at mem1 (bv_unsigned (getr regs 10)) u us1 /\
    Z.of_nat (length us1) = (- (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) mod 8.
Proof.
  intros blk L1 A1 mem1 md1 IV.
  eapply ustr; eassumption.
Qed.

Lemma nm_nil : u = [] -> forall p c, nm_pk p = p /\ nm_c c = c.
Proof. intros E p c. unfold nm_pk, nm_c. rewrite E. split; reflexivity. Qed.

Lemma nm_cons : u <> [] -> forall p c, nm_pk p = Z.max p (lsum Lam + Z.of_nat (length u) + 3) /\ nm_c c = c + 1.
Proof. intros E p c. unfold nm_pk, nm_c. destruct u as [|x r]; [contradiction|]. split; reflexivity. Qed.

Lemma frame_kept : forall K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2,
  bpost B MR K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 -> MR L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> (forall a, E a -> a < alloc_ceiling) ->
  forall a, spZ regs - 112 <= a < spZ regs ->
    mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a).
Proof.
  intros K1 E L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 BP HM1 SP1 HE a Ha.
  destruct pre_facts as (HAC & H63 & _).
  destruct BP as (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _). rewrite SEG in Hfr.
  pose proof alloc_ceiling_val as Hacv.
  apply Hfr; [left; unfold spZ in *; pose proof (zr_word (getr regs 2)) as Z; unfold inr64 in Z; lia | | | |].
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 O). lia.
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 O). lia.
  - intros [Sc|Sc]; [lia | unfold errno_low in ERR; lia].
  - intros He. pose proof (HE a He). lia.
Qed.

Lemma u_statics : forall blk L1 A1 mem1 md1 (us1 : list byte), crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  Z.of_nat (length us1) = (- (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) mod 8 ->
  off_statics (bv_unsigned (getr regs 10)) (Z.of_nat (length u + 1 + length us1)).
Proof.
  intros blk L1 A1 mem1 md1 us1 IV Lus.
  pose proof IV as (HM1 & _).
  replace (Z.of_nat (length u + 1 + length us1)) with
    ((Z.of_nat (length u) + 1) + (- (bv_unsigned (getr regs 10) + (Z.of_nat (length u) + 1))) mod 8)
    by (rewrite Z.add_assoc; lia).
  apply off_statics_slack; [lia|]. intros z Hz.
  replace z with (ua + (z - ua)) by lia.
  apply (static_not_block B API SFA AX L1 A1 mem1 md1 ua uk (z - ua) HM1 (u_home blk L1 A1 mem1 md1 IV)). lia.
Qed.

Lemma guard_of_MR : forall L1 A1 mem1 md1, MR L1 A1 mem1 md1 -> guard_cells B mem1.
Proof.
  intros L1 A1 mem1 md1 HM. destruct (YL01.ax_statics AX L1 A1 mem1 md1 HM) as (G1 & (g & _ & G2) & _).
  split; [exact G1 | exists g; exact G2].
Qed.

Lemma pre_k_of_inv : forall blk L1 A1 mem1 md1 regs1 K1,
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  0 <= K1 <= 8448 ->
  call_pre_k B MR K1 L1 A1 regs1 mem1 md1.
Proof.
  intros blk L1 A1 mem1 md1 regs1 K1 IV SP1 RA1 TP1 HK.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & _ & _ & _ & HSC & _).
  pose proof alloc_ceiling_val as Hacv.
  unfold call_pre_k. rewrite SP1.
  split; [exact HM1|]. split; [exact HWF1|]. split; [exact HBD1|]. split; [exact RA1|].
  split; [Z.div_mod_to_equations; lia|].
  split; [lia|]. split; [lia|].
  split; [intros a Ha; rewrite SEG; apply HSC; left; rewrite crtk_val; lia|].
  split; [rewrite TP1; exact HTP|].
  split; [intros a Ha; rewrite SEG; apply HSC; right; exact Ha|].
  intros H. rewrite INIT1 in H. discriminate.
Qed.

Lemma names_glue : forall blk (fx1 : FPState) L1 A1 regs1 mem1 md1 pk1 c1 b1 (tb ts : list byte) Q',
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  frm_zero (@fp_csr fx1) ->
  getr regs1 11 = getr regs 10 ->
  cstr_at mem1 (bv_unsigned (getr regs1 10)) tb ts ->
  str_home L1 A1 (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1)) ->
  4096 <= bv_unsigned (getr regs1 10) -> Z.of_nat (length tb) + 1 < 2 ^ 62 ->
  bv_unsigned (getr regs1 10) + Z.of_nat (length tb + 1 + length ts) <= alloc_ceiling + 8 ->
  off_statics (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1 + length ts)) ->
  alloc_words B mem1 (lsum Lam) pk1 c1 (2 ^ 64 - 1) -> lsum Lam <= pk1 < 2 ^ 64 -> 0 <= c1 -> c1 + 1 < 2 ^ 63 ->
  res_ok_slots A1 b1 -> nroom b1 ->
  (forall (fx2 : FPState) L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md blk L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     frm_zero (@fp_csr fx2) ->
     getr regs2 10 = Z_to_bv 64 (names (ManifestMem.zbytes tb) (ManifestMem.zbytes u)) ->
     alloc_words B mem2 (lsum Lam) (nm_pk pk1) (nm_c c1) (2 ^ 64 - 1) ->
     lsum Lam <= nm_pk pk1 < 2 ^ 64 ->
     res_ok_slots A2 b1 ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SR (ms_segs B) (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 names_c.NAMES) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros blk fx1 L1 A1 regs1 mem1 md1 pk1 c1 b1 tb ts Q' IV SP1 RA1 TP1 FRM1 R11 CT HT T4 LT TB OT AW PK C0 C1
    RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & _ & _ & _ & HSC & RA & GK).
  destruct (u_cstr blk L1 A1 mem1 md1 IV) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  pose proof QT as (QF & QC0 & QC1).
  assert (LG1 : ledger B L1 A1 mem1 Lam pk1 c1 (2 ^ 64 - 1)).
  { eapply ledger_rebuild; [exact SEG | exact IV | exact LG | exact AW | lia | lia | lia]. }
  pose proof (guard_of_MR L1 A1 mem1 md1 HM1) as GC1.
  pose proof (img_strings_keep mem mem1 RA0 RA IMG) as IMG1.
  pose proof (u_statics blk L1 A1 mem1 md1 us1 IV Lus1) as OU.
  pose proof (u_home blk L1 A1 mem1 md1 IV) as UH1.
  assert (SPr : bv_unsigned (getr regs1 2) = spZ regs - 112) by exact SP1.
  eapply SR_bind.
  { apply (NAMES fx1 L1 A1 regs1 mem1 md1 b1 tb ts u us1 Lam pk1 c1 (2 ^ 64 - 1)).
    - exact SEG.
    - apply (pre_k_of_inv blk); [exact IV | exact SP1 | exact RA1 | exact TP1 | rewrite namesk_val; lia].
    - exact INIT1.
    - rewrite SPr. lia.
    - exact FRM1.
    - exact RA.
    - exact GC1.
    - exact CT.
    - rewrite R11. exact CU1.
    - exact HT.
    - rewrite R11. left. exists ua, uk. split; [exact UH1|]. lia.
    - exact T4.
    - rewrite R11. lia.
    - exact LT.
    - exact LEN.
    - exact IMG1.
    - unfold off_stack. rewrite SPr, namesk_val. left. lia.
    - unfold off_stack. rewrite SPr, R11, namesk_val. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold PREFIX_LC_STR. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold PREFIX_UC_STR. left. lia.
    - unfold off_stack. rewrite SPr, namesk_val. unfold FMT_WHOLE_STR. left. lia.
    - exact OT.
    - rewrite R11. exact OU.
    - exact LG1.
    - exact RES1.
    - exact (proj1 ROOM1).
    - exact (proj1 (proj2 ROOM1)).
    - exact (proj2 (proj2 ROOM1)). }
  intros c' POST.
  destruct POST as (fx2 & L2 & A2 & regs2 & mem2 & md2 & res & -> & FRM2 & INIT2 & BP & RES10 & _ & _ & ARMS & SLOTS).
  pose proof BP as (_ & _ & _ & RP2 & _).
  apply (K fx2 L2 A2 regs2 mem2 md2).
  - eapply (inv_bpost B API) with (K1 := NAMES_K) (regs1 := regs1) (L1 := L1) (A1 := A1) (mem1 := mem1) (md1 := md1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact BP | exact INIT2
            | rewrite ?SP1, ?crtk_val, ?namesk_val; lia].
  - exact RP2.
  - exact FRM2.
  - rewrite RES10. f_equal.
    destruct ARMS as [(Eub & Er & _) | [(_ & Ecf & _) | (_ & _ & Er & _)]].
    + rewrite Er, Eub. reflexivity.
    + lia.
    + exact Er.
  - destruct ARMS as [(Eub & Er & LG2) | [(_ & Ecf & _) | (Nub & _ & _ & LG2)]].
    + destruct (nm_nil Eub pk1 c1) as [-> ->]. exact (proj1 LG2).
    + lia.
    + destruct (nm_cons Nub pk1 c1) as [-> ->]. rewrite (Z.mod_small (c1 + 1) (2 ^ 64)) in LG2 by lia. exact (proj1 LG2).
  - destruct ARMS as [(Eub & Er & LG2) | [(_ & Ecf & _) | (Nub & _ & _ & LG2)]].
    + rewrite (proj1 (nm_nil Eub pk1 c1)). exact (proj1 (proj2 LG2)).
    + lia.
    + rewrite (proj1 (nm_cons Nub pk1 c1)). exact (proj1 (proj2 LG2)).
  - exact SLOTS.
  - apply (frame_kept NAMES_K stat_writes L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 BP HM1 SP1).
    intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
Qed.

Lemma as_ruled_glue : forall blk (fx1 : FPState) L1 A1 regs1 mem1 md1 pk1 c1 b1 (tb ts : list byte) Q',
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  frm_zero (@fp_csr fx1) ->
  getr regs1 11 = getr regs 10 ->
  cstr_at mem1 (bv_unsigned (getr regs1 10)) tb ts ->
  str_home L1 A1 (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1)) ->
  4096 <= bv_unsigned (getr regs1 10) -> Z.of_nat (length tb) + 1 < 2 ^ 62 ->
  bv_unsigned (getr regs1 10) + Z.of_nat (length tb + 1 + length ts) <= alloc_ceiling ->
  off_statics (bv_unsigned (getr regs1 10)) (Z.of_nat (length tb + 1 + length ts)) ->
  alloc_words B mem1 (lsum Lam) pk1 c1 (2 ^ 64 - 1) -> lsum Lam <= pk1 < 2 ^ 64 -> 0 <= c1 -> c1 + 1 < 2 ^ 63 ->
  res_ok_slots A1 b1 -> nroom b1 ->
  (forall (fx2 : FPState) L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md blk L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     frm_zero (@fp_csr fx2) ->
     alloc_words B mem2 (lsum Lam) (nm_pk pk1) (nm_c c1) (2 ^ 64 - 1) ->
     lsum Lam <= nm_pk pk1 < 2 ^ 64 ->
     res_ok_slots A2 b1 ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SR (ms_segs B) (mkCfg (@mkst fx2 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 AS_RULED) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros blk fx1 L1 A1 regs1 mem1 md1 pk1 c1 b1 tb ts Q' IV SP1 RA1 TP1 FRM1 R11 CT HT T4 LT TB OT AW PK C0 C1
    RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & _ & _ & _ & HSC & RA & GK).
  destruct (u_cstr blk L1 A1 mem1 md1 IV) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  pose proof QT as (QF & QC0 & QC1).
  assert (LG1 : ledger B L1 A1 mem1 Lam pk1 c1 (2 ^ 64 - 1)).
  { eapply ledger_rebuild; [exact SEG | exact IV | exact LG | exact AW | lia | lia | lia]. }
  pose proof (guard_of_MR L1 A1 mem1 md1 HM1) as GC1.
  pose proof (img_strings_keep mem mem1 RA0 RA IMG) as IMG1.
  pose proof (u_statics blk L1 A1 mem1 md1 us1 IV Lus1) as OU.
  pose proof (u_home blk L1 A1 mem1 md1 IV) as UH1.
  assert (SPr : bv_unsigned (getr regs1 2) = spZ regs - 112) by exact SP1.
  eapply SR_bind.
  { apply (ASR fx1 L1 A1 regs1 mem1 md1 b1 tb ts u us1 Lam pk1 c1 (2 ^ 64 - 1)).
    - exact SEG.
    - apply (pre_k_of_inv blk); [exact IV | exact SP1 | exact RA1 | exact TP1 | rewrite asrk_val; lia].
    - exact INIT1.
    - rewrite SPr. lia.
    - exact FRM1.
    - exact RA.
    - exact GC1.
    - exact CT.
    - rewrite R11. exact CU1.
    - exact HT.
    - rewrite R11. left. exists ua, uk. split; [exact UH1|]. lia.
    - exact T4.
    - rewrite R11. lia.
    - exact LT.
    - exact LEN.
    - exact IMG1.
    - unfold off_stack. rewrite SPr, asrk_val. left. lia.
    - unfold off_stack. rewrite SPr, R11, asrk_val. left.
      assert (C8 : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 + Z.of_nat (length us1) <= alloc_ceiling).
      { rewrite Lus1. apply ceil8_le; [lia|]. destruct Hacv as [_ Hm]. Z.div_mod_to_equations. lia. }
      lia.
    - exact OT.
    - rewrite R11. exact OU.
    - exact LG1.
    - split; [reflexivity|]. lia.
    - exact RES1.
    - exact (proj1 ROOM1).
    - exact (proj1 (proj2 ROOM1)).
    - exact (proj2 (proj2 ROOM1)). }
  intros c' POST.
  destruct POST as (fx2 & L2 & A2 & regs2 & mem2 & md2 & -> & FRM2 & INIT2 & BP & _ & _ & ARMS & SLOTS).
  pose proof BP as (_ & _ & _ & RP2 & _).
  apply (K fx2 L2 A2 regs2 mem2 md2).
  - eapply (inv_bpost B API) with (K1 := AS_RULED_K) (regs1 := regs1) (L1 := L1) (A1 := A1) (mem1 := mem1) (md1 := md1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact BP | exact INIT2
            | rewrite ?SP1, ?crtk_val, ?asrk_val; lia].
  - exact RP2.
  - exact FRM2.
  - destruct ARMS as [(Eub & LG2) | (Nub & LG2)].
    + destruct (nm_nil Eub pk1 c1) as [-> ->]. exact (proj1 LG2).
    + destruct (nm_cons Nub pk1 c1) as [-> ->]. exact (proj1 LG2).
  - destruct ARMS as [(Eub & LG2) | (Nub & LG2)].
    + rewrite (proj1 (nm_nil Eub pk1 c1)). exact (proj1 (proj2 LG2)).
    + rewrite (proj1 (nm_cons Nub pk1 c1)). exact (proj1 (proj2 LG2)).
  - exact SLOTS.
  - apply (frame_kept AS_RULED_K stat_writes L1 A1 regs1 mem1 md1 L2 A2 regs2 mem2 md2 BP HM1 SP1).
    intros a Ha. unfold stat_writes, G_LIVE, G_COUNT, G_FAIL in Ha. lia.
Qed.


Lemma frame_post : forall L1 A1 regs1 mem1 md1 E L2 A2 regs2 mem2 md2,
  call_post B MR L1 A1 regs1 mem1 md1 E L2 A2 regs2 mem2 md2 -> MR L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> (forall a, E a -> a < alloc_ceiling) ->
  forall a, spZ regs - 112 <= a < spZ regs ->
    mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a).
Proof.
  intros L1 A1 regs1 mem1 md1 E L2 A2 regs2 mem2 md2 CP HM1 SP1 HE a Ha.
  destruct pre_facts as (HAC & H63 & _).
  destruct CP as (HM2 & _ & _ & _ & _ & _ & _ & Hfr & _). rewrite SEG in Hfr.
  pose proof alloc_ceiling_val as Hacv.
  apply Hfr; [left; unfold spZ in *; pose proof (zr_word (getr regs 2)) as Z; unfold inr64 in Z; lia | | | |].
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM1 O). lia.
  - intros O. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ a HM2 O). lia.
  - intros [Sc|Sc]; [lia | unfold errno_low in ERR; lia].
  - intros He. pose proof (HE a He). lia.
Qed.

Lemma malloc_glue : forall (fx1 : FPState) L1 A1 regs1 mem1 md1 pk c b1 sz Q',
  crt_inv B API CRT_K L A regs mem md [] L1 A1 mem1 md1 ->
  spZ regs1 = spZ regs - 112 -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  getr regs1 10 = Z_to_bv 64 sz ->
  alloc_words B mem1 (lsum Lam) pk c (2 ^ 64 - 1) ->
  res_ok_slots A1 b1 -> room_slots b1 sz ->
  (forall L2 A2 regs2 mem2 md2 res,
     crt_inv B API CRT_K L A regs mem md [(res, sz)] L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     getr regs2 10 = Z_to_bv 64 res -> res mod 16 = 0 -> fresh_block B res sz ->
     alloc_words B mem2 (lsum Lam) pk c (2 ^ 64 - 1) ->
     res_ok_slots A2 (sb_malloc b1 sz) ->
     (forall a, spZ regs - 112 <= a < spZ regs ->
        mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x14ce0) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros fx1 L1 A1 regs1 mem1 md1 pk c b1 sz Q' IV SP1 RA1 TP1 A10 AW RES1 ROOM1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & _ & _ & _ & _ & _ & _ & _ & _ & RA & _).
  destruct MSO as [EM _]. rewrite <- EM.
  eapply SR_bind.
  { apply (MAL fx1 L1 A1 regs1 mem1 md1 sz b1).
    - apply call_pre_k_alloc. apply (pre_k_of_inv []); [exact IV | exact SP1 | exact RA1 | exact TP1 | unfold ALLOC_STACK; lia].
    - rewrite SEG. exact RA.
    - exact A10.
    - exact RES1.
    - exact ROOM1. }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & res & -> & CP & R10 & Rn & R16 & FB & SPL & BK & RA2 & GK2 & _ & INIT2 & _ & SLOTS).
  apply call_post_k_alloc in CP.
  pose proof CP as (_ & _ & _ & _ & _ & RP2 & _).
  apply (K L2 A2 regs2 mem2 md2 res).
  - eapply (inv_malloc B API) with (regs1 := regs1) (regs2 := regs2);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact CP | exact SPL
            | exact INIT2 | exact GK2 | (rewrite SEG in RA2; exact RA2)
            | (intros a k i Hin Hi; exact (BK a k i Hin (fun x => x) Hi))
            | rewrite ?SP1, ?crtk_val; unfold ALLOC_STACK; lia].
  - exact RP2.
  - exact R10.
  - exact R16.
  - exact FB.
  - eapply (aw_cpost B API SFA SF SNE); [exact AW | exact HM1 | exact CP | intros x _ []| rewrite SP1; unfold ALLOC_STACK; lia].
  - exact SLOTS.
  - apply (frame_post L1 A1 regs1 mem1 md1 (fun _ => False) L2 A2 regs2 mem2 md2 CP HM1 SP1). intros a [].
Qed.

Lemma free_glue : forall (fx1 : FPState) L1 A1 regs1 mem1 md1 pk c b1 res sz Q',
  crt_inv B API CRT_K L A regs mem md [(res, sz)] L1 A1 mem1 md1 -> 0 < sz ->
  spZ regs1 = spZ regs -> YK0s.ret_ok (getr regs1 1) -> getr regs1 4 = getr regs 4 ->
  getr regs1 10 = Z_to_bv 64 res ->
  alloc_words B mem1 (lsum Lam) pk c (2 ^ 64 - 1) ->
  res_ok_slots A1 b1 ->
  (forall L2 A2 regs2 mem2 md2,
     crt_inv B API CRT_K L A regs mem md [] L2 A2 mem2 md2 -> regs_preserved regs1 regs2 ->
     alloc_words B mem2 (lsum Lam) pk c (2 ^ 64 - 1) ->
     res_ok_slots A2 (sb_free b1 sz) ->
     SR (ms_segs B) (mkCfg (@mkst fx1 regs2 (getr regs1 1) mem2 (seg_rom (ms_segs B))) md2) Q') ->
  SR (ms_segs B) (mkCfg (@mkst fx1 regs1 (Z_to_bv 64 0x14ba0) mem1 (seg_rom (ms_segs B))) md1) Q'.
Proof.
  intros fx1 L1 A1 regs1 mem1 md1 pk c b1 res sz Q' IV Hsz SP1 RA1 TP1 A10 AW RES1 K.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & HWF1 & HBD1 & INIT1 & _ & (c1 & c2 & Ec1 & _) & _ & _ & HSC & RA & _).
  assert (Hin : In (res, sz) (blocks L1 A1)) by exact (blk_in L1 A1 c1 [(res, sz)] c2 res sz Ec1 (or_introl eq_refl)).
  destruct (in_blocks L1 A1 res sz Hin) as (p & Hp & Ep).
  destruct MSO as [_ EF]. rewrite <- EF.
  eapply SR_bind.
  { apply (FRE fx1 L1 A1 regs1 mem1 md1 p sz b1).
    - unfold call_pre. split; [exact HM1|]. split; [exact HWF1|]. split; [exact HBD1|]. split; [exact RA1|].
      rewrite SP1. split; [exact H16|]. split; [unfold ALLOC_STACK; lia|]. split; [exact H63|].
      split; [intros a Ha; rewrite SEG; apply HSC; left; rewrite crtk_val; unfold ALLOC_STACK in Ha; lia|].
      split; [rewrite TP1; exact HTP|].
      split; [intros a Ha; rewrite SEG; apply HSC; right; exact Ha|].
      intros H. rewrite INIT1 in H. discriminate.
    - rewrite SEG. exact RA.
    - exact Hp.
    - rewrite <- Ep. exact A10.
    - exact RES1. }
  intros c' (L2 & A2 & regs2 & mem2 & md2 & -> & CP & SPL & BK & RA2 & GK2 & _ & INIT2 & _ & SLOTS).
  pose proof CP as (_ & _ & _ & _ & _ & RP2 & _).
  rewrite <- Ep in CP, SPL, BK.
  apply (K L2 A2 regs2 mem2 md2).
  - eapply (inv_free B API) with (regs1 := regs1) (regs2 := regs2) (res := res) (sz := sz);
      first [exact SEG | exact AX | exact CTX | exact ERR | exact GS | exact IV | exact HM0 | exact CP | exact SPL
            | exact (INIT2 INIT1) | exact GK2 | exact Hsz | (rewrite SEG in RA2; exact RA2)
            | (intros a k i H1 H2 H3; exact (BK a k i H1 H2 H3))
            | rewrite ?SP1, ?crtk_val; unfold ALLOC_STACK; lia].
  - exact RP2.
  - eapply aw_cpost; first [exact SFA | exact SF | exact SNE | exact AW | exact HM1 | exact CP
                         | rewrite SP1; unfold ALLOC_STACK; lia | idtac].
    intros x Hx Hr. apply (static_not_block B API SFA AX L1 A1 mem1 md1 res sz (x - res) HM1 Hin); [lia|].
    replace (res + (x - res)) with x by lia. exact Hx.
  - exact SLOTS.
Qed.

Definition zu : list Z := ManifestMem.zbytes u.
Definition nz : Z := Z.of_nat (length u).
Definition szb : Z := 3 * nz + 64.
Definition QF : config -> Prop := crt_post B API L A regs mem md u Lam peak cnt b.
Definition fr (j : list byte) : list cell :=
  frame_cells j (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 1).
Definition blk_ok (res : Z) : Prop := res mod 16 = 0 /\ fresh_block B res szb.
Definition bm : sbound := sb_malloc b szb.

Definition kmid (blk : list (Z * Z)) (L1 : layout) (A1 : astate) (R : bvmap 5 word) (mem1 : word -> option byte)
    (md1 : Model) (pk c : Z) (b1 : sbound) : Prop :=
  crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 /\
  spZ R = spZ regs - 112 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 10 /\
  (exists j, rw_cells rsegs mem1 (spZ regs - 112) (fr j)) /\
  alloc_words B mem1 (lsum Lam) pk c (2 ^ 64 - 1) /\ lsum Lam <= pk < 2 ^ 64 /\
  res_ok_slots A1 b1.

Definition at_p1 (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1, frm_zero (@fp_csr f) /\
    kmid [] L1 A1 R mem1 md1 (nm_pk peak) (nm_c cnt) b /\
    getr R 10 = Z_to_bv 64 0 /\ getr R 19 = Z_to_bv 64 nz.

Definition at_p2 (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\ u <> [] /\
    kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) (cnt + 1) bm /\
    getr R 10 = Z_to_bv 64 res /\ getr R 9 = Z_to_bv 64 szb /\ getr R 19 = Z_to_bv 64 nz.

Definition at_p3 (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\ u <> [] /\
    kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) (cnt + 2) bm /\
    getr R 10 = Z_to_bv 64 1 /\ getr R 9 = Z_to_bv 64 szb /\ getr R 18 = Z_to_bv 64 res /\
    getr R 19 = Z_to_bv 64 nz.

Definition at_p4 (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\ u <> [] /\
    kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) (cnt + 3) bm /\
    getr R 9 = Z_to_bv 64 szb /\ getr R 18 = Z_to_bv 64 res /\ getr R 19 = Z_to_bv 64 nz.

Definition fmt_regs (R : bvmap 5 word) : Prop :=
  getr R 20 = Z_to_bv 64 0x1035d /\ getr R 21 = Z_to_bv 64 0x1041d /\
  getr R 22 = Z_to_bv 64 0x103bf /\ getr R 23 = Z_to_bv 64 0x10391.

Definition at_head (k m : nat) (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\
    kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm /\
    head_regs (getr R 8) (getr R 19) (getr R 24) (getr R 25) (getr R 26) (getr R 27) u k /\
    getr R 9 = Z_to_bv 64 szb /\ getr R 18 = Z_to_bv 64 res /\ fmt_regs R /\
    (m + rt_used zu k (length u - k + 1) = rt_nk zu)%nat /\
    forallb (fun c => negb (c =? 62)) (firstn (k - 1) zu) = true.

Definition at_t (i k m : nat) (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\
    kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat i) bm /\
    body_regs (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 24) u k res /\ fmt_regs R /\
    getr R 25 = Z_to_bv 64 (nz - Z.of_nat k) /\ getr R 26 = Z_to_bv 64 1 /\ getr R 27 = Z_to_bv 64 62 /\
    ((i < 4)%nat -> getr R 10 = Z_to_bv 64 1) /\
    forallb (fun c => negb (c =? 62)) (firstn k zu) = true /\ plain_name (skipn k zu) = true /\
    (m + 1 + rt_used zu (S k) (length u - k) = rt_nk zu)%nat.

Definition at_exit (f : FPState) (R : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
  exists L1 A1 res, frm_zero (@fp_csr f) /\ blk_ok res /\ u <> [] /\
    crt_inv B API CRT_K L A regs mem md [(res, szb)] L1 A1 mem1 md1 /\
    alloc_words B mem1 (lsum Lam) (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) (2 ^ 64 - 1) /\
    lsum Lam <= nm_pk peak < 2 ^ 64 /\
    res_ok_slots A1 bm /\
    spZ R = spZ regs /\ getr R 10 = Z_to_bv 64 res /\
    (forall r, callee_saved r -> getr R (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\ getr R 1 = getr regs 1.

Definition HeadK (k m : nat) : Prop :=
  forall f R mem1 md1, at_head k m f R mem1 md1 ->
    SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.

Lemma pf_img_free_of : forall res, blk_ok res -> pf_img_free res szb.
Proof.
  intros res (_ & _ & _ & FB) i Hi s0 Hs Hr. apply (FB i Hi). unfold in_img. rewrite SEG.
  split; [exact rsegs_ne|]. exists s0. auto.
Qed.

Lemma blk_off_img : forall res i, blk_ok res -> 0 <= i < szb -> res + i < 65536 \/ 122880 <= res + i.
Proof.
  intros res i (_ & _ & _ & FB) Hi. pose proof (FB i Hi) as N.
  destruct (off_img B SEG (res + i) N); [left | right]; lia.
Qed.

Lemma stk_norm_of : forall blk L1 A1 mem1 md1, crt_inv B API CRT_K L A regs mem md blk L1 A1 mem1 md1 ->
  stk rsegs (normalize_cj rsegs mem1) (spZ regs - 8560) (spZ regs - 112).
Proof.
  intros blk L1 A1 mem1 md1 IV. destruct pre_facts as (HAC & H63 & _).
  pose proof IV as (_ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof alloc_ceiling_val as Hacv.
  apply stk_normalize; [|lia]. apply stk_of_writable; [lia | lia |].
  intros a Ha. apply HSC. left. rewrite crtk_val. lia.
Qed.

Lemma snp_env_of : forall L1 A1 mem1 md1 res, crt_inv B API CRT_K L A regs mem md [(res, szb)] L1 A1 mem1 md1 ->
  blk_ok res -> exists junk, snp_env (normalize_cj rsegs mem1) (spZ regs - 8560) (spZ regs - 112) res szb junk.
Proof.
  intros L1 A1 mem1 md1 res IV BO.
  destruct pre_facts as (HAC & H63 & _).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & _ & _ & _ & _ & (c1 & c2 & Ec1 & _) & _ & _ & _ & RA & _).
  assert (Hin : In (res, szb) (blocks L1 A1)) by exact (blk_in L1 A1 c1 [(res, szb)] c2 res szb Ec1 (or_introl eq_refl)).
  pose proof BO as (_ & F1 & F2 & _).
  assert (Hsz : 0 <= szb) by (unfold szb, nz; lia).
  destruct (blk_rw B API L1 A1 mem1 md1 res szb HM1 Hin Hsz) as (junk & BLK).
  destruct (guard_of_MR L1 A1 mem1 md1 HM1) as (G1 & g & G2).
  destruct (YL01.ax_statics AX L1 A1 mem1 md1 HM1) as (_ & (g' & Hg' & G3) & _).
  destruct GS as [GS1 GS2]. rewrite SEG, GS1, GS2 in *.
  exists junk. unfold snp_env.
  split; [exact (stk_norm_of _ _ _ _ _ IV)|].
  split; [unfold SNPRINTF_K; lia|].
  split; [unfold IMG_END; lia|].
  split; [lia|].
  split; [apply mem_inv_normalize|].
  split; [apply crt_strings_norm; [exact RA | exact (crt_strings_keep mem mem1 RA0 RA CS0)]|].
  split; [apply bytes_at_norm; [exact RA | apply word_mem_bytes; [unfold GUARD; lia | unfold GOT_GUARD; lia | unfold GOT_GUARD; lia | exact G1] | rewrite length_le8; unfold GOT_GUARD, TASK_SIZE; lia]|].
  split; [exists (Z_to_bv 64 g'); apply bytes_at_norm; [exact RA | apply word_mem_bytes; [lia | unfold GUARD; lia | unfold GUARD; lia | exact G3] | rewrite length_le8; unfold GUARD, TASK_SIZE; lia]|].
  split; [apply rw_cells_normalize; [exact RA | exact BLK |]; intros x Hx; cbn [cells_size csize] in Hx;
          destruct (blk_off_img res (x - res) BO ltac:(lia)) as [H|H]; [left | right]; unfold TASK_SIZE; lia|].
  split; [lia|]. split; [lia|]. split; [exact (pf_img_free_of res BO)|]. split; [apply task_mem_normalize | lia].
Qed.

Lemma uenv_of : forall L1 A1 mem1 md1 res, crt_inv B API CRT_K L A regs mem md [(res, szb)] L1 A1 mem1 md1 ->
  blk_ok res -> exists us1, u_env (normalize_cj rsegs mem1) (spZ regs - 8560) res szb (bv_unsigned (getr regs 10)) u us1 /\
    cstr_at mem1 (bv_unsigned (getr regs 10)) u us1.
Proof.
  intros L1 A1 mem1 md1 res IV BO.
  destruct pre_facts as (HAC & H63 & _).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & _ & _ & _ & _ & (c1 & c2 & Ec1 & Ec0) & _ & _ & _ & RA & _).
  destruct (u_cstr [(res, szb)] L1 A1 mem1 md1 IV) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof BO as (R16 & F1 & F2 & _).
  pose proof (mr_blocks_disjoint _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as PD. rewrite Ec1 in PD.
  pose proof (pairwise_mid c1 [(res, szb)] c2 PD (ua, uk) (res, szb) ltac:(rewrite <- Ec0; exact UB) (or_introl eq_refl)) as D.
  unfold ranges_disjoint in D. cbn [fst snd] in D.
  set (y := bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1) in *.
  assert (Hy : y <= ua + uk) by (unfold y; lia).
  assert (Hc : y + (- y) mod 8 <= alloc_ceiling).
  { apply ceil8_le; [lia|]. destruct Hacv as [_ Hm]. Z.div_mod_to_equations. lia. }
  exists us1. split; [|exact CU1].
  split; [apply cstr_normalize; [exact RA | exact CU1 | unfold y in *; unfold TASK_SIZE; lia]|].
  split; [lia|]. split; [unfold y in *; lia|].
  destruct D as [D|D].
  - left. assert (Hr : y + (- y) mod 8 <= res) by (apply ceil8_le; [lia | Z.div_mod_to_equations; lia]). unfold y in *. lia.
  - right. lia.
Qed.

Lemma text_ok : forall L1 A1 mem1 md1 res (T : list Z) (junk : list byte),
  crt_inv B API CRT_K L A regs mem md [(res, szb)] L1 A1 mem1 md1 -> blk_ok res ->
  length junk = Z.to_nat szb -> Z.of_nat (length T) + 1 <= szb ->
  str_home L1 A1 res (Z.of_nat (length (pf_bytes T) + 1)) /\ 4096 <= res /\
  Z.of_nat (length (pf_bytes T)) + 1 < 2 ^ 62 /\
  res + Z.of_nat (length (pf_bytes T) + 1 + length (skipn (length T + 1) junk)) <= alloc_ceiling /\
  off_statics res (Z.of_nat (length (pf_bytes T) + 1 + length (skipn (length T + 1) junk))).
Proof.
  intros L1 A1 mem1 md1 res T junk IV BO Lj LT.
  pose proof IV as (HM1 & _ & _ & _ & _ & (c1 & c2 & Ec1 & _) & _).
  assert (Hin : In (res, szb) (blocks L1 A1)) by exact (blk_in L1 A1 c1 [(res, szb)] c2 res szb Ec1 (or_introl eq_refl)).
  pose proof BO as (_ & F1 & F2 & _).
  assert (Lt : Z.of_nat (length (pf_bytes T) + 1 + length (skipn (length T + 1) junk)) = szb).
  { unfold pf_bytes. rewrite length_map, length_skipn, Lj. unfold szb, nz in *. lia. }
  rewrite Lt. unfold pf_bytes. rewrite length_map.
  split; [left; exists res, szb; split; [exact Hin | lia]|].
  split; [lia|]. split; [unfold szb, nz in *; lia|]. split; [lia|].
  apply off_statics_in; [unfold szb, nz; lia|]. intros z Hz.
  replace z with (res + (z - res)) by lia.
  apply (static_not_block B API SFA AX L1 A1 mem1 md1 res szb (z - res) HM1 Hin). lia.
Qed.

Lemma kmid_after : forall blk L1 A1 R1 mem1 md1 pk c b1 R2 mem2 W,
  kmid blk L1 A1 R1 mem1 md1 pk c b1 ->
  munch W mem1 mem2 -> wmono rsegs mem1 mem2 -> ro_agree rsegs mem2 ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ outside W x ->
     (spZ regs - 8560 <= x < spZ regs - 112) \/ exists a k, In (a, k) blk /\ a <= x < a + k) ->
  spZ R2 = spZ regs - 112 -> getr R2 3 = getr regs 3 -> getr R2 4 = getr regs 4 -> getr R2 8 = getr regs 10 ->
  kmid blk L1 A1 R2 mem2 md1 pk c b1.
Proof.
  intros blk L1 A1 R1 mem1 md1 pk c b1 R2 mem2 W KM MU WM RA2 HW S2 G3 G4 G8.
  destruct KM as (IV & _ & _ & _ & _ & (j & FR) & AW & PK & RES).
  destruct pre_facts as (HAC & H63 & _).
  pose proof alloc_ceiling_val as Hacv.
  pose proof IV as (HM1 & _ & _ & _ & _ & (c1 & c2 & Ec1 & _) & _).
  assert (BL : forall x a k, In (a, k) blk -> a <= x < a + k -> 0 <= x < alloc_ceiling /\ ~ in_img B x).
  { intros x a k Hin Hx.
    destruct (blk_off B API AX L1 A1 mem1 md1 a k (x - a) HM1 (blk_in L1 A1 c1 blk c2 a k Ec1 Hin) ltac:(lia)) as [NI LO].
    replace (a + (x - a)) with x in NI, LO by lia. split; [lia | exact NI]. }
  assert (OH : forall x, spZ regs - 112 <= x < 2 ^ 64 -> outside W x).
  { intros x Hx. destruct (outside_dec W x) as [O|O]; [exact O|]. exfalso.
    destruct (HW x ltac:(lia) O) as [Hs|(a & k & Hin & Hr)]; [lia|].
    destruct (BL x a k Hin Hr). lia. }
  split.
  { eapply (inv_munch B API) with (W := W); first [exact SEG | exact AX | exact CTX | exact GS | exact IV | exact MU
      | exact WM | exact RA2 | rewrite crtk_val; lia | idtac].
    intros x Hx O. destruct (HW x Hx O) as [Hs|Hb]; [left; rewrite crtk_val; lia | right; exact Hb]. }
  split; [exact S2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G8|].
  split.
  { exists j. apply (rw_cells_keep mem1 mem2 _ _ FR). intros a Ha. cbn [fr frame_cells cells_size csize] in Ha.
    split; [apply (mbyte_munch _ W); [exact MU | lia | apply OH; lia]|].
    apply (writable_munch _ W); [exact MU | lia | apply OH; lia]. }
  split.
  { apply (aw_munch B mem1 mem2 W _ _ _ _ AW MU). intros x Hx.
    destruct (SFA x Hx) as (Hi & _ & _). pose proof (in_img_low B SEG x Hi) as Hl.
    destruct (outside_dec W x) as [O|O]; [exact O|]. exfalso.
    destruct (HW x ltac:(lia) O) as [Hs|(a & k & Hin & Hr)]; [lia|].
    destruct (BL x a k Hin Hr) as [_ NI]. exact (NI Hi). }
  split; [exact PK | exact RES].
Qed.

Lemma kmid_call : forall blk L1 A1 R1 mem1 md1 pk c b1 L2 A2 R2 mem2 md2 pk' c' b2,
  kmid blk L1 A1 R1 mem1 md1 pk c b1 -> crt_inv B API CRT_K L A regs mem md blk L2 A2 mem2 md2 ->
  regs_preserved R1 R2 ->
  alloc_words B mem2 (lsum Lam) pk' c' (2 ^ 64 - 1) -> lsum Lam <= pk' < 2 ^ 64 -> res_ok_slots A2 b2 ->
  (forall a, spZ regs - 112 <= a < spZ regs ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  kmid blk L2 A2 R2 mem2 md2 pk' c' b2.
Proof.
  intros blk L1 A1 R1 mem1 md1 pk c b1 L2 A2 R2 mem2 md2 pk' c' b2 KM IV2 RP AW PK RES FK.
  destruct KM as (_ & S1 & G3 & G4 & G8 & (j & FR) & _).
  split; [exact IV2|].
  split; [unfold spZ in *; rewrite <- S1; f_equal; exact (RP 2 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G3; exact (RP 3 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G4; exact (RP 4 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G8; exact (RP 8 ltac:(unfold callee_saved; lia))|].
  split; [exists j; apply (rw_cells_keep mem1 mem2 _ _ FR); intros a Ha; cbn [fr frame_cells cells_size csize] in Ha; apply FK; lia|].
  split; [exact AW|]. split; [exact PK | exact RES].
Qed.

Lemma len_zu : length zu = length u.
Proof. unfold zu. apply length_map. Qed.

Lemma room_m : nroom bm.
Proof. unfold nroom, bm, sb_malloc, szb, nz. cbn [sb_live sb_bytes sb_cap]. lia. Qed.

Lemma room_b : nroom b.
Proof. unfold nroom. lia. Qed.

Lemma rt_nk_le : (rt_nk zu <= length u - 1)%nat.
Proof. unfold rt_nk. pose proof (rt_used_le zu (length zu) 1). rewrite len_zu in *. lia. Qed.

Lemma st_p3 : (forall f R mem1 md1, at_p4 f R mem1 md1 ->
     SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133bc) mem1 (seg_rom (ms_segs B))) md1) QF) ->
  forall f R mem1 md1, at_p3 f R mem1 md1 ->
    SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x13390) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros P4 f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R10 & R9 & R18 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_wx SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk).
    - exact R10.
    - exact R9.
    - exact R18.
    - exact NL.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13a38) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x133bc) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 2) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_wholex (ManifestMem.zbytes u)) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_wholex, length_zb; unfold szb, nz; lia|].
  rewrite <- SEG.
  apply (as_ruled_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 2) bm
           (pf_bytes (txt_wholex (ManifestMem.zbytes u))) (skipn (length (txt_wholex (ManifestMem.zbytes u)) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. exact TB.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 AW3 PK3 SL FK.
    rewrite Q1. apply P4.
    destruct (nm_cons NE (nm_pk peak) (cnt + 2)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|]. split; [exact NE|].
    split; [replace (cnt + 3) with (cnt + 2 + 1) by lia; exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK)|].
    split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
    split; [transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Definition PtK (P : FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (pc : Z) : Prop :=
  forall f R mem1 md1, P f R mem1 md1 ->
    SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 pc) mem1 (seg_rom (ms_segs B))) md1) QF.

Lemma e_zu_cons : u <> [] -> exists x r, zu = x :: r.
Proof.
  intros NE. destruct zu as [|x r] eqn:E; [|exists x, r; reflexivity].
  exfalso. apply NE. apply length_zero_iff_nil. rewrite <- len_zu, E. reflexivity.
Qed.

Lemma e_rt_cons : u <> [] ->
  rt_calls zu = 3 + 4 * Z.of_nat (rt_nk zu) /\
  rt_peak zu (lsum Lam) peak = nm_pk peak.
Proof.
  intros NE. destruct (nm_cons NE peak cnt) as [EP _]. rewrite EP.
  destruct (e_zu_cons NE) as (x & r & E).
  rewrite <- len_zu. rewrite E.
  split; reflexivity.
Qed.

Lemma st_exit : PtK at_exit 0x14ba0.
Proof.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & IV & AW & PK & RES & SP & R10 & CS & R1).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NK.
  destruct (e_rt_cons NE) as (EC & EP).
  apply (free_glue f L1 A1 R mem1 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) bm res szb).
  - exact IV.
  - unfold szb, nz. lia.
  - exact SP.
  - rewrite R1. exact HRA.
  - exact (CS 4 ltac:(unfold callee_saved; lia)).
  - exact R10.
  - exact AW.
  - exact RES.
  - intros L2 A2 regs2 mem2 md2 IV2 RP AW2 RES2.
    pose proof IV2 as (_ & _ & _ & INIT2 & _).
    assert (RPa : regs_preserved regs regs2).
    { intros r Hr. transitivity (getr R (Z_to_bv 5 r)); [exact (RP r Hr) | exact (CS r Hr)]. }
    rewrite R1. apply SR_ret. unfold QF, crt_post.
    exists f, L2, A2, regs2, mem2, md2.
    split; [reflexivity|].
    split; [exact FRM|].
    split; [exact INIT2|].
    split; [eapply (bpost_of_inv B API); first [exact SEG | exact IV2 | exact RPa]|].
    split; [destruct (u_cstr [] L2 A2 mem2 md2 IV2) as (us1 & CU1 & _); exists us1; exact CU1|].
    change (ManifestMem.zbytes u) with zu.
    split.
    + rewrite EP, EC.
      replace (cnt + (3 + 4 * Z.of_nat (rt_nk zu))) with (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) by lia.
      eapply ledger_rebuild; [exact SEG | exact IV2 | exact LG | exact AW2 | lia | lia | lia].
    + unfold bm in RES2. rewrite sb_free_malloc in RES2. exact RES2.
Qed.

Lemma exit_cont : forall s ms' (Fx : bvmap 5 word) (fcx : bv 32) (sp0 : Z)
    (gp tp t0 t1 t2 r10 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) R mem1 md1 L1 A1 res c b1,
  ms_rel_cj rsegs s (exit_state (getr regs 1) sp0 gp tp t0 t1 t2 (getr regs 8) (getr regs 9) r10 a1 a2 a3 a4 a5 a6 a7
    (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
    (getr regs 25) (getr regs 26) (getr regs 27) t3 t4 t5 t6 Fx fcx (normalize_cj rsegs mem1)) ->
  cj_same rsegs mem1 (ms_mem s) -> ms_eqv s ms' ->
  PtK at_exit 0x14ba0 -> frm_zero fcx -> blk_ok res -> u <> [] ->
  kmid [(res, szb)] L1 A1 R mem1 md1 (nm_pk peak) c b1 ->
  sp0 = spZ regs - 112 -> gp = getr regs 3 -> tp = getr regs 4 -> r10 = Z_to_bv 64 res ->
  c = cnt + 3 + 4 * Z.of_nat (rt_nk zu) -> b1 = bm ->
  SR (ms_segs B) (mkCfg ms' md1) QF.
Proof.
  intros s ms' Fx fcx sp0 gp tp t0 t1 t2 r10 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 R mem1 md1 L1 A1 res c b1
    REL ROS EQV EX FRM BO NE KM -> -> -> -> -> ->.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & _ & AW & PK & RES).
  pose proof IV as (_ & _ & _ & _ & _ & _ & _ & _ & _ & RA1 & _).
  destruct pre_facts as (HAC & H63 & _).
  unfold exit_state in REL.
  destruct (ka_post s _ Fx (Z_to_bv 64 0x14ba0) fcx (normalize_cj rsegs mem1) ms' mem1 [] REL ROS EQV RA1
    (munch_refl _ _) (wmono_refl _ _)) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (KM2 : kmid [(res, szb)] L1 A1 R mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R mem2 [] KM MU2 WM2 RA2); try assumption.
    intros x Hx O. exfalso. apply O. exact I. }
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  rewrite <- SEG. apply (EX (mkFP Fx fcx) R2 mem2 md1).
  exists L1, A1, res. split; [exact FRM|]. split; [exact BO|]. split; [exact NE|].
  split; [exact IV2|]. split; [exact AW2|]. split; [exact PK2|]. split; [exact RES2|].
  split.
  { unfold spZ at 1. rewrite <- (getr_eqv _ _ XR).
    change (bv_unsigned (Z_to_bv 64 (spZ regs - 112 + 112)) = spZ regs).
    replace (spZ regs - 112 + 112) with (spZ regs) by lia. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
  split; [|rewrite <- (getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite <- (getr_eqv _ _ XR (Z_to_bv 5 r)). unfold callee_saved in Hr.
  assert (HC : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct HC as [-> | HC].
  - change (Z_to_bv 64 (spZ regs - 112 + 112) = getr regs (Z_to_bv 5 2)).
    replace (spZ regs - 112 + 112) with (spZ regs) by lia. unfold spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - destruct HC as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]];
      reflexivity.
Qed.

Lemma st_t4 : PtK at_exit 0x14ba0 -> forall k m, HeadK (S k) (S m) -> PtK (at_t 4 k m) 0x134b4.
Proof.
  intros EX k m HK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FMT & R25 & R26 & R27 & _ & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof BR as (R9 & R18 & R19 & R24 & Hk & HL & S0p & S0b).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (Nat.lt_ge_cases (S k) (length u)) as [LT|GE].
  - eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_next with (n := Z.of_nat (length u)) (k := Z.of_nat k).
      - exact R19.
      - exact R24.
      - exact R25.
      - lia.
      - lia.
      - lia.
      - exact S0b. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ (Z_to_bv 64 0x133f4) _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (H8 : getr R2 8 = getr R 8) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4)
                    bm).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    rewrite <- SEG. apply (HK _ R2 mem2 md1).
    exists L1, A1, res. split; [exact FRM|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat (S m)) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4) by lia.
      replace (2 + 4 * S m)%nat with (2 + 4 * m + 4)%nat by lia. exact KM2. }
    split.
    { unfold head_regs. rewrite H8.
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); rewrite Nat2Z.inj_succ; reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); exact R26|].
      split; [rewrite <- (getr_eqv _ _ XR); exact R27|].
      split; [lia|]. split; [lia|]. split; [exact S0p | exact S0b]. }
    split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
    split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
    split.
    { destruct FMT as (F20 & F21 & F22 & F23). unfold fmt_regs. rewrite <- !(getr_eqv _ _ XR).
      exact (conj F20 (conj F21 (conj F22 F23))). }
    split.
    { replace (length u - S k + 1)%nat with (length u - k)%nat by lia. lia. }
    replace (S k - 1)%nat with k by lia. exact FA.
  - assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
    assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (fr j)).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx.
      cbn [fr frame_cells cells_size csize] in Hx. right. lia. }
    assert (RU : rt_used zu (S k) (length u - k) = 0%nat).
    { replace (length u - k)%nat with 1%nat by lia. cbn [rt_used]. rewrite len_zu.
      replace ((S k <? length u)%nat) with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
    assert (NK : rt_nk zu = S m) by lia.
    eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_last with (n := Z.of_nat (length u)) (k := Z.of_nat k).
      - exact R25.
      - lia.
      - lia.
      - lia.
      - exact FRn.
      - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    eapply exit_cont; [exact REL | exact ROS | exact EQV | exact EX | exact FRM | exact BO | exact NE | exact KM
      | exact S1 | exact G3 | exact G4 | exact R18 | rewrite NK; lia | reflexivity].
Qed.

Lemma cs_cases : forall r, callee_saved r -> r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/
  r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27.
Proof. unfold callee_saved. lia. Qed.

Lemma cs_post : forall (R R2 : bvmap 5 word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  xregs_eqv (mkR ra (Sem.reg_get R 2) (Sem.reg_get R 3) (Sem.reg_get R 4) t0 t1 t2 (Sem.reg_get R 8) (Sem.reg_get R 9)
     a0 a1 a2 a3 a4 a5 a6 a7 (Sem.reg_get R 18) (Sem.reg_get R 19) (Sem.reg_get R 20) (Sem.reg_get R 21)
     (Sem.reg_get R 22) (Sem.reg_get R 23) (Sem.reg_get R 24) (Sem.reg_get R 25) (Sem.reg_get R 26) (Sem.reg_get R 27)
     t3 t4 t5 t6) R2 ->
  forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r).
Proof.
  intros R R2 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 XR r Hr.
  rewrite <- (getr_eqv _ _ XR).
  pose proof (cs_cases r Hr) as C.
  repeat (destruct C as [C|C]; [subst r; reflexivity|]). subst r. reflexivity.
Qed.

Lemma t_regs : forall (R R' : bvmap 5 word) k res,
  (forall r, callee_saved r -> getr R' (Z_to_bv 5 r) = getr R (Z_to_bv 5 r)) ->
  body_regs (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 24) u k res -> fmt_regs R ->
  getr R 25 = Z_to_bv 64 (nz - Z.of_nat k) -> getr R 26 = Z_to_bv 64 1 -> getr R 27 = Z_to_bv 64 62 ->
  body_regs (getr R' 8) (getr R' 9) (getr R' 18) (getr R' 19) (getr R' 24) u k res /\ fmt_regs R' /\
  getr R' 25 = Z_to_bv 64 (nz - Z.of_nat k) /\ getr R' 26 = Z_to_bv 64 1 /\ getr R' 27 = Z_to_bv 64 62.
Proof.
  intros R R' k res H BR FM E25 E26 E27.
  assert (X8 : getr R' 8 = getr R 8) by exact (H 8 ltac:(unfold callee_saved; lia)).
  assert (X9 : getr R' 9 = getr R 9) by exact (H 9 ltac:(unfold callee_saved; lia)).
  assert (X18 : getr R' 18 = getr R 18) by exact (H 18 ltac:(unfold callee_saved; lia)).
  assert (X19 : getr R' 19 = getr R 19) by exact (H 19 ltac:(unfold callee_saved; lia)).
  assert (X20 : getr R' 20 = getr R 20) by exact (H 20 ltac:(unfold callee_saved; lia)).
  assert (X21 : getr R' 21 = getr R 21) by exact (H 21 ltac:(unfold callee_saved; lia)).
  assert (X22 : getr R' 22 = getr R 22) by exact (H 22 ltac:(unfold callee_saved; lia)).
  assert (X23 : getr R' 23 = getr R 23) by exact (H 23 ltac:(unfold callee_saved; lia)).
  assert (X24 : getr R' 24 = getr R 24) by exact (H 24 ltac:(unfold callee_saved; lia)).
  assert (X25 : getr R' 25 = getr R 25) by exact (H 25 ltac:(unfold callee_saved; lia)).
  assert (X26 : getr R' 26 = getr R 26) by exact (H 26 ltac:(unfold callee_saved; lia)).
  assert (X27 : getr R' 27 = getr R 27) by exact (H 27 ltac:(unfold callee_saved; lia)).
  unfold fmt_regs in *.
  rewrite X8, X9, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27.
  exact (conj BR (conj FM (conj E25 (conj E26 E27)))).
Qed.

Lemma st_t3 : forall k m, PtK (at_t 4 k m) 0x134b4 -> PtK (at_t 3 k m) 0x13488.
Proof.
  intros k m P4. unfold PtK in P4.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t1x SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F23.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13a38) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x134b4) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t1x (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t1x _ _ LK), length_zb; unfold szb, nz; lia|].
  rewrite <- SEG.
  apply (as_ruled_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3)
           bm (pf_bytes (txt_t1x (ManifestMem.zbytes u) k))
           (skipn (length (txt_t1x (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. exact TB.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 AW3 PK3 SL FK.
    rewrite Q1. apply P4.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 4) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3 + 1) by lia.
      replace (2 + 4 * m + 4)%nat with (S (2 + 4 * m + 3)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split; [intros H4; lia|].
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma st_t2 : forall k m, PtK (at_t 3 k m) 0x13488 -> PtK (at_t 2 k m) 0x1345c.
Proof.
  intros k m P3. unfold PtK in P3.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t3 SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F22.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13488) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t3 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t3 _ _ LK), length_zb; unfold szb, nz; lia|].
  assert (ZF : Forall (fun c => 0 <= c < 256) (txt_t3 (ManifestMem.zbytes u) k)).
  { eapply Forall_impl; [|exact (nz_t3 _ k (zb_nz u (proj1 (proj2 CU1))))]. intros c Hc. cbv beta in Hc |- *. lia. }
  rewrite <- SEG.
  apply (names_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2)
           bm (pf_bytes (txt_t3 (ManifestMem.zbytes u) k))
           (skipn (length (txt_t3 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply P3.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 3) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2 + 1) by lia.
      replace (2 + 4 * m + 3)%nat with (S (2 + 4 * m + 2)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split.
    { intros _. rewrite R10', (zbytes_pf _ ZF). f_equal. apply rt_t3; [rewrite length_zb; lia | exact FA | exact PN]. }
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma st_t1 : forall k m, PtK (at_t 2 k m) 0x1345c -> PtK (at_t 1 k m) 0x13430.
Proof.
  intros k m P2. unfold PtK in P2.
  intros f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & BR & FM & R25 & R26 & R27 & R10i & FA & PN & CNT).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof rt_nk_le as NKL.
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof BR as (B9 & B18 & B19 & B24 & Hk & Hu & HU0 & HU1).
  pose proof FM as (F20 & F21 & F22 & F23).
  assert (NE : u <> []) by (intros E; apply length_zero_iff_nil in E; lia).
  assert (LK : (k <= length (ManifestMem.zbytes u))%nat) by (rewrite length_zb; lia).
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t2 SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact BR.
    - exact (R10i ltac:(lia)).
    - exact R26.
    - exact F21.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  pose proof (cs_post R R2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ XR) as CS.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x1345c) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact B18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t2 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite (len_t2 _ _ LK), length_zb; unfold szb, nz; lia|].
  assert (ZF : Forall (fun c => 0 <= c < 256) (txt_t2 (ManifestMem.zbytes u) k)).
  { eapply Forall_impl; [|exact (nz_t2 _ k (zb_nz u (proj1 (proj2 CU1))))]. intros c Hc. cbv beta in Hc |- *. lia. }
  rewrite <- SEG.
  apply (names_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1)
           bm (pf_bytes (txt_t2 (ManifestMem.zbytes u) k))
           (skipn (length (txt_t2 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply P2.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (CS2 : forall r, callee_saved r -> getr regs2 (Z_to_bv 5 r) = getr R (Z_to_bv 5 r))
      by (intros r Hr; exact (eq_trans (RP r Hr) (CS r Hr))).
    destruct (t_regs R regs2 k res CS2 BR FM R25 R26 R27) as (BR2 & FM2 & E25 & E26 & E27).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 2) with (cnt + 3 + 4 * Z.of_nat m + Z.of_nat 1 + 1) by lia.
      replace (2 + 4 * m + 2)%nat with (S (2 + 4 * m + 1)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split; [exact BR2|]. split; [exact FM2|]. split; [exact E25|]. split; [exact E26|]. split; [exact E27|].
    split.
    { intros _. rewrite R10', (zbytes_pf _ ZF). f_equal. apply rt_t2; [rewrite length_zb; lia | exact FA | exact PN]. }
    split; [exact FA|]. split; [exact PN | exact CNT].
Qed.

Lemma h_firstn_snoc : forall (l : list Z) i, (i < length l)%nat -> firstn (S i) l = firstn i l ++ [nth i l 0].
Proof.
  induction l as [|x l IH]; intros [|i] H; cbn [length] in H; try lia; [reflexivity|].
  cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.

Lemma h_fb_step : forall (l : list Z) k, (1 <= k <= length l)%nat ->
  forallb (fun c => negb (c =? 62)) (firstn (k - 1) l) = true -> byte_at l (k - 1) <> 62 ->
  forallb (fun c => negb (c =? 62)) (firstn k l) = true.
Proof.
  intros l k Hk F Bn. destruct k as [|k]; [lia|].
  replace (S k - 1)%nat with k in F, Bn by lia.
  rewrite (h_firstn_snoc l k) by lia. rewrite forallb_app, F. cbn [forallb andb].
  unfold byte_at in Bn. apply Z.eqb_neq in Bn. rewrite Bn. reflexivity.
Qed.

Lemma h_rt_p : forall (l : list Z) k f, (k < length l)%nat -> byte_at l (k - 1) <> 62 ->
  plain_name (skipn k l) = true -> rt_used l k (S f) = S (rt_used l (S k) f).
Proof.
  intros l k f Hk Hb Hp. cbn [rt_used].
  destruct ((k <? length l)%nat && negb (byte_at l (k - 1) =? 62)) eqn:E.
  - rewrite Hp. reflexivity.
  - exfalso. apply andb_false_iff in E as [E|E].
    + apply Nat.ltb_ge in E. lia.
    + apply negb_false_iff, Z.eqb_eq in E. exact (Hb E).
Qed.

Lemma h_rt_np : forall (l : list Z) k f, (k < length l)%nat -> byte_at l (k - 1) <> 62 ->
  plain_name (skipn k l) = false -> rt_used l k (S f) = rt_used l (S k) f.
Proof.
  intros l k f Hk Hb Hp. cbn [rt_used].
  destruct ((k <? length l)%nat && negb (byte_at l (k - 1) =? 62)) eqn:E.
  - rewrite Hp. reflexivity.
  - exfalso. apply andb_false_iff in E as [E|E].
    + apply Nat.ltb_ge in E. lia.
    + apply negb_false_iff, Z.eqb_eq in E. exact (Hb E).
Qed.

Lemma h_rt_gt : forall (l : list Z) k f, byte_at l (k - 1) = 62 -> rt_used l k (S f) = 0%nat.
Proof.
  intros l k f Hb. cbn [rt_used]. rewrite Hb.
  destruct (k <? length l)%nat; reflexivity.
Qed.

Lemma h_rt_end : forall (l : list Z) k f, (length l <= k)%nat -> rt_used l k f = 0%nat.
Proof.
  intros l k [|f] Hk; [reflexivity|]. cbn [rt_used].
  replace (k <? length l)%nat with false by (symmetry; apply Nat.ltb_ge; exact Hk).
  reflexivity.
Qed.

Lemma h_exit_regs : forall (S : Z) (gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) R2,
  S = spZ regs - 112 -> gp = getr regs 3 -> tp = getr regs 4 ->
  xregs_eqv (mkR (getr regs 1) (Z_to_bv 64 (S + 112)) gp tp t0 t1 t2 (getr regs 8) (getr regs 9) s2 a1 a2 a3 a4 a5 a6 a7
     (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
     (getr regs 25) (getr regs 26) (getr regs 27) t3 t4 t5 t6) R2 ->
  spZ R2 = spZ regs /\ getr R2 10 = s2 /\
  (forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\ getr R2 1 = getr regs 1.
Proof.
  intros S gp tp t0 t1 t2 s2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 R2 ES Eg Et XR.
  assert (SP : Z_to_bv 64 (S + 112) = getr regs 2).
  { rewrite ES. replace (spZ regs - 112 + 112) with (spZ regs) by lia. unfold spZ. apply Z_to_bv_bv_unsigned. }
  split.
  { unfold spZ. rewrite <- (getr_eqv _ _ XR). transitivity (bv_unsigned (Z_to_bv 64 (S + 112))); [reflexivity|].
    rewrite SP. reflexivity. }
  split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
  split; [|rewrite <- (getr_eqv _ _ XR); reflexivity].
  intros r Hr. rewrite <- (getr_eqv _ _ XR). unfold callee_saved in Hr.
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
              r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct C as [C|[C|[C|C]]]; [subst r; exact SP | subst r; exact Eg | subst r; exact Et |].
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]; subst r; reflexivity.
Qed.

Lemma h_at_exit : forall f R R2 mem2 md1 L1 A1 res, frm_zero (@fp_csr f) -> blk_ok res -> u <> [] ->
  kmid [(res, szb)] L1 A1 R mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu)) bm ->
  spZ R2 = spZ regs -> getr R2 10 = Z_to_bv 64 res ->
  (forall r, callee_saved r -> getr R2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> getr R2 1 = getr regs 1 ->
  at_exit f R2 mem2 md1.
Proof.
  intros f R R2 mem2 md1 L1 A1 res FRM BO NE (IV & _ & _ & _ & _ & _ & AW & PK & RES) S2 R10 CS R1.
  exists L1, A1, res.
  exact (conj FRM (conj BO (conj NE (conj IV (conj AW (conj PK (conj RES (conj S2 (conj R10 (conj CS R1)))))))))).
Qed.

Lemma h_gt : PtK at_exit 0x14ba0 -> forall k m f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) = 62 ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros EX k m f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BG.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_gt zu k (length u - k) BG) in CNT.
  assert (Em : m = rt_nk zu) by lia. subst m.
  assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ regs - 112) (fr j)).
  { apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx. cbn [fr frame_cells cells_size csize] in Hx.
    right. lia. }
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply crt_gt with (u := u) (us := us1) (j := j) (k := k)
      (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18) (xs3 := getr regs 19) (xs4 := getr regs 20)
      (xs5 := getr regs 21) (xs6 := getr regs 22) (xs7 := getr regs 23) (xs8 := getr regs 24) (xs9 := getr regs 25)
      (xs10 := getr regs 26) (xs11 := getr regs 27) (xra := getr regs 1).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BG.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact FRn.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
  intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0. unfold exit_state in REL.
  destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  destruct (h_exit_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2 S1 G3 G4 XR) as (S2 & R10 & CS & R1).
  assert (KM2 : kmid [(res, szb)] L1 A1 R (ms_mem s) md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R (ms_mem s) [] KM MU2 WM2 RA2); try assumption.
    intros x _ O. exfalso. apply O. exact I. }
  rewrite <- SEG. apply EX.
  apply (h_at_exit _ R R2 (ms_mem s) md1 L1 A1 res); [exact FRM | exact BO | exact NE | exact KM2 | exact S2 | | exact CS | exact R1].
  rewrite R10. exact R18.
Qed.

Lemma h_np_last : PtK at_exit 0x14ba0 -> forall k m f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = false -> (k + 1 = length u)%nat ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros EX k m f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN HL.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & U0 & ULo & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  replace (length u - k + 1)%nat with (S (S O)) in CNT by lia.
  rewrite (h_rt_np zu k 1 ltac:(rewrite len_zu; lia) BN PN) in CNT.
  rewrite (h_rt_end zu (S k) 1 ltac:(rewrite len_zu; lia)) in CNT.
  assert (Em : m = rt_nk zu) by lia. subst m.
  assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ regs - 112) (fr j)).
  { apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx. cbn [fr frame_cells cells_size csize] in Hx.
    right. lia. }
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_np_last PLN) with (lo := spZ regs - 8560) (u := u) (us := us1) (j := j) (k := k)
      (xs0 := getr regs 8) (xs1 := getr regs 9) (xs2 := getr regs 18) (xs3 := getr regs 19) (xs4 := getr regs 20)
      (xs5 := getr regs 21) (xs6 := getr regs 22) (xs7 := getr regs 23) (xs8 := getr regs 24) (xs9 := getr regs 25)
      (xs10 := getr regs 26) (xs11 := getr regs 27) (xra := getr regs 1).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BN.
    - exact PN.
    - exact HL.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact (stk_norm_of _ _ _ _ _ IV).
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia.
    - apply mem_inv_normalize.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact ULo.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact FRn.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI).
  subst s0. unfold exit_state in REL.
  destruct (ka_post s _ _ _ _ _ ms' mem1 _ REL ROS EQV RA1 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  destruct (h_exit_regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R2 S1 G3 G4 XR) as (S2 & R10 & CS & R1).
  assert (KM2 : kmid [(res, szb)] L1 A1 R (ms_mem s) md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat (rt_nk zu))
                  bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R (ms_mem s) _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O. left. lia. }
  rewrite <- SEG. apply EX.
  apply (h_at_exit _ R R2 (ms_mem s) md1 L1 A1 res); [exact FRM | exact BO | exact NE | exact KM2 | exact S2 | | exact CS | exact R1].
  rewrite R10. exact R18.
Qed.

Lemma h_np_next : forall k m, HeadK (S k) m -> forall f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = false -> (k + 1 < length u)%nat ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros k m HK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN HL.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  pose proof UE as (CUn & U0 & ULo & _).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_np zu k (length u - k) ltac:(rewrite len_zu; lia) BN PN) in CNT.
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_np_next PLN) with (lo := spZ regs - 8560) (u := u) (us := us1) (k := k).
    - exact HR.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact CUn.
    - exact BN.
    - exact PN.
    - exact HL.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact (stk_norm_of _ _ _ _ _ IV).
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia.
    - apply mem_inv_normalize.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact ULo. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
    E & MU & WM & MI).
  subst s0.
  destruct (ka_post s _ _ _ _ _ ms' mem1 _ REL ROS EQV RA1 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O. left. lia. }
  rewrite <- SEG. apply HK.
  exists L1, A1, res. split; [exact FRM|]. split; [exact BO|]. split; [exact KM2|].
  split.
  { unfold head_regs. rewrite <- !(getr_eqv _ _ XR).
    refine (conj eq_refl (conj eq_refl (conj eq_refl (conj E10 (conj E11 (conj _ (conj Hu (conj H0 H256)))))))).
    lia. }
  split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
  split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
  split; [unfold fmt_regs; rewrite <- !(getr_eqv _ _ XR); exact FM|].
  split; [replace (length u - S k + 1)%nat with (length u - k)%nat by lia; exact CNT|].
  replace (S k - 1)%nat with k by lia.
  apply h_fb_step; [rewrite len_zu; lia | exact FB | exact BN].
Qed.

Lemma h_t1 : forall k m, PtK (at_t 1 k m) 0x13430 -> forall f R mem1 md1, at_head k m f R mem1 md1 ->
  byte_at zu (k - 1) <> 62 -> plain_name (skipn k zu) = true ->
  SR (ms_segs B) (mkCfg (@mkst f R (Z_to_bv 64 0x133f4) mem1 (seg_rom (ms_segs B))) md1) QF.
Proof.
  intros k m TK f R mem1 md1 (L1 & A1 & res & FRM & BO & KM & HR & R9 & R18 & FM & CNT & FB) BN PN.
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  pose proof HR as (E3 & E8 & E9 & E10 & E11 & Hk & Hu & H0 & H256).
  assert (NE : u <> []) by (intros E; rewrite E in Hk; cbn in Hk; lia).
  pose proof FM as (F20 & F21 & F22 & F23).
  replace (length u - k + 1)%nat with (S (length u - k)) in CNT by lia.
  rewrite (h_rt_p zu k (length u - k) ltac:(rewrite len_zu; lia) BN PN) in CNT.
  pose proof rt_nk_le as NK.
  assert (FBk : forallb (fun c => negb (c =? 62)) (firstn k zu) = true)
    by (apply h_fb_step; [rewrite len_zu; lia | exact FB | exact BN]).
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_t1 PLN SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk) (k := k).
    - exact HR.
    - exact R9.
    - exact R18.
    - exact F20.
    - exact BN.
    - exact PN.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13430) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr R 8) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q8' : getr R2 8 = getr regs 10) by (rewrite Q8; exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); exact R18).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q19 : getr R2 19 = getr R 19) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q20 : getr R2 20 = Z_to_bv 64 0x1035d) by (rewrite <- (getr_eqv _ _ XR); exact F20).
  assert (Q21 : getr R2 21 = Z_to_bv 64 0x1041d) by (rewrite <- (getr_eqv _ _ XR); exact F21).
  assert (Q22 : getr R2 22 = Z_to_bv 64 0x103bf) by (rewrite <- (getr_eqv _ _ XR); exact F22).
  assert (Q23 : getr R2 23 = Z_to_bv 64 0x10391) by (rewrite <- (getr_eqv _ _ XR); exact F23).
  assert (Q24 : getr R2 24 = getr R 24) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q25 : getr R2 25 = getr R 25) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q26 : getr R2 26 = getr R 26) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q27 : getr R2 27 = getr R 27) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_t1 (ManifestMem.zbytes u) k) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_t1, length_zb by (rewrite length_zb; lia); unfold szb, nz; lia|].
  rewrite <- SEG.
  apply (names_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m) bm
           (pf_bytes (txt_t1 (ManifestMem.zbytes u) k)) (skipn (length (txt_t1 (ManifestMem.zbytes u) k) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply TK.
    destruct (nm_cons NE (nm_pk peak) (cnt + 3 + 4 * Z.of_nat m)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    assert (P8 : getr regs2 8 = getr R 8)
      by (transitivity (getr R2 8); [exact (RP 8 ltac:(unfold callee_saved; lia)) | exact Q8]).
    assert (P9 : getr regs2 9 = Z_to_bv 64 szb)
      by (transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]).
    assert (P18 : getr regs2 18 = Z_to_bv 64 res)
      by (transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]).
    assert (P19 : getr regs2 19 = getr R 19)
      by (transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19]).
    assert (P20 : getr regs2 20 = Z_to_bv 64 0x1035d)
      by (transitivity (getr R2 20); [exact (RP 20 ltac:(unfold callee_saved; lia)) | exact Q20]).
    assert (P21 : getr regs2 21 = Z_to_bv 64 0x1041d)
      by (transitivity (getr R2 21); [exact (RP 21 ltac:(unfold callee_saved; lia)) | exact Q21]).
    assert (P22 : getr regs2 22 = Z_to_bv 64 0x103bf)
      by (transitivity (getr R2 22); [exact (RP 22 ltac:(unfold callee_saved; lia)) | exact Q22]).
    assert (P23 : getr regs2 23 = Z_to_bv 64 0x10391)
      by (transitivity (getr R2 23); [exact (RP 23 ltac:(unfold callee_saved; lia)) | exact Q23]).
    assert (P24 : getr regs2 24 = getr R 24)
      by (transitivity (getr R2 24); [exact (RP 24 ltac:(unfold callee_saved; lia)) | exact Q24]).
    assert (P25 : getr regs2 25 = getr R 25)
      by (transitivity (getr R2 25); [exact (RP 25 ltac:(unfold callee_saved; lia)) | exact Q25]).
    assert (P26 : getr regs2 26 = getr R 26)
      by (transitivity (getr R2 26); [exact (RP 26 ltac:(unfold callee_saved; lia)) | exact Q26]).
    assert (P27 : getr regs2 27 = getr R 27)
      by (transitivity (getr R2 27); [exact (RP 27 ltac:(unfold callee_saved; lia)) | exact Q27]).
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|].
    split.
    { replace (2 + 4 * m + 1)%nat with (S (2 + 4 * m)) by lia.
      exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK). }
    split.
    { unfold body_regs. rewrite P8, P9, P18, P19, P24.
      exact (conj eq_refl (conj eq_refl (conj E3 (conj E8 (conj Hk (conj Hu (conj H0 H256))))))). }
    split; [unfold fmt_regs; rewrite P20, P21, P22, P23; exact (conj eq_refl (conj eq_refl (conj eq_refl eq_refl)))|].
    split; [rewrite P25; exact E9|].
    split; [rewrite P26; exact E10|].
    split; [rewrite P27; exact E11|].
    split.
    { intros _. rewrite R10'. f_equal. rewrite zbytes_pf.
      - apply rt_t1; [rewrite length_zb; lia | exact FBk | exact PN].
      - eapply Forall_impl; [|apply nz_t1; apply zbytes_nz; exact (proj1 (proj2 CU1))]. intros c Hc. cbv beta in Hc |- *. lia. }
    split; [exact FBk|]. split; [exact PN|]. lia.
Qed.

Lemma st_head : PtK at_exit 0x14ba0 -> (forall k m, HeadK (S k) (S m) -> PtK (at_t 1 k m) 0x13430) ->
  forall k m, HeadK k m.
Proof.
  intros EX T1.
  assert (IND : forall n k m, (length u - k = n)%nat -> HeadK k m).
  { induction n as [|n IH]; intros k m En f R mem1 md1 HD.
    - exfalso. destruct HD as (L1 & A1 & res & _ & _ & _ & (_ & _ & _ & _ & _ & Hk & _) & _). lia.
    - pose proof HD as (L1 & A1 & res & _ & _ & _ & (_ & _ & _ & _ & _ & Hk & _) & _).
      destruct (Z.eq_dec (byte_at zu (k - 1)) 62) as [BG|BN].
      + exact (h_gt EX k m f R mem1 md1 HD BG).
      + destruct (plain_name (skipn k zu)) eqn:PN.
        * exact (h_t1 k m (T1 k m (IH (S k) (S m) ltac:(lia))) f R mem1 md1 HD BN PN).
        * destruct (Nat.eq_dec (k + 1) (length u)) as [HL|HL].
          -- exact (h_np_last EX k m f R mem1 md1 HD BN PN HL).
          -- exact (h_np_next k m (IH (S k) m ltac:(lia)) f R mem1 md1 HD BN PN ltac:(lia)). }
  intros k m. exact (IND _ k m eq_refl).
Qed.

Lemma st_p4 : PtK at_exit 0x14ba0 -> HeadK 1 0 -> PtK at_p4 0x133bc.
Proof.
  intros EX HK f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R9 & R18 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  destruct u_bounds as (UB1 & UB2).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  destruct (Nat.eq_dec (length u) 1) as [E1|E1].
  - assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (fr j)).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |]. intros x Hx.
      cbn [fr frame_cells cells_size csize] in Hx. right. lia. }
    assert (NK : rt_nk zu = 0%nat).
    { unfold rt_nk. rewrite len_zu, E1. cbn [rt_used]. rewrite len_zu, E1. reflexivity. }
    assert (R19' : getr R 19 = Z_to_bv 64 1) by (rewrite R19; unfold nz; rewrite E1; reflexivity).
    eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_init1.
      - exact R19'.
      - exact FRn.
      - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    eapply exit_cont; [exact REL | exact ROS | exact EQV | exact EX | exact FRM | exact BO | exact NE | exact KM
      | exact S1 | exact G3 | exact G4 | exact R18 | rewrite NK; lia | reflexivity].
  - eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_init with (n := Z.of_nat (length u)).
      - exact R19.
      - lia.
      - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. lia. }
    intros s s0 P0 REL ROS ms' EQV.
    destruct P0 as (a0' & a1' & a2' & a3' & E0). subst s0.
    destruct (ka_post s _ _ (Z_to_bv 64 0x133f4) _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (H19 : getr R2 19 = Z_to_bv 64 (bv_unsigned (getr R2 8) + Z.of_nat 1))
      by (rewrite <- !(getr_eqv _ _ XR); reflexivity).
    assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 3) bm).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    rewrite <- SEG. apply (HK _ R2 mem2 md1).
    exists L1, A1, res. split; [exact FRM|]. split; [exact BO|].
    split; [replace (cnt + 3 + 4 * Z.of_nat 0) with (cnt + 3) by lia; exact KM2|].
    split.
    { unfold head_regs.
      split; [exact H19|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [rewrite <- (getr_eqv _ _ XR); reflexivity|].
      split; [lia|]. split; [lia|]. rewrite Q8. split; lia. }
    split; [rewrite <- (getr_eqv _ _ XR); exact R9|].
    split; [rewrite <- (getr_eqv _ _ XR); exact R18|].
    split.
    { unfold fmt_regs. rewrite <- !(getr_eqv _ _ XR).
      split; [reflexivity|]. split; [reflexivity|]. split; reflexivity. }
    split; [|reflexivity].
    unfold rt_nk. rewrite len_zu. replace (length u - 1 + 1)%nat with (length u) by lia. reflexivity.
Qed.

Lemma st_p2 : PtK at_p3 0x13390 -> PtK at_p2 0x13364.
Proof.
  intros P3 f R mem1 md1 (L1 & A1 & res & FRM & BO & NE & KM & R10 & R9 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (snp_env_of L1 A1 mem1 md1 res IV BO) as (junk & SE).
  destruct (uenv_of L1 A1 mem1 md1 res IV BO) as (us1 & UE & CU1).
  assert (Lj : length junk = Z.to_nat szb) by (destruct SE as (_ & _ & _ & _ & _ & _ & _ & _ & BLK & _); destruct BLK as [[[Lj _] _] _]; exact Lj).
  assert (NL : (1 <= length u <= 255)%nat).
  { assert (length u <> 0)%nat by (intros H0; apply NE; apply length_zero_iff_nil; exact H0). lia. }
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_whole SNP) with (lo := spZ regs - 8560) (res := res) (u := u) (us := us1) (junk := junk).
    - exact R10.
    - exact R9.
    - exact NL.
    - exact FRM.
    - change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. exact SE.
    - change (Sem.reg_get R 8) with (getr R 8). rewrite G8. exact UE. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & m' &
    E & FRM' & MU & WM & MI & TC). subst s0.
  destruct (ka_post s _ Ft (Z_to_bv 64 0x13c1c) fc' m' ms' mem1 _ REL ROS EQV RA1 MU WM)
    as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13390) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); exact R9).
  assert (Q18 : getr R2 18 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
  assert (Q10 : getr R2 10 = Z_to_bv 64 res) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
  change (bv_unsigned (Sem.reg_get R 2)) with (spZ R) in MU2. rewrite S1 in MU2.
  assert (KM2 : kmid [(res, szb)] L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 1) bm).
  { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 _ KM MU2 WM2 RA2); try assumption.
    intros x Hx O. cbn [outside] in O.
    destruct (Z_lt_le_dec x (spZ regs - 112)) as [H1|H1].
    - destruct (Z_le_gt_dec (spZ regs - 8560) x) as [H2|H2]; [left; lia|].
      right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia.
    - right. exists res, szb. split; [left; reflexivity|]. unfold szb, nz in *. lia. }
  pose proof (cstr_rel mem2 m' res _ _ MR2 TC) as TC2.
  pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
  assert (UQ : bv_unsigned (getr R2 10) = res) by (rewrite Q10; apply unsigned_lit; destruct BO as (_ & F1 & F2 & _); unfold szb, nz in *; lia).
  destruct (text_ok L1 A1 mem2 md1 res (txt_whole (ManifestMem.zbytes u)) junk IV2 BO Lj)
    as (HT & T4 & LT & TB & OT); [rewrite len_whole, length_zb; unfold szb, nz; lia|].
  rewrite <- SEG.
  apply (names_glue [(res, szb)] (mkFP Ft fc') L1 A1 R2 mem2 md1 (nm_pk peak) (cnt + 1) bm
           (pf_bytes (txt_whole (ManifestMem.zbytes u))) (skipn (length (txt_whole (ManifestMem.zbytes u)) + 1) junk)).
  - exact IV2.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM'.
  - exact Q11.
  - rewrite UQ. exact TC2.
  - rewrite UQ. exact HT.
  - rewrite UQ. exact T4.
  - exact LT.
  - rewrite UQ. lia.
  - rewrite UQ. exact OT.
  - exact AW2.
  - exact PK2.
  - lia.
  - lia.
  - exact RES2.
  - exact room_m.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10' AW3 PK3 SL FK.
    rewrite Q1. apply (P3 fx2 regs2 mem3 md2).
    destruct (nm_cons NE (nm_pk peak) (cnt + 1)) as [EP EC].
    destruct (nm_cons NE peak cnt) as [EP0 _].
    assert (EPP : nm_pk (nm_pk peak) = nm_pk peak) by (rewrite EP, EP0; apply Zmax_idem).
    rewrite EPP, EC in AW3. rewrite EPP in PK3.
    exists L2, A2, res. split; [exact FRM2|]. split; [exact BO|]. split; [exact NE|].
    split; [replace (cnt + 2) with (cnt + 1 + 1) by lia; exact (kmid_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KM2 IV3 RP AW3 PK3 SL FK)|].
    split.
    { rewrite R10'. f_equal. rewrite zbytes_pf; [apply rt_whole; rewrite length_zb; lia|].
      pose proof (nz_whole _ (zbytes_nz u (proj1 (proj2 CU1)))) as Hn.
      rewrite Forall_forall in Hn |- *. intros c Hc. specialize (Hn c Hc). lia. }
    split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
    split; [transitivity (getr R2 18); [exact (RP 18 ltac:(unfold callee_saved; lia)) | exact Q18]|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma e_kmid_call : forall blk blk2 L1 A1 R1 mem1 md1 pk c b1 L2 A2 R2 mem2 md2 pk' c' b2,
  kmid blk L1 A1 R1 mem1 md1 pk c b1 -> crt_inv B API CRT_K L A regs mem md blk2 L2 A2 mem2 md2 ->
  regs_preserved R1 R2 ->
  alloc_words B mem2 (lsum Lam) pk' c' (2 ^ 64 - 1) -> lsum Lam <= pk' < 2 ^ 64 -> res_ok_slots A2 b2 ->
  (forall a, spZ regs - 112 <= a < spZ regs ->
     mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)) ->
  kmid blk2 L2 A2 R2 mem2 md2 pk' c' b2.
Proof.
  intros blk blk2 L1 A1 R1 mem1 md1 pk c b1 L2 A2 R2 mem2 md2 pk' c' b2 KM IV2 RP AW PK RES FK.
  destruct KM as (_ & S1 & G3 & G4 & G8 & (j & FR) & _).
  split; [exact IV2|].
  split; [unfold spZ in *; rewrite <- S1; f_equal; exact (RP 2 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G3; exact (RP 3 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G4; exact (RP 4 ltac:(unfold callee_saved; lia))|].
  split; [rewrite <- G8; exact (RP 8 ltac:(unfold callee_saved; lia))|].
  split; [exists j; apply (rw_cells_keep mem1 mem2 _ _ FR); intros a Ha; cbn [fr frame_cells cells_size csize] in Ha; apply FK; lia|].
  split; [exact AW|]. split; [exact PK | exact RES].
Qed.

Lemma st_p1 : PtK at_p2 0x13364 -> PtK at_p1 0x13348.
Proof.
  intros P2. unfold PtK in P2. intros f R mem1 md1 (L1 & A1 & FRM & KM & R10 & R19).
  pose proof KM as (IV & S1 & G3 & G4 & G8 & (j & FR) & AW & PK & RES).
  pose proof IV as (HM1 & _ & _ & INIT1 & _ & _ & _ & _ & HSC & RA1 & _).
  destruct (mr_model _ _ (aa_laws API) L1 A1 mem1 md1 HM1) as (Hh & Hl & _).
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  destruct (Nat.eq_dec (length u) 0) as [E0|E0].
  - assert (EU : u = []) by (apply length_zero_iff_nil; exact E0).
    assert (NZ : nz = 0) by (unfold nz; rewrite E0; reflexivity).
    rewrite NZ in R19.
    assert (FRn : rw_cells rsegs (normalize_cj rsegs mem1) (spZ R) (frame_cells j (getr regs 8) (getr regs 9)
      (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
      (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 1))).
    { rewrite S1. apply rw_cells_normalize; [exact RA1 | exact FR |].
      intros x Hx. cbn [frame_cells cells_size csize] in Hx. right. lia. }
    eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_zero; [exact R10 | exact R19 | exact FRn |].
      change (bv_unsigned (Sem.reg_get R 2)) with (spZ R). rewrite S1. lia. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q2 : getr R2 2 = getr regs 2).
    { rewrite <- (getr_eqv _ _ XR).
      transitivity (Z_to_bv 64 (spZ R + 112)); [reflexivity|].
      rewrite S1. apply bv_eq. rewrite unsigned_lit by lia. unfold spZ. lia. }
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (RP0 : regs_preserved regs R2).
    { intros r Hr. unfold callee_saved in Hr.
      assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct C as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
        first [exact Q2 | exact Q3 | exact Q4 | rewrite <- (getr_eqv _ _ XR); reflexivity]. }
    assert (IV2 : crt_inv B API CRT_K L A regs mem md [] L1 A1 mem2 md1).
    { eapply (inv_munch B API) with (W := []); first [exact SEG | exact AX | exact CTX | exact GS | exact IV
        | exact MU2 | exact WM2 | exact RA2 | rewrite crtk_val; lia | idtac].
      intros x Hx O. exfalso. apply O. exact I. }
    destruct (nm_nil EU peak cnt) as [EP EC].
    rewrite EP, EC in AW. rewrite EP in PK.
    rewrite (ret_pc_ok _ HRA). rewrite <- SEG. apply SR_ret. unfold QF, crt_post.
    eexists _, L1, A1, R2, mem2, md1.
    split; [reflexivity|].
    split; [exact FRM|].
    split; [exact INIT1|].
    split; [eapply (bpost_of_inv B API); first [exact SEG | exact IV2 | exact RP0]|].
    split; [destruct (u_cstr [] L1 A1 mem2 md1 IV2) as (us1 & CU1 & _); exists us1; exact CU1|].
    rewrite EU. cbn [ManifestMem.zbytes map rt_peak rt_calls].
    split; [|exact RES].
    rewrite Z.add_0_r.
    eapply ledger_rebuild; [exact SEG | exact IV2 | exact LG | | lia | lia | lia].
    apply (aw_munch B mem1 mem2 [] _ _ _ _ AW MU2). intros x _. exact I.
  - assert (NE : u <> []) by (intros E; apply E0; rewrite E; reflexivity).
    assert (NL : 1 <= nz <= 255) by (unfold nz; lia).
    eapply (ka_step (ms_segs B)); [exact SEG | exact RA1 | exact Hh | exact Hl | |].
    { unfold mkR_of. eapply crt_mal with (n := nz); [exact R10 | exact R19 | exact NL]. }
    intros s s0 P0 REL ROS ms' EQV. cbv beta in P0. subst s0.
    destruct (ka_post s _ _ _ _ _ ms' mem1 [] REL ROS EQV RA1 (munch_refl _ _) (wmono_refl _ _))
      as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
    set (mem2 := ms_mem s) in *.
    assert (Q1 : getr R2 1 = Z_to_bv 64 0x13364) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q2 : spZ R2 = spZ regs - 112) by (unfold spZ; rewrite <- (getr_eqv _ _ XR); exact S1).
    assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); exact G3).
    assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); exact G4).
    assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); exact G8).
    assert (Q9 : getr R2 9 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q10 : getr R2 10 = Z_to_bv 64 szb) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
    assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); exact R19).
    assert (KM2 : kmid [] L1 A1 R2 mem2 md1 (nm_pk peak) (nm_c cnt) b).
    { apply (kmid_after _ _ _ _ _ _ _ _ _ R2 mem2 [] KM MU2 WM2 RA2); try assumption.
      intros x Hx O. exfalso. apply O. exact I. }
    pose proof KM2 as (IV2 & _ & _ & _ & _ & _ & AW2 & PK2 & RES2).
    destruct (nm_cons NE peak cnt) as [EP EC].
    assert (HR1 : room_slots b szb) by (apply room_slots_small; unfold szb, nz; lia).
    rewrite <- SEG.
    apply (malloc_glue _ L1 A1 R2 mem2 md1 (nm_pk peak) (nm_c cnt) b szb).
    + exact IV2.
    + exact Q2.
    + rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
    + exact Q4.
    + exact Q10.
    + exact AW2.
    + exact RES2.
    + exact HR1.
    + intros L2 A2 regs2 mem3 md2 res IV3 RP R10' R16 FB AW3 SL FK.
      rewrite Q1. apply P2.
      exists L2, A2, res. split; [exact FRM|]. split; [exact (conj R16 FB)|]. split; [exact NE|].
      split.
      { rewrite EC in AW3.
        eapply e_kmid_call; [exact KM2 | exact IV3 | exact RP | exact AW3 | exact PK2 | exact SL | exact FK]. }
      split; [exact R10'|].
      split; [transitivity (getr R2 9); [exact (RP 9 ltac:(unfold callee_saved; lia)) | exact Q9]|].
      transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma st_entry : PtK at_p1 0x13348 ->
  SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) QF.
Proof.
  intros P1. unfold PtK in P1.
  destruct pre_facts as (HAC & H63 & H16 & HRA & HTP & HM0).
  pose proof alloc_ceiling_val as Hacv.
  pose proof QT as (QF0 & QC0 & QC1).
  pose proof LG as (AW0 & PK0 & _).
  rewrite QF0 in AW0.
  destruct (mr_model _ _ (aa_laws API) L A mem md HM0) as (Hh & Hl & _).
  assert (IV0 : crt_inv B API CRT_K L A regs mem md [] L A mem md).
  { eapply (inv_init B API); first [exact SEG | exact PRE | exact INIT0 | exact RA0]. }
  pose proof IV0 as (_ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  destruct (u_cstr [] L A mem md IV0) as (us1 & CU1 & Lus1).
  destruct u_bounds as (UB1 & UB2).
  pose proof (ceil8_ge (bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1)) as Rus.
  assert (STK : stk rsegs (normalize_cj rsegs mem) (spZ regs - 8560) (spZ regs)).
  { apply stk_normalize; [|lia]. apply stk_of_writable; [lia | lia |].
    intros a Ha. apply HSC. left. rewrite crtk_val. lia. }
  eapply (ka_step (ms_segs B)); [exact SEG | exact RA0 | exact Hh | exact Hl | |].
  { unfold mkR_of.
    eapply (crt_pro STRL) with (lo := spZ regs - 8560) (u := u) (us := us1).
    - exact STK.
    - change (bv_unsigned (Sem.reg_get regs 2)) with (spZ regs). lia.
    - apply mem_inv_normalize.
    - assert (C8 : bv_unsigned (getr regs 10) + Z.of_nat (length u) + 1 + Z.of_nat (length us1) <= alloc_ceiling).
      { rewrite Lus1. apply ceil8_le; [lia|]. destruct Hacv as [_ Hm]. Z.div_mod_to_equations. lia. }
      apply cstr_normalize; [exact RA0 | exact CU1 |]. try change (Sem.reg_get regs 10) with (getr regs 10). lia.
    - change (bv_unsigned (Sem.reg_get regs 2)) with (spZ regs).
      change (Sem.reg_get regs 10) with (getr regs 10). lia. }
  intros s s0 P0 REL ROS ms' EQV.
  destruct P0 as (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & junk & m' &
    E & FR' & MU & WM & MI). subst s0.
  destruct (ka_post s _ _ _ _ _ ms' mem _ REL ROS EQV RA0 MU WM) as (R2 & -> & XR & MR2 & MU2 & WM2 & RA2).
  set (mem2 := ms_mem s) in *.
  assert (Q1 : getr R2 1 = Z_to_bv 64 0x13348) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q2 : spZ R2 = spZ regs - 112).
  { change (spZ R2) with (bv_unsigned (getr R2 2)). rewrite <- (getr_eqv _ _ XR).
    change (bv_unsigned (Z_to_bv 64 (spZ regs + -112)) = spZ regs - 112).
    rewrite unsigned_lit by lia. lia. }
  assert (Q3 : getr R2 3 = getr regs 3) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q4 : getr R2 4 = getr regs 4) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q8 : getr R2 8 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q10 : getr R2 10 = Z_to_bv 64 0x102e7) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q11 : getr R2 11 = getr regs 10) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (Q19 : getr R2 19 = Z_to_bv 64 nz) by (rewrite <- (getr_eqv _ _ XR); reflexivity).
  assert (MU3 : munch [(spZ regs - 112, spZ regs)] mem mem2) by exact MU2.
  assert (IV1 : crt_inv B API CRT_K L A regs mem md [] L A mem2 md).
  { eapply (inv_munch B API) with (W := [(spZ regs - 112, spZ regs)]); first [exact SEG | exact AX | exact CTX
      | exact GS | exact IV0 | exact MU3 | exact WM2 | exact RA2 | rewrite crtk_val; lia | idtac].
    intros x Hx O. left. rewrite crtk_val. cbn [outside] in O. lia. }
  assert (FR2 : rw_cells rsegs mem2 (spZ regs - 112) (fr junk)) by exact (rw_cells_rel mem2 m' _ _ MR2 FR').
  assert (AW1 : alloc_words B mem2 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply (aw_munch B mem mem2 [(spZ regs - 112, spZ regs)] _ _ _ _ AW0 MU3).
    intros x Hx. unfold alloc_statics, G_LIVE, G_PEAK, G_COUNT, G_FAIL in Hx. cbn [outside]. split; [lia | exact I]. }
  pose proof (crt_strings_keep mem mem2 RA0 RA2 CS0) as (CE & _).
  assert (UQ : bv_unsigned (getr R2 10) = 0x102e7) by (rewrite Q10; apply unsigned_lit; lia).
  rewrite <- SEG.
  apply (names_glue [] _ L A R2 mem2 md peak cnt b [] []).
  - exact IV1.
  - exact Q2.
  - rewrite Q1. apply ret_ok_even. vm_compute. reflexivity.
  - exact Q4.
  - exact FRM0.
  - exact Q11.
  - rewrite UQ. split; [exact CE|]. split; [constructor|]. apply Z.leb_le. reflexivity.
  - rewrite UQ. right. intros i Hi. cbn [length] in Hi. apply ro_first. lia.
  - rewrite UQ. lia.
  - cbn [length]. lia.
  - rewrite UQ. cbn [length]. lia.
  - rewrite UQ. unfold off_statics, G_LIVE, G_COUNT, G_FAIL. cbn [length]. lia.
  - exact AW1.
  - exact PK0.
  - exact QC0.
  - lia.
  - exact RES0.
  - exact room_b.
  - intros fx2 L2 A2 regs2 mem3 md2 IV3 RP FRM2 R10n AW3 PK3 SL FK.
    rewrite Q1. apply P1.
    exists L2, A2. split; [exact FRM2|].
    split.
    { split; [exact IV3|].
      split; [transitivity (spZ R2); [unfold spZ; f_equal; exact (RP 2 ltac:(unfold callee_saved; lia)) | exact Q2]|].
      split; [transitivity (getr R2 3); [exact (RP 3 ltac:(unfold callee_saved; lia)) | exact Q3]|].
      split; [transitivity (getr R2 4); [exact (RP 4 ltac:(unfold callee_saved; lia)) | exact Q4]|].
      split; [transitivity (getr R2 8); [exact (RP 8 ltac:(unfold callee_saved; lia)) | exact Q8]|].
      split; [exists junk; apply (rw_cells_keep mem2 mem3 _ _ FR2); intros a Ha;
              cbn [fr frame_cells cells_size csize] in Ha; apply FK; lia|].
      split; [exact AW3|]. split; [exact PK3 | exact SL]. }
    split; [rewrite R10n; f_equal; apply rt_empty|].
    transitivity (getr R2 19); [exact (RP 19 ltac:(unfold callee_saved; lia)) | exact Q19].
Qed.

Lemma crt_all : SR (ms_segs B) (mkCfg (@mkst fx regs (Z_to_bv 64 CHECK_ROUND_TRIP) mem (seg_rom (ms_segs B))) md) QF.
Proof.
  pose proof st_exit as EX.
  assert (T1 : forall k m, HeadK (S k) (S m) -> PtK (at_t 1 k m) 0x13430).
  { intros k m HK. exact (st_t1 k m (st_t2 k m (st_t3 k m (st_t4 EX k m HK)))). }
  pose proof (st_head EX T1) as HD.
  exact (st_entry (st_p1 (st_p2 (st_p3 (st_p4 EX (HD 1%nat 0%nat)))))).
Qed.

End G.
