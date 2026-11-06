(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c. *)
(* Modified by Theorem Labs: for reac-repacer/fuzz_uci. Sections G / G2 are
   libreac/fuzz_decode's released lib/Prog/crt_glue.v with its module paths changed and its one decode-specific
   import (check_braid_c, for braid_map) dropped. Section Body is the invariant layer of that release's
   lib/Prog/check_round_trip.v `Section Body` (cr_inv, cr_pre, cr_inv_call, cr_inv_A, cr_inv_kept, cr_heap_E,
   cr_free_keep, cr_old_in, cr_frame_call), with the one change that the function's own stack size is the section
   variable K instead of decode's CRT_STACK, and with cr_frame_call generalised from decode's fixed frame cell list
   to any (base, cells): so fuzz_uci's check_no_overread and check_value, whose frames differ, share one copy. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YM05 YL0i YL01 YO10.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib Require Import Contract KindBGlue Img0.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Lib Require MState Mem Frame Exec Regs6ss RegisterBridge
Cells Step.
Import ListNotations.
Local Open Scope Z_scope.

Lemma crt_vm : forall vm1 vm2 md, with_vmmaps vm2 (with_vmmaps vm1 md) = with_vmmaps vm2 md.
Proof. intros vm1 vm2 [f [mp lz mt] io fs pr li ti]. reflexivity. Qed.

Lemma crt_rm : forall {T : Type} (x : T) a1 a2 b1 b2, ~ In x (a1 ++ a2) -> a1 ++ x :: a2 = b1 ++ x :: b2 ->
  a1 ++ a2 = b1 ++ b2.
Proof.
  intros T x a1. induction a1 as [|y a1 IH]; intros a2 b1 b2 Hn E; destruct b1 as [|z b1]; cbn in *.
  - injection E as E. exact E.
  - injection E as E1 E2. subst z. exfalso. apply Hn. rewrite E2. apply in_or_app. right. left. reflexivity.
  - injection E as E1 E2. subst y. exfalso. apply Hn. left. reflexivity.
  - injection E as E1 E2. subst z. f_equal. apply IH; [intros H; apply Hn; right; exact H | exact E2].
Qed.

Lemma crt_pw_mid : forall (l1 l2 : list (Z * Z)) x y, pairwise ranges_disjoint (l1 ++ x :: l2) ->
  In y (l1 ++ l2) -> ranges_disjoint x y.
Proof.
  induction l1 as [|z l1 IH]; intros l2 x y H Hy; cbn in H, Hy.
  - destruct H as [H _]. exact (H y Hy).
  - destruct H as [Hz H]. destruct Hy as [<-|Hy].
    + pose proof (Hz x ltac:(apply in_or_app; right; left; reflexivity)) as D. unfold ranges_disjoint in *. lia.
    + exact (IH l2 x y H Hy).
Qed.

Lemma crt_notin : forall (l1 l2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) -> 0 < snd x ->
  ~ In x (l1 ++ l2).
Proof.
  intros l1 l2 x H Hx Hin. pose proof (crt_pw_mid l1 l2 x x H Hin) as D. unfold ranges_disjoint in D. lia.
Qed.

Lemma crt_bu : forall L A a k, In (a, k) (blocks L A) -> exists p, In (p, k) (user_blocks A) /\ ptr_addr L p = a.
Proof.
  intros L A a k Hin. unfold blocks in Hin. apply in_map_iff in Hin.
  destruct Hin as ([q k'] & E & Hq). cbn [fst snd] in E. injection E as E1 E2. subst k'.
  exists q. split; [exact Hq | exact E1].
Qed.

Lemma crt_ub : forall L A p k, In (p, k) (user_blocks A) -> In (ptr_addr L p, k) (blocks L A).
Proof. intros L A p k H. unfold blocks. apply in_map_iff. exists (p, k). split; [reflexivity | exact H]. Qed.

Lemma crt_wx : wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma crt_pw_del : forall (l1 l2 : list (Z * Z)) x, pairwise ranges_disjoint (l1 ++ x :: l2) ->
  pairwise ranges_disjoint (l1 ++ l2).
Proof.
  induction l1 as [|z l1 IH]; intros l2 x H; cbn in H |- *.
  - exact (proj2 H).
  - destruct H as [Hz H]. split; [|exact (IH l2 x H)].
    intros y Hy. apply Hz. apply in_app_or in Hy. apply in_or_app.
    destruct Hy as [Hy|Hy]; [left; exact Hy | right; right; exact Hy].
Qed.

Lemma crt_in_ins : forall {T : Type} (l1 l2 : list T) x y, In y (l1 ++ l2) -> In y (l1 ++ x :: l2).
Proof.
  intros T l1 l2 x y H. apply in_app_or in H. apply in_or_app.
  destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma crt_in_mid : forall {T : Type} (l1 l2 : list T) x, In x (l1 ++ x :: l2).
Proof. intros. apply in_or_app. right. left. reflexivity. Qed.

Lemma crt_fst_unique : forall {X Y : Type} (l : list (X * Y)) x a c, List.NoDup (map fst l) ->
  In (x, a) l -> In (x, c) l -> a = c.
Proof.
  induction l as [|[x' y'] l IH]; intros x a c ND Ha Hc; [destruct Ha|].
  cbn in ND. inversion ND as [|? ? Hn ND']; subst.
  destruct Ha as [Ea|Ha]; destruct Hc as [Ec|Hc].
  - injection Ea as E1 E2. injection Ec as E3 E4. congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. apply in_map_iff. exists (x, c). split; [reflexivity | exact Hc].
  - injection Ec as E1 E2. subst. exfalso. apply Hn. apply in_map_iff. exists (x, a). split; [reflexivity | exact Ha].
  - exact (IH x a c ND' Ha Hc).
Qed.

Lemma crt_pw : forall (l1 l2 : list (Z * Z)) a n c k, pairwise ranges_disjoint (l1 ++ (a, n) :: l2) ->
  In (c, k) (l1 ++ l2) -> a + n <= c \/ c + k <= a.
Proof. intros l1 l2 a n c k H Hi. exact (crt_pw_mid l1 l2 (a, n) (c, k) H Hi). Qed.

Section G.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Lemma crt_run_fp : forall regs pc mem md
    (K : bvmap 5 word -> bvmap 5 word -> word -> bv 32 -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt (ms_segs B) (fun ms => exists R F pc' fc mem',
      ms = MState.MS R F pc' fc None mem' (seg_rom (ms_segs B)) /\ K R F pc' fc mem')
    (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom (ms_segs B))) ->
  (forall R F pc' fc mem' regs', K R F pc' fc mem' -> (forall r, getr regs' r = getr R r) ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP F fc) regs' pc' mem' (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md K P Hh Hl HE HK.
  eapply (evt_SR_canon (ms_segs B) (mkst regs pc mem (seg_rom (ms_segs B))) _ md P); [exact HE | exact Hh | exact Hl |].
  intros ms' (can & (R & F & pc' & fc & mem' & -> & HKR) & Heq).
  destruct Heq as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF, Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ _ _ regs' HKR). apply kb_getr_eqv. exact HR.
Qed.

Lemma crt_runA : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_fregs ms = fp_regs /\
     ms_fcsr ms = fp_csr /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms regs', Q ms -> (forall r, getr regs' r = getr (ms_regs ms) r) ->
     SR (ms_segs B) (mkCfg (mkst regs' (ms_pc_val ms) (ms_mem ms) (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl HE HQ HK. rewrite <- HS in HE, HQ.
  apply (kb_run B regs pc mem md (fun R pc' mem' => Q (MState.MS R fp_regs pc' fp_csr None mem' (seg_rom (ms_segs B))))
    P Hh Hl).
  - eapply Exec.evt_mono; [exact HE|]. intros ms Hms. destruct (HQ ms Hms) as (E1 & E2 & E3 & E4 & E5).
    assert (Ems : ms = MState.MS (ms_regs ms) fp_regs (ms_pc_val ms) fp_csr None (ms_mem ms) (seg_rom (ms_segs B)))
      by (destruct ms as [r f p sv rv fc m ro]; cbn in E1, E2, E3, E4, E5; subst; reflexivity).
    exists (ms_regs ms), (ms_pc_val ms), (ms_mem ms). split; [exact Ems | rewrite <- Ems; exact Hms].
  - intros R pc' mem' regs' HR Hg. exact (HK _ regs' HR Hg).
Qed.

Lemma crt_runQ : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms regs', Q ms -> (forall r, getr regs' r = getr (ms_regs ms) r) ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) regs' (ms_pc_val ms) (ms_mem ms)
       (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl HE HQ HK. rewrite <- HS in HE, HQ.
  apply (crt_run_fp regs pc mem md (fun R F pc' fc mem' => Q (MState.MS R F pc' fc None mem' (seg_rom (ms_segs B))))
    P Hh Hl).
  - eapply Exec.evt_mono; [exact HE|]. intros ms Hms. destruct (HQ ms Hms) as (E1 & E2 & E3).
    assert (Ems : ms = MState.MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) None (ms_mem ms)
      (seg_rom (ms_segs B))) by (destruct ms as [r f p sv rv fc m ro]; cbn in E1, E2, E3; subst; reflexivity).
    exists (ms_regs ms), (ms_fregs ms), (ms_pc_val ms), (ms_fcsr ms), (ms_mem ms).
    split; [exact Ems | rewrite <- Ems; exact Hms].
  - intros R F pc' fc mem' regs' HR Hg. exact (HK _ regs' HR Hg).
Qed.

Lemma crt_runN : ms_segs B = rsegs -> forall regs pc mem md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree rsegs mem ->
  Exec.evt rsegs Q (MState.MS (rmk regs) fp_regs pc fp_csr None (normalize rsegs mem) (seg_rom rsegs)) ->
  (forall ms, Q ms -> ms_svc_pending ms = None /\ ms_resv ms = None /\ ms_rom ms = seg_rom rsegs) ->
  (forall ms s0 regs', Q s0 -> ms_rel rsegs ms s0 -> ro_same rsegs mem (ms_mem ms) ->
     (forall r, getr regs' r = getr (ms_regs s0) r) ->
     SR (ms_segs B) (mkCfg (@mkst (mkFP (ms_fregs s0) (ms_fcsr s0)) regs' (ms_pc_val s0) (ms_mem ms)
       (seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (mkst regs pc mem (seg_rom (ms_segs B))) md) P.
Proof.
  intros HS regs pc mem md Q P Hh Hl Hro HE HQ HK.
  apply (crt_runQ HS regs pc mem md (fun s => exists s0, Q s0 /\ ms_rel rsegs s s0 /\ ro_same rsegs mem (ms_mem s))
    P Hh Hl).
  - exact (evt_normalize rsegs Q (rmk regs) fp_regs pc fp_csr None mem (seg_rom rsegs) crt_wx Hro HE).
  - intros ms (s0 & HQs & Hrel & _). destruct (HQ s0 HQs) as (E1 & E2 & E3).
    destruct Hrel as (_ & _ & _ & Es & Er & _ & Eo & _). rewrite Es, Er, Eo. auto.
  - intros ms regs' (s0 & HQs & Hrel & Hsame) Hg.
    pose proof Hrel as (Er & Ef & Ep & _ & _ & Ec & _).
    rewrite Ef, Ep, Ec. apply (HK ms s0 regs' HQs Hrel Hsame). intros r. rewrite Hg, Er. reflexivity.
Qed.

Lemma crt_nown : AllocExtra B (aa_MR API) -> ctx_owned B API ->
  forall L A mem md L' A' mem' md' a, aa_MR API L A mem md -> aa_MR API L' A' mem' md' ->
  (alloc_ceiling <= a < 2 ^ 64 \/ in_img B a) -> ~ owned B L A a -> ~ owned B L' A' a.
Proof.
  intros AX CT L A mem md L' A' mem' md' a HM HM' Ha Ho Ho'.
  destruct Ha as [Ha|Ha].
  - pose proof (mr_owned_low B _ (aa_laws API) _ _ _ _ _ HM' Ho'). lia.
  - destruct Ho' as [Hal|Hst]; apply Ho; [|right; exact Hst].
    apply (CT L A mem md a HM). exact (ax_img AX L' A' mem' md' a HM' Ha Hal).
Qed.

Lemma crt_seq : AllocExtra B (aa_MR API) -> ctx_owned B API ->
  forall K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2,
  aa_MR API L A mem md ->
  kb_mid B API K sp L A mem md E1 L1 A1 mem1 md1 ->
  kb_mid B API K2 sp2 L1 A1 mem1 md1 E2 L2 A2 mem2 md2 ->
  sp - K <= sp2 - K2 -> sp2 <= sp -> alloc_ceiling + K <= sp -> sp <= 2 ^ 64 ->
  (forall a, sp - K <= a < sp -> ~ (sp2 - K2 <= a < sp2) -> ~ E2 a) ->
  (length (st_regions A) <= length (st_regions A1))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A1)) ->
  kb_mid B API K sp L A mem md (fun a => E1 a \/ E2 a) L2 A2 mem2 md2.
Proof.
  intros AX CT K sp L A mem md E1 L1 A1 mem1 md1 K2 sp2 E2 L2 A2 mem2 md2 M0
    (M1 & W1 & B1 & Y1 & P1 & D1 & F1 & K1 & S1) (M2 & W2 & B2 & Y2 & P2 & D2 & F2 & K2' & S2) H1 H2 H3 H4 H5 HL HU.
  pose proof alloc_ceiling_value as Hc.
  split; [exact M2|]. split; [exact W2|]. split; [exact B2|].
  split.
  { destruct Y1 as (Y1a & Y1b & Y1c & Y1d). destruct Y2 as (Y2a & Y2b & Y2c & Y2d).
    split; [congruence|]. split; [congruence|]. split; [congruence|].
    intros r Hr. rewrite (Y2d r ltac:(lia)). exact (Y1d r Hr). }
  split.
  { intros p n Hin Hin2. pose proof (HU p n Hin) as Hin1. rewrite (P2 p n Hin1 Hin2). exact (P1 p n Hin Hin1). }
  split.
  { destruct D1 as (vm1 & E). destruct D2 as (vm2 & E'). subst md1 md2. exists vm2. apply crt_vm. }
  split.
  { intros a Ha Ho Ho2 Hs He.
    assert (Ho1 : ~ owned B L1 A1 a) by exact (crt_nown AX CT L A mem md L1 A1 mem1 md1 a M0 M1 Ha Ho).
    destruct (F1 a Ha Ho Ho1 Hs ltac:(tauto)) as [E1a E1w].
    destruct (F2 a Ha Ho1 Ho2 ltac:(intros [Hx|Hx]; apply Hs; [left; lia | right; exact Hx]) ltac:(tauto))
      as [E2a E2w].
    split; [congruence | tauto]. }
  split.
  { intros p n i Hin Hin2 Hi. pose proof (HU p n Hin) as Hin1.
    rewrite <- (P1 p n Hin Hin1). rewrite (K2' p n i Hin1 Hin2 Hi). rewrite (P1 p n Hin Hin1).
    exact (K1 p n i Hin Hin1 Hi). }
  intros a Ha.
  assert (Hd : (sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4) \/
               ~ ((sp2 - K2 <= a < sp2) \/ (errno_addr B <= a < errno_addr B + 4))) by lia.
  destruct Hd as [Hd|[Hd|Hd]]; [apply S2; left; exact Hd | apply S2; right; exact Hd |].
  destruct Ha as [Ha|Ha]; [|exfalso; apply Hd; right; exact Ha].
  assert (No1 : ~ owned B L1 A1 a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho); lia).
  assert (No2 : ~ owned B L2 A2 a) by (intro Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho); lia).
  apply (proj2 (F2 a ltac:(left; lia) No1 No2 Hd ltac:(apply H5; lia))). apply S1. left. exact Ha.
Qed.

Lemma crt_drop : forall K sp L A mem md (E : Z -> Prop) L' A' mem' md',
  kb_mid B API K sp L A mem md E L' A' mem' md' ->
  (forall a, E a -> a < alloc_ceiling /\ ~ in_img B a) ->
  kb_mid B API K sp L A mem md (fun _ => False) L' A' mem' md'.
Proof.
  intros K sp L A mem md E L' A' mem' md' (H1 & H2 & H3 & H4 & H5 & H7 & H8 & H9 & H10) HE.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H7|]. split; [|split; [exact H9 | exact H10]].
  intros a Ha Ho Ho' Hs _. apply H8; try assumption.
  intros He. destruct (HE a He) as [E1 E2]. destruct Ha as [Ha|Ha]; [lia | exact (E2 Ha)].
Qed.

Lemma crt_seg_img : ms_segs B = rsegs -> forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros HS x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HS; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma crt_fs_none : ms_segs B = rsegs -> forall a, ~ in_img B a -> find_segment (ms_segs B) a 1 = None.
Proof.
  intros HS a H. destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. exact (H (crt_seg_img HS a seg E)).
Qed.

Lemma crt_img_low : ms_segs B = rsegs -> img_low B.
Proof.
  intros HS. apply (img_low_of_check B 140735332483072).
  - unfold img_check. rewrite HS. vm_compute. reflexivity.
  - pose proof alloc_ceiling_value. lia.
Qed.

Lemma crt_fs_high : img_low B -> forall a, alloc_ceiling <= a -> find_segment (ms_segs B) a 1 = None.
Proof.
  intros [_ HI] a Ha. destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (HI a seg E). lia.
Qed.

Lemma crt_ro_false : forall a, 0 <= a < 2 ^ 64 -> find_segment (ms_segs B) a 1 = None ->
  Mem.ro_addr (ms_segs B) (Mem.wa a) = false.
Proof.
  intros a Ha H. unfold Mem.ro_addr, Mem.wa. rewrite MState.unsigned_lit by lia. rewrite H. reflexivity.
Qed.

Lemma crt_pres : forall (m m' : word -> option byte) a, find_segment (ms_segs B) (bv_unsigned a) 1 = None ->
  (wview (ms_segs B) m a <> None -> wview (ms_segs B) m' a <> None) -> m a <> None -> m' a <> None.
Proof.
  intros m m' a Hf Hw Hm. unfold wview in Hw. rewrite Hf in Hw.
  destruct (m a) as [b|]; [|contradiction]. destruct (m' a) as [b'|]; [discriminate|].
  intros _. exact (Hw ltac:(discriminate) eq_refl).
Qed.

Lemma crt_present_wr : forall m a, present m a -> writable_at (ms_segs B) m a.
Proof. intros m a (b & Hb). unfold writable_at, wview. rewrite Hb. discriminate. Qed.

Lemma crt_stk : img_low B -> forall m lo hi, alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> writable_at (ms_segs B) m a) -> Frame.stk (ms_segs B) m lo hi.
Proof.
  intros [_ HI] m lo hi Hlo Hhi HW. pose proof alloc_ceiling_value as Hc.
  split; [lia|]. split; [lia|]. intros a Ha.
  assert (Hw : writable_at (ms_segs B) m a) by (apply HW; lia).
  split; [exact Hw|].
  revert Hw. unfold Mem.mrd, Mem.wa, writable_at, wview.
  destruct (m (Z_to_bv 64 a)) as [b|]; intros Hw; [exists b; reflexivity|].
  rewrite MState.unsigned_lit in Hw by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:F; [|contradiction].
  exfalso. destruct (HI a seg F). lia.
Qed.

Lemma crt_stk_norm : img_low B -> forall m lo hi, Frame.stk (ms_segs B) m lo hi -> ro_agree (ms_segs B) m ->
  alloc_ceiling <= lo -> Frame.stk (ms_segs B) (normalize (ms_segs B) m) lo hi.
Proof.
  intros HI m lo hi (H1 & H2 & H) Hro Hlo. pose proof (mem_rel_normalize (ms_segs B) m Hro) as HR.
  split; [exact H1|]. split; [exact H2|]. intros a Ha. destruct (H a Ha) as [Hw [b Hb]].
  assert (Hra : Mem.ro_addr (ms_segs B) (Mem.wa a) = false)
    by (apply crt_ro_false; [lia | apply (crt_fs_high HI); lia]).
  split.
  - rewrite (wview_rel_rw (ms_segs B) m _ _ HR Hra). exact Hw.
  - exists b. rewrite <- (mrd_rel (ms_segs B) m _ _ HR). exact Hb.
Qed.

Lemma crt_wr_norm : ms_segs B = rsegs -> forall m a n, ro_agree (ms_segs B) m -> 0 <= a -> a + n <= 2 ^ 64 ->
  (forall i, 0 <= i < n -> present m (a + i) /\ ~ in_img B (a + i)) ->
  Mem.wr_at (ms_segs B) (normalize (ms_segs B) m) a n.
Proof.
  intros HS m a n Hro Ha Hn H.
  apply (wr_at_norm (ms_segs B) m); [exact (mem_rel_normalize _ m Hro) | |].
  - split; [exact Ha|]. split; [exact Hn|]. intros i Hi. destruct (H i Hi) as [[b Hb] _].
    unfold wview, Mem.wa. rewrite Hb. discriminate.
  - intros i Hi. destruct (H i Hi) as [_ Hni]. apply crt_ro_false; [lia | exact (crt_fs_none HS _ Hni)].
Qed.

Lemma crt_ro_munch : forall W m m', ro_agree (ms_segs B) m -> Frame.munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Frame.outside W a -> find_segment (ms_segs B) a 1 = None) ->
  ro_agree (ms_segs B) m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold Mem.mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (HW (bv_unsigned a) Hr Ho) as E.
    pose proof (crt_ro_false (bv_unsigned a) Hr E) as F. unfold Mem.wa in F.
    rewrite Z_to_bv_bv_unsigned in F. congruence.
Qed.

Lemma crt_cells_keep : forall m m' A cs, Step.rw_cells (ms_segs B) m A cs ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) -> m' (Z_to_bv 64 (A + i)) = m (Z_to_bv 64 (A + i))) ->
  Step.rw_cells (ms_segs B) m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wn & Hw)] E.
  pose proof (Cells.cells_bytes_length cs Hwf) as LN.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi).
    unfold Mem.mrd, Mem.wa. rewrite (E (Z.of_nat i)); [reflexivity | lia].
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi. specialize (Hw i Hi).
    unfold wview, Mem.wa in *. rewrite (E i Hi). exact Hw.
Qed.

Lemma crt_cells_mb : forall m m' A cs, Step.rw_cells (ms_segs B) m A cs ->
  (forall i, 0 <= i < Z.of_nat (Cells.cells_size cs) ->
     mbyte (ms_segs B) m' (A + i) = mbyte (ms_segs B) m (A + i) /\
     (writable_at (ms_segs B) m (A + i) -> writable_at (ms_segs B) m' (A + i))) ->
  Step.rw_cells (ms_segs B) m' A cs.
Proof.
  intros m m' A cs [[Hwf (Ha & Hl & Hb)] (Wa & Wn & Hw)] E.
  pose proof (Cells.cells_bytes_length cs Hwf) as LN.
  split; [split; [exact Hwf|]|].
  - split; [exact Ha|]. split; [exact Hl|]. intros i Hi. rewrite <- (Hb i Hi).
    exact (proj1 (E (Z.of_nat i) ltac:(lia))).
  - split; [exact Wa|]. split; [exact Wn|]. intros i Hi. exact (proj2 (E i Hi) (Hw i Hi)).
Qed.

Lemma crt_blk : AllocExtra B (aa_MR API) -> forall Lk Ak mk mdk P n,
  aa_MR API Lk Ak mk mdk -> In (P, n) (blocks Lk Ak) ->
  4096 <= P /\ P + n <= alloc_ceiling /\ P mod 16 = 0 /\
  forall i, 0 <= i < n -> present mk (P + i) /\ ~ in_img B (P + i) /\ ~ owned B Lk Ak (P + i).
Proof.
  intros AX Lk Ak mk mdk P n HM Hin.
  destruct (crt_bu Lk Ak P n Hin) as (p & Hp & <-).
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hp) as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  split; [exact (mr_blocks_aligned _ _ (aa_laws API) _ _ _ _ p n HM Hp)|].
  intros i Hi. destruct (mr_blocks _ _ (aa_laws API) _ _ _ _ p n i HM Hp Hi) as (Hpr & _ & _ & Hno).
  split; [exact Hpr|]. split; [exact (ax_blocks_img AX Lk Ak mk mdk p n i HM Hp Hi) | exact Hno].
Qed.

Lemma crt_heap_E : forall Lk Ak mk mdk p n, AllocExtra B (aa_MR API) -> aa_MR API Lk Ak mk mdk ->
  In (p, n) (user_blocks Ak) ->
  forall a, ptr_addr Lk p <= a < ptr_addr Lk p + n -> a < alloc_ceiling /\ ~ in_img B a.
Proof.
  intros Lk Ak mk mdk p n AX HMk Hp a Ha.
  destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p _ HMk Hp) as [Hr1 Hr2].
  split; [lia|]. replace a with (ptr_addr Lk p + (a - ptr_addr Lk p)) by lia.
  exact (ax_blocks_img AX Lk Ak mk mdk p n (a - ptr_addr Lk p) HMk Hp ltac:(lia)).
Qed.

Lemma crt_keep_pres : forall (r r' : bvmap 5 word) (l : list Z),
  (forall x, In x l -> callee_saved x) -> regs_preserved r r' ->
  forall x, In x l -> getr r' (Z_to_bv 5 x) = getr r (Z_to_bv 5 x).
Proof. intros r r' l Hl Hp x Hx. exact (Hp x (Hl x Hx)). Qed.

(* The function's own frame: K is its call_pre_k stack, regs its entry registers. *)
Section Body.
Variables (K : Z) (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model).
Hypothesis PRE : call_pre_k B (aa_MR API) K L A regs mem md.

Definition cg_inv (L' : layout) (A' : astate) (m' : word -> option byte) (md' : Model) : Prop :=
  kb_mid B API K (spZ regs) L A mem md (fun _ => False) L' A' m' md' /\
  (length (st_regions A) <= length (st_regions A'))%nat /\
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) /\
  ro_agree (ms_segs B) m' /\ guard_kept B mem m'.

Lemma cg_pre : forall Lk Ak mk mdk regsk f K1,
  cg_inv Lk Ak mk mdk -> spZ regsk = spZ regs - f -> 0 <= f -> 0 <= K1 -> f + K1 <= K ->
  spZ regsk mod 16 = 0 -> getr regsk 4 = getr regs 4 -> YK0s.ret_ok (getr regsk 1) -> st_init_done Ak = true ->
  call_pre_k B (aa_MR API) K1 Lk Ak regsk mk mdk.
Proof.
  intros Lk Ak mk mdk regsk f K1 ((M1 & W1 & B1 & _ & _ & _ & _ & _ & S1) & _) Hsp Hf HK1 HfK H16 H4 Hra Hinit.
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _ & Htp & _).
  refine (conj M1 (conj W1 (conj B1 (conj Hra (conj H16 (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - lia.
  - lia.
  - intros a Ha. apply S1. left. lia.
  - rewrite H4. exact Htp.
  - intros a Ha. apply S1. right. exact Ha.
  - intros E. rewrite Hinit in E. discriminate.
Qed.

Lemma cg_inv_call : AllocExtra B (aa_MR API) -> ctx_owned B API ->
  forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2,
  cg_inv Lk Ak mk mdk ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  spZ regs - K <= spZ regsk - K2 -> spZ regsk <= spZ regs ->
  (forall a, E2 a -> a < alloc_ceiling /\ ~ in_img B a) ->
  (length (st_regions Ak) <= length (st_regions A2))%nat ->
  (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A2)) ->
  ro_agree (ms_segs B) m2 -> guard_kept B mk m2 ->
  cg_inv L2 A2 m2 md2.
Proof.
  intros AX CT Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 (I1 & I2 & I3 & I4 & I5) Hpost H1 H2 HE HL HU Hro Hg.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  destruct (kb_mid_call B API _ _ _ _ _ _ _ _ _ _ _ _ Hpost) as [Hmid _].
  split.
  { apply (crt_drop _ _ _ _ _ _ (fun a => False \/ E2 a)).
    - eapply (crt_seq AX CT); [exact HM | exact I1 | exact Hmid | lia | lia | lia | lia | | exact I2 | exact I3].
      intros a Ha _ He. destruct (HE a He) as [Ha' _]. lia.
    - intros a [[]|He]. exact (HE a He). }
  split; [lia|]. split; [exact HU|]. split; [exact Hro|].
  intros i Hi. rewrite (Hg i Hi). exact (I5 i Hi).
Qed.

Lemma cg_inv_A : ms_segs B = rsegs -> forall Lk Ak mk mdk mk' W,
  cg_inv Lk Ak mk mdk ->
  Frame.munch W mk mk' -> Frame.wmono (ms_segs B) mk mk' -> (forall x, mk x <> None -> mk' x <> None) ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ Frame.outside W x ->
     (spZ regs - K <= x < spZ regs) \/
     (x < alloc_ceiling /\ ~ in_img B x /\ ~ owned B Lk Ak x /\
      forall p n i, In (p, n) (user_blocks A) -> 0 <= i < n -> ptr_addr L p + i <> x)) ->
  ro_agree (ms_segs B) mk' ->
  cg_inv Lk Ak mk' mdk.
Proof.
  intros HS Lk Ak mk mdk mk' W (I1 & I2 & I3 & I4 & I5) Hm Hw Hp HW Hro.
  pose proof PRE as (HM & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  pose proof (crt_img_low HS) as HIL.
  pose proof I1 as (M1 & _).
  split.
  { apply (crt_drop _ _ _ _ _ _
      (fun x => False \/ (0 <= x < 2 ^ 64 /\ ~ Frame.outside W x /\ ~ (spZ regs - K <= x < spZ regs)))).
    - apply (kb_mid_tail B API HIL _ _ _ _ _ _ _ Lk Ak mk mdk mk' W); [exact I1 | exact Hm | exact Hw | exact Hp | | |].
      + intros x Hx Hs He. destruct (kb_outside_dec W x) as [Ho|Ho]; [exact Ho|]. exfalso. apply He. tauto.
      + intros x Hx Ho. destruct (kb_outside_dec W x) as [Hout|Hout]; [exact Hout|]. exfalso.
        destruct (HW x ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
      + intros p n i Hin Hin' Hi. destruct (kb_outside_dec W (ptr_addr L p + i)) as [Hout|Hout]; [exact Hout|].
        exfalso. destruct (mr_blocks_range _ _ (aa_laws API) _ _ _ _ p n HM Hin) as [Hr1 Hr2].
        destruct (HW (ptr_addr L p + i) ltac:(lia) Hout) as [Hs | (_ & _ & _ & H4)];
          [lia | exact (H4 p n i Hin Hi eq_refl)].
    - intros x [[]|(Hx & Ho & Hs)].
      destruct (HW x Hx Ho) as [H|(H1 & H2 & _)]; [contradiction | split; assumption]. }
  split; [exact I2|]. split; [exact I3|]. split; [exact Hro|].
  intros i Hi. rewrite <- (I5 i Hi).
  assert (Ho : owned B Lk Ak (ms_got_guard B + i))
    by (right; unfold static_owned; right; right; right; right; left; lia).
  pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho) as Hr.
  apply (mbyte_munch (ms_segs B) W mk mk'); [exact Hm | lia |].
  destruct (kb_outside_dec W (ms_got_guard B + i)) as [Hout|Hout]; [exact Hout|]. exfalso.
  destruct (HW (ms_got_guard B + i) ltac:(lia) Hout) as [Hs | (_ & _ & H3 & _)]; [lia | exact (H3 Ho)].
Qed.

Lemma cg_inv_kept : forall Lk Ak mk mdk, cg_inv Lk Ak mk mdk -> blocks_kept B L A mem mk (fun _ => False).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & _ & _ & _ & K1 & _) & _ & I3 & _) a k i Hin _ Hi.
  destruct (crt_bu L A a k Hin) as (p & Hp & <-). exact (K1 p k i Hp (I3 p k Hp) Hi).
Qed.

Lemma cg_old_in : forall Lk Ak mk mdk, cg_inv Lk Ak mk mdk -> forall y, In y (blocks L A) -> In y (blocks Lk Ak).
Proof.
  intros Lk Ak mk mdk ((_ & _ & _ & _ & P1 & _) & _ & I3 & _) [a k] Hy.
  destruct (crt_bu L A a k Hy) as (p & Hp & <-).
  pose proof (I3 p k Hp) as Hp'. rewrite <- (P1 p k Hp Hp'). exact (crt_ub Lk Ak p k Hp').
Qed.

Lemma cg_free_keep : forall Lk Ak mk mdk p n,
  cg_inv Lk Ak mk mdk -> In (p, n) (user_blocks Ak) -> 0 < n ->
  (forall y, In y (blocks L A) -> ranges_disjoint (ptr_addr Lk p, n) y) ->
  forall q k, In (q, k) (user_blocks A) -> q <> p.
Proof.
  intros Lk Ak mk mdk p n ((M1 & W1 & _ & _ & P1 & _) & _ & I3 & _) Hp Hn HD q k Hq Eq. subst q.
  pose proof (I3 p k Hq) as Hpk.
  pose proof (user_block_ptrs_NoDup Ak W1) as ND.
  pose proof (crt_fst_unique _ p k n ND Hpk Hp) as Ek. subst k.
  pose proof (HD _ (crt_ub L A p n Hq)) as D.
  rewrite (P1 p n Hq Hpk) in D. unfold ranges_disjoint in D. cbn [fst snd] in D. lia.
Qed.

(* decode's cr_frame_call, over any (base, cells) instead of its own frame *)
Lemma cg_cells_call : forall Lk Ak mk mdk regsk K2 (E2 : Z -> Prop) L2 A2 regs2 m2 md2 base cs,
  cg_inv Lk Ak mk mdk -> Step.rw_cells (ms_segs B) mk base cs ->
  call_post_k B (aa_MR API) K2 Lk Ak regsk mk mdk E2 L2 A2 regs2 m2 md2 ->
  alloc_ceiling <= base -> base + Z.of_nat (Cells.cells_size cs) <= spZ regs -> spZ regsk <= base ->
  (forall a, E2 a -> a < alloc_ceiling) -> errno_addr B + 4 <= alloc_ceiling ->
  Step.rw_cells (ms_segs B) m2 base cs.
Proof.
  intros Lk Ak mk mdk regsk K2 E2 L2 A2 regs2 m2 md2 base cs ((M1 & _) & _) FR Hpost Hb1 Hb2 Hsp HE ERR.
  pose proof Hpost as (M2 & _ & _ & _ & _ & _ & _ & Hfr & _).
  pose proof PRE as (_ & _ & _ & _ & _ & Hlo & Hhi & _).
  pose proof alloc_ceiling_value as Hc.
  apply (crt_cells_mb mk m2 _ _ FR). intros i Hi.
  assert (Hr : alloc_ceiling <= base + i < 2 ^ 64) by lia.
  destruct (Hfr (base + i)) as [E W].
  - left. exact Hr.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M1 Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ M2 Ho). lia.
  - unfold scratch_k. lia.
  - intros He. pose proof (HE _ He). lia.
  - split; [exact E | intros Hw; apply W; exact Hw].
Qed.

End Body.
End G.

