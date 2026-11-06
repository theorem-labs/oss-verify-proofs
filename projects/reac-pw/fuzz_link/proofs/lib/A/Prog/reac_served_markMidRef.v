(* reac_served_mark (fuzz_link.asan 0x895a8) on image A, the MID segment's semantic half: what the cut memory holds
   before the first callee (lib/A/Prog/reac_served_markDefs.v `srm_base` with X = False), and the post of the three
   refusals (+0x1b4 `beqz s6`, +0x1b8 `beqz s4`, +0x1d0 `beqz a0` after `lbu a0, 0(s4)`), which answer - E_INVAL
   with g_nl, the marks block and the FILE as at the entry (link_spec.v mark_core on a NULL or empty name).
   The byte transports are generic; the cut views come from the Kit (lib/A/Prog/reac_served_markKit.v:
   srm_kept_noside, srm_name_view, srm_table_view) and the block transports from
   lib/A/Prog/reac_served_markXfer.v (xfer_amarks, xfer_amemfile_k, xfer_gnl_img, xfer_gnl_awrange).

   Proves no function (kind: segment lemma of reac_served_mark's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markUniq reac_served_markKit reac_served_markXfer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ==========================================================================
   Byte transports between two memories with the same views on the bytes read
   ========================================================================== *)
Section g.
Variable segs : list Segment.

Lemma srm_mid_abytes : forall H H' (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
  abytes segs (mrestrict H m) a bs -> abytes segs (mrestrict H' m') a bs.
Proof.
  intros H H' m m' a bs Hv (H0 & H1 & Hn). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (Hn i Hi). apply (mbyte_of_aview segs). apply Hv. lia.
Qed.

Lemma srm_mid_val_mem : forall H H' (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs H' m' x = aview segs H m x) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
  intros H H' m m' a n v Hv HV k Hk.
  rewrite (mbyte_of_aview segs H H' m m' (a + Z.of_nat k)) by (apply Hv; lia).
  exact (HV k Hk).
Qed.

Lemma srm_mid_acstr : forall H H' (m m' : word -> option byte) a s,
  (forall x, a <= x <= a + Z.of_nat (length s) -> aview segs H' m' x = aview segs H m x) ->
  acstr_at segs (mrestrict H m) a s -> acstr_at segs (mrestrict H' m') a s.
Proof.
  intros H H' m m' a s Hv (HB & HN). split; [|exact HN].
  apply (srm_mid_abytes H H' m m'); [|exact HB].
  intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hv. lia.
Qed.

Lemma srm_mid_anlk : forall H H' (m m' : word -> option byte) g bs,
  (forall x, g <= x < g + NK_SIZE -> aview segs H' m' x = aview segs H m x) ->
  awrange segs (mrestrict H' m') g NK_SIZE ->
  anlk_at segs (mrestrict H m) g bs -> anlk_at segs (mrestrict H' m') g bs.
Proof.
  intros H H' m m' g bs Hv Hw ((HB & _) & HL). split; [|exact HL]. split.
  - apply (srm_mid_abytes H H' m m'); [|exact HB]. intros i Hi. apply Hv. lia.
  - rewrite HL. exact Hw.
Qed.

(* g_nl's interface table: its slots by the views of g_nl's table area, its strings by the views the caller gives
   for the strings the table names at the source memory *)
Lemma srm_mid_aiftab : forall H H' (m m' : word -> option byte) g bs tab,
  (forall x, g + NK_IF_NAME <= x < g + NK_SIZE -> aview segs H' m' x = aview segs H m x) ->
  (forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at segs (mrestrict H m) (g + NK_IF_NAME + 8 * Z.of_nat i) p -> acstr_at segs (mrestrict H m) p n2 ->
     forall x, p <= x <= p + Z.of_nat (length n2) -> aview segs H' m' x = aview segs H m x) ->
  aiftab_at segs (mrestrict H m) g bs tab -> aiftab_at segs (mrestrict H' m') g bs tab.
Proof.
  intros H H' m m' g bs tab Hg Hs (Hn & Hl & Ht). split; [exact Hn|]. split; [exact Hl|].
  intros i nm ix Hi. destruct (Ht i nm ix Hi) as (Hix & p & Hp & Hp0 & Hc & Hx).
  assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  split; [exact Hix|]. exists p. split; [|split; [exact Hp0|split]].
  - apply (srm_mid_val_mem H H' m m'); [|exact Hp]. intros x Hx'. apply Hg.
    unfold NK_IF_NAME, NK_SIZE in *. lia.
  - apply (srm_mid_acstr H H' m m'); [|exact Hc]. exact (Hs i nm ix p Hi Hp Hc).
  - apply (srm_mid_val_mem H H' m m'); [|exact Hx]. intros x Hx'. apply Hg.
    unfold NK_IF_NAME, NK_IF_INDEX, NK_SIZE in *. lia.
Qed.
End g.

(* mark_core on a NULL or an empty name: the refusal, nothing changed *)
Lemma srm_mid_mark_refused : forall tab nm marks reqs K, (nm = None \/ nm = Some []) ->
  mark_lib tab nm marks reqs K = Mres (- E_INVAL) marks reqs K.
Proof. intros tab nm marks reqs K [-> | ->]; reflexivity. Qed.

Lemma srm_mid_mk_n : forall gbs, marks_wf gbs -> mk_n gbs = Z.of_nat (length (mk_names gbs)).
Proof. intros gbs (Hn & _). unfold mk_names. rewrite length_map, length_seq. lia. Qed.

Lemma srm_mid_n_sent : forall kbs, nlk_wf kbs -> nk_n_sent kbs = Z.of_nat (length (nk_sent kbs)).
Proof. intros kbs (_ & _ & Hs & _). unfold nk_sent. rewrite length_map, length_seq. lia. Qed.

Lemma srm_mid_next : forall kbs, nlk_wf kbs -> nk_next kbs = Z.of_nat (k_next (nk_kstate kbs)).
Proof. intros kbs (_ & Hn & _). unfold nk_kstate. cbn [k_next]. lia. Qed.

(* the registers srm_base names, and s5, as a list and as equalities *)
Definition srm_mid_rlist : list (bv 5) :=
  [2%bv; 9%bv; 8%bv; 18%bv; 19%bv; 25%bv; 26%bv; 20%bv; 22%bv; 3%bv; 4%bv; 27%bv; 21%bv].
Definition srm_mid_regs_same (R R' : bvmap 5 word) : Prop :=
  getr R' 2 = getr R 2 /\ getr R' 9 = getr R 9 /\ getr R' 8 = getr R 8 /\ getr R' 18 = getr R 18 /\
  getr R' 19 = getr R 19 /\ getr R' 25 = getr R 25 /\ getr R' 26 = getr R 26 /\ getr R' 20 = getr R 20 /\
  getr R' 22 = getr R 22 /\ getr R' 3 = getr R 3 /\ getr R' 4 = getr R 4 /\ getr R' 27 = getr R 27 /\
  getr R' 21 = getr R 21.

(* ==========================================================================
   The cut before the first callee
   ========================================================================== *)
(* the base's X before the first callee *)
Definition srm_X0 : Z -> Prop := fun _ => False.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.

(* g_nl: an image byte outside the runtime statics and errno, so akept's image clause keeps it *)
Lemma srm_mid_gnl_view : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 a,
  srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms3 md3 ->
  LA_G_NL <= a < LA_G_NL + NK_SIZE ->
  aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H (sm_W cx)) (sm_memc cx) a.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms3 md3 a HB Ha.
  pose proof (srm_kept_noside SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms3 md3 HB)
    as (_ & _ & K3 & _).
  assert (Hx : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4))
    by (eapply xfer_gnl_img; eassumption).
  destruct Hx as (Hi & Ho & He). exact (K3 a Hi Ho He (fun H => H)).
Qed.

(* the entry's kernel and interface table, at the cut *)
Lemma srm_mid_kern_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 kbs tab,
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms3 md3 ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 ->
  anlk_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs /\ aiftab_at SEGS (rdW W3 (ms_mem ms3)) LA_G_NL kbs tab.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms3 md3 kbs tab HPRE HB HNLK.
  pose proof HNLK as (Hnlk & _ & _ & _ & _ & Hift & _ & _).
  assert (HG : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
            aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (sm_W cx)) (sm_memc cx) x)
    by (intros x Hx; exact (srm_mid_gnl_view cx fpos ly3 S3 W3 ms3 md3 x HB Hx)).
  assert (HWG : awrange SEGS (rdW W3 (ms_mem ms3)) LA_G_NL NK_SIZE) by (eapply xfer_gnl_awrange; eassumption).
  split.
  - exact (srm_mid_anlk SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3) LA_G_NL kbs HG HWG Hnlk).
  - apply (srm_mid_aiftab SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [| |exact Hift].
    + intros x Hx. apply HG. unfold NK_IF_NAME, NK_SIZE in *. lia.
    + intros i n2 ix p Hi Hp Hc x Hx.
      assert (Hpr : 0 <= p < 2 ^ 64) by (pose proof (srm_acstr_range SEGS _ _ _ Hc); lia).
      assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
      destruct Hift as (_ & Hl & _).
      assert (Hp3 : au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
      { apply (srm_mid_val_mem SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3)); [|exact Hp].
        intros y Hy. apply HG. unfold NK_IF_NAME, NK_SIZE in *. lia. }
      exact (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms3 md3 kbs tab i n2 ix p x
               HPRE HB (fun a (H : srm_X0 a) => False_ind (srm_E cx a) H) HNLK Hi Hp3 Hpr Hx).
Qed.

(* the marks block and the FILE, at the cut (heap blocks of the entry; the base's akept without its aside part) *)
Lemma srm_mid_blocks_at : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms3 md3 ->
  (forall k, amemfile_k SEGS (srm_m0 cx) (sm_sink cx) k -> amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k) /\
  (srm_mk cx <> 0 -> forall gbs, amarks_at SEGS (srm_m0 cx) (srm_mk cx) gbs ->
     amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs).
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms3 md3 HPRE HB.
  pose proof HPRE as (_ & _ & HP).
  destruct HP as (kbs0 & tab0 & nm0 & k0 & Hsink & Hledg & _).
  pose proof HB as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & Hperm3 & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof (srm_kept_noside SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms3 md3 HB) as HK0.
  assert (Hin3 : forall x, In x (ablocks B (sm_lyc cx) (sm_Sc cx)) -> In x (ablocks B ly3 S3))
    by (intros x Hx; exact (Permutation_in x (Permutation_sym Hperm3) Hx)).
  pose proof (Hin3 _ Hsink) as Hsink3.
  split.
  - intros k Hk. eapply xfer_amemfile_k; try eassumption.
    all: lazymatch goal with |- forall a, _ -> ~ _ => intros ? _ [] | _ => idtac end.
  - intros Hmk gbs Hg. destruct (Hledg Hmk) as (Hmk1 & _). pose proof (Hin3 _ Hmk1) as Hmk3.
    eapply xfer_amarks; try eassumption.
    all: lazymatch goal with |- forall a, _ -> ~ _ => intros ? _ [] | _ => idtac end.
Qed.

(* ==========================================================================
   The refusals: - E_INVAL, nothing of the write set changed
   ========================================================================== *)
Lemma srm_mid_refuse : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos srm_X0 ly3 S3 W3 ms3 md3 ->
  (srm_mk cx = 0 \/ srm_name cx = 0 \/ aview SEGS (w_H W3) (ms_mem ms3) (srm_name cx) = Some 0) ->
  srm_pf cx (- E_INVAL) (rdW W3 (ms_mem ms3)).
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos ly3 S3 W3 ms3 md3 HPRE HB Hcase.
  pose proof HPRE as (_ & _ & HP).
  destruct HP as (kbs0 & tab0 & nm0 & k0 & Hsink & Hledg & HNLK & Herr & Hsy & Hsd & Htab & Hpol & Hgsay & Hs0
    & HMF & Hk0 & Hfblk & Hnm & Hnmok & Hblk).
  pose proof HNLK as (Hnlk0 & Hwf0 & Hopen0 & _ & _ & Hift0 & _ & _).
  destruct (srm_mid_kern_at cx fpos ly3 S3 W3 ms3 md3 kbs0 tab0 HPRE HB HNLK) as (Hnlk3 & Hift3).
  destruct (srm_mid_blocks_at cx fpos ly3 S3 W3 ms3 md3 HPRE HB) as (HMF3 & HMK3).
  assert (HG : forall x, LA_G_NL <= x < LA_G_NL + NK_SIZE ->
            aview SEGS (w_H W3) (ms_mem ms3) x = aview SEGS (w_H (sm_W cx)) (sm_memc cx) x)
    by (intros x Hx; exact (srm_mid_gnl_view cx fpos ly3 S3 W3 ms3 md3 x HB Hx)).
  assert (HWG : awrange SEGS (rdW W3 (ms_mem ms3)) LA_G_NL NK_SIZE) by (eapply xfer_gnl_awrange; eassumption).
  intros regs' Hr10. unfold reac_served_mark_apost. split; [|split].
  - intros k Hk. exists k. split; [unfold MARK_LINE_MAX; lia | exact (HMF3 k Hk)].
  - intros _. split; [exact Hr10|]. intros kbs Hk.
    exact (srm_mid_anlk SEGS (w_H (sm_W cx)) (w_H W3) (sm_memc cx) (ms_mem ms3) LA_G_NL kbs HG HWG Hk).
  - intros Hmk kbs tab nm gbs Hk Ht Hn Hg. cbv zeta.
    pose proof (anlk_at_unique SEGS _ _ _ _ Hk Hnlk0) as Ek. subst kbs.
    pose proof (aiftab_at_unique SEGS _ _ _ _ Ht Hift0) as Et. subst tab.
    destruct (Hblk Hmk) as (_ & _ & _ & _ & gbs0 & Hg0 & Hgw0).
    pose proof (amarks_at_unique SEGS _ _ _ _ Hg Hg0) as Eg. subst gbs.
    change (aarg (sm_regs cx) 1) with (srm_name cx) in Hn.
    assert (Hnm' : nm = None \/ nm = Some []).
    { destruct Hcase as [Hc | [Hc | Hc]]; [exfalso; exact (Hmk Hc) | |].
      - destruct nm as [s|]; [|left; reflexivity]. destruct Hn as (Hn0 & _). exfalso. exact (Hn0 Hc).
      - destruct nm as [s|]; [|left; reflexivity]. right.
        destruct s as [|x s']; [reflexivity|]. exfalso.
        pose proof (srm_name_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos srm_X0 ly3 S3 W3 ms3 md3 (x :: s')
          (srm_name cx) HPRE HB (fun a (H : srm_X0 a) => False_ind (srm_E cx a) H) Hn ltac:(lia)) as Hv.
        rewrite Hc in Hv.
        destruct Hn as (_ & (_ & _ & Hb) & HNo).
        specialize (Hb 0%nat ltac:(cbn [length app]; lia)).
        cbn [Z.of_nat app nth_error] in Hb. rewrite Z.add_0_r in Hb. unfold srm_m0 in Hb.
        unfold aview in Hv. rewrite Hb in Hv. cbn [option_map] in Hv. injection Hv as Hx.
        apply HNo. left. apply bv_eq. rewrite <- Hx. reflexivity. }
    rewrite (srm_mid_mark_refused tab0 nm (mk_names gbs0) (nk_sent kbs0) (nk_kstate kbs0) Hnm').
    cbn [m_rc m_marks m_reqs m_state].
    split; [exact Hr10|]. split.
    + exists gbs0. split; [exact (HMK3 Hmk gbs0 Hg0)|]. split; [exact Hgw0|].
      split; [reflexivity | exact (srm_mid_mk_n gbs0 Hgw0)].
    + exists kbs0. split; [exact Hnlk3|]. split; [exact Hwf0|].
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hift3|].
      split; [exact (srm_mid_next kbs0 Hwf0)|]. split; [reflexivity|].
      split; [exact (srm_mid_n_sent kbs0 Hwf0)|]. split; [exact Hopen0|].
      split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

(* ==========================================================================
   The base at a later state of the same memory (a run of branches, loads and register moves)
   ========================================================================== *)
Lemma srm_mid_base_move : forall cx fpos (X X' : Z -> Prop) ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_base fx SK B cx fpos X ly3 S3 W3 ms md -> (forall a, X a -> X' a) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  ms_mem ms' = ms_mem ms -> srm_mid_regs_same (ms_regs ms) (ms_regs ms') ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X' ly3 S3 W3 ms' md'.
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros cx fpos X X' ly3 S3 W3 ms ms' md md' HB HXX H1 H2 H3 H4 H5 Hmem
    (Q2 & Q9 & Q8 & Q18 & Q19 & Q25 & Q26 & Q20 & Q22 & Q3 & Q4 & Q27 & _) HJ Hfds Hfs.
  destruct HB as (_ & _ & _ & _ & _ & _ & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & B18
    & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).
  unfold srm_base; cbv zeta. rewrite Hmem in HJ |- *.
  rewrite Q2, Q9, Q8, Q18, Q19, Q25, Q26, Q20, Q22, Q3, Q4, Q27.
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact HJ|].
  do 22 (split; [assumption|]).
  split; [|split; [|split; [|split; [exact B32 | exact B33]]]].
  - apply (akept_mono SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ B29).
    intros a [Ha|Ha]; [left; exact (HXX a Ha) | right; exact Ha].
  - rewrite Hfds. exact B30.
  - rewrite Hfs. exact B31.
Qed.

(* the base registers and s5 after a run that leaves them atoms *)
Lemma srm_mid_regs_same_of : forall E ss (ms ms' : machine_state) extra (H : word -> bool),
  st_ok_pi SEGS (@pa_val _ link_listing PI) E ss (restrict H ms') -> env_agree 32 (Ereg (ms_regs ms) extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) srm_mid_rlist = true ->
  srm_mid_regs_same (ms_regs ms) (ms_regs ms').
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros E ss ms ms' extra H HS HA Hl.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict H ms') (ms_regs ms) extra _ HS HA Hl) as K.
  cbn [ms_regs restrict] in K.
  unfold srm_mid_regs_same. repeat split; apply K; unfold srm_mid_rlist; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* the same at an absolute end state (a run that stops at a call) *)
Lemma srm_mid_regs_same_abs : forall E ss (ms ms' : machine_state) extra (H : word -> bool),
  st_ok SEGS E ss (restrict H ms') -> env_agree 32 (Ereg (ms_regs ms) extra) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) srm_mid_rlist = true ->
  srm_mid_regs_same (ms_regs ms) (ms_regs ms').
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros E ss ms ms' extra H HS HA Hl.
  pose proof (regs_kept_of_st_ok SEGS E ss (restrict H ms') (ms_regs ms) extra _ HS HA Hl) as K.
  cbn [ms_regs restrict] in K.
  unfold srm_mid_regs_same. repeat split; apply K; unfold srm_mid_rlist; cbn [In]; repeat (first [left; reflexivity | right]).
Qed.

(* an env that agrees with the registers below 32, extended above K >= 32 *)
Lemma srm_mid_agree_ext : forall E0 E K ws, env_agree 32 E0 E -> (32 <= K)%nat -> env_agree 32 E0 (extK E K ws).
Proof using SK LAWS TB RELRO_IMG HSEGS.
  intros E0 E K ws [A0 D0] HK. destruct (env_agree_extK E K ws) as [A1 D1]. split.
  - intros n Hn. rewrite A1 by lia. exact (A0 n Hn).
  - rewrite D1. exact D0.
Qed.

End b.
End a.
