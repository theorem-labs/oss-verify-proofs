(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YL0i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/Reusable/YL0i.v, with its module paths changed; 212 of its 255 lines of code are new or changed and 429 lines of the source are left out. *)
(* The slot LLVMFuzzerTestOneInput (fuzz_link.c:764-790), plain image: the post of its SR frame (S-FR item 7).

   The obligation's continuation (lib/Reusable/YL0i.v lib_contract_x_T at lib/MemFileRI.v mf_shape, G = llvm_G,
   output fun _ => [], stk = SLOT_STACK) asks lib_post_x_T of the final config, whose open-file clause is the
   frame lane's `mf_sink B link_mf mem' md'` (YL0i.v:255). lpost_T is lib_post_x_T's text (YL0i.v:240-259) with
   that clause as a parameter SINK and lib_delta read at mf_shape (it is the identity); lpost_T_mf shows the
   copy is exact at SINK = mf_sink, and cut_post_lib states the post in lib_post_x_T itself.

   cut_post gives lpost_T at SINK = mf_sink from the frame relation LFR (lib/Prog/Slot/LFr.v) at the slot's
   return: a0 = 0, the callee-saved registers restored, the NUL at long_alias[300], and the slot's own blocks
   hb either the new kept set (no block kept at entry) or none (the entry's kept FILE stays kept).
   cut_post_cfg gives the same from a cut CUT at the return address. Shape of libreac/fuzz_pcap
   lib/Prog/Slot/PGlue.v post_FR (released 4b6f0df50aa); every fact is link's. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import Contract Img0 FrameAPI MemFile MemFileRI.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib Require Import AllocSlots AllocRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import LLVMFuzzerTestOneInput_c link_mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require mk_leaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LFr.
Import ListNotations.
Local Open Scope Z_scope.

(* ==========================================================================
   1. Closed facts: the image bytes closed_stdio_env reads, and the kept-set accounting
   ========================================================================== *)

(* an address in one of the image's segments (then in_img: LFr.lfr_find_img) *)
Definition lpo_img_chk (a : Z) : bool :=
  match find_segment rsegs a 1 with Some _ => true | None => false end.

Definition lpo_rng_img (lo n : Z) : bool := forallb (fun i => lpo_img_chk (lo + Z.of_nat i)) (seq 0 (Z.to_nat n)).

Lemma lpo_rng_img_ok : forall lo n, lpo_rng_img lo n = true -> forall a, lo <= a < lo + n -> lpo_img_chk a = true.
Proof.
  intros lo n H a Ha. unfold lpo_rng_img in H. rewrite forallb_forall in H.
  replace a with (lo + Z.of_nat (Z.to_nat (a - lo))) by lia.
  apply H. apply in_seq. lia.
Qed.

(* musl's `threaded` byte (0x95899) and the open-file list lock (0x95cc0, 4 bytes): .bss of the last LOAD
   segment [0x218f0, 0x960e0) (LFF: sk_threaded = 0x95898 + 1, sk_ofl_lock = 0x95cc0) *)
Lemma lpo_env_chk : lpo_rng_img 0x95899 1 = true /\ lpo_rng_img 0x95cc0 4 = true.
Proof. vm_compute. split; reflexivity. Qed.

(* NoDup here is stdpp's (stdpp.base, through the semantics' imports); NoDup_ListNoDup moves to Stdlib's *)
Lemma lpo_nodup_disj : forall (l1 l2 : list (Z * Z)) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  intros l1 l2 x H. apply (proj1 (stdpp.base.NoDup_ListNoDup _)) in H. revert l2 x H.
  induction l1 as [|y l1 IH]; intros l2 x H H1 H2; [destruct H1|].
  cbn [app] in H. apply List.NoDup_cons_iff in H as [Hn Hd].
  destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 x Hd H1 H2)].
Qed.

(* no block kept at entry: the post's bound TD [] T b0 is the frame's sb_hb b0 T *)
Lemma lpo_TD_open : forall (T : list (Z * Z)) b, TD [] T b = sb_hb b T.
Proof.
  intros T b. unfold TD. cbn [fold_left]. rewrite TD_malloc_form. unfold sb_hb.
  assert (E : fold_right (fun t s => snd t + s) 0 T = hb_bytes T).
  { unfold hb_bytes. induction T as [|t T IH]; [reflexivity|]. cbn [fold_right map]. rewrite IH. reflexivity. }
  rewrite E. reflexivity.
Qed.

(* the same kept set before and after: the bound is unchanged *)
Lemma lpo_TD_keep : forall (T : list (Z * Z)) b, TD T T b = b.
Proof.
  intros T [l y c]. unfold TD. rewrite TD_free_form, TD_malloc_form. cbn [sb_live sb_bytes sb_cap]. f_equal; lia.
Qed.

Lemma lpo_fds_vm : forall vm md, m_fds (with_vmmaps vm md) = m_fds md.
Proof. intros vm md. destruct md. reflexivity. Qed.

(* ==========================================================================
   2. The post
   ========================================================================== *)

Section PO.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis FF : LFF B API.
Local Abbreviation segs := (ms_segs B).
Local Abbreviation MR := (aa_MR API).

(* lib_post_x_T (YL0i.v:240-259) word for word, with `SINK mem' md'` for `sink_none B mem' md'` and
   `lib_delta n b` at mf_shape (= b) *)
Definition lpost_T (SINK : (word -> option byte) -> Model -> Prop) (G : list (Z * Z)) (out : list byte)
(stk : Z) (L : layout) (A : astate) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf) (T T' : list (Z * Z))
(L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
MR L' A' mem' md' /\ WF A' /\ bounded A' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 0 /\
regs_preserved regs regs' /\
(exists vm' fds' pins', md' = os_upd vm' fds' (ll_fs l) pins' md /\ forall k, fd_lookup fds' k = fd_lookup (m_fds md) k) /\
(forall q k, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T ->
exists q', In (q', k) (user_blocks A') /\ ptr_addr L' q' = ptr_addr L q) /\
(forall a, YM05.alloc_ceiling <= a < 2 ^ 64 -> ~ lib_scratch B stk regs a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall a, in_img B a -> ~ static_owned B a -> ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) ->
~ (errno_addr B <= a < errno_addr B + 4) -> ~ in_globals G a ->
mbyte segs mem' a = mbyte segs mem a /\ (writable_at segs mem a <-> writable_at segs mem' a)) /\
(forall q k i, In (q, k) (user_blocks A) -> ~ In (ptr_addr L q, k) T -> ptr_addr L q <> p -> 0 <= i < k ->
mbyte segs mem' (ptr_addr L q + i) = mbyte segs mem (ptr_addr L q + i)) /\
(forall a, lib_scratch B stk regs a -> writable_at segs mem' a) /\
ll_ret l = 0 /\ ll_out l = out /\ Fs.fs_sorted (ll_fs l) = true /\
SINK mem' md' /\
res_ok_slots A' (TD T T' b) /\
(forall i, 0 <= i < n -> mbyte segs mem' (p + i) = mbyte segs mem (p + i)) /\
tb_live L' A' T' /\
(forall t, In t T' -> In t (blocks L A) -> In t T).

(* the copy is exact: at SINK = mf_sink (the frame lane's open-file clause, now on the branch: YL0i.v:255) it
   is lib_post_x_T at mf_shape *)
Lemma lpost_T_mf : forall G out stk L A regs mem md p n b l T T' L' A' regs' mem' md',
  lpost_T (mf_sink B link_mf) G out stk L A regs mem md p n b l T T' L' A' regs' mem' md' <->
  lib_post_x_T (LS:=mf_shape) B API G out stk L A regs mem md p n b l T T' L' A' regs' mem' md'.
Proof.
  intros G out stk L A regs mem md p n b l T T' L' A' regs' mem' md'.
  unfold lpost_T, lib_post_x_T. split; intros H; exact H.
Qed.

Lemma lpo_img_of_chk : forall a, lpo_img_chk a = true -> in_img B a.
Proof.
  intros a H. unfold lpo_img_chk in H.
  destruct (find_segment rsegs a 1) as [seg|] eqn:E; [|discriminate H].
  exact (lfr_find_img B a seg (lff_segs B API FF) E).
Qed.

(* the bytes closed_stdio_env reads are image bytes a call keeps (LFR's image clause) and are not in llvm_G *)
Lemma lpo_env_addr : forall a, (a = @sk_threaded SK \/ @sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) ->
  lf_img B a /\ ~ in_globals llvm_G a.
Proof.
  intros a Ha.
  pose proof FF as (SEG & MAL & FRE & REA & CAL & ERRC & GUA & GOT & CTX & LCK & LIBC & SCL & SMC & MDC & DBR & TP
    & EOFF & REP & VML & DBL & OFH & OFL & THR & CTXRO & ALLOC).
  rewrite THR, OFL in Ha.
  assert (Hc : lpo_img_chk a = true).
  { destruct lpo_env_chk as [C1 C2]. destruct Ha as [Ha | Ha].
    - apply (lpo_rng_img_ok _ _ C1). lia.
    - apply (lpo_rng_img_ok _ _ C2). lia. }
  split; [split; [|split; [|split]]|].
  - exact (lpo_img_of_chk a Hc).
  - assert (V1 : vml_lo B = 0) by (unfold vml_lo; rewrite VML; reflexivity).
    assert (V2 : vml_len B = 0) by (unfold vml_len; rewrite VML; reflexivity).
    unfold static_owned. rewrite LCK, LIBC, GOT, GUA, DBR, DBL, SCL, SMC, MDC, V1, V2, Z.max_id. lia.
  - rewrite CTX. unfold CTX_SIZE. lia.
  - unfold errno_addr. rewrite TP, EOFF. lia.
  - intros (lo & len & Hin & Hr). unfold llvm_G, frame_G in Hin. cbn [In] in Hin.
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end;
      try (injection Hin as <- <-; lia); contradiction.
Qed.

Lemma lpo_env_keep : forall (mem0 mem : word -> option byte),
  (forall a, lf_img B a -> ~ in_globals llvm_G a ->
     mbyte segs mem a = mbyte segs mem0 a /\ (writable_at segs mem0 a <-> writable_at segs mem a)) ->
  closed_stdio_env B mem0 -> closed_stdio_env B mem.
Proof.
  intros mem0 mem H [H1 H2].
  assert (E : forall a, (a = @sk_threaded SK \/ @sk_ofl_lock SK <= a < @sk_ofl_lock SK + 4) ->
              mbyte segs mem a = mbyte segs mem0 a).
  { intros a Ha. destruct (lpo_env_addr a Ha) as [Hi Hg]. exact (proj1 (H a Hi Hg)). }
  split.
  - intros k Hk. rewrite E by (left; lia). exact (H1 k Hk).
  - intros k Hk. rewrite E by (right; lia). exact (H2 k Hk).
Qed.

(* the entry's open-file facts (lib_pre_x's sink clause, mf_sink) *)
Lemma lgv_sink : forall g, LGV B API g ->
  closed_stdio_env B (lg_mem g) /\ Namei.fd_names_path (m_fds (lg_md g)) sink_path = false.
Proof.
  intros g ((_ & _ & _ & _ & _ & (Henv & Hn & _) & _) & _). split; [exact Henv | exact Hn].
Qed.

(* The post from the frame relation at the slot's return. *)
Lemma cut_post : forall g hb T L A regs mem md,
  LFR B API g hb T L A mem md ->
  getr regs 10 = Z_to_bv 64 0 -> regs_preserved (lg_regs g) regs ->
  bytes_at rsegs mem (A_LONG_ALIAS + 300) [Z_to_bv 8 0] ->
  ((lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = [])) ->
  lpost_T (mf_sink B link_mf) llvm_G [] SLOT_STACK (lg_L g) (lg_A g) (lg_regs g) (lg_mem g) (lg_md g)
    (lg_p g) (lg_n g) (lg_b g) (LL 0 (m_fs (lg_md g)) []) (lg_T g) T L A regs mem md /\
  llvm_GI B (S (lg_j g)) T mem.
Proof.
  intros g hb T L A regs mem md HFR H10 HRP HLA Hcase.
  pose proof HFR as (HGV & HMR & HWF & HBD & HIN & Hmd & Hhi & Himg & Hblk0 & Hstkw & Herrw & _ & _ & Hres
    & HP & Hkept & Hgi).
  pose proof HGV as (Hpx & _ & Htb0 & HnT0 & _).
  pose proof Hpx as (Hpre & _ & _ & _ & _ & _ & _ & Hsort & _).
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpay & _).
  destruct (lgv_sink g HGV) as [Henv0 Hnm0].
  destruct Hmd as (vm & ->).
  (* the allocator's blocks have no duplicates (frame_allocator's blocks_nodup, at any FP state: fx0), so a
     block of hb is not an entry block *)
  assert (HND : NoDup (hb ++ blocks (lg_L g) (lg_A g))).
  { destruct (lff_alloc B API FF YK11.fx0) as (_ & _ & _ & _ & _ & _ & _ & _ & HNd & _).
    apply (proj2 (stdpp.base.NoDup_ListNoDup _)).
    eapply Permutation.Permutation_NoDup; [exact HP|]. eapply List.NoDup_map_inv.
    apply (proj1 (stdpp.base.NoDup_ListNoDup _)). exact (HNd L A _ _ HMR). }
  (* the kept set: the bound, tb_live, and the kept blocks that were entry blocks *)
  assert (HK : res_ok_slots A (TD (lg_T g) T (lg_b g)) /\ tb_live L A T /\
               (forall t, In t T -> In t (blocks (lg_L g) (lg_A g)) -> In t (lg_T g))).
  { destruct Hcase as [(HT0 & Hhb) | (HT0 & Hhb)]; subst hb.
    - rewrite HT0, lpo_TD_open. split; [exact Hres|]. split.
      + split.
        * apply (proj2 (stdpp.base.NoDup_ListNoDup _)).
          destruct Hkept as [(Hne & _) | (_ & [-> | (f & -> & _)])];
            [contradiction | constructor | constructor; [intros [] | constructor]].
        * intros t Ht. apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Ht.
      + intros t Ht Hb. exfalso. exact (lpo_nodup_disj _ _ t HND Ht Hb).
    - destruct Hkept as [(_ & HTe) | (Habs & _)]; [|contradiction].
      subst T. rewrite lpo_TD_keep. rewrite sb_hb_nil in Hres. split; [exact Hres|]. split.
      + destruct Htb0 as [Hnd0 Hin0]. split; [exact Hnd0|].
        intros t Ht. apply (Permutation_in _ (Permutation_sym HP)). exact (Hin0 t Ht).
      + intros t Ht _. exact Ht. }
  destruct HK as (HKres & HKtb & HKin).
  split; [|split; [exact Hgi | exact HLA]].
  unfold lpost_T.
  split; [exact HMR|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact HIN|].
  split; [exact H10|]. split; [exact HRP|].
  split.
  { exists vm, (m_fds (lg_md g)), (m_statpins (lg_md g)).
    split; [exact (with_vmmaps_os_upd vm (lg_md g)) | intros k; reflexivity]. }
  split.
  { intros q k Hq _.
    assert (Hb : In (ptr_addr (lg_L g) q, k) (blocks L A)).
    { apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. right. unfold blocks.
      exact (in_map (fun b => (ptr_addr (lg_L g) (fst b), snd b)) _ (q, k) Hq). }
    unfold blocks in Hb. apply in_map_iff in Hb as ([q' k'] & E & Hq'). cbn [fst snd] in E.
    injection E as E1 E2. subst k'. exists q'. split; [exact Hq' | exact E1]. }
  split.
  { intros a Ha Hns. apply Hhi; [exact Ha|]. intros Hw. apply Hns. unfold lib_scratch. left. exact Hw. }
  split.
  { intros a H1 H2 H3 H4 H5. exact (Himg a (conj H1 (conj H2 (conj H3 H4))) H5). }
  split.
  { intros q k i Hq HT _ Hi. apply (Hblk0 (ptr_addr (lg_L g) q) k i); [|exact HT | exact Hi].
    unfold blocks. exact (in_map (fun b => (ptr_addr (lg_L g) (fst b), snd b)) _ (q, k) Hq). }
  split.
  { intros a Ha. unfold lib_scratch in Ha. destruct Ha as [Ha | Ha]; [apply Hstkw; exact Ha | apply Herrw; exact Ha]. }
  split; [reflexivity|]. split; [reflexivity|]. split; [exact Hsort|].
  split.
  { apply (mf_sink_of_gi B link_mf T); [exact Hgi | exact (lpo_env_keep (lg_mem g) mem Himg Henv0) |].
    rewrite lpo_fds_vm. exact Hnm0. }
  split; [exact HKres|].
  split.
  { intros i Hi. destruct Hpay as [(Hn0 & _) | (Hn0 & q & Hq & Hpq)]; [lia|].
    apply (Hblk0 (lg_p g) (lg_n g) i); [|exact (HnT0 Hn0) | exact Hi].
    rewrite <- Hpq. unfold blocks.
    exact (in_map (fun b => (ptr_addr (lg_L g) (fst b), snd b)) _ (q, lg_n g) Hq). }
  split; [exact HKtb | exact HKin].
Qed.

(* The same at the config level: from the cut at the return address (the exit files' last cut), whose
   evt-level predicate P carries a0 = 0, the restored registers and the long_alias NUL. P holds of a state
   ms_eqv to the config's view lcanon: the same registers up to x0, and the memory normalize_cj of the
   config's (bytes_at transfers back by MemNorm.bytes_at_rel_cj). *)
Lemma cut_post_cfg : forall g hb T (P : machine_state -> Prop) c,
  CUT B API g (lg_ra g) hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 10 = Z_to_bv 64 0 /\ regs_preserved (lg_regs g) (ms_regs ms) /\
     bytes_at rsegs (ms_mem ms) (A_LONG_ALIAS + 300) [Z_to_bv 8 0]) ->
  ((lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = [])) ->
  exists (fx' : YK11.FPState) L' A' regs' mem' md' T',
    c = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 (lg_ra g)) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lpost_T (mf_sink B link_mf) llvm_G ((fun _ : list byte => @nil byte) (lg_pl g)) SLOT_STACK (lg_L g) (lg_A g)
      (lg_regs g) (lg_mem g) (lg_md g) (lg_p g) (lg_n g) (lg_b g) (LL 0 (m_fs (lg_md g)) []) (lg_T g) T'
      L' A' regs' mem' md' /\
    llvm_GI B (S (lg_j g)) T' mem'.
Proof.
  intros g hb T P c (fx' & L & A & regs & mem & md & Hc & Hf & HFR & (c0 & HP0 & Heqv)) HPost Hcase.
  destruct (HPost c0 HP0) as (H10 & HRP & HLA).
  destruct Heqv as (Hx & _ & _ & _ & _ & _ & Hm & _).
  change (ms_regs (lcanon fx' regs (lg_ra g) mem)) with regs in Hx.
  change (ms_mem (lcanon fx' regs (lg_ra g) mem)) with (normalize_cj rsegs mem) in Hm.
  assert (Eg : forall r, getr (ms_regs c0) r = getr regs r) by (intros r; exact (mk_leaf.getr_eqv _ _ Hx r)).
  assert (Eg' : forall r, YK11.getr (ms_regs c0) r = YK11.getr regs r) by (intros r; exact (Eg r)).
  assert (HRO : ro_agree rsegs mem).
  { pose proof HFR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
    rewrite (lff_segs B API FF) in HRO. exact HRO. }
  rewrite Hm in HLA.
  assert (H10' : getr regs 10 = Z_to_bv 64 0) by (rewrite <- Eg; exact H10).
  assert (HRP' : regs_preserved (lg_regs g) regs) by (intros r Hr; rewrite <- Eg'; exact (HRP r Hr)).
  assert (HLA' : bytes_at rsegs mem (A_LONG_ALIAS + 300) [Z_to_bv 8 0])
    by exact (bytes_at_rel_cj rsegs mem _ _ _ (mem_rel_cj_normalize rsegs mem HRO) HLA).
  destruct (cut_post g hb T L A regs mem md HFR H10' HRP' HLA' Hcase) as [Hpost HGI].
  exists fx', L, A, regs, mem, md, T. split; [exact Hc|]. split; [exact Hf|]. split; [exact Hpost | exact HGI].
Qed.

(* the same, in the obligation's own words: lib_post_x_T at mf_shape and GI (S j) *)
Lemma cut_post_lib : forall g hb T (P : machine_state -> Prop) c,
  CUT B API g (lg_ra g) hb T P c ->
  (forall ms, P ms -> getr (ms_regs ms) 10 = Z_to_bv 64 0 /\ regs_preserved (lg_regs g) (ms_regs ms) /\
     bytes_at rsegs (ms_mem ms) (A_LONG_ALIAS + 300) [Z_to_bv 8 0]) ->
  ((lg_T g = [] /\ hb = T) \/ (lg_T g <> [] /\ hb = [])) ->
  exists (fx' : YK11.FPState) L' A' regs' mem' md' T',
    c = mkCfg (@YK11.mkst fx' regs' (Z_to_bv 64 (lg_ra g)) mem' (seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    lib_post_x_T (LS:=mf_shape) B API llvm_G ((fun _ : list byte => @nil byte) (lg_pl g)) SLOT_STACK
      (lg_L g) (lg_A g) (lg_regs g) (lg_mem g) (lg_md g) (lg_p g) (lg_n g) (lg_b g) (LL 0 (m_fs (lg_md g)) [])
      (lg_T g) T' L' A' regs' mem' md' /\
    llvm_GI B (S (lg_j g)) T' mem'.
Proof.
  intros g hb T P c HC HP Hcase.
  destruct (cut_post_cfg g hb T P c HC HP Hcase) as (fx' & L' & A' & regs' & mem' & md' & T' & Hc & Hf & Hpost & HGI).
  exists fx', L', A', regs', mem', md', T'. split; [exact Hc|]. split; [exact Hf|].
  split; [apply lpost_T_mf; exact Hpost | exact HGI].
Qed.

End PO.
