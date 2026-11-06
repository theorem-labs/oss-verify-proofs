From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memset_c same_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_parse_c pj_free_c parse_noting_c padded_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import check_no_overread_c check_no_overread_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section U.
Context {fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState} {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B MR.

Lemma cno_seg_in_img : forall x seg, find_segment (ms_segs B) x 1 = Some seg -> in_img B x.
Proof.
  intros x seg E. destruct (kb_find_segment _ x 1 seg E) as (Hin & H1 & H2).
  assert (C : forallb (fun s => existsb (fun rr => (bv_unsigned (fst rr) <=? Z.of_N (seg_base s)) &&
      (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved (ms_segs B))) (ms_segs B) = true) by (rewrite HS; vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C seg Hin). apply existsb_exists in C. destruct C as (rr & Hr & Hc).
  apply andb_prop in Hc as (Hc1 & Hc2). apply Z.leb_le in Hc1, Hc2.
  split; [intros E'; rewrite E' in Hin; destruct Hin | exists rr; split; [exact Hr | lia]].
Qed.

Lemma cno_mbyte_raw : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> mbyte (ms_segs B) m a = m (Z_to_bv 64 a).
Proof.
  intros m a Ha Hn. unfold mbyte. destruct (m (Z_to_bv 64 a)) as [b|]; [reflexivity|].
  unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom, memory_read. rewrite unsigned_lit by lia. change (Z.of_N 1) with 1.
  destruct (find_segment (ms_segs B) a 1) as [s|] eqn:E; [exfalso; exact (Hn (cno_seg_in_img a s E)) | reflexivity].
Qed.

Lemma cno_present_of_writable : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a ->
  writable_at (ms_segs B) m a -> present m a.
Proof.
  intros m a Ha Hn W. unfold writable_at, wview in W. unfold present.
  destruct (m (Z_to_bv 64 a)) as [x|] eqn:E; [exists x; reflexivity|]. exfalso.
  rewrite unsigned_lit in W by lia.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:F; [|apply W; reflexivity].
  exact (Hn (cno_seg_in_img a seg F)).
Qed.

Lemma cno_writable_of_present : forall m a, present m a -> writable_at (ms_segs B) m a.
Proof. intros m a [x Hx]. unfold writable_at, wview. rewrite Hx. discriminate. Qed.

Lemma cno_rw_of_present : forall m lo k, 0 <= lo -> lo + k <= 2 ^ 64 -> 0 <= k ->
  (forall i, 0 <= i < k -> present m (lo + i)) -> exists junk, rw_cells rsegs m lo [CB (Z.to_nat k) junk].
Proof.
  intros m lo k Hlo Hhi Hk HP.
  assert (ST : stk rsegs m lo (lo + k)).
  { split; [lia|]. split; [lia|]. intros a Ha. destruct (HP (a - lo)) as [x Hx]; [lia|].
    replace (lo + (a - lo)) with a in Hx by lia. unfold wa. split.
    - unfold wview. rewrite Hx. discriminate.
    - exists x. unfold mrd. rewrite Hx. reflexivity. }
  destruct (stk_carve rsegs m lo (lo + k) (Z.to_nat k) ST ltac:(lia)) as [_ [junk H]].
  exists junk. replace (lo + k - Z.of_nat (Z.to_nat k)) with lo in H by lia. exact H.
Qed.

Lemma cno_ro_false : forall a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha Hn. unfold ro_addr. rewrite unsigned_lit by lia. rewrite <- HS.
  destruct (find_segment (ms_segs B) a 1) as [seg|] eqn:E; [exfalso; exact (Hn (cno_seg_in_img a seg E)) | reflexivity].
Qed.

Lemma cno_ro_agree_munch : forall W m m', ro_agree rsegs m -> munch W m m' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ outside W a -> ~ in_img B a) -> ro_agree rsegs m'.
Proof.
  intros W m m' H HM HW a Ha. destruct (kb_outside_dec W (bv_unsigned a)) as [Ho|Ho].
  - pose proof (H a Ha) as E. unfold mrd in *. rewrite (HM a Ho). exact E.
  - exfalso. pose proof (bv_unsigned_in_range 64 a) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
    pose proof (cno_ro_false (bv_unsigned a) Hr (HW _ Hr Ho)) as E. rewrite Z_to_bv_bv_unsigned in E. congruence.
Qed.

Lemma cno_bytes_frame : forall m m' a bs, bytes_at rsegs m a bs ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte (ms_segs B) m' (a + i) = mbyte (ms_segs B) m (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs (H0 & H1 & H) Hm. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite <- (H i Hi). pose proof (Hm (Z.of_nat i) ltac:(lia)) as E. unfold mbyte in E. rewrite HS in E.
  exact E.
Qed.

Lemma cno_errno_img : forall a, errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO ->
  errno_addr B <= a < errno_addr B + 4 -> in_img B a.
Proof.
  intros a E Ha. rewrite E in Ha.
  assert (C : existsb (fun rr => (bv_unsigned (fst rr) <=? OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO) &&
      (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO + 4 <=? bv_unsigned (fst rr) + bv_unsigned (snd rr)))
      (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  apply existsb_exists in C. destruct C as (rr & Hr & Hc). apply andb_prop in Hc as (Hc1 & Hc2).
  apply Z.leb_le in Hc1, Hc2. split; [rewrite HS; discriminate|]. exists rr. rewrite HS. split; [exact Hr | lia].
Qed.

Lemma cno_rd_cells : forall L A m md, MR L A m md -> ro_agree (ms_segs B) m -> rd_cells B m.
Proof.
  intros L A m md HM RA. destruct (ax_statics AX L A m md HM) as (G1 & (g & _ & G2) & _).
  split; [exact RA|]. split; [exact G1|]. exists g. exact G2.
Qed.

Lemma cno_run_n : forall regs pc mem md (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] -> ro_agree (ms_segs B) mem ->
  evt (ms_segs B) (fun ms => exists R pc' mem', ms = MS R fp_regs pc' fp_csr None mem' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B)) /\ K R pc' mem')
    (MS (rmk regs) fp_regs pc fp_csr None (normalize (ms_segs B) mem) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) ->
  (forall R pc' m0 mem' regs', K R pc' m0 -> mem_rel (ms_segs B) mem' m0 -> ro_same (ms_segs B) mem mem' ->
     (forall r, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' r = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R r) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs' pc' mem' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs pc mem (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros regs pc mem md K P Hh Hl RA HE HK.
  apply (kb_run B regs pc mem md
    (fun R pc' mem' => exists m0, K R pc' m0 /\ mem_rel (ms_segs B) mem' m0 /\ ro_same (ms_segs B) mem mem') P Hh Hl).
  - eapply evt_mono; [apply (evt_normalize (ms_segs B)); [rewrite HS; vm_compute; reflexivity | exact RA | exact HE] |].
    intros s (s0 & (R & pc' & m0 & -> & HKR) & HREL & HRS).
    destruct s as [R1 F1 pc1 sv1 rv1 fc1 m1 ro1]. destruct HREL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in *. subst.
    exists R, pc', m1. split; [reflexivity|]. exists m0. split; [exact HKR|]. split; [exact E8 | exact HRS].
  - intros R pc' mem' regs' (m0 & HKR & HREL & HRS) HG. exact (HK R pc' m0 mem' regs' HKR HREL HRS HG).
Qed.

Lemma cno_back : forall m mr m0 W, ro_agree (ms_segs B) m -> mem_rel (ms_segs B) mr m0 -> ro_same (ms_segs B) m mr ->
  munch W (normalize (ms_segs B) m) m0 -> wmono (ms_segs B) (normalize (ms_segs B) m) m0 ->
  munch W m mr /\ wmono (ms_segs B) m mr /\ ro_agree (ms_segs B) mr.
Proof.
  intros m mr m0 W HA HR HS0 MU WM. pose proof (mem_rel_normalize (ms_segs B) m HA) as HN.
  split; [exact (munch_rel (ms_segs B) W m (normalize (ms_segs B) m) mr m0 HN HR HS0 MU)|].
  split; [exact (wmono_rel (ms_segs B) m (normalize (ms_segs B) m) mr m0 HN HR HS0 WM)|].
  exact (ro_agree_same (ms_segs B) m mr HA HS0).
Qed.

End U.

Definition cno_tv (r : option jv) : jv := match r with Some t => t | None => JNull end.

Lemma cno_node_rw : forall segs m L p t D, pj_node segs m L p t D -> pj_rw segs m p.
Proof.
  intros segs m L p t D H. destruct t; cbn [pj_node] in H;
    destruct H as (_ & _ & num & str & kids & keys & n & cap & (Hrw & _) & _); exact Hrw.
Qed.

Lemma cno_rw_writable : forall segs m p a, pj_rw segs m p -> p <= a < p + 56 -> writable_at segs m a.
Proof. intros segs m p a (_ & _ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma cno_free_k : forall d, (d <= 32)%nat -> 0 <= PJ_FREE_K d /\ 240 + PJ_FREE_K d <= CNO_K.
Proof.
  intros d Hd. pose proof (Z.le_max_r (PARSE_VALUE_K 0) (PJ_FREE_K 33)) as H.
  assert (E : PJ_FREE_K 33 = 9824) by reflexivity. rewrite E in H.
  assert (HP : 9824 + 48 <= PJ_PARSE_K) by (unfold PJ_PARSE_K, PJ_PARSE_F; rewrite E; lia).
  assert (Ed : PJ_FREE_K d = 48 * Z.of_nat d + 8240) by (unfold PJ_FREE_K, PJ_FREE_F, FREE_K, ALLOC_STACK; lia).
  rewrite Ed. unfold CNO_K, CNO_F, PN_K, PN_F. split; lia.
Qed.

Lemma cno_parse_k : 0 <= PN_K /\ 240 + PN_K <= CNO_K.
Proof. pose proof cno_k_le. unfold CNO_K, CNO_F in *. lia. Qed.

Section P.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Variable F : ResForm.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis HPAD : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @padded_contract fx rc B API F.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.

Let J := cj B API L0 A0 regs0 mem0 md0.
Let KA := cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0.
Let KC := cj_callpost B API L0 A0 regs0 mem0 md0 PRE0.
Let KR := cj_rpost B API HS HG L0 A0 regs0 mem0 md0 PRE0.

Lemma cno_call_pre : forall L A regs m md K,
  J L A m md -> spZ regs = spZ regs0 - 240 -> 0 <= K -> 240 + K <= CNO_K ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) m) ->
  call_pre_k B MR K L A regs m md.
Proof.
  intros L A regs m md K Jc Hsp HK0 HKK Htp Hra HAUX.
  pose proof Jc as (HM & HWF & HBD & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & HRA).
  pose proof PRE0 as (_ & _ & _ & _ & HSP16 & HK & HK63 & _ & HTP & _).
  pose proof cno_k_le as HKv.
  split; [exact HM|]. split; [exact HWF|]. split; [exact HBD|]. split; [exact Hra|].
  rewrite Hsp. split; [clear -HSP16; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
  split; [intros a Ha; apply HSC; left; lia|]. split; [rewrite Htp; exact HTP|].
  split; [intros a Ha; apply HSC; right; exact Ha|].
  intros Hf. rewrite <- Hsp. exact (HAUX Hf).
Qed.

(* One call of the out-of-line padded (0x1448c): a0 = d (the input), a1 = n, a2 = fill.  Under rf_room its malloc is
   not refused (padded_contract): the post is malloc's at padded's stack bound PADDED_K, with the new block holding
   the copy followed by 16 bytes of fill. *)
Lemma cno_call_padded : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md bnd d n fill (xs : list byte) (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 d -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 n ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 fill -> 0 <= fill < 256 ->
  Z.of_nat (length xs) = n -> n <= 0x300000 -> Mem.bytes_at (ms_segs B) m d xs ->
  (xs <> [] -> exists a k, In (a, k) (blocks L A) /\ a <= d /\ d + n <= a + k) ->
  (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) m) ->
  rf_ok F A bnd -> rf_room F bnd (n + 16) ->
  (forall L' A' regs' m' md' q,
     J L' A' m' md' ->
     call_post_k B MR PADDED_K L A regs m md (fun _ => False) L' A' regs' m' md' ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 q -> q <> 0 -> fresh_block B q (n + 16) ->
     (exists b1 b2, blocks L' A' = b1 ++ (q, n + 16) :: b2 /\ blocks L A = b1 ++ b2) ->
     (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) ->
     st_init_done A' = true ->
     rf_ok F A' (rf_malloc F bnd (n + 16)) ->
     Mem.bytes_at (ms_segs B) m' q (xs ++ repeat (Z_to_bv 8 fill) 16) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 0x1448c) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md bnd d n fill xs P Jc Hsp Htp Hra R10 R11 R12 HF HL HN HB HX HAUX HRES HROOM K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & _ & HRA).
  pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hac.
  assert (HPK : PADDED_K = 8240) by (unfold PADDED_K, PADDED_F, ALLOC_STACK; reflexivity).
  eapply SR_bind; [apply (HPAD fx L A regs m md bnd d n fill xs) |].
  - apply (cno_call_pre L A regs m md PADDED_K Jc Hsp); [lia | lia | exact Htp | exact Hra | exact HAUX].
  - exact HRA.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact HF.
  - exact HL.
  - exact HN.
  - exact HB.
  - exact HX.
  - exact HRES.
  - exact HROOM.
  - intros c' ((L' & A' & regs' & m' & md' & q & -> & CP & R10' & Hq & Hq16 & FR & BL & BK & RA' & GK & SURV & INIT &
               LEN & RES') & (ms' & md'' & E & BY)).
    injection E as E1 E2. subst ms' md''.
    cbv beta iota delta [ms_mem ms_regs OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst] in BY.
    rewrite R10' in BY. pose proof FR as (FR1 & FR2 & _). rewrite unsigned_lit in BY by lia.
    apply (K L' A' regs' m' md' q); try assumption.
    apply (KC L A m md PADDED_K regs (fun _ => False) L' A' regs' m' md' Jc CP).
    + lia.
    + lia.
    + intros a [].
    + intros p k Hp. exact (SURV p k (proj1 (HUB p k Hp))).
    + exact INIT.
    + exact LEN.
    + exact RA'.
Qed.

Lemma cno_call_free : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md bnd p n (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  In (p, n) (user_blocks A) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  (forall q k, In (q, k) (user_blocks A0) -> q <> p) ->
  st_init_done A = true -> rf_ok F A bnd ->
  (forall L' A' regs' m' md',
     J L' A' m' md' ->
     call_post B MR L A regs m md (fun a => ptr_addr L p <= a < ptr_addr L p + n) L' A' regs' m' md' ->
     (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A')) ->
     st_init_done A' = true -> rf_ok F A' (rf_free F bnd n) ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 0x18250) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md bnd p n P Jc Hsp Htp Hra Hp R10 HNS INIT HRES K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & _ & HRA).
  pose proof cno_k_le as HKv.
  rewrite <- HFREE.
  eapply SR_bind; [apply (FREE fx L A regs m md p n bnd) |].
  - apply (proj2 (call_pre_k_alloc B MR L A regs m md)).
    apply (cno_call_pre L A regs m md ALLOC_STACK Jc Hsp); [unfold ALLOC_STACK; lia | unfold ALLOC_STACK; lia | exact Htp | exact Hra |].
    intros Hf. congruence.
  - exact HRA.
  - exact Hp.
  - exact R10.
  - exact HRES.
  - intros c' (L' & A' & regs' & m' & md' & -> & CP & BL & BK & RA' & GK & SURV & INIT' & LEN & RES').
    apply (K L' A' regs' m' md'); try assumption; [| exact (INIT' INIT)].
    pose proof (proj1 (call_post_k_alloc B MR L A regs m md _ L' A' regs' m' md') CP) as CPk.
    apply (KC L A m md ALLOC_STACK regs _ L' A' regs' m' md' Jc CPk).
    + unfold ALLOC_STACK. lia.
    + lia.
    + intros a Ha. pose proof (cno_ub_blocks L A p n Hp) as Hb.
      destruct (cno_block_facts B API AX L A m md _ n (a - ptr_addr L p) HM Hb ltac:(lia)) as (_ & _ & H3 & _ & H5).
      replace (ptr_addr L p + (a - ptr_addr L p)) with a in H5 by lia. split; [lia | exact H5].
    + intros q k Hq. apply SURV; [exact (proj1 (HUB q k Hq)) | exact (HNS q k Hq)].
    + exact (INIT' INIT).
    + exact LEN.
    + exact RA'.
Qed.

Hypothesis HTP : ms_tp B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.

Lemma cno_frame_out : forall L A m md out, J L A m md -> spZ regs0 - 240 <= out -> out + 56 <= spZ regs0 ->
  out mod 8 = 0 -> pj_rw (ms_segs B) m out /\
  forall i, 0 <= i < 56 -> ~ owned B L A (out + i) /\ ~ alloc_statics (out + i) /\
    ~ (errno_addr B <= out + i < errno_addr B + 4) /\ ~ in_img B (out + i).
Proof.
  intros L A m md out Jc H1 H2 H3.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  assert (HNI : forall a, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a -> ~ in_img B a).
  { intros a Ha Hi. pose proof (cno_img_low B HS a Hi). lia. }
  split.
  - split; [exact H3|]. split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at (ms_segs B) m a) by (apply HSC; left; lia).
    split; [exact W|]. destruct (cno_present_of_writable B HS m a ltac:(lia) (HNI a ltac:(lia)) W) as [b Hb].
    exists b. unfold mrd, wa. rewrite Hb. reflexivity.
  - intros i Hi. split; [intros Ho; pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho); lia|].
    split; [intros Hs; destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _); lia|].
    split; [rewrite HERR; unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO; lia|]. apply HNI. lia.
Qed.

(* One reading: jal parse_noting (0x13a38, #102: no ran_out pointer, it reads g_ran_out as its caller left it) with
   a0 = q (a copy), a1 = n, a2 = out (a tree buffer in the frame), g_ran_out 0 before the call.  parse_noting's room
   route keeps every allocation in room, so its post leaves g_ran_out = 0. *)
Lemma cno_call_parse : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md Lam' pk ct bnd q out (tb : list byte) (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  frm_zero fp_csr ->
  ledger B L A m Lam' pk ct (2 ^ 64 - 1) -> rf_ok F A bnd ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 q -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 (Z.of_nat (length tb)) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 out ->
  In (q, Z.of_nat (length tb) + 16) (blocks L A) -> ~ In (q + 16, Z.of_nat (length tb)) Lam' ->
  Mem.bytes_at (ms_segs B) m q tb -> Z.of_nat (length tb) <= 0x300000 ->
  spZ regs0 - 240 <= out -> out + 56 <= spZ regs0 -> out mod 8 = 0 ->
  Mem.bytes_at (ms_segs B) m G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
  st_init_done A = true ->
  ct + 2 * Z.of_nat (length tb) + 2 < 2 ^ 64 - 1 ->
  room_run F bnd (cno_tr tb) ->
  (forall (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L' A' regs' m' md' Lam'' pk' D,
     J L' A' m' md' ->
     rpost B API PN_K L A regs m md (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' ->
     frm_zero (@fp_csr fx') ->
     Mem.bytes_at (ms_segs B) m' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
     ledger B L' A' m' Lam'' pk' (ct + Z.of_nat (ncalls jr_strtod (zb tb))) (2 ^ 64 - 1) ->
     pk <= pk' ->
     Permutation Lam'' (D ++ Lam') -> new_blks L A D ->
     pj_node (ms_segs B) m' (lin Lam'') out (cno_tv (json_read jr_strtod (zb tb))) D ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 (match json_read jr_strtod (zb tb) with Some _ => 0 | None => -1 end) ->
     match json_read jr_strtod (zb tb) with
     | Some _ => cno_dl (cno_tr tb) D /\ rf_ok F A' (rf_run F bnd (cno_tr tb))
     | None => D = [] /\ exists E, cno_dl (cno_tr tb) E /\ rf_ok F A' (rf_frees F (rf_run F bnd (cno_tr tb)) E)
     end ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx' regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x13a38) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md Lam' pk ct bnd q out tb P Jc Hsp Htp Hra HFZ HL HRES R10 R11 R12 HQB HQL HTB HLEN
    HO1 HO2 HO3 HGR0 HINIT HCT HROOM K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & HSC & HRA).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof cno_parse_k as HPK.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  set (n := Z.of_nat (length tb)) in *.
  destruct (cno_block_facts B API AX L A m md q (n + 16) 0 HM HQB ltac:(lia)) as (_ & Hq1 & Hq2 & _).
  destruct (cno_frame_out L A m md out Jc HO1 HO2 HO3) as (HRW & HOUT).
  destruct (cno_gro_free B API HG G_RAN_OUT ltac:(lia)) as (_ & HGlo & _ & HGown).
  destruct (HGown L A m md HM) as (_ & HGblk).
  pose proof (HGblk q (n + 16) HQB) as HGq.
  eapply SR_bind; [apply (PARSE fx L A regs m md Lam' pk ct (2 ^ 64 - 1) bnd q n out tb) |].
  - split; [exact HS|]. split; [exact HTP|]. split; [exact HERR|]. split; [exact HGG|]. split; [exact HGD|].
    split; [apply (cno_call_pre L A regs m md PN_K Jc Hsp); [lia | lia | exact Htp | exact Hra | intros Hf; congruence]|].
    split; [lia|]. split; [lia|]. split; [exact HFZ|].
    exact (cno_rd_cells B API AX L A m md HM HRA).
  - exact HL.
  - exact HRES.
  - exact R10.
  - exact R11.
  - exact R12.
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - exact HTB.
  - pose proof (PjRoundTrip.G12_1 (zb tb)) as G. assert (EL : length (zb tb) = length tb) by (unfold zb; apply length_map).
    subst n. lia.
  - split.
    + right. right. left. exists q, (n + 16). split; [exact HQB|]. split; [|lia].
      unfold lin. replace (n + 16 - 16) with n by lia. exact HQL.
    + intros i Hi. destruct (cno_block_facts B API AX L A m md q (n + 16) i HM HQB ltac:(lia)) as (_ & _ & _ & Hno & Hni).
      split; [exact Hno|]. split; [intros Hs; exact (Hni (proj1 (cno_statics_free B API HG _ Hs)))|].
      intros He. exact (Hni (cno_errno_img B HS _ HERR He)).
  - lia.
  - exact HRW.
  - split; [left; rewrite Hsp; lia|]. split; [intros _ Hf; congruence|]. exact HOUT.
  - intros a k Hin. destruct (ledger_block_range B API L A m md Lam' pk ct _ a k HM HL Hin). right. lia.
  - cbn [Frame.disjoint_from]. split; [right; lia | exact I].
  - exact HGR0.
  - cbn [Frame.disjoint_from]. split; [lia|]. split; [left; lia | exact I].
  - cbn [Frame.disjoint_from]. rewrite Hsp. split; [right; lia|]. split; [left; lia | exact I].
  - lia.
  - exact HROOM.
  - intros c' (fx' & L' & A' & regs' & m' & md' & Lam'' & pk' & ct' & fl' & ok & res & tr & -> & FZ' & _ & RP & RD &
               GR0 & LED' & JR & OKS & CT' & FL' & PK' & _ & _ & SUC & MATCH).
    assert (NC : (ncalls jr_strtod (zb tb) <= 2 * length (zb tb) + 2)%nat) by apply G7_4.
    assert (EL : length (zb tb) = length tb) by (unfold zb; apply length_map).
    subst n.
    destruct SUC as [ERES ECALLS]; [right; lia|].
    assert (ETR : tr = cno_tr tb).
    { assert (HU : forall i, (i < ncalls jr_strtod (zb tb))%nat -> nth i ok true = true).
      { intros i Hi. rewrite (OKS i ltac:(lia)). apply negb_true_iff. apply Z.eqb_neq. lia. }
      rewrite (G7_1 jr_strtod (zb tb) ok HU) in JR. injection JR as _ E. symmetry. exact E. }
    assert (EFL : fl' = 2 ^ 64 - 1) by (apply (proj2 FL'); lia).
    rewrite ECALLS in CT'. subst ct' fl'.
    assert (Jc' : forall D, pj_node (ms_segs B) m' (lin Lam'') out (cno_tv (json_read jr_strtod (zb tb))) D -> J L' A' m' md').
    { intros D HN. apply (KR L A m md PN_K regs (parse_noting_writes out) (fun _ _ => False) L' A' regs' m' md' Jc RP).
      - rewrite Hsp. lia.
      - lia.
      - intros a [Ha|Ha].
        + right. left. split; [lia|]. exact (cno_rw_writable _ m' out a (cno_node_rw _ _ _ _ _ _ HN) Ha).
        + left. exact Ha.
      - intros p0 n0 _ [].
      - exact (proj1 RD). }
    rewrite ERES in MATCH. rewrite ETR in MATCH. destruct (json_read jr_strtod (zb tb)) as [t|] eqn:EJR.
    + destruct MATCH as (R10' & RF & D & PERM & LS & LN & NEW & NODE).
      apply (K fx' L' A' regs' m' md' Lam'' pk' D (Jc' D NODE) RP FZ' GR0 LED'); try assumption.
      * rewrite PK'. lia.
      * split; [exact (cno_dl_of _ D LS LN) | exact RF].
    + destruct MATCH as (R10' & (D0 & D' & HP & LS & LN & RF) & PERM & ZERO).
      assert (NODE : pj_node (ms_segs B) m' (lin Lam'') out JNull []) by exact (pj_zero_node _ m' (lin Lam'') out ZERO).
      apply (K fx' L' A' regs' m' md' Lam'' pk' [] (Jc' [] NODE) RP FZ' GR0 LED'); try assumption.
      * rewrite PK'. lia.
      * intros a k [].
      * split; [reflexivity|]. exists D'. split; [exact (cno_dl_perm _ D0 D' HP (cno_dl_of _ D0 LS LN)) | exact RF].
Qed.

Lemma cno_call_pjfree : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md Lam' pk ct bnd v t D (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  frm_zero fp_csr ->
  ledger B L A m Lam' pk ct (2 ^ 64 - 1) -> rf_ok F A bnd ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 v -> spZ regs0 - 240 <= v -> v + 56 <= spZ regs0 -> v mod 8 = 0 ->
  st_init_done A = true ->
  pj_node (ms_segs B) m (lin Lam') v t D -> (depth t <= 32)%nat ->
  (forall a k, In (a, k) D -> ~ In (a - 16, k + 16) (blocks L0 A0)) ->
  (forall L' A' regs' m' md' Lam'',
     J L' A' m' md' ->
     rpost B API (PJ_FREE_K (depth t)) L A regs m md (pj_free_writes v D) (freed D) L' A' regs' m' md' ->
     Permutation Lam' (D ++ Lam'') -> ledger B L' A' m' Lam'' pk ct (2 ^ 64 - 1) ->
     (exists D', Permutation D D' /\ rf_ok F A' (rf_frees F bnd D')) -> pj_zero (ms_segs B) m' v ->
     SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst regs (Z_to_bv 64 0x16340) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md Lam' pk ct bnd v t D P Jc Hsp Htp Hra HFZ HL HRES R10 HV1 HV2 HV3 HINIT HN HD HNEW K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & HSC & HRA).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof (cno_free_k (depth t) HD) as HFK.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  destruct (cno_frame_out L A m md v Jc HV1 HV2 HV3) as (HRW & HOUT).
  assert (DL : forall a k, In (a, k) D -> lblock B L A m a k).
  { intros a k Hin. pose proof (pj_node_blocks _ t m (lin Lam') v D HN a k Hin) as HinL. unfold lin in HinL.
    destruct HL as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA. exact (FA (a, k) HinL). }
  eapply SR_bind; [apply (PJFREE fx L A regs m md Lam' pk ct (2 ^ 64 - 1) bnd v (depth t) D) |].
  - split; [exact HS|]. split; [exact HTP|]. split; [exact HERR|]. split; [exact HGG|]. split; [exact HGD|].
    split; [apply (cno_call_pre L A regs m md (PJ_FREE_K (depth t)) Jc Hsp); [lia | lia | exact Htp | exact Hra | intros Hf; congruence]|].
    split; [lia|]. split; [lia|]. split; [exact HFZ|].
    exact (cno_rd_cells B API AX L A m md HM HRA).
  - exact HL.
  - exact HRES.
  - exact R10.
  - right. split; [lia|]. split; [exact (pj_node_fd _ t m (lin Lam') v D HN)|]. split.
    + split; [left; rewrite Hsp; lia|]. split; [intros _ Hf; congruence|]. exact HOUT.
    + cbn [Frame.disjoint_from]. rewrite Hsp. split; [left; lia | exact I].
  - intros c' (L' & A' & regs' & m' & md' & Lam'' & -> & RP & RD & PERM & LED' & RES' & _ & VZ).
    pose proof (VZ ltac:(lia)) as VZ'.
    apply (K L' A' regs' m' md' Lam''); try assumption.
    apply (KR L A m md (PJ_FREE_K (depth t)) regs (pj_free_writes v D) (freed D) L' A' regs' m' md' Jc RP).
    + rewrite Hsp. lia.
    + lia.
    + intros a (_ & [Ha|[(a0 & k0 & Hin & Hr)|Ha]]).
      * right. left. split; [lia|]. exact (cno_rw_writable _ m' v a (proj1 VZ') Ha).
      * right. right. destruct (DL a0 k0 Hin) as (Hk0 & HinB & _ & HNI).
        destruct (cno_block_range B API L A m md _ _ HM HinB) as [Hb1 Hb2].
        split; [lia|]. split; [replace a with (a0 - 16 + (a - (a0 - 16))) by lia; apply HNI; lia|].
        intros p0 n0 Hp0 Hpa. pose proof (cno_ub_blocks L0 A0 p0 n0 Hp0) as Hb0.
        pose proof (cj_blocks0 B API L0 A0 regs0 mem0 md0 L A m md _ _ Jc Hb0) as Hb0'.
        assert (Hne : (ptr_addr L0 p0, n0) <> (a0 - 16, k0 + 16)).
        { intros E. apply (HNEW a0 k0 Hin). rewrite <- E. exact Hb0. }
        destruct (cno_blocks_sep B API L A m md _ _ HM Hb0' HinB Hne) as [S1|S1]; cbn [fst snd] in S1; lia.
      * left. exact Ha.
    + intros p0 n0 Hp0 Hfr. unfold freed in Hfr. apply (HNEW _ _ Hfr).
      replace (ptr_addr L0 p0 + 16 - 16) with (ptr_addr L0 p0) by lia. replace (n0 - 16 + 16) with n0 by lia.
      exact (cno_ub_blocks L0 A0 p0 n0 Hp0).
    + exact (proj1 RD).
Qed.

Lemma cno_tree_rpost : forall L A regs m md Kc Ec gc L' A' regs' m' md' Lam1 Lam2 pk ct fl p t D,
  rpost B API Kc L A regs m md Ec gc L' A' regs' m' md' ->
  ledger B L A m Lam1 pk ct fl -> pj_node (ms_segs B) m (lin Lam1) p t D ->
  (forall a k, In (a, k) D -> In (a, k) Lam2) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= p -> p + 56 <= 2 ^ 64 ->
  (forall i, 0 <= i < 56 -> ~ scratch_k B Kc regs (p + i) /\ ~ Ec (p + i)) ->
  (forall a k, In (a, k) D -> ~ gc (a - 16) (k + 16) /\ forall i, 0 <= i < k -> ~ Ec (a + i)) ->
  pj_node (ms_segs B) m' (lin Lam2) p t D.
Proof.
  intros L A regs m md Kc Ec gc L' A' regs' m' md' Lam1 Lam2 pk ct fl p t D RP HL HN HSUB Hp1 Hp2 HPO HDO.
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & SURV & _ & _ & _ & HI & _ & BK & _).
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
  apply (pj_node_frame _ t m (lin Lam1) m' (lin Lam2) p D HN); [exact HSUB|].
  intros x Hx. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
  rewrite <- (Z_to_bv_bv_unsigned x). set (z := bv_unsigned x) in *.
  destruct Hx as [Hz | ((a, k) & Hin & Hz)].
  - assert (Hni : ~ in_img B z) by (intros Hi; pose proof (cno_img_low B HS z Hi); lia).
    destruct (HPO (z - p) ltac:(lia)) as [H1 H2]. replace (p + (z - p)) with z in H1, H2 by lia.
    destruct (HI z ltac:(lia) H1 H2) as [E _].
    rewrite <- (cno_mbyte_raw B HS m' z Rx Hni), <- (cno_mbyte_raw B HS m z Rx Hni). exact E.
  - unfold pj_holds in Hz. cbn [fst snd] in Hz.
    pose proof (pj_node_blocks _ t m (lin Lam1) p D HN a k Hin) as HinL. unfold lin in HinL.
    pose proof HL as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
    destruct (FA (a, k) HinL) as (Hk & HinB & _ & HNI). cbn [fst snd] in *.
    destruct (cno_in_blocks L A _ _ HinB) as (q & Hq & Eq).
    destruct (HDO a k Hin) as [Hg HE].
    assert (Hq' : In (q, k + 16) (user_blocks A')) by (apply (SURV q (k + 16) Hq); rewrite Eq; exact Hg).
    assert (Hni : ~ in_img B z) by (replace z with (a - 16 + (z - (a - 16))) by lia; apply HNI; lia).
    pose proof (BK q (k + 16) (z - (a - 16)) Hq Hq' ltac:(lia)) as E.
    rewrite Eq in E. replace (a - 16 + (z - (a - 16))) with z in E by lia.
    specialize (E ltac:(replace z with (a + (z - a)) by lia; apply HE; lia)).
    rewrite <- (cno_mbyte_raw B HS m' z Rx Hni), <- (cno_mbyte_raw B HS m z Rx Hni). exact E.
Qed.

Lemma cno_hi_rpost : forall L A regs m md Kc Ec gc L' A' regs' m' md' a bs,
  rpost B API Kc L A regs m md Ec gc L' A' regs' m' md' -> bytes_at rsegs m a bs ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ scratch_k B Kc regs (a + i) /\ ~ Ec (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros L A regs m md Kc Ec gc L' A' regs' m' md' a bs RP HB Ha HO.
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HI & _).
  pose proof (bytes_at_bound _ _ _ _ HB) as Hb.
  apply (cno_bytes_frame B HS m m' a bs HB). intros i Hi. destruct (HO i Hi) as [H1 H2].
  exact (proj1 (HI (a + i) ltac:(lia) H1 H2)).
Qed.

Lemma cno_blk_rpost : forall L A regs m md Kc Ec gc L' A' regs' m' md' q k bs,
  rpost B API Kc L A regs m md Ec gc L' A' regs' m' md' -> bytes_at rsegs m (ptr_addr L q) bs ->
  In (q, k) (user_blocks A) -> ~ gc (ptr_addr L q) k -> Z.of_nat (length bs) <= k ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ Ec (ptr_addr L q + i)) ->
  In (q, k) (user_blocks A') /\ ptr_addr L' q = ptr_addr L q /\ bytes_at rsegs m' (ptr_addr L q) bs.
Proof.
  intros L A regs m md Kc Ec gc L' A' regs' m' md' q k bs RP HB Hq Hg Hl HO.
  destruct RP as (_ & _ & _ & _ & _ & _ & _ & SURV & PTR & _ & _ & _ & _ & BK & _).
  assert (Hq' : In (q, k) (user_blocks A')) by exact (SURV q k Hq Hg).
  split; [exact Hq'|]. split; [exact (PTR q k Hq Hq')|].
  apply (cno_bytes_frame B HS m m' _ bs HB). intros i Hi. exact (BK q k i Hq Hq' ltac:(lia) (HO i Hi)).
Qed.

Lemma cno_hi_cp : forall L A regs m md Kc Ec L' A' regs' m' md' a bs,
  call_post_k B MR Kc L A regs m md Ec L' A' regs' m' md' -> MR L A m md -> bytes_at rsegs m a bs ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ scratch_k B Kc regs (a + i) /\ ~ Ec (a + i)) ->
  bytes_at rsegs m' a bs.
Proof.
  intros L A regs m md Kc Ec L' A' regs' m' md' a bs CP HM HB Ha HO.
  destruct CP as (HM' & _ & _ & _ & _ & _ & _ & HFR & _).
  pose proof (bytes_at_bound _ _ _ _ HB) as Hb.
  apply (cno_bytes_frame B HS m m' a bs HB). intros i Hi. destruct (HO i Hi) as [H1 H2].
  assert (Hr : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= a + i < 2 ^ 64) by lia.
  refine (proj1 (HFR (a + i) (or_introl Hr) _ _ H1 H2)).
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM Ho). lia.
  - intros Ho. pose proof (mr_owned_low _ _ (aa_laws API) _ _ _ _ _ HM' Ho). lia.
Qed.

End P.

(* The nine words the prologue saves at sp + 0xa8 .. sp + 0xe8 (s7, s6, s5, s4, s3, s2, s1, s0, ra). *)
Definition cno_saved (regs0 : bvmap 5 word) : list byte :=
  le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 23) ++ le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 22) ++
  le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 21) ++ le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 20) ++
  le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 19) ++ le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 18) ++
  le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 9) ++ le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 8) ++
  le8 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 1).

Definition cno_Q {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil} (B : malloc_syms) (API : AllocAPI B) (F : ResForm) (L0 : layout) (A0 : astate)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (Lam : list (Z * Z)) (peak cnt : Z)
    (b : rf_R F) (data : Z) (x : list byte) (c' : config) : Prop :=
  exists (fx' : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L' A' regs' mem' md' peak' E1 E2 E3,
    c' = mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx' regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 1) mem' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md' /\
    frm_zero (@fp_csr fx') /\
    rpost B API CNO_K L0 A0 regs0 mem0 md0 cno_writes (fun _ _ => False) L' A' regs' mem' md' /\
    rd_cells B mem' /\ st_init_done A' = true /\
    ledger B L' A' mem' Lam peak' (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))) (2 ^ 64 - 1) /\
    peak <= peak' /\
    Mem.bytes_at (ms_segs B) mem' data x /\
    Mem.bytes_at (ms_segs B) mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
    cno_dl (cno_tr x) E1 /\ cno_dl (cno_tr x) E2 /\ cno_dl (cno_tr x) E3 /\
    rf_ok F A' (cno_free3 F (cno_mid F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x) E1 E2 E3) (Z.of_nat (length x))) /\
    OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 0 /\
    Mem.bytes_at (ms_segs B) mem' G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) /\
    Mem.bytes_at (ms_segs B) mem' GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
