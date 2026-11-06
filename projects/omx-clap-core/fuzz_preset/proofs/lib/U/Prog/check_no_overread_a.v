From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c same_c pj_parse_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import padded_c padded.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* Phase A of check_no_overread (#102 ubsan, entry 0x13868, frame 240): from the entry through the three calls of
   padded (0x1448c; fill 0x31, 0x32, 0; copies to s0, s1, s2), the zeroing of the trees at sp + 0x70, sp + 0x38, sp,
   and the first out_of_memory() test (g_own_ran_out and g_ran_out both 0: cno_segM) to the first parse_noting call
   (0x13a38, ra 0x1392c), where cno_KB takes over.  padded's contract comes from padded_holds; g_own_ran_out and
   g_ran_out keep the 0 of the entry along the frame invariant (cno_cj_own, cno_cj_gro). *)

Ltac cnoA_ret := unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

Lemma cnoA_pairwise_mid : forall {T : Type} (R : T -> T -> Prop) b1 z b2, pairwise R (b1 ++ z :: b2) ->
  forall y, In y (b1 ++ b2) -> R z y \/ R y z.
Proof.
  intros T R b1. induction b1 as [|w b1 IH]; intros z b2 H y Hy; cbn in *.
  - destruct H as [H _]. left. apply H. exact Hy.
  - destruct H as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_or_app. right. left. reflexivity.
    + exact (IH z b2 H2 y Hy).
Qed.

Lemma cnoA_nout1 : forall lo hi z, ~ outside [(lo, hi)] z -> lo <= z < hi.
Proof.
  intros lo hi z H. cbn [outside] in H.
  destruct (Z_le_gt_dec lo z) as [H1|H1]; [destruct (Z_lt_ge_dec z hi) as [H2|H2]|].
  - split; assumption.
  - exfalso. apply H. split; [lia | exact I].
  - exfalso. apply H. split; [lia | exact I].
Qed.

Lemma cnoA_out1 : forall lo hi z, z < lo \/ hi <= z -> outside [(lo, hi)] z.
Proof. intros lo hi z H. cbn [outside]. split; [lia | exact I]. Qed.

Lemma cnoA_padk : PADDED_K = 8240.
Proof. reflexivity. Qed.

Section Ph.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x18390.
Hypothesis HFREE : ms_free B = 0x18250.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.
Hypothesis RD0 : rd_cells B mem0.
Hypothesis HTP : ms_tp B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).
Hypothesis LED0 : ledger B L0 A0 mem0 Lam peak cnt (2 ^ 64 - 1).
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis XLEN : Z.of_nat (length x) <= 0x300000.
Hypothesis XB : Mem.bytes_at (ms_segs B) mem0 data x.
Hypothesis XBLK : x <> [] -> exists a k, In (a, k) (blocks L0 A0) /\ a <= data /\ data + Z.of_nat (length x) <= a + k.
Hypothesis ROOM : cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x).
Hypothesis GRO0 : Mem.bytes_at (ms_segs B) mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis OWN0 : Mem.bytes_at (ms_segs B) mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).

Let J := cj B API L0 A0 regs0 mem0 md0.
Let Q := cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x.

Local Abbreviation nx := (Z.of_nat (length x)).

(* The registers phase A keeps from the entry: sp (lowered by 240), gp, tp, s8..s11. *)
Definition cnoA_R (regs : bvmap 5 word) : Prop :=
  spZ regs = spZ regs0 - 240 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 /\ OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 /\
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)).

Definition cnoA_kp (regs regs' : bvmap 5 word) : Prop :=
  forall r, r = 2 \/ r = 3 \/ r = 4 \/ 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r).

Ltac cnoA_mvE HG :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; rewrite HG;
  destruct Hr as [->|[->|[->|Hr]]]; [reflexivity .. |];
  assert (Hr' : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->| ->]]]; reflexivity.

Lemma cnoA_R_kp : forall regs regs', cnoA_R regs -> cnoA_kp regs regs' -> cnoA_R regs'.
Proof.
  intros regs regs' (Hs & H3 & H4 & H24) E.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (E 2); lia|].
  split; [rewrite <- H3; apply (E 3); lia|].
  split; [rewrite <- H4; apply (E 4); lia|].
  intros r Hr. rewrite <- (H24 r Hr). apply E. lia.
Qed.

Lemma cnoA_kp_rp : forall regs regs', regs_preserved regs regs' -> cnoA_kp regs regs'.
Proof. intros regs regs' RP r Hr. apply RP. unfold callee_saved. lia. Qed.

Lemma cnoA_saved_len : length (cno_saved regs0) = 72%nat.
Proof. unfold cno_saved. rewrite !length_app, !Mem.length_le8. reflexivity. Qed.

Lemma cnoA_herr : errno_addr B + 4 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling.
Proof.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  rewrite HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
Qed.

(* The text address the code passes on: data, or 0 for the empty text at 2^64 (the same register value). *)
Definition cnoA_dd : Z := if Z.ltb data (2 ^ 64) then data else 0.

Lemma cnoA_dd_facts : 0 <= cnoA_dd < 2 ^ 64 /\ Z_to_bv 64 cnoA_dd = Z_to_bv 64 data /\ (x <> [] -> cnoA_dd = data).
Proof.
  pose proof XB as (XB0 & XB1 & _).
  destruct (Z_lt_ge_dec data (2 ^ 64)) as [H|H].
  - assert (E : cnoA_dd = data) by (unfold cnoA_dd; rewrite (proj2 (Z.ltb_lt _ _) H); reflexivity).
    rewrite E. split; [lia|]. split; [reflexivity | intros _; reflexivity].
  - assert (E : cnoA_dd = 0) by (unfold cnoA_dd; rewrite (proj2 (Z.ltb_ge data (2 ^ 64)) ltac:(lia)); reflexivity).
    assert (Ed : data = 2 ^ 64) by lia.
    assert (E0 : length x = 0%nat) by lia.
    rewrite E. split; [lia|]. split.
    + rewrite Ed. apply bv_eq. vm_compute. reflexivity.
    + intros Hx. exfalso. apply Hx. apply length_zero_iff_nil. exact E0.
Qed.

Lemma cnoA_data : forall L A m md, J L A m md -> bytes_at rsegs m data x.
Proof.
  intros L A m md HJ. pose proof XB as XB'. rewrite HS in XB'.
  pose proof XB' as (XB0 & XB1 & _).
  assert (Hx : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  destruct Hx as [Hx|Hx].
  - rewrite Hx. apply bytes_at_nil. lia.
  - apply (cno_bytes_frame B HS mem0 m data x XB'). intros i Hi.
    destruct (XBLK Hx) as (a & k & Hin & Ha & Hk).
    replace (data + i) with (a + (data + i - a)) by lia.
    apply (cj_mem0 B API AX HG L0 A0 regs0 mem0 md0 PRE0 L A m md a k (data + i - a) HJ Hin). lia.
Qed.

Lemma cnoA_dd_bytes : forall L A m md, J L A m md -> bytes_at rsegs m cnoA_dd x.
Proof.
  intros L A m md HJ. pose proof cnoA_dd_facts as (Hr & _ & Heq).
  assert (Hx : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  destruct Hx as [Hx|Hx].
  - rewrite Hx. apply bytes_at_nil. lia.
  - rewrite (Heq Hx). exact (cnoA_data L A m md HJ).
Qed.

Lemma cnoA_auxv : forall L A m md, J L A m md -> st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs0 - 240) m.
Proof.
  intros L A m md HJ Hf.
  pose proof HJ as (HM & _ & _ & (_ & Hsec & _) & HI & HLB & _ & _ & _ & HHI & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _ & _ & _ & HAUX).
  assert (Hf0 : st_init_done A0 = false).
  { destruct (st_init_done A0) eqn:E; [rewrite (HI eq_refl) in Hf; discriminate | reflexivity]. }
  destruct (HAUX Hf0) as (av & ar & W1 & W2 & W3 & W4 & H5 & H6 & H7 & H8 & H9 & H10).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  pose proof cnoA_herr as HE.
  assert (HIx : forall a v, spZ regs0 <= a -> a + 8 <= 2 ^ 63 -> word_mem (ms_segs B) mem0 a v ->
            word_mem (ms_segs B) m a v).
  { intros a v H1 H2 Hw. apply (word_mem_frame (ms_segs B) mem0 m a v Hw). intros k Hk.
    refine (proj1 (HHI (a + k) _ _ _)); [lia | intros [Hs|Hs]; lia |].
    intros Hs. destruct (cno_statics_free B API HG _ Hs) as (_ & Hl & _). lia. }
  rewrite Hsec. exists av, ar.
  split; [intros k Hk; rewrite (HLB Hf (Z.of_nat k)) by lia; exact (W1 k Hk)|].
  split; [intros k Hk; apply HIx; [lia | lia | exact (W2 k Hk)]|].
  split; [apply HIx; [lia | lia | exact W3]|].
  split; [apply HIx; [lia | lia | exact W4]|].
  repeat split; lia.
Qed.

Lemma cnoA_aw_munch : forall m m' W live pk ct fl, alloc_words B m live pk ct fl -> munch W m m' ->
  (forall a, alloc_statics a -> outside W a) -> alloc_words B m' live pk ct fl.
Proof.
  intros m m' W live pk ct fl (W1 & W2 & W3 & W4) MU HO.
  assert (E : forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha. destruct (cno_statics_free B API HG a Ha) as (_ & Hr & _).
    apply (mbyte_munch _ W m m' a MU); [pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt; lia | exact (HO a Ha)]. }
  unfold alloc_words.
  split; [|split; [|split]]; (eapply word_mem_frame; [eassumption|]); intros k Hk; apply E; unfold alloc_statics; lia.
Qed.

Lemma cnoA_aw_cp : forall K L A regs m md E L' A' regs' m' md' live pk ct fl,
  aa_MR API L A m md -> call_post_k B MR K L A regs m md E L' A' regs' m' md' ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling + K <= spZ regs -> (forall a, alloc_statics a -> ~ E a) ->
  alloc_words B m live pk ct fl -> alloc_words B m' live pk ct fl.
Proof.
  intros K L A regs m md E L' A' regs' m' md' live pk ct fl HM CP HK HE (W1 & W2 & W3 & W4).
  assert (EQ : forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha.
    exact (kb_post_globals B API omx_G K L A regs m md E L' A' regs' m' md' a HG HM CP HK (cno_statics_img a Ha) (HE a Ha)). }
  unfold alloc_words.
  split; [|split; [|split]]; (eapply word_mem_frame; [eassumption|]); intros k Hk; apply EQ; unfold alloc_statics; lia.
Qed.

(* The nine saved words (sp + 168 .. sp + 240) survive a padded call: they are above its window. *)
Lemma cnoA_saved_cp : forall L A regs m md L' A' regs' m' md', aa_MR API L A m md ->
  call_post_k B MR PADDED_K L A regs m md (fun _ => False) L' A' regs' m' md' -> spZ regs = spZ regs0 - 240 ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) -> bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0).
Proof.
  intros L A regs m md L' A' regs' m' md' HM CP Hsp BY.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  apply (cno_hi_cp B API HS L A regs m md PADDED_K _ L' A' regs' m' md' _ _ CP HM BY); [lia|].
  rewrite cnoA_saved_len. intros i Hi. split; [|intros []].
  unfold scratch_k. rewrite cnoA_padk, HERR. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.strtod_c.STRTOD_ERRNO. lia.
Qed.

Lemma cnoA_blk_munch : forall m m' lo hi a, munch [(lo, hi)] m m' -> a + nx <= lo ->
  bytes_at rsegs m a x -> bytes_at rsegs m' a x.
Proof. intros m m' lo hi a MU D BX. apply (cno_bytes_munch1 m m' lo hi a x BX MU). lia. Qed.

Lemma cnoA_blk_cp : forall Kc L A regs m md Ec L' A' regs' m' md' p a,
  call_post_k B MR Kc L A regs m md Ec L' A' regs' m' md' ->
  In (p, nx + 16) (user_blocks A) -> In (p, nx + 16) (user_blocks A') -> ptr_addr L p = a ->
  bytes_at rsegs m a x -> bytes_at rsegs m' a x /\ ptr_addr L' p = a.
Proof.
  intros Kc L A regs m md Ec L' A' regs' m' md' p a CP Hp Hp' Ha BX.
  pose proof CP as (_ & _ & _ & _ & PTR & _ & _ & _ & BK & _).
  split; [|rewrite (PTR p _ Hp Hp'); exact Ha].
  apply (cno_bytes_frame B HS m m' a x BX). intros i Hi. rewrite <- Ha. apply (BK p (nx + 16) i Hp Hp'). lia.
Qed.

Lemma cnoA_newblk : forall L A L' A' m' md' q k, aa_MR API L' A' m' md' ->
  (exists b1 b2, blocks L' A' = b1 ++ (q, k) :: b2 /\ blocks L A = b1 ++ b2) ->
  In (q, k) (blocks L' A') /\ (forall a k', In (a, k') (blocks L A) -> q + k <= a \/ a + k' <= q).
Proof.
  intros L A L' A' m' md' q k HM (b1 & b2 & E1 & E0). split.
  - rewrite E1. apply in_or_app. right. left. reflexivity.
  - intros a k' Hin. rewrite E0 in Hin.
    pose proof (mr_blocks_disjoint _ _ (aa_laws API) L' A' m' md' HM) as PW. rewrite E1 in PW.
    destruct (cnoA_pairwise_mid _ b1 (q, k) b2 PW (a, k') Hin) as [H|H];
      unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YO0f.ranges_disjoint in H; cbn [fst snd] in H; lia.
Qed.

Lemma cnoA_notA0 : forall L A m md p a, J L A m md -> In (p, nx + 16) (user_blocks A) -> ptr_addr L p = a ->
  ~ In (a, nx + 16) (blocks L0 A0) -> forall q k, In (q, k) (user_blocks A0) -> q <> p.
Proof.
  intros L A m md p a HJ Hp Ha Hn q k Hq E. subst q.
  pose proof HJ as (_ & HWF & _ & _ & _ & _ & _ & HUB & _).
  destruct (HUB p k Hq) as (Hq1 & Hpa).
  pose proof (cno_nodup_fst _ p _ _ (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YO10.user_block_ptrs_NoDup A HWF) Hq1 Hp) as Ek. subst k.
  apply Hn. rewrite <- Ha, Hpa. apply cno_ub_blocks. exact Hq.
Qed.

Lemma cnoA_present_norm : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> present m a -> present (normalize rsegs m) a.
Proof. intros m a Ha Hn [v Hv]. exists v. unfold normalize. rewrite (cno_ro_false B HS a Ha Hn). exact Hv. Qed.

(* The entry run 0x13868 .. 0x1389c: prologue (nine words saved at sp + 168 .. sp + 240), s4 = n, s2 = data,
   a2 = 0x31, to padded with ra 0x138a0. *)
Lemma cnoA_seg0 : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) (P : config -> Prop),
  ro_agree (ms_segs B) mem0 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 10 = Z_to_bv 64 cnoA_dd -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 11 = Z_to_bv 64 nx ->
  (forall regs1 m1, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 1 = Z_to_bv 64 0x138a0 -> cnoA_R regs1 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 10 = Z_to_bv 64 cnoA_dd -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 11 = Z_to_bv 64 nx ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 12 = Z_to_bv 64 0x31 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 18 = Z_to_bv 64 cnoA_dd -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 20 = Z_to_bv 64 nx ->
     J L0 A0 m1 md0 -> munch [(spZ regs0 - 72, spZ regs0)] mem0 m1 ->
     bytes_at rsegs m1 (spZ regs0 - 72) (cno_saved regs0) ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs1 (Z_to_bv 64 0x1448c) m1 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md0) P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs0 (Z_to_bv 64 0x13868) mem0 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md0) P.
Proof.
  intros fx P RA0 R10 R11 K.
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & HSW0 & _).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  pose proof cnoA_dd_facts as (Hdd & _).
  destruct (kb_md B API L0 A0 mem0 md0 HM0) as (Hh0 & Hz0).
  assert (PS : forall i, 0 <= i < 72 -> present mem0 (spZ regs0 - 72 + i)).
  { intros i Hi. apply (cno_present_of_writable B HS mem0 (spZ regs0 - 72 + i)); [lia | | apply HSW0; lia].
    intros Hi'. pose proof (cno_img_low B HS _ Hi'). lia. }
  destruct (cno_rw_of_present mem0 (spZ regs0 - 72) 72 ltac:(lia) ltac:(lia) ltac:(lia) PS) as (j & RWJ).
  apply (kb_run B regs0 (Z_to_bv 64 0x13868) mem0 md0
    (fun R pc' m' => seg0_post (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 1) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 18) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 19) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 20)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 23) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 25)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 27) (@fp_regs fx) (@fp_csr fx) mem0 cnoA_dd nx
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh0 Hz0).
  - rewrite HS. unfold rmk. rewrite R10, R11.
    eapply evt_mono.
    + apply cno_seg0 with (m := mem0) (d := cnoA_dd) (n := nx) (j := j); [lia | lia | |].
      * change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2)) with (spZ regs0). lia.
      * change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2)) with (spZ regs0).
        assert (E72 : spZ regs0 + -72 = spZ regs0 - 72) by lia. rewrite E72. exact RWJ.
    + intros ms PO. pose proof PO as PO'. unfold seg0_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO].
  - intros R pc' m1 regs1 HQ HGr. cbv beta in HQ. unfold seg0_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & RW).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m1. clear E.
    change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 2)) with (spZ regs0) in MU, RW.
    assert (E72 : spZ regs0 + -72 = spZ regs0 - 72) by lia. rewrite E72 in MU, RW.
    rewrite <- HS in WM.
    assert (RA1 : ro_agree (ms_segs B) m'').
    { rewrite HS. apply (cno_ro_agree_munch B HS [(spZ regs0 - 72, spZ regs0)] mem0 m'');
        [rewrite <- HS; exact RA0 | exact MU |].
      intros a Ha Ho Hi. apply cnoA_nout1 in Ho. pose proof (cno_img_low B HS a Hi). lia. }
    assert (J1 : J L0 A0 m'' md0).
    { apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L0 A0 mem0 md0 m'' _
               (cj_init B API L0 A0 regs0 mem0 md0 PRE0 RA0) MU WM RA1).
      intros z Hz Ho. apply cnoA_nout1 in Ho. left. lia. }
    assert (BY : bytes_at rsegs m'' (spZ regs0 - 72) (cno_saved regs0)).
    { destruct RW as ((_ & Hb) & _). cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
      unfold cno_saved. exact Hb. }
    assert (G2 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs1 2 = Z_to_bv 64 (spZ regs0 - 240)) by (rewrite HGr; reflexivity).
    assert (R1 : cnoA_R regs1).
    { split; [unfold spZ at 1; rewrite G2; apply unsigned_lit; lia|].
      split; [rewrite HGr; reflexivity|]. split; [rewrite HGr; reflexivity|].
      intros r Hr. rewrite HGr.
      assert (Hr' : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
      destruct Hr' as [->|[->|[->| ->]]]; reflexivity. }
    apply (K regs1 m'').
    + rewrite HGr. reflexivity.
    + exact R1.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + exact J1.
    + exact MU.
    + exact BY.
Qed.

(* One call of padded (0x1448c) from the frame: text cnoA_dd of n bytes, the given fill.  The continuation gets
   malloc's post at padded's window PADDED_K, the new block q of n + 16 bytes, and the copy of x at q. *)
Lemma cnoA_call_padded : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md bnd fill (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK0s.ret_ok (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 cnoA_dd -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 nx ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 fill -> 0 <= fill < 256 ->
  (st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs) m) ->
  rf_ok F A bnd -> rf_room F bnd (nx + 16) ->
  (forall L' A' regs' m' md' q,
     J L' A' m' md' ->
     call_post_k B MR PADDED_K L A regs m md (fun _ => False) L' A' regs' m' md' ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = Z_to_bv 64 q -> fresh_block B q (nx + 16) ->
     (exists b1 b2, blocks L' A' = b1 ++ (q, nx + 16) :: b2 /\ blocks L A = b1 ++ b2) ->
     (forall p n, In (p, n) (user_blocks A) -> In (p, n) (user_blocks A')) ->
     st_init_done A' = true ->
     rf_ok F A' (rf_malloc F bnd (nx + 16)) ->
     bytes_at rsegs m' q x ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md') P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x1448c) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md bnd fill P Jc Hsp Htp Hra R10 R11 R12 Hfill HAUX HRES HROOM K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & HUB & _ & _ & _ & _ & _ & HRA).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc.
  pose proof cnoA_dd_facts as (Hdd & _ & Heq).
  eapply SR_bind; [apply (padded_holds B API F HS cnoA_herr HMAL MALLOC MEMCPY MEMSET fx L A regs m md bnd cnoA_dd nx fill x) |].
  - apply (cno_call_pre B API L0 A0 regs0 mem0 md0 PRE0 L A regs m md PADDED_K Jc Hsp);
      [rewrite cnoA_padk; lia | rewrite cnoA_padk; lia | exact Htp | exact Hra | exact HAUX].
  - exact HRA.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact Hfill.
  - reflexivity.
  - exact XLEN.
  - rewrite HS. exact (cnoA_dd_bytes L A m md Jc).
  - intros Hx. destruct (XBLK Hx) as (a & k & Hin & Ha & Hk). exists a, k.
    split; [exact (cj_blocks0 B API L0 A0 regs0 mem0 md0 L A m md a k Jc Hin)|].
    rewrite (Heq Hx). split; [exact Ha | exact Hk].
  - exact HRES.
  - exact HROOM.
  - intros c' ((L' & A' & regs' & m' & md' & q & -> & CP & R10' & Hq & Hq16 & FR & BL & BK & RA' & GK & SURV & INIT & LEN & RES') & (ms' & md'' & E & BQ)).
    injection E as Ems Emd. subst ms' md''.
    cbn [OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst ms_mem ms_regs] in BQ. rewrite R10' in BQ.
    pose proof FR as (Fq1 & Fq2 & _).
    rewrite unsigned_lit in BQ by lia.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BQ. destruct BQ as [BQ _].
    apply (K L' A' regs' m' md' q); try assumption.
    + apply (cj_callpost B API L0 A0 regs0 mem0 md0 PRE0 L A m md PADDED_K regs (fun _ => False) L' A' regs' m' md' Jc CP).
      * pose proof PRE0 as (_ & _ & _ & _ & _ & HK & _). rewrite cnoA_padk. lia.
      * lia.
      * intros a [].
      * intros p n Hp. exact (SURV p n (proj1 (HUB p n Hp))).
      * exact INIT.
      * exact LEN.
      * exact RA'.
    + rewrite HS in BQ. exact BQ.
Qed.

(* 0x138c8 .. 0x13928 (cno_segM, on the normalized memory): s2 = the third copy, the three trees zeroed, s7 =
   CNO_S7, s3 = 1, the first out_of_memory() test (both bytes 0), a0 = s0, a1 = s4, a2 = sp + 112, to parse_noting
   with ra 0x1392c.  Only the frame below the saved words is written. *)
Lemma cnoA_segM : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 ->
  (forall regs' m', OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 1 = Z_to_bv 64 0x1392c ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 8 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 9 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 18 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 20 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 19 = Z_to_bv 64 1 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 23 = Z_to_bv 64 CNO_S7 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 10 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 11 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 ->
     OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' 12 = Z_to_bv 64 (spZ regs + 112) ->
     cnoA_kp regs regs' ->
     J L A m' md -> munch [(spZ regs, spZ regs + 168)] m m' ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' (Z_to_bv 64 0x13a38) m' (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x138c8) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md P Jc Hsp K.
  pose proof Jc as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & RA).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  destruct (kb_md B API L A m md HM) as (Hh & Hl).
  assert (PN : forall i, 0 <= i < 168 -> present (normalize rsegs m) (spZ regs + i)).
  { intros i Hi.
    assert (Hni : ~ in_img B (spZ regs + i)) by (intros Hi'; pose proof (cno_img_low B HS _ Hi'); lia).
    apply cnoA_present_norm; [lia | exact Hni |].
    apply (cno_present_of_writable B HS m (spZ regs + i) ltac:(lia) Hni). apply HSC. left. lia. }
  assert (PN56 : forall i, 0 <= i < 56 -> present (normalize rsegs m) (spZ regs + 56 + i)).
  { intros i Hi. replace (spZ regs + 56 + i) with (spZ regs + (56 + i)) by lia. apply PN. lia. }
  assert (PN112 : forall i, 0 <= i < 56 -> present (normalize rsegs m) (spZ regs + 112 + i)).
  { intros i Hi. replace (spZ regs + 112 + i) with (spZ regs + (112 + i)) by lia. apply PN. lia. }
  assert (PN0 : forall i, 0 <= i < 56 -> present (normalize rsegs m) (spZ regs + i)).
  { intros i Hi. apply PN. lia. }
  destruct (cno_rw_of_present (normalize rsegs m) (spZ regs) 56 ltac:(lia) ltac:(lia) ltac:(lia) PN0) as (j0 & RW0).
  destruct (cno_rw_of_present (normalize rsegs m) (spZ regs + 56) 56 ltac:(lia) ltac:(lia) ltac:(lia) PN56)
    as (j1 & RW1).
  destruct (cno_rw_of_present (normalize rsegs m) (spZ regs + 112) 56 ltac:(lia) ltac:(lia) ltac:(lia) PN112)
    as (j2 & RW2).
  pose proof (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md Jc OWN0) as OW.
  pose proof (cno_cj_gro B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md Jc GRO0) as GR.
  rewrite HS in OW, GR, RA.
  pose proof (bytes_at_normalize rsegs m _ _ RA OW) as OWn.
  pose proof (bytes_at_normalize rsegs m _ _ RA GR) as GRn.
  destruct (cno_own_free B API HG GL_OWN_RAN_OUT ltac:(lia)) as (_ & OL & _).
  destruct (cno_gro_free B API HG G_RAN_OUT ltac:(lia)) as (_ & GL & _).
  rewrite <- HS in RA.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x138c8) m md
    (fun R pc' m' => segM_post (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 21) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 22) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 24) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 25)
       (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 26) (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 27) (@fp_regs fx) (@fp_csr fx) (normalize rsegs m)
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk.
    eapply evt_mono.
    + apply (cno_segM MEMSET) with (j0 := j0) (j1 := j1) (j2 := j2).
      * change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). lia.
      * change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). lia.
      * change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs). lia.
      * exact RW0.
      * exact RW1.
      * exact RW2.
      * exact OWn.
      * exact GRn.
      * apply mem_inv_normalize.
    + intros ms PO. pose proof PO as PO'. unfold segM_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO].
  - intros R pc' m0 mem' regs' HQ HREL HRS HGr.
    cbv beta in HQ. unfold segM_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & _).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m0. clear E.
    change (bv_unsigned (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 2)) with (spZ regs) in MU.
    rewrite <- HS in MU, WM.
    destruct (cno_back B m mem' m'' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply (K regs' mem').
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + unfold cnoA_kp. cnoA_mvE HGr.
    + apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L A m md mem' _ Jc MU' WM' RA').
      intros z Hz Ho. apply cnoA_nout1 in Ho. left. lia.
    + exact MU'.
Qed.

Lemma cnoA_holds : cno_KB B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x ->
  forall fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState, frm_zero (@fp_csr fx) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.MemNorm.ro_agree (ms_segs B) mem0 -> rf_ok F A0 b ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 10 = Z_to_bv 64 data -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs0 (Z_to_bv 64 0x13868) mem0 (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md0) Q.
Proof.
  intros KB fx FZ RA0 RF0 R10 R11.
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt as Hc. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as (Hcv & _).
  pose proof LED0 as (AW0 & HPK0 & HCT0 & _).
  pose proof cnoA_dd_facts as (Hdd & Ebv & _).
  pose proof ROOM as (RM1 & RM2 & RM3 & _).
  pose proof cnoA_padk as EPK.
  rewrite <- Ebv in R10.
  (* entry run *)
  apply (cnoA_seg0 fx Q RA0 R10 R11).
  intros regs1 m1 G1_1 R1 G1_10 G1_11 G1_12 G1_18 G1_20 J1 MU1 BY1.
  pose proof R1 as (Hsp1 & _ & G1_4 & _).
  pose proof J1 as (HMa & _).
  assert (AW1 : alloc_words B m1 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply (cnoA_aw_munch mem0 m1 _ _ _ _ _ AW0 MU1). intros a Ha. apply cnoA_out1.
    destruct (cno_statics_free B API HG a Ha) as (_ & Hl & _). lia. }
  (* first copy: padded(data, n, 0x31) *)
  apply (cnoA_call_padded fx L0 A0 regs1 m1 md0 b 0x31 Q J1 Hsp1 G1_4);
    [rewrite G1_1; cnoA_ret | exact G1_10 | exact G1_11 | exact G1_12 | lia
    | intros Hf; rewrite Hsp1; exact (cnoA_auxv L0 A0 m1 md0 J1 Hf) | exact RF0 | exact RM1 |].
  intros L1 A1 regs2 m2 md1 qa1 J2 CP2 R10a FR1 BL1 SURV1 INIT1 RF1 BX1.
  rewrite G1_1.
  pose proof CP2 as (HM1 & _ & _ & _ & _ & RP2 & _).
  pose proof FR1 as (Hq1a & Hq1b & _).
  destruct (cnoA_newblk L0 A0 L1 A1 m2 md1 qa1 (nx + 16) HM1 BL1) as (QIN1 & SEP1).
  assert (QNEW1 : ~ In (qa1, nx + 16) (blocks L0 A0)) by (intros H; destruct (SEP1 _ _ H); lia).
  pose proof (cnoA_R_kp regs1 regs2 R1 (cnoA_kp_rp regs1 regs2 RP2)) as R2.
  assert (G2_18 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18 = Z_to_bv 64 cnoA_dd)
    by (rewrite <- G1_18; apply (RP2 18); unfold callee_saved; lia).
  assert (G2_20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20 = Z_to_bv 64 nx)
    by (rewrite <- G1_20; apply (RP2 20); unfold callee_saved; lia).
  pose proof (cnoA_aw_cp PADDED_K L0 A0 regs1 m1 md0 _ L1 A1 regs2 m2 md1 _ _ _ _ HMa CP2
                ltac:(rewrite EPK; lia) (fun a _ H => H) AW1) as AW2.
  pose proof (cnoA_saved_cp L0 A0 regs1 m1 md0 L1 A1 regs2 m2 md1 HMa CP2 Hsp1 BY1) as BY2.
  destruct (cno_in_blocks L1 A1 qa1 _ QIN1) as (p1 & Hp1 & Pp1).
  (* 0x138a0: s0 = the first copy; a0 = s2, a1 = s4, a2 = 0x32; padded, ra 0x138b4 *)
  pose proof J2 as (HM1' & _). destruct (kb_md B API L1 A1 m2 md1 HM1') as (Hh2 & Hz2).
  eapply (cno_jump B HS fx regs2 _ m2 md1 _ _ Q Hh2 Hz2).
  { unfold rmk. apply cno_segP1. }
  intros regs3 HG3.
  assert (R3 : cnoA_R regs3) by (apply (cnoA_R_kp regs2 regs3 R2); unfold cnoA_kp; cnoA_mvE HG3).
  pose proof R3 as (Hsp3 & _ & G3_4 & _).
  assert (G3_1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 1 = Z_to_bv 64 0x138b4) by (rewrite HG3; reflexivity).
  assert (G3_8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 8 = Z_to_bv 64 qa1)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 10); [rewrite HG3; reflexivity | exact R10a]).
  assert (G3_10 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 10 = Z_to_bv 64 cnoA_dd)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18); [rewrite HG3; reflexivity | exact G2_18]).
  assert (G3_11 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 11 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20); [rewrite HG3; reflexivity | exact G2_20]).
  assert (G3_12 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 12 = Z_to_bv 64 0x32) by (rewrite HG3; reflexivity).
  assert (G3_18 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 18 = Z_to_bv 64 cnoA_dd)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 18); [rewrite HG3; reflexivity | exact G2_18]).
  assert (G3_20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs3 20 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs2 20); [rewrite HG3; reflexivity | exact G2_20]).
  (* second copy: padded(data, n, 0x32) *)
  apply (cnoA_call_padded fx L1 A1 regs3 m2 md1 (rf_malloc F b (nx + 16)) 0x32 Q J2 Hsp3 G3_4);
    [rewrite G3_1; cnoA_ret | exact G3_10 | exact G3_11 | exact G3_12 | lia | intros Hf; congruence | exact RF1
    | exact RM2 |].
  intros L2 A2 regs4 m4 md2 qa2 J4 CP4 R10b FR2 BL2 SURV2 INIT2 RF2 BX2.
  rewrite G3_1.
  pose proof CP4 as (HM2 & _ & _ & _ & _ & RP4 & _).
  pose proof FR2 as (Hq2a & Hq2b & _).
  destruct (cnoA_newblk L1 A1 L2 A2 m4 md2 qa2 (nx + 16) HM2 BL2) as (QIN2 & SEP2).
  assert (QNEW2 : ~ In (qa2, nx + 16) (blocks L0 A0)).
  { intros H. destruct (SEP2 _ _ (cj_blocks0 B API L0 A0 regs0 mem0 md0 L1 A1 m2 md1 _ _ J2 H)); lia. }
  pose proof (cnoA_R_kp regs3 regs4 R3 (cnoA_kp_rp regs3 regs4 RP4)) as R4.
  assert (G4_8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 8 = Z_to_bv 64 qa1) by (rewrite <- G3_8; apply (RP4 8); unfold callee_saved; lia).
  assert (G4_18 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 18 = Z_to_bv 64 cnoA_dd)
    by (rewrite <- G3_18; apply (RP4 18); unfold callee_saved; lia).
  assert (G4_20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 20 = Z_to_bv 64 nx)
    by (rewrite <- G3_20; apply (RP4 20); unfold callee_saved; lia).
  pose proof J2 as (HM1'' & _).
  pose proof (cnoA_aw_cp PADDED_K L1 A1 regs3 m2 md1 _ L2 A2 regs4 m4 md2 _ _ _ _ HM1'' CP4
                ltac:(rewrite EPK; lia) (fun a _ H => H) AW2) as AW4.
  pose proof (cnoA_saved_cp L1 A1 regs3 m2 md1 L2 A2 regs4 m4 md2 HM1'' CP4 Hsp3 BY2) as BY4.
  pose proof (SURV2 p1 _ Hp1) as Hp1b.
  destruct (cnoA_blk_cp PADDED_K L1 A1 regs3 m2 md1 _ L2 A2 regs4 m4 md2 p1 qa1 CP4 Hp1 Hp1b Pp1 BX1)
    as (BX1b & Pp1b).
  destruct (cno_in_blocks L2 A2 qa2 _ QIN2) as (p2 & Hp2 & Pp2).
  pose proof (cno_ub_blocks L2 A2 p1 _ Hp1b) as QIN1b. rewrite Pp1b in QIN1b.
  (* 0x138b4: s1 = the second copy; a0 = s2, a1 = s4, a2 = 0; padded, ra 0x138c8 *)
  pose proof J4 as (HM2' & _). destruct (kb_md B API L2 A2 m4 md2 HM2') as (Hh4 & Hz4).
  eapply (cno_jump B HS fx regs4 _ m4 md2 _ _ Q Hh4 Hz4).
  { unfold rmk. apply cno_segP2. }
  intros regs5 HG5.
  assert (R5 : cnoA_R regs5) by (apply (cnoA_R_kp regs4 regs5 R4); unfold cnoA_kp; cnoA_mvE HG5).
  pose proof R5 as (Hsp5 & _ & G5_4 & _).
  assert (G5_1 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 1 = Z_to_bv 64 0x138c8) by (rewrite HG5; reflexivity).
  assert (G5_8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 8 = Z_to_bv 64 qa1)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 8); [rewrite HG5; reflexivity | exact G4_8]).
  assert (G5_9 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 9 = Z_to_bv 64 qa2)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 10); [rewrite HG5; reflexivity | exact R10b]).
  assert (G5_10 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 10 = Z_to_bv 64 cnoA_dd)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 18); [rewrite HG5; reflexivity | exact G4_18]).
  assert (G5_11 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 11 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 20); [rewrite HG5; reflexivity | exact G4_20]).
  assert (G5_12 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 12 = Z_to_bv 64 0) by (rewrite HG5; reflexivity).
  assert (G5_20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs5 20 = Z_to_bv 64 nx)
    by (transitivity (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs4 20); [rewrite HG5; reflexivity | exact G4_20]).
  (* third copy: padded(data, n, 0) *)
  apply (cnoA_call_padded fx L2 A2 regs5 m4 md2 (rf_malloc F (rf_malloc F b (nx + 16)) (nx + 16)) 0 Q J4 Hsp5 G5_4);
    [rewrite G5_1; cnoA_ret | exact G5_10 | exact G5_11 | exact G5_12 | lia | intros Hf; congruence | exact RF2
    | exact RM3 |].
  intros L3 A3 regs6 m6 md3 qa3 J6 CP6 R10c FR3 BL3 SURV3 INIT3 RF3 BX3.
  rewrite G5_1.
  pose proof CP6 as (HM3 & _ & _ & _ & _ & RP6 & _).
  pose proof FR3 as (Hq3a & Hq3b & _).
  destruct (cnoA_newblk L2 A2 L3 A3 m6 md3 qa3 (nx + 16) HM3 BL3) as (QIN3 & SEP3).
  assert (QNEW3 : ~ In (qa3, nx + 16) (blocks L0 A0)).
  { intros H. destruct (SEP3 _ _ (cj_blocks0 B API L0 A0 regs0 mem0 md0 L2 A2 m4 md2 _ _ J4 H)); lia. }
  pose proof (cnoA_R_kp regs5 regs6 R5 (cnoA_kp_rp regs5 regs6 RP6)) as R6. pose proof R6 as (Hsp6 & _).
  assert (G6_8 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs6 8 = Z_to_bv 64 qa1)
    by (rewrite <- G5_8; apply (RP6 8); unfold callee_saved; lia).
  assert (G6_9 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs6 9 = Z_to_bv 64 qa2) by (rewrite <- G5_9; apply (RP6 9); unfold callee_saved; lia).
  assert (G6_20 : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs6 20 = Z_to_bv 64 nx)
    by (rewrite <- G5_20; apply (RP6 20); unfold callee_saved; lia).
  pose proof J4 as (HM2'' & _).
  pose proof (cnoA_aw_cp PADDED_K L2 A2 regs5 m4 md2 _ L3 A3 regs6 m6 md3 _ _ _ _ HM2'' CP6
                ltac:(rewrite EPK; lia) (fun a _ H => H) AW4) as AW6.
  pose proof (cnoA_saved_cp L2 A2 regs5 m4 md2 L3 A3 regs6 m6 md3 HM2'' CP6 Hsp5 BY4) as BY6.
  pose proof (SURV3 p1 _ Hp1b) as Hp1c.
  destruct (cnoA_blk_cp PADDED_K L2 A2 regs5 m4 md2 _ L3 A3 regs6 m6 md3 p1 qa1 CP6 Hp1b Hp1c Pp1b BX1b)
    as (BX1c & Pp1c).
  pose proof (SURV3 p2 _ Hp2) as Hp2b.
  destruct (cnoA_blk_cp PADDED_K L2 A2 regs5 m4 md2 _ L3 A3 regs6 m6 md3 p2 qa2 CP6 Hp2 Hp2b Pp2 BX2)
    as (BX2b & Pp2b).
  destruct (cno_in_blocks L3 A3 qa3 _ QIN3) as (p3 & Hp3 & Pp3).
  (* 0x138c8: s2 = the third copy, the trees zeroed, the first out_of_memory() test, to parse_noting *)
  apply (cnoA_segM fx L3 A3 regs6 m6 md3 Q J6 Hsp6).
  intros regs7 m7 G7_1 G7_8 G7_9 G7_18 G7_20 G7_19 G7_23 G7_10 G7_11 G7_12 KP7 J7 MU7.
  pose proof (cnoA_R_kp regs6 regs7 R6 KP7) as (Hsp7 & G7_3 & G7_4 & G7_24).
  pose proof (cnoA_aw_munch m6 m7 _ _ _ _ _ AW6 MU7) as AW7.
  assert (AW7' : alloc_words B m7 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply AW7. intros a Ha. apply cnoA_out1. destruct (cno_statics_free B API HG a Ha) as (_ & Hl & _). lia. }
  assert (BY7 : bytes_at rsegs m7 (spZ regs0 - 72) (cno_saved regs0)).
  { apply (cno_bytes_munch1 m6 m7 _ _ _ _ BY6 MU7). right. lia. }
  pose proof (cnoA_blk_munch m6 m7 _ _ qa1 MU7 ltac:(lia) BX1c) as BX1d.
  pose proof (cnoA_blk_munch m6 m7 _ _ qa2 MU7 ltac:(lia) BX2b) as BX2c.
  pose proof (cnoA_blk_munch m6 m7 _ _ qa3 MU7 ltac:(lia) BX3) as BX3b.
  (* the join state at the first parse *)
  apply (KB fx L3 A3 regs7 m7 md3 p1 p2 p3 qa1 qa2 qa3 J7 Hsp7 G7_1 G7_3 G7_4).
  - rewrite G7_8. exact G6_8.
  - rewrite G7_9. exact G6_9.
  - rewrite G7_18. exact R10c.
  - rewrite G7_20. exact G6_20.
  - exact G7_19.
  - exact G7_23.
  - exact G7_24.
  - rewrite G7_10. exact G6_8.
  - rewrite G7_11. exact G6_20.
  - rewrite G7_12, Hsp6. reflexivity.
  - exact BY7.
  - exact FZ.
  - exact (cno_ledger_cj B API AX HG L0 A0 regs0 mem0 md0 PRE0 L3 A3 m7 md3 Lam peak cnt (2 ^ 64 - 1) peak cnt
             (2 ^ 64 - 1) LED0 J7 AW7' HPK0 HCT0 ltac:(lia)).
  - exact RF3.
  - exact Hp1c.
  - exact Pp1c.
  - rewrite HS. exact BX1d.
  - exact Hp2b.
  - exact Pp2b.
  - rewrite HS. exact BX2c.
  - exact Hp3.
  - exact Pp3.
  - rewrite HS. exact BX3b.
  - exact QNEW1.
  - exact QNEW2.
  - exact QNEW3.
  - intros q k Hq. split; [|split].
    + exact (cnoA_notA0 L3 A3 m7 md3 p1 qa1 J7 Hp1c Pp1c QNEW1 q k Hq).
    + exact (cnoA_notA0 L3 A3 m7 md3 p2 qa2 J7 Hp2b Pp2b QNEW2 q k Hq).
    + exact (cnoA_notA0 L3 A3 m7 md3 p3 qa3 J7 Hp3 Pp3 QNEW3 q k Hq).
  - intros E. assert (Eq : qa1 = qa2) by congruence. destruct (SEP2 _ _ QIN1); lia.
  - intros E. assert (Eq : qa1 = qa3) by congruence. destruct (SEP3 _ _ QIN1b); lia.
  - intros E. assert (Eq : qa2 = qa3) by congruence. destruct (SEP3 _ _ QIN2); lia.
  - exact INIT3.
Qed.

End Ph.
