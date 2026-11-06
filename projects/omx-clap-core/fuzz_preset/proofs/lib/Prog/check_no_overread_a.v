From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO10.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Contract Img0 KindBGlue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require RegisterBridge Regs6ss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import Ledger PjStruct ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import memcpy_c memset_c same_c pj_parse_c pj_free_c PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_glue check_no_overread_calls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import check_no_overread_spec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import fuzz_alloc_ran_out_c.
Module Mem := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib.Mem.
Module YO10 := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YO10.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* Phase A of check_no_overread (#102 plain, entry 0x13778): default_malloc(n + 16) three times (0x178d8), each followed
   by fuzz_preset.c's inlined padded copy (memcpy of x if n > 0, then a 16-byte fill of 0x31, 0x32 or 0; malloc's
   contract gives a non-NULL block, so no NULL arm runs), the zeroing of the trees at sp + 0x70, sp + 0x38, sp and the
   first out_of_memory() test (g_own_ran_out = 0, then fuzz_alloc_ran_out = 0), to the first parse_noting call
   (0x13a04, ra 0x138b8; a0 = one, a1 = n, a2 = sp + 0x70, s7 = 0x347b8), where cno_KB takes over. *)

Ltac cnoA_ret := unfold YK0s.ret_ok; apply bv_eq; vm_compute; reflexivity.

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

Section Ph.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Let MR := aa_MR API.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis HMAL : ms_malloc B = 0x178d8.
Hypothesis HFREE : ms_free B = 0x17798.
Hypothesis AX : AllocExtra B MR.
Hypothesis CTX : ctx_owned B API.
Hypothesis HG : globals_free B API omx_G.
Hypothesis MALLOC : forall fx : YK11.FPState, @malloc_contract_r fx rc B API F.
Hypothesis FREE : forall fx : YK11.FPState, @free_contract_r fx rc B API F.
Hypothesis MEMCPY : memcpy_contract.
Hypothesis MEMSET : memset_contract.
Hypothesis PARSE : forall fx : YK11.FPState, @parse_noting_contract fx rc B API F.
Hypothesis PJFREE : forall fx : YK11.FPState, @pj_free_contract fx rc B API F.
Hypothesis SAME : same_contract.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Hypothesis PRE0 : call_pre_k B MR CNO_K L0 A0 regs0 mem0 md0.
Hypothesis RD0 : rd_cells B mem0.
Hypothesis HTP : ms_tp B = strtod_c.STRTOD_TP.
Hypothesis HERR : errno_addr B = strtod_c.STRTOD_ERRNO.
Hypothesis HGG : ms_got_guard B = strtod_c.STRTOD_GOT_GUARD.
Hypothesis HGD : ms_guard B = strtod_c.STRTOD_GUARD.
Hypothesis HSP47 : spZ regs0 <= 2 ^ 47.
Hypothesis HGLOB : strtod_c.STRTOD_GLOBALS_TOP <= spZ regs0 - CNO_K.
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).
Hypothesis LED0 : ledger B L0 A0 mem0 Lam peak cnt (2 ^ 64 - 1).
Hypothesis CNT0 : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis XLEN : Z.of_nat (length x) <= 0x300000.
Hypothesis XB : Mem.bytes_at (ms_segs B) mem0 data x.
Hypothesis XBLK : x <> [] -> exists a k, In (a, k) (blocks L0 A0) /\ a <= data /\ data + Z.of_nat (length x) <= a + k.
Hypothesis ROOM : cno_room F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x).
Hypothesis FAR : fuzz_alloc_ran_out_contract.
Hypothesis GRO0 : Mem.bytes_at (ms_segs B) mem0 G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).
Hypothesis OWN0 : Mem.bytes_at (ms_segs B) mem0 GL_OWN_RAN_OUT (Mem.le1 (Z_to_bv 64 0)).

Let J := cj B API L0 A0 regs0 mem0 md0.
Let Q := cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x.

Local Abbreviation nx := (Z.of_nat (length x)).

(* The callee-saved registers phase A keeps from the entry: sp (lowered by 240), gp, tp, s8..s11 (s7 holds 0x347b8
   from the auipc at 0x137b8 on). *)
Definition cnoA_R (regs : bvmap 5 word) : Prop :=
  spZ regs = spZ regs0 - 240 /\ YK11.getr regs 3 = YK11.getr regs0 3 /\ YK11.getr regs 4 = YK11.getr regs0 4 /\
  (forall r, 24 <= r <= 27 -> YK11.getr regs (Z_to_bv 5 r) = YK11.getr regs0 (Z_to_bv 5 r)).

Definition cnoA_kp (regs regs' : bvmap 5 word) : Prop :=
  forall r, r = 2 \/ r = 3 \/ r = 4 \/ 24 <= r <= 27 -> YK11.getr regs' (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r).

Ltac cnoA_mvE HG :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr' := fresh "Hr" in
  intros r Hr; rewrite HG;
  destruct Hr as [->|[->|[->|Hr]]]; [reflexivity .. |];
  assert (Hr' : r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct Hr' as [->|[->|[->| ->]]]; reflexivity.

Lemma cnoA_R_kp : forall regs regs', cnoA_R regs -> cnoA_kp regs regs' -> cnoA_R regs'.
Proof.
  intros regs regs' (Hs & H3 & H4 & H22) E.
  split; [unfold spZ in *; rewrite <- Hs; f_equal; apply (E 2); lia|].
  split; [rewrite <- H3; apply (E 3); lia|].
  split; [rewrite <- H4; apply (E 4); lia|].
  intros r Hr. rewrite <- (H22 r Hr). apply E. lia.
Qed.

Lemma cnoA_kp_rp : forall regs regs', regs_preserved regs regs' -> cnoA_kp regs regs'.
Proof. intros regs regs' RP r Hr. apply RP. unfold callee_saved. lia. Qed.

Lemma cnoA_saved_len : length (cno_saved regs0) = 72%nat.
Proof. unfold cno_saved. rewrite !length_app, !Mem.length_le8. reflexivity. Qed.

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

Lemma cnoA_dd_sep : forall L A m md q, J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  nx = 0 \/ cnoA_dd + nx <= q \/ q + nx + 16 <= cnoA_dd.
Proof.
  intros L A m md q HJ Hq Hn. pose proof cnoA_dd_facts as (_ & _ & Heq).
  assert (Hx : x = [] \/ x <> []) by (destruct x; [left; reflexivity | right; discriminate]).
  destruct Hx as [Hx|Hx]; [left; rewrite Hx; reflexivity | right].
  rewrite (Heq Hx).
  destruct (XBLK Hx) as (a & k & Hin & Ha & Hk).
  pose proof HJ as (HM & _).
  pose proof (cj_blocks0 B API L0 A0 regs0 mem0 md0 L A m md _ _ HJ Hin) as HinL.
  assert (Hne : (q, nx + 16) <> (a, k)) by (intros E; rewrite E in Hn; exact (Hn Hin)).
  destruct (cno_blocks_sep B API L A m md _ _ HM Hq HinL Hne) as [S|S]; cbn [fst snd] in S; lia.
Qed.

Lemma cnoA_auxv : forall L A m md, J L A m md -> st_init_done A = false -> auxv_pre B (ly_sec L) (spZ regs0 - 240) m.
Proof.
  intros L A m md HJ Hf.
  pose proof HJ as (HM & _ & _ & (_ & Hsec & _) & HI & HLB & _ & _ & _ & HHI & _).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _ & _ & _ & HAUX).
  assert (Hf0 : st_init_done A0 = false).
  { destruct (st_init_done A0) eqn:E; [rewrite (HI eq_refl) in Hf; discriminate | reflexivity]. }
  destruct (HAUX Hf0) as (av & ar & W1 & W2 & W3 & W4 & H5 & H6 & H7 & H8 & H9 & H10).
  pose proof cno_k_le as HKv. pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as (Hcv & _).
  assert (HE : errno_addr B + 4 <= YM05.alloc_ceiling) by (rewrite HERR; unfold strtod_c.STRTOD_ERRNO; lia).
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
    apply (mbyte_munch _ W m m' a MU); [pose proof YM05.alloc_ceiling_lt; lia | exact (HO a Ha)]. }
  unfold alloc_words.
  split; [|split; [|split]]; (eapply word_mem_frame; [eassumption|]); intros k Hk; apply E; unfold alloc_statics; lia.
Qed.

Lemma cnoA_aw_cp : forall K L A regs m md E L' A' regs' m' md' live pk ct fl,
  aa_MR API L A m md -> call_post_k B MR K L A regs m md E L' A' regs' m' md' ->
  YM05.alloc_ceiling + K <= spZ regs -> (forall a, alloc_statics a -> ~ E a) ->
  alloc_words B m live pk ct fl -> alloc_words B m' live pk ct fl.
Proof.
  intros K L A regs m md E L' A' regs' m' md' live pk ct fl HM CP HK HE (W1 & W2 & W3 & W4).
  assert (EQ : forall a, alloc_statics a -> mbyte (ms_segs B) m' a = mbyte (ms_segs B) m a).
  { intros a Ha.
    exact (kb_post_globals B API omx_G K L A regs m md E L' A' regs' m' md' a HG HM CP HK (cno_statics_img a Ha) (HE a Ha)). }
  unfold alloc_words.
  split; [|split; [|split]]; (eapply word_mem_frame; [eassumption|]); intros k Hk; apply EQ; unfold alloc_statics; lia.
Qed.

Lemma cnoA_aw_copy : forall L A m md m' q live pk ct fl, aa_MR API L A m md -> In (q, nx + 16) (blocks L A) ->
  munch [(q, q + nx + 16)] m m' -> alloc_words B m live pk ct fl -> alloc_words B m' live pk ct fl.
Proof.
  intros L A m md m' q live pk ct fl HM Hq MU AW. apply (cnoA_aw_munch m m' _ _ _ _ _ AW MU).
  intros a Ha. apply cnoA_out1. destruct (cno_statics_free B API HG a Ha) as (_ & _ & _ & HB).
  destruct (HB L A m md HM) as (_ & Hn). pose proof (Hn _ _ Hq). lia.
Qed.

Lemma cnoA_saved_cp : forall L A regs m md L' A' regs' m' md', aa_MR API L A m md ->
  call_post_k B MR ALLOC_STACK L A regs m md (fun _ => False) L' A' regs' m' md' -> spZ regs = spZ regs0 - 240 ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) -> bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0).
Proof.
  intros L A regs m md L' A' regs' m' md' HM CP Hsp BY.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _). pose proof cno_k_le as HKv.
  pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as (Hcv & _).
  apply (cno_hi_cp B API HS L A regs m md ALLOC_STACK _ L' A' regs' m' md' _ _ CP HM BY); [lia|].
  rewrite cnoA_saved_len. intros i Hi. split; [|intros []].
  unfold scratch_k, ALLOC_STACK. rewrite HERR. unfold strtod_c.STRTOD_ERRNO. lia.
Qed.

Lemma cnoA_saved_copy : forall L A m md m' q, aa_MR API L A m md -> In (q, nx + 16) (blocks L A) ->
  munch [(q, q + nx + 16)] m m' -> bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  bytes_at rsegs m' (spZ regs0 - 72) (cno_saved regs0).
Proof.
  intros L A m md m' q HM Hq MU BY.
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & _). pose proof cno_k_le as HKv.
  destruct (cno_block_range B API L A m md q _ HM Hq) as [H1 H2].
  apply (cno_bytes_munch1 m m' q (q + nx + 16) _ _ BY MU). right. lia.
Qed.

Lemma cnoA_blk_copy : forall m m' q a, munch [(q, q + nx + 16)] m m' -> (q + (nx + 16) <= a \/ a + (nx + 16) <= q) ->
  bytes_at rsegs m a x -> bytes_at rsegs m' a x.
Proof. intros m m' q a MU D BX. apply (cno_bytes_munch1 m m' q (q + nx + 16) a x BX MU). lia. Qed.

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
      unfold YO0f.ranges_disjoint in H; cbn [fst snd] in H; lia.
Qed.

Lemma cnoA_notA0 : forall L A m md p a, J L A m md -> In (p, nx + 16) (user_blocks A) -> ptr_addr L p = a ->
  ~ In (a, nx + 16) (blocks L0 A0) -> forall q k, In (q, k) (user_blocks A0) -> q <> p.
Proof.
  intros L A m md p a HJ Hp Ha Hn q k Hq E. subst q.
  pose proof HJ as (_ & HWF & _ & _ & _ & _ & _ & HUB & _).
  destruct (HUB p k Hq) as (Hq1 & Hpa).
  pose proof (cno_nodup_fst _ p _ _ (YO10.user_block_ptrs_NoDup A HWF) Hq1 Hp) as Ek. subst k.
  apply Hn. rewrite <- Ha, Hpa. apply cno_ub_blocks. exact Hq.
Qed.

Lemma cnoA_present_norm : forall m a, 0 <= a < 2 ^ 64 -> ~ in_img B a -> present m a -> present (normalize rsegs m) a.
Proof. intros m a Ha Hn [v Hv]. exists v. unfold normalize. rewrite (cno_ro_false B HS a Ha Hn). exact Hv. Qed.

Lemma cnoA_rw_new : forall L A m md q k, aa_MR API L A m md -> In (q, k) (blocks L A) -> 0 <= k ->
  exists junk, rw_cells rsegs (normalize rsegs m) q [CB (Z.to_nat k) junk].
Proof.
  intros L A m md q k HM Hq Hk. destruct (cno_block_range B API L A m md q k HM Hq) as [H1 H2].
  pose proof YM05.alloc_ceiling_lt as Hc.
  apply cno_rw_of_present; [lia | lia | lia |].
  intros i Hi. destruct (cno_block_facts B API AX L A m md q k i HM Hq Hi) as (Hp & _ & _ & _ & Hni).
  apply cnoA_present_norm; [lia | exact Hni | exact Hp].
Qed.

(* A copy run writes only its new block. *)
Lemma cnoA_J_copy : forall L A m md m' q, J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  munch [(q, q + nx + 16)] m m' -> wmono (ms_segs B) m m' -> ro_agree (ms_segs B) m' -> J L A m' md.
Proof.
  intros L A m md m' q HJ Hq Hn MU WM RA'. pose proof HJ as (HM & _).
  apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L A m md m' _ HJ MU WM RA').
  intros z Hz Ho. apply cnoA_nout1 in Ho. right. exists q, (nx + 16).
  split; [exact Hq|]. split; [exact Hn|]. split; [lia|].
  destruct (cno_block_facts B API AX L A m md q (nx + 16) (z - q) HM Hq ltac:(lia)) as (Hp & _ & _ & _ & Hni).
  assert (Ez : q + (z - q) = z) by lia. rewrite Ez in Hp, Hni.
  apply (cno_present_of_writable B HS m' z Hz Hni).
  exact (WM (Z_to_bv 64 z) (cno_writable_of_present B m z Hp)).
Qed.

Lemma cnoA_copy_pre : forall L A m md q, J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  m_halted md = None /\ m_vm_lazy md = [] /\ ro_agree (ms_segs B) m /\ 4096 <= q /\ q + (nx + 16) <= YM05.alloc_ceiling /\
  0 <= cnoA_dd /\ cnoA_dd + nx <= 2 ^ 64 /\ bytes_at rsegs (normalize rsegs m) cnoA_dd x /\
  (exists junk, rw_cells rsegs (normalize rsegs m) q [CB (Z.to_nat (nx + 16)) junk]) /\
  (nx = 0 \/ cnoA_dd + nx <= q \/ q + nx + 16 <= cnoA_dd).
Proof.
  intros L A m md q HJ Hq Hn. pose proof HJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RA).
  destruct (kb_md B API L A m md HM) as (Hh & Hl).
  destruct (cno_block_range B API L A m md q (nx + 16) HM Hq) as (Hq0 & Hq1).
  pose proof (cnoA_dd_bytes L A m md HJ) as BD. pose proof (bytes_at_bound _ _ _ _ BD) as (Hd0 & Hd1).
  split; [exact Hh|]. split; [exact Hl|]. split; [exact RA|]. split; [exact Hq0|]. split; [exact Hq1|].
  split; [exact Hd0|]. split; [exact Hd1|].
  split; [rewrite <- HS; apply bytes_at_normalize; [exact RA | rewrite HS; exact BD]|].
  split; [exact (cnoA_rw_new L A m md q (nx + 16) HM Hq ltac:(lia))|].
  exact (cnoA_dd_sep L A m md q HJ Hq Hn).
Qed.

(* The entry run: prologue (ra, s0..s7 saved at sp + 0xe8 .. sp + 0xa8), s2 = s3 + 16 = n + 16, s4 = data, to
   default_malloc(n + 16) with ra 0x137b4. *)
Lemma cnoA_seg0 : forall (fx : YK11.FPState) (P : config -> Prop),
  ro_agree (ms_segs B) mem0 ->
  YK11.getr regs0 10 = Z_to_bv 64 cnoA_dd -> YK11.getr regs0 11 = Z_to_bv 64 nx ->
  (forall regs1 m1, YK11.getr regs1 1 = Z_to_bv 64 0x137b4 -> cnoA_R regs1 ->
     YK11.getr regs1 10 = Z_to_bv 64 (nx + 16) -> YK11.getr regs1 18 = Z_to_bv 64 (nx + 16) ->
     YK11.getr regs1 19 = Z_to_bv 64 nx -> YK11.getr regs1 20 = Z_to_bv 64 cnoA_dd ->
     J L0 A0 m1 md0 -> munch [(spZ regs0 - 72, spZ regs0)] mem0 m1 ->
     bytes_at rsegs m1 (spZ regs0 - 72) (cno_saved regs0) ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs1 (Z_to_bv 64 0x178d8) m1 (YK11.seg_rom (ms_segs B))) md0) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 0x13778) mem0 (YK11.seg_rom (ms_segs B))) md0) P.
Proof.
  intros fx P RA0 R10 R11 K.
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & HSW0 & _).
  pose proof cno_k_le as HKv. pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as (Hcv & _).
  pose proof cnoA_dd_facts as (Hdd & _).
  destruct (kb_md B API L0 A0 mem0 md0 HM0) as (Hh0 & Hz0).
  assert (PS : forall i, 0 <= i < 72 -> present mem0 (spZ regs0 - 72 + i)).
  { intros i Hi. apply (cno_present_of_writable B HS mem0 (spZ regs0 - 72 + i)); [lia | | apply HSW0; lia].
    intros Hi'. pose proof (cno_img_low B HS _ Hi'). lia. }
  destruct (cno_rw_of_present mem0 (spZ regs0 - 72) 72 ltac:(lia) ltac:(lia) ltac:(lia) PS) as (j & RWJ).
  apply (kb_run B regs0 (Z_to_bv 64 0x13778) mem0 md0
    (fun R pc' m' => seg0_post (YK11.getr regs0 1) (YK11.getr regs0 2) (YK11.getr regs0 3) (YK11.getr regs0 4)
       (YK11.getr regs0 8) (YK11.getr regs0 9) (YK11.getr regs0 18) (YK11.getr regs0 19) (YK11.getr regs0 20)
       (YK11.getr regs0 21) (YK11.getr regs0 22) (YK11.getr regs0 23) (YK11.getr regs0 24) (YK11.getr regs0 25)
       (YK11.getr regs0 26) (YK11.getr regs0 27) (@fp_regs fx) (@fp_csr fx) mem0 cnoA_dd nx
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh0 Hz0).
  - rewrite HS. unfold rmk. rewrite R10, R11.
    eapply evt_mono.
    + apply cno_seg0 with (m := mem0) (d := cnoA_dd) (n := nx) (j := j); [lia | lia | |].
      * change (bv_unsigned (YK11.getr regs0 2)) with (spZ regs0). lia.
      * change (bv_unsigned (YK11.getr regs0 2)) with (spZ regs0).
        assert (E72 : spZ regs0 + -72 = spZ regs0 - 72) by lia. rewrite E72. exact RWJ.
    + intros ms PO. pose proof PO as PO'. unfold seg0_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO].
  - intros R pc' m1 regs1 HQ HGr. cbv beta in HQ. unfold seg0_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & RW).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m1. clear E.
    change (bv_unsigned (YK11.getr regs0 2)) with (spZ regs0) in MU, RW.
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
    assert (G2 : YK11.getr regs1 2 = Z_to_bv 64 (spZ regs0 - 240)) by (rewrite HGr; reflexivity).
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
    + exact J1.
    + exact MU.
    + exact BY.
Qed.

(* First copy (0x137b4): s0 = q; auipc s7 (s7 = 0x347b8); beqz q not taken; memcpy(q, data, n) if n > 0;
   memset(q + n, 0x31, 16); default_malloc(n + 16), ra 0x137f8. *)
Lemma cnoA_copy1 : forall (fx : YK11.FPState) L A regs m md q (P : config -> Prop),
  J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  YK11.getr regs 10 = Z_to_bv 64 q -> YK11.getr regs 18 = Z_to_bv 64 (nx + 16) ->
  YK11.getr regs 19 = Z_to_bv 64 nx -> YK11.getr regs 20 = Z_to_bv 64 cnoA_dd ->
  (forall regs' m', YK11.getr regs' 1 = Z_to_bv 64 0x137f8 -> YK11.getr regs' 8 = Z_to_bv 64 q ->
     YK11.getr regs' 10 = Z_to_bv 64 (nx + 16) -> YK11.getr regs' 18 = Z_to_bv 64 (nx + 16) ->
     YK11.getr regs' 19 = Z_to_bv 64 nx -> YK11.getr regs' 20 = Z_to_bv 64 cnoA_dd ->
     YK11.getr regs' 23 = Z_to_bv 64 0x347b8 -> cnoA_kp regs regs' ->
     J L A m' md -> munch [(q, q + nx + 16)] m m' -> bytes_at rsegs m' q x ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 0x178d8) m' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x137b4) m (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md q P HJ Hq Hn E10 E18 E19 E20 K.
  destruct (cnoA_copy_pre L A m md q HJ Hq Hn) as (Hh & Hl & RA & Hq0 & Hq1 & Hd0 & Hd1 & BD & (junk & RW) & DS).
  pose proof YM05.alloc_ceiling_lt as Hc.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x137b4) m md
    (fun R pc' m' => exists a1' a2', copy_post (Z_to_bv 64 0x137f8) (YK11.getr regs 2) (YK11.getr regs 3)
       (YK11.getr regs 4) (Z_to_bv 64 q) (YK11.getr regs 9) (Z_to_bv 64 (nx + 16)) (Z_to_bv 64 nx)
       (Z_to_bv 64 cnoA_dd) (YK11.getr regs 21) (YK11.getr regs 22) (Z_to_bv 64 0x347b8) (YK11.getr regs 24)
       (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) (Z_to_bv 64 (nx + 16)) a1' a2' 0x178d8
       (@fp_regs fx) (@fp_csr fx) (normalize rsegs m) q cnoA_dd nx x 49
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite E10, E18, E19, E20.
    eapply evt_mono.
    + apply (cno_copy1 MEMCPY MEMSET) with (m := normalize rsegs m) (q := q) (d := cnoA_dd) (n := nx) (x := x)
        (junk := junk);
        [lia | lia | lia | lia | lia | symmetry; apply Nat2Z.id | exact BD | exact RW | exact DS | apply mem_inv_normalize].
    + intros ms (a1' & a2' & PO). pose proof PO as PO'. unfold copy_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity|]. cbv beta. exists a1', a2'. exact PO.
  - intros R pc' m0 mem' regs' HK HREL HRS HGr.
    cbv beta in HK. destruct HK as (a1' & a2' & HK). unfold copy_post in HK.
    destruct HK as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & _ & BQ & _).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m0. clear E.
    rewrite <- HS in MU, WM, BQ.
    destruct (cno_back B m mem' m'' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply (proj2 (bytes_at_rel _ _ _ _ _ HREL)) in BQ.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BQ. destruct BQ as [BQ _]. rewrite HS in BQ.
    apply (K regs' mem').
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + unfold cnoA_kp. cnoA_mvE HGr.
    + exact (cnoA_J_copy L A m md mem' q HJ Hq Hn MU' WM' RA').
    + exact MU'.
    + exact BQ.
Qed.

(* Second copy (0x137f8): s1 = q; beqz q not taken; the same copy with fill 0x32; default_malloc(n + 16),
   ra 0x13838. *)
Lemma cnoA_copy2 : forall (fx : YK11.FPState) L A regs m md q (P : config -> Prop),
  J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  YK11.getr regs 10 = Z_to_bv 64 q -> YK11.getr regs 18 = Z_to_bv 64 (nx + 16) ->
  YK11.getr regs 19 = Z_to_bv 64 nx -> YK11.getr regs 20 = Z_to_bv 64 cnoA_dd ->
  (forall regs' m', YK11.getr regs' 1 = Z_to_bv 64 0x13838 -> YK11.getr regs' 8 = YK11.getr regs 8 ->
     YK11.getr regs' 9 = Z_to_bv 64 q -> YK11.getr regs' 10 = Z_to_bv 64 (nx + 16) ->
     YK11.getr regs' 19 = Z_to_bv 64 nx -> YK11.getr regs' 20 = Z_to_bv 64 cnoA_dd ->
     YK11.getr regs' 23 = YK11.getr regs 23 -> cnoA_kp regs regs' ->
     J L A m' md -> munch [(q, q + nx + 16)] m m' -> bytes_at rsegs m' q x ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 0x178d8) m' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x137f8) m (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md q P HJ Hq Hn E10 E18 E19 E20 K.
  destruct (cnoA_copy_pre L A m md q HJ Hq Hn) as (Hh & Hl & RA & Hq0 & Hq1 & Hd0 & Hd1 & BD & (junk & RW) & DS).
  pose proof YM05.alloc_ceiling_lt as Hc.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x137f8) m md
    (fun R pc' m' => exists a1' a2', copy_post (Z_to_bv 64 0x13838) (YK11.getr regs 2) (YK11.getr regs 3)
       (YK11.getr regs 4) (YK11.getr regs 8) (Z_to_bv 64 q) (Z_to_bv 64 (nx + 16)) (Z_to_bv 64 nx)
       (Z_to_bv 64 cnoA_dd) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24)
       (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) (Z_to_bv 64 (nx + 16)) a1' a2' 0x178d8
       (@fp_regs fx) (@fp_csr fx) (normalize rsegs m) q cnoA_dd nx x 50
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite E10, E18, E19, E20.
    eapply evt_mono.
    + apply (cno_copy2 MEMCPY MEMSET) with (m := normalize rsegs m) (q := q) (d := cnoA_dd) (n := nx) (x := x)
        (junk := junk);
        [lia | lia | lia | lia | lia | symmetry; apply Nat2Z.id | exact BD | exact RW | exact DS | apply mem_inv_normalize].
    + intros ms (a1' & a2' & PO). pose proof PO as PO'. unfold copy_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity|]. cbv beta. exists a1', a2'. exact PO.
  - intros R pc' m0 mem' regs' HK HREL HRS HGr.
    cbv beta in HK. destruct HK as (a1' & a2' & HK). unfold copy_post in HK.
    destruct HK as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & _ & BQ & _).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m0. clear E.
    rewrite <- HS in MU, WM, BQ.
    destruct (cno_back B m mem' m'' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply (proj2 (bytes_at_rel _ _ _ _ _ HREL)) in BQ.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BQ. destruct BQ as [BQ _]. rewrite HS in BQ.
    apply (K regs' mem').
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + unfold cnoA_kp. cnoA_mvE HGr.
    + exact (cnoA_J_copy L A m md mem' q HJ Hq Hn MU' WM' RA').
    + exact MU'.
    + exact BQ.
Qed.

(* Third copy (0x13838): s2 = q; beqz q not taken; the same copy with fill 0, back at 0x13864 (ra 0x13864). *)
Lemma cnoA_copy3 : forall (fx : YK11.FPState) L A regs m md q (P : config -> Prop),
  J L A m md -> In (q, nx + 16) (blocks L A) -> ~ In (q, nx + 16) (blocks L0 A0) ->
  YK11.getr regs 10 = Z_to_bv 64 q -> YK11.getr regs 19 = Z_to_bv 64 nx -> YK11.getr regs 20 = Z_to_bv 64 cnoA_dd ->
  (forall regs' m', YK11.getr regs' 8 = YK11.getr regs 8 -> YK11.getr regs' 9 = YK11.getr regs 9 ->
     YK11.getr regs' 18 = Z_to_bv 64 q -> YK11.getr regs' 19 = Z_to_bv 64 nx ->
     YK11.getr regs' 23 = YK11.getr regs 23 -> cnoA_kp regs regs' ->
     J L A m' md -> munch [(q, q + nx + 16)] m m' -> bytes_at rsegs m' q x ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 0x13864) m' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x13838) m (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md q P HJ Hq Hn E10 E19 E20 K.
  destruct (cnoA_copy_pre L A m md q HJ Hq Hn) as (Hh & Hl & RA & Hq0 & Hq1 & Hd0 & Hd1 & BD & (junk & RW) & DS).
  pose proof YM05.alloc_ceiling_lt as Hc.
  apply (cno_run_n B HS regs (Z_to_bv 64 0x13838) m md
    (fun R pc' m' => exists a0' a1' a2', copy_post (Z_to_bv 64 0x13864) (YK11.getr regs 2) (YK11.getr regs 3)
       (YK11.getr regs 4) (YK11.getr regs 8) (YK11.getr regs 9) (Z_to_bv 64 q) (Z_to_bv 64 nx)
       (Z_to_bv 64 cnoA_dd) (YK11.getr regs 21) (YK11.getr regs 22) (YK11.getr regs 23) (YK11.getr regs 24)
       (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) a0' a1' a2' 0x13864
       (@fp_regs fx) (@fp_csr fx) (normalize rsegs m) q cnoA_dd nx x 0
       (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite E10, E19, E20.
    eapply evt_mono.
    + apply (cno_copy3 MEMCPY MEMSET) with (m := normalize rsegs m) (q := q) (d := cnoA_dd) (n := nx) (x := x)
        (junk := junk);
        [lia | lia | lia | lia | lia | symmetry; apply Nat2Z.id | exact BD | exact RW | exact DS | apply mem_inv_normalize].
    + intros ms (a0' & a1' & a2' & PO). pose proof PO as PO'. unfold copy_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity|]. cbv beta. exists a0', a1', a2'. exact PO.
  - intros R pc' m0 mem' regs' HK HREL HRS HGr.
    cbv beta in HK. destruct HK as (a0' & a1' & a2' & HK). unfold copy_post in HK.
    destruct HK as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & _ & BQ & _).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m0. clear E.
    rewrite <- HS in MU, WM, BQ.
    destruct (cno_back B m mem' m'' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply (proj2 (bytes_at_rel _ _ _ _ _ HREL)) in BQ.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in BQ. destruct BQ as [BQ _]. rewrite HS in BQ.
    apply (K regs' mem').
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + unfold cnoA_kp. cnoA_mvE HGr.
    + exact (cnoA_J_copy L A m md mem' q HJ Hq Hn MU' WM' RA').
    + exact MU'.
    + exact BQ.
Qed.

(* The zero run (0x13864): s5 = g_own_ran_out (0); the trees at sp + 0x70, sp + 0x38, sp zeroed (memset of 0x38
   bytes each); s4 = -1; out_of_memory() = 0 (bnez s5 and bnez fuzz_alloc_ran_out() not taken); a2 = sp + 0x70,
   a0 = s0, a1 = s3; parse_noting (0x13a04), ra 0x138b8.  It writes only the frame sp .. sp + 168. *)
Lemma cnoA_zero : forall (fx : YK11.FPState) L A regs m md (P : config -> Prop),
  J L A m md -> spZ regs = spZ regs0 - 240 -> YK11.getr regs 23 = Z_to_bv 64 0x347b8 ->
  (forall regs' m', YK11.getr regs' 1 = Z_to_bv 64 0x138b8 -> YK11.getr regs' 8 = YK11.getr regs 8 ->
     YK11.getr regs' 9 = YK11.getr regs 9 -> YK11.getr regs' 18 = YK11.getr regs 18 ->
     YK11.getr regs' 19 = YK11.getr regs 19 -> YK11.getr regs' 23 = YK11.getr regs 23 ->
     YK11.getr regs' 10 = YK11.getr regs 8 -> YK11.getr regs' 11 = YK11.getr regs 19 ->
     YK11.getr regs' 12 = Z_to_bv 64 (spZ regs + 112) -> cnoA_kp regs regs' ->
     J L A m' md -> munch [(spZ regs, spZ regs + 168)] m m' ->
     SR (ms_segs B) (mkCfg (@YK11.mkst fx regs' (Z_to_bv 64 0x13a04) m' (YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 0x13864) m (YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx L A regs m md P HJ Hsp G23 K.
  pose proof HJ as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC & RA).
  destruct (kb_md B API L A m md HM) as (Hh & Hl).
  pose proof PRE0 as (_ & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as (Hcv & _).
  assert (PS : forall i, 0 <= i < 168 -> present (normalize rsegs m) (spZ regs + i)).
  { intros i Hi. assert (Hni : ~ in_img B (spZ regs + i)) by (intros Hi'; pose proof (cno_img_low B HS _ Hi'); lia).
    apply cnoA_present_norm; [lia | exact Hni |].
    apply (cno_present_of_writable B HS m (spZ regs + i)); [lia | exact Hni |]. apply HSC. left. lia. }
  destruct (cno_rw_of_present (normalize rsegs m) (spZ regs) 168 ltac:(lia) ltac:(lia) ltac:(lia) PS) as (j & RWJ).
  assert (OWN : ro_cells rsegs (normalize rsegs m) GL_OWN_RAN_OUT [C1 (Z_to_bv 8 0)]).
  { apply cno_bytes_ro1. rewrite <- HS. apply bytes_at_normalize; [exact RA|].
    exact (cno_cj_own B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ OWN0). }
  assert (GRO : ro_cells rsegs (normalize rsegs m) G_RAN_OUT [C1 (Z_to_bv 8 0)]).
  { apply cno_bytes_ro1. rewrite <- HS. apply bytes_at_normalize; [exact RA|].
    exact (cno_cj_gro B API HS HG L0 A0 regs0 mem0 md0 PRE0 L A m md HJ GRO0). }
  apply (cno_run_n B HS regs (Z_to_bv 64 0x13864) m md
    (fun R pc' m' => zero_post (YK11.getr regs 2) (YK11.getr regs 3) (YK11.getr regs 4) (YK11.getr regs 8)
       (YK11.getr regs 9) (YK11.getr regs 18) (YK11.getr regs 19) (YK11.getr regs 22) (Z_to_bv 64 0x347b8)
       (YK11.getr regs 24) (YK11.getr regs 25) (YK11.getr regs 26) (YK11.getr regs 27) (@fp_regs fx) (@fp_csr fx)
       (normalize rsegs m) (MS R (@fp_regs fx) pc' (@fp_csr fx) None m' (seg_rom rsegs)))
    P Hh Hl RA).
  - rewrite HS. unfold rmk. rewrite G23.
    eapply evt_mono.
    + apply (cno_zero MEMSET FAR) with (j := j).
      * change (bv_unsigned (YK11.getr regs 2)) with (spZ regs). lia.
      * change (bv_unsigned (YK11.getr regs 2)) with (spZ regs). unfold GL_OWN_RAN_OUT. lia.
      * change (bv_unsigned (YK11.getr regs 2)) with (spZ regs). unfold G_RAN_OUT. lia.
      * exact RWJ.
      * apply mem_inv_normalize.
      * exact OWN.
      * exact GRO.
    + intros ms PO. pose proof PO as PO'. unfold zero_post in PO'.
      destruct PO' as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & t3 & t4 & t5 & t6 & m' & E & _).
      subst ms. do 3 eexists. split; [reflexivity | exact PO].
  - intros R pc' m0 mem' regs' HQ HREL HRS HGr.
    cbv beta in HQ. unfold zero_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & t3 & t4 & t5 & t6 & m'' & E & MU & WM & _).
    pose proof (f_equal ms_regs E) as ER. pose proof (f_equal ms_pc_val E) as EP. pose proof (f_equal ms_mem E) as EM.
    cbn [ms_regs ms_pc_val ms_mem MS] in ER, EP, EM. subst R pc' m0. clear E.
    change (bv_unsigned (YK11.getr regs 2)) with (spZ regs) in MU.
    rewrite <- HS in MU, WM.
    destruct (cno_back B m mem' m'' _ RA HREL HRS MU WM) as (MU' & WM' & RA').
    apply (K regs' mem').
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. symmetry. exact G23.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + rewrite HGr. reflexivity.
    + unfold cnoA_kp. cnoA_mvE HGr.
    + apply (cj_kindA B API HS AX L0 A0 regs0 mem0 md0 PRE0 L A m md mem' _ HJ MU' WM' RA').
      intros z Hz Ho. apply cnoA_nout1 in Ho. left. lia.
    + exact MU'.
Qed.

Lemma cnoA_holds : cno_KB B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x ->
  forall fx : YK11.FPState, frm_zero (@fp_csr fx) -> MemNorm.ro_agree (ms_segs B) mem0 -> rf_ok F A0 b ->
  YK11.getr regs0 10 = Z_to_bv 64 data -> YK11.getr regs0 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
  SR (ms_segs B) (mkCfg (@YK11.mkst fx regs0 (Z_to_bv 64 0x13778) mem0 (YK11.seg_rom (ms_segs B))) md0) Q.
Proof.
  intros KB fx FZ RA0 RF0 R10 R11.
  pose proof PRE0 as (HM0 & _ & _ & _ & _ & HK & HK63 & _).
  pose proof cno_k_le as HKv. pose proof YM05.alloc_ceiling_lt as Hc. pose proof YM05.alloc_ceiling_value as (Hcv & _).
  pose proof LED0 as (AW0 & HPK0 & HCT0 & _).
  pose proof cnoA_dd_facts as (Hdd & Ebv & _).
  pose proof ROOM as (RM1 & RM2 & RM3 & _).
  rewrite <- Ebv in R10.
  (* entry run *)
  apply (cnoA_seg0 fx Q RA0 R10 R11).
  intros regs1 m1 G1_1 R1 G1_10 G1_18 G1_19 G1_20 J1 MU1 BY1.
  pose proof R1 as (Hsp1 & _ & G1_4 & _).
  pose proof J1 as (HMa & _).
  assert (AW1 : alloc_words B m1 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply (cnoA_aw_munch mem0 m1 _ _ _ _ _ AW0 MU1). intros a Ha. apply cnoA_out1.
    destruct (cno_statics_free B API HG a Ha) as (_ & Hl & _). lia. }
  (* first malloc *)
  apply (cno_call_malloc B API HMAL F MALLOC L0 A0 regs0 mem0 md0 PRE0 fx L0 A0 regs1 m1 md0 b (nx + 16) Q J1 Hsp1 G1_4);
    [rewrite G1_1; cnoA_ret | exact G1_10 | intros Hf; rewrite Hsp1; exact (cnoA_auxv L0 A0 m1 md0 J1 Hf) | exact RF0
    | exact RM1 |].
  intros L1 A1 regs2 m2 md1 qa1 J2 CP2 R10a _ FR1 BL1 SURV1 INIT1 RF1.
  rewrite G1_1.
  pose proof CP2 as (HM1 & _ & _ & _ & _ & RP2 & _).
  destruct FR1 as (Hq1a & Hq1b & _).
  destruct (cnoA_newblk L0 A0 L1 A1 m2 md1 qa1 (nx + 16) HM1 BL1) as (QIN1 & SEP1).
  assert (QNEW1 : ~ In (qa1, nx + 16) (blocks L0 A0)) by (intros H; destruct (SEP1 _ _ H); lia).
  pose proof (cnoA_R_kp regs1 regs2 R1 (cnoA_kp_rp regs1 regs2 RP2)) as R2.
  assert (G2_18 : YK11.getr regs2 18 = Z_to_bv 64 (nx + 16))
    by (rewrite <- G1_18; apply (RP2 18); unfold callee_saved; lia).
  assert (G2_19 : YK11.getr regs2 19 = Z_to_bv 64 nx) by (rewrite <- G1_19; apply (RP2 19); unfold callee_saved; lia).
  assert (G2_20 : YK11.getr regs2 20 = Z_to_bv 64 cnoA_dd)
    by (rewrite <- G1_20; apply (RP2 20); unfold callee_saved; lia).
  pose proof (cnoA_aw_cp ALLOC_STACK L0 A0 regs1 m1 md0 _ L1 A1 regs2 m2 md1 _ _ _ _ HMa CP2
                ltac:(unfold ALLOC_STACK; lia) (fun a _ H => H) AW1) as AW2.
  pose proof (cnoA_saved_cp L0 A0 regs1 m1 md0 L1 A1 regs2 m2 md1 HMa CP2 Hsp1 BY1) as BY2.
  (* first copy *)
  apply (cnoA_copy1 fx L1 A1 regs2 m2 md1 qa1 Q J2 QIN1 QNEW1 R10a G2_18 G2_19 G2_20).
  intros regs3 m3 G3_1 G3_8 G3_10 G3_18 G3_19 G3_20 G3_23 KP3 J3 MU3 BX1.
  pose proof (cnoA_R_kp regs2 regs3 R2 KP3) as R3. pose proof R3 as (Hsp3 & _ & G3_4 & _).
  pose proof (cnoA_aw_copy L1 A1 m2 md1 m3 qa1 _ _ _ _ HM1 QIN1 MU3 AW2) as AW3.
  pose proof (cnoA_saved_copy L1 A1 m2 md1 m3 qa1 HM1 QIN1 MU3 BY2) as BY3.
  destruct (cno_in_blocks L1 A1 qa1 _ QIN1) as (p1 & Hp1 & Pp1).
  (* second malloc *)
  apply (cno_call_malloc B API HMAL F MALLOC L0 A0 regs0 mem0 md0 PRE0 fx L1 A1 regs3 m3 md1 (rf_malloc F b (nx + 16))
           (nx + 16) Q J3 Hsp3 G3_4);
    [rewrite G3_1; cnoA_ret | exact G3_10 | intros Hf; congruence | exact RF1 | exact RM2 |].
  intros L2 A2 regs4 m4 md2 qa2 J4 CP4 R10b _ FR2 BL2 SURV2 INIT2 RF2.
  rewrite G3_1.
  pose proof CP4 as (HM2 & _ & _ & _ & _ & RP4 & _).
  destruct FR2 as (Hq2a & Hq2b & _).
  destruct (cnoA_newblk L1 A1 L2 A2 m4 md2 qa2 (nx + 16) HM2 BL2) as (QIN2 & SEP2).
  assert (QNEW2 : ~ In (qa2, nx + 16) (blocks L0 A0)).
  { intros H. destruct (SEP2 _ _ (cj_blocks0 B API L0 A0 regs0 mem0 md0 L1 A1 m3 md1 _ _ J3 H)); lia. }
  pose proof (cnoA_R_kp regs3 regs4 R3 (cnoA_kp_rp regs3 regs4 RP4)) as R4.
  assert (G4_8 : YK11.getr regs4 8 = Z_to_bv 64 qa1) by (rewrite <- G3_8; apply (RP4 8); unfold callee_saved; lia).
  assert (G4_18 : YK11.getr regs4 18 = Z_to_bv 64 (nx + 16))
    by (rewrite <- G3_18; apply (RP4 18); unfold callee_saved; lia).
  assert (G4_19 : YK11.getr regs4 19 = Z_to_bv 64 nx) by (rewrite <- G3_19; apply (RP4 19); unfold callee_saved; lia).
  assert (G4_20 : YK11.getr regs4 20 = Z_to_bv 64 cnoA_dd)
    by (rewrite <- G3_20; apply (RP4 20); unfold callee_saved; lia).
  assert (G4_23 : YK11.getr regs4 23 = Z_to_bv 64 0x347b8)
    by (rewrite <- G3_23; apply (RP4 23); unfold callee_saved; lia).
  pose proof J3 as (HM1' & _).
  pose proof (cnoA_aw_cp ALLOC_STACK L1 A1 regs3 m3 md1 _ L2 A2 regs4 m4 md2 _ _ _ _ HM1' CP4
                ltac:(unfold ALLOC_STACK; lia) (fun a _ H => H) AW3) as AW4.
  pose proof (cnoA_saved_cp L1 A1 regs3 m3 md1 L2 A2 regs4 m4 md2 HM1' CP4 Hsp3 BY3) as BY4.
  pose proof (SURV2 p1 _ Hp1) as Hp1b.
  destruct (cnoA_blk_cp ALLOC_STACK L1 A1 regs3 m3 md1 _ L2 A2 regs4 m4 md2 p1 qa1 CP4 Hp1 Hp1b Pp1 BX1)
    as (BX1b & Pp1b).
  (* second copy *)
  apply (cnoA_copy2 fx L2 A2 regs4 m4 md2 qa2 Q J4 QIN2 QNEW2 R10b G4_18 G4_19 G4_20).
  intros regs5 m5 G5_1 G5_8 G5_9 G5_10 G5_19 G5_20 G5_23 KP5 J5 MU5 BX2.
  pose proof (cnoA_R_kp regs4 regs5 R4 KP5) as R5. pose proof R5 as (Hsp5 & _ & G5_4 & _).
  pose proof (cnoA_aw_copy L2 A2 m4 md2 m5 qa2 _ _ _ _ HM2 QIN2 MU5 AW4) as AW5.
  pose proof (cnoA_saved_copy L2 A2 m4 md2 m5 qa2 HM2 QIN2 MU5 BY4) as BY5.
  pose proof (cnoA_blk_copy m4 m5 qa2 qa1 MU5 (SEP2 _ _ QIN1) BX1b) as BX1c.
  destruct (cno_in_blocks L2 A2 qa2 _ QIN2) as (p2 & Hp2 & Pp2).
  pose proof (cno_ub_blocks L2 A2 p1 _ Hp1b) as QIN1b. rewrite Pp1b in QIN1b.
  (* third malloc *)
  apply (cno_call_malloc B API HMAL F MALLOC L0 A0 regs0 mem0 md0 PRE0 fx L2 A2 regs5 m5 md2
           (rf_malloc F (rf_malloc F b (nx + 16)) (nx + 16)) (nx + 16) Q J5 Hsp5 G5_4);
    [rewrite G5_1; cnoA_ret | exact G5_10 | intros Hf; congruence | exact RF2 | exact RM3 |].
  intros L3 A3 regs6 m6 md3 qa3 J6 CP6 R10c _ FR3 BL3 SURV3 INIT3 RF3.
  rewrite G5_1.
  pose proof CP6 as (HM3 & _ & _ & _ & _ & RP6 & _).
  destruct FR3 as (Hq3a & Hq3b & _).
  destruct (cnoA_newblk L2 A2 L3 A3 m6 md3 qa3 (nx + 16) HM3 BL3) as (QIN3 & SEP3).
  assert (QNEW3 : ~ In (qa3, nx + 16) (blocks L0 A0)).
  { intros H. destruct (SEP3 _ _ (cj_blocks0 B API L0 A0 regs0 mem0 md0 L2 A2 m5 md2 _ _ J5 H)); lia. }
  pose proof (cnoA_R_kp regs5 regs6 R5 (cnoA_kp_rp regs5 regs6 RP6)) as R6. pose proof R6 as (Hsp6 & _).
  assert (G6_8 : YK11.getr regs6 8 = Z_to_bv 64 qa1)
    by (rewrite <- G4_8, <- G5_8; apply (RP6 8); unfold callee_saved; lia).
  assert (G6_9 : YK11.getr regs6 9 = Z_to_bv 64 qa2) by (rewrite <- G5_9; apply (RP6 9); unfold callee_saved; lia).
  assert (G6_19 : YK11.getr regs6 19 = Z_to_bv 64 nx) by (rewrite <- G5_19; apply (RP6 19); unfold callee_saved; lia).
  assert (G6_20 : YK11.getr regs6 20 = Z_to_bv 64 cnoA_dd)
    by (rewrite <- G5_20; apply (RP6 20); unfold callee_saved; lia).
  assert (G6_23 : YK11.getr regs6 23 = Z_to_bv 64 0x347b8)
    by (rewrite <- G4_23, <- G5_23; apply (RP6 23); unfold callee_saved; lia).
  pose proof J5 as (HM2' & _).
  pose proof (cnoA_aw_cp ALLOC_STACK L2 A2 regs5 m5 md2 _ L3 A3 regs6 m6 md3 _ _ _ _ HM2' CP6
                ltac:(unfold ALLOC_STACK; lia) (fun a _ H => H) AW5) as AW6.
  pose proof (cnoA_saved_cp L2 A2 regs5 m5 md2 L3 A3 regs6 m6 md3 HM2' CP6 Hsp5 BY5) as BY6.
  pose proof (SURV3 p1 _ Hp1b) as Hp1c.
  destruct (cnoA_blk_cp ALLOC_STACK L2 A2 regs5 m5 md2 _ L3 A3 regs6 m6 md3 p1 qa1 CP6 Hp1b Hp1c Pp1b BX1c)
    as (BX1d & Pp1c).
  pose proof (SURV3 p2 _ Hp2) as Hp2b.
  destruct (cnoA_blk_cp ALLOC_STACK L2 A2 regs5 m5 md2 _ L3 A3 regs6 m6 md3 p2 qa2 CP6 Hp2 Hp2b Pp2 BX2)
    as (BX2b & Pp2b).
  (* third copy *)
  apply (cnoA_copy3 fx L3 A3 regs6 m6 md3 qa3 Q J6 QIN3 QNEW3 R10c G6_19 G6_20).
  intros regs7 m7 G7_8 G7_9 G7_18 G7_19 G7_23 KP7 J7 MU7 BX3.
  pose proof (cnoA_R_kp regs6 regs7 R6 KP7) as R7. pose proof R7 as (Hsp7 & _).
  pose proof (cnoA_aw_copy L3 A3 m6 md3 m7 qa3 _ _ _ _ HM3 QIN3 MU7 AW6) as AW7.
  pose proof (cnoA_saved_copy L3 A3 m6 md3 m7 qa3 HM3 QIN3 MU7 BY6) as BY7.
  pose proof (cnoA_blk_copy m6 m7 qa3 qa1 MU7 (SEP3 _ _ QIN1b) BX1d) as BX1e.
  pose proof (cnoA_blk_copy m6 m7 qa3 qa2 MU7 (SEP3 _ _ QIN2) BX2b) as BX2c.
  destruct (cno_in_blocks L3 A3 qa3 _ QIN3) as (p3 & Hp3 & Pp3).
  pose proof (cno_ub_blocks L3 A3 p1 _ Hp1c) as QIN1c. rewrite Pp1c in QIN1c.
  pose proof (cno_ub_blocks L3 A3 p2 _ Hp2b) as QIN2b. rewrite Pp2b in QIN2b.
  destruct (cno_block_range B API L3 A3 m6 md3 qa1 _ HM3 QIN1c) as (Hr1a & Hr1b).
  destruct (cno_block_range B API L3 A3 m6 md3 qa2 _ HM3 QIN2b) as (Hr2a & Hr2b).
  destruct (cno_block_range B API L3 A3 m6 md3 qa3 _ HM3 QIN3) as (Hr3a & Hr3b).
  (* the zero run and the first out_of_memory() test *)
  apply (cnoA_zero fx L3 A3 regs7 m7 md3 Q J7 Hsp7 ltac:(rewrite G7_23; exact G6_23)).
  intros regs8 m8 G8_1 G8_8 G8_9 G8_18 G8_19 G8_23 G8_10 G8_11 G8_12 KP8 J8 MU8.
  pose proof (cnoA_R_kp regs7 regs8 R7 KP8) as (Hsp8 & G8_3 & G8_4 & G8_24).
  rewrite Hsp7 in MU8.
  assert (AW8 : alloc_words B m8 (lsum Lam) peak cnt (2 ^ 64 - 1)).
  { apply (cnoA_aw_munch m7 m8 _ _ _ _ _ AW7 MU8). intros a Ha. apply cnoA_out1.
    destruct (cno_statics_free B API HG a Ha) as (_ & Hl & _). lia. }
  assert (BY8 : bytes_at rsegs m8 (spZ regs0 - 72) (cno_saved regs0)).
  { apply (cno_bytes_munch1 m7 m8 _ _ _ _ BY7 MU8). right. lia. }
  assert (BX1f : bytes_at rsegs m8 qa1 x) by (apply (cno_bytes_munch1 m7 m8 _ _ _ _ BX1e MU8); left; lia).
  assert (BX2d : bytes_at rsegs m8 qa2 x) by (apply (cno_bytes_munch1 m7 m8 _ _ _ _ BX2c MU8); left; lia).
  assert (BX3b : bytes_at rsegs m8 qa3 x) by (apply (cno_bytes_munch1 m7 m8 _ _ _ _ BX3 MU8); left; lia).
  (* the join state at the first parse_noting call *)
  apply (KB fx L3 A3 regs8 m8 md3 p1 p2 p3 qa1 qa2 qa3 J8 Hsp8 G8_1 G8_3 G8_4).
  - rewrite G8_8, G7_8. exact G6_8.
  - rewrite G8_9, G7_9. exact G6_9.
  - rewrite G8_18. exact G7_18.
  - rewrite G8_19. exact G7_19.
  - rewrite G8_23, G7_23. exact G6_23.
  - exact G8_24.
  - rewrite G8_10, G7_8. exact G6_8.
  - rewrite G8_11. exact G7_19.
  - rewrite G8_12, Hsp7. reflexivity.
  - exact BY8.
  - exact FZ.
  - exact (cno_ledger_cj B API AX HG L0 A0 regs0 mem0 md0 PRE0 L3 A3 m8 md3 Lam peak cnt (2 ^ 64 - 1) peak cnt
             (2 ^ 64 - 1) LED0 J8 AW8 HPK0 HCT0 ltac:(lia)).
  - exact RF3.
  - exact Hp1c.
  - exact Pp1c.
  - rewrite HS. exact BX1f.
  - exact Hp2b.
  - exact Pp2b.
  - rewrite HS. exact BX2d.
  - exact Hp3.
  - exact Pp3.
  - rewrite HS. exact BX3b.
  - exact QNEW1.
  - exact QNEW2.
  - exact QNEW3.
  - intros q k Hq. split; [|split].
    + exact (cnoA_notA0 L3 A3 m8 md3 p1 qa1 J8 Hp1c Pp1c QNEW1 q k Hq).
    + exact (cnoA_notA0 L3 A3 m8 md3 p2 qa2 J8 Hp2b Pp2b QNEW2 q k Hq).
    + exact (cnoA_notA0 L3 A3 m8 md3 p3 qa3 J8 Hp3 Pp3 QNEW3 q k Hq).
  - intros E. assert (Eq : qa1 = qa2) by congruence. destruct (SEP2 _ _ QIN1); lia.
  - intros E. assert (Eq : qa1 = qa3) by congruence. destruct (SEP3 _ _ QIN1b); lia.
  - intros E. assert (Eq : qa2 = qa3) by congruence. destruct (SEP3 _ _ QIN2); lia.
  - exact INIT3.
Qed.

End Ph.
