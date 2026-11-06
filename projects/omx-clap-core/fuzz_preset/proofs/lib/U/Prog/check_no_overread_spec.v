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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes GIInit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import memcpy_c memset_c same_c pj_parse_c pj_free_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import fuzz_alloc_ran_out_c parse_noting_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_c check_no_overread_seg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import check_no_overread_glue check_no_overread_calls.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* The three phases of check_no_overread (#102 ubsan, entry 0x13868, frame 240) and the states that join them:
   phase A runs from the entry through the three padded copies (0x1448c), the zeroing of the trees and the first
   out_of_memory() test to the first parse_noting call (pc 0x13a38, ra 0x1392c) and ends in cno_KB;
   phase B runs the three readings, each followed by its out_of_memory() test (g_own_ran_out byte, then
   fuzz_alloc_ran_out: both 0), and, when the readings succeed, the two compare calls, up to the first pj_free call
   (pc 0x16340, ra 0x139d8, s3 = ran_out = 0), and ends in cno_KC;
   phase C runs the three tree frees, the three block frees and the return with a0 = s3.
   The trees are at sp + 112, sp + 56 and sp; the nine saved words at sp + 168 .. sp + 240. *)

Definition cno_rv (x : list byte) : Z := match json_read jr_strtod (zb x) with Some _ => 0 | None => -1 end.

Section T.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HS : ms_segs B = rsegs.
Hypothesis AX : AllocExtra B (aa_MR API).

Lemma cno_jump : forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) regs pc m md R' (pc' : word) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs (jump_post R' (@fp_regs fx) pc' (@fp_csr fx) m) (MS (rmk regs) (@fp_regs fx) pc (@fp_csr fx) None m (seg_rom rsegs)) ->
  (forall regs', (forall r, OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs' r = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr R' r) ->
     SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs' pc' m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs pc m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md) P.
Proof.
  intros fx regs pc m md R' pc' P Hh Hl HE HK.
  apply (kb_run B regs pc m md (fun R p m' => R = R' /\ p = pc' /\ m' = m) P Hh Hl).
  - rewrite HS. eapply evt_mono; [exact HE|]. intros ms E. unfold jump_post in E. subst ms.
    exists R', pc', m. split; [reflexivity | auto].
  - intros R p m' regs' (-> & -> & ->) HG. apply HK. exact HG.
Qed.

Lemma cno_foot : forall L A m md Lam pk ct fl p t D,
  aa_MR API L A m md -> ledger B L A m Lam pk ct fl -> pj_node (ms_segs B) m (lin Lam) p t D ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= p -> p + 56 <= 2 ^ 64 ->
  forall z, pj_foot p D z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z /\ (p <= z < p + 56 \/ 4096 <= z < OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling).
Proof.
  intros L A m md Lam pk ct fl p t D HM HL HN Hp1 Hp2 z [Hz | ((a, k) & Hin & Hz)].
  - pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value.
    split; [lia|]. split; [intros Hi; pose proof (cno_img_low B HS z Hi); lia | left; exact Hz].
  - unfold pj_holds in Hz. cbn [fst snd] in Hz.
    pose proof (pj_node_blocks _ t m (lin Lam) p D HN a k Hin) as HinL. unfold lin in HinL.
    destruct (ledger_block_range B API L A m md Lam pk ct fl a k HM HL HinL) as (R1 & R2 & R3).
    pose proof HL as (_ & _ & _ & _ & _ & FA). rewrite Forall_forall in FA.
    destruct (FA (a, k) HinL) as (_ & _ & _ & HNI). cbn [fst snd] in HNI.
    split; [lia|]. split; [|right; lia].
    replace z with (a - 16 + (z - (a - 16))) by lia. apply HNI. lia.
Qed.

Lemma cno_node_norm : forall m L p t D, pj_node (ms_segs B) m L p t D ->
  (forall z, pj_foot p D z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z) ->
  pj_node (ms_segs B) (normalize (ms_segs B) m) L p t D.
Proof.
  intros m L p t D HN HF. apply (pj_node_frame _ t m L (normalize (ms_segs B) m) L p D HN);
    [exact (pj_node_blocks _ t m L p D HN)|].
  intros x Hx. destruct (HF _ Hx) as [Hr Hn]. unfold normalize.
  pose proof (cno_ro_false B HS (bv_unsigned x) Hr Hn) as E. rewrite Z_to_bv_bv_unsigned in E. rewrite HS, E. reflexivity.
Qed.

Lemma cno_node_back : forall mr m0 L p t D, mem_rel (ms_segs B) mr m0 -> pj_node (ms_segs B) m0 L p t D ->
  (forall z, pj_foot p D z -> 0 <= z < 2 ^ 64 /\ ~ in_img B z) ->
  pj_node (ms_segs B) mr L p t D.
Proof.
  intros mr m0 L p t D HR HN HF. apply (pj_node_frame _ t m0 L mr L p D HN);
    [exact (pj_node_blocks _ t m0 L p D HN)|].
  intros x Hx. destruct (HF _ Hx) as [Hr Hn].
  pose proof (cno_ro_false B HS (bv_unsigned x) Hr Hn) as E. rewrite Z_to_bv_bv_unsigned in E.
  symmetry. apply (mem_rel_rw (ms_segs B) mr m0 x HR). rewrite HS. exact E.
Qed.

Lemma cno_word_munch : forall m m' W a v, word_mem (ms_segs B) m a v -> munch W m m' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ outside W z -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= z) -> 0 <= a ->
  a + 8 <= OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling ->
  word_mem (ms_segs B) m' a v.
Proof.
  intros m m' W a v Hw HM HW Ha1 Ha2. pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_lt.
  apply (kb_word_munch (ms_segs B) m m' W a v Hw HM). intros k Hk. split; [lia|].
  destruct (kb_outside_dec W (a + k)) as [Ho|Ho]; [exact Ho|]. exfalso. pose proof (HW (a + k) ltac:(lia) Ho). lia.
Qed.

Lemma cno_ledger_munch : forall L A m md m' W Lam pk ct fl,
  aa_MR API L A m md -> ledger B L A m Lam pk ct fl -> munch W m m' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ outside W z -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling <= z) ->
  ledger B L A m' Lam pk ct fl.
Proof.
  intros L A m md m' W Lam pk ct fl HM HL HMU HW.
  pose proof OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.alloc_ceiling_value as Hac.
  pose proof HL as ((W1 & W2 & W3 & W4) & P & C & F & ND & FA).
  split.
  { unfold alloc_words, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    split; [|split; [|split]]; (eapply cno_word_munch; [eassumption | exact HMU | exact HW | lia | lia]). }
  split; [exact P|]. split; [exact C|]. split; [exact F|]. split; [exact ND|].
  rewrite Forall_forall in FA |- *. intros [a k] Hin. destruct (FA (a, k) Hin) as (Hk & HinB & Hw & HNI).
  cbn [fst snd] in *. destruct (ledger_block_range B API L A m md Lam pk ct fl a k HM HL Hin) as (R1 & R2 & R3).
  split; [exact Hk|]. split; [exact HinB|]. split; [|exact HNI].
  eapply cno_word_munch; [exact Hw | exact HMU | exact HW | lia | lia].
Qed.

Lemma cno_bytes_munch1 : forall m m' lo hi a bs, bytes_at rsegs m a bs -> munch [(lo, hi)] m m' ->
  (a + Z.of_nat (length bs) <= lo \/ hi <= a) -> bytes_at rsegs m' a bs.
Proof.
  intros m m' lo hi a bs HB HM D. eapply bytes_at_transport; [exact HB | exact HM |].
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

End T.

Section S.
Context {rc : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Variable F : ResForm.
Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (Lam : list (Z * Z)) (peak cnt : Z) (b : rf_R F) (data : Z) (x : list byte).

(* The state at the first pj_free call (0x16340, ra 0x139d8, a0 = sp + 0x70), sp = spZ regs0 - 240, s3 = 0 (ran_out).
   Nodes: sp + 112 holds D1, sp + 56 holds D2, sp holds D0 (all the same tree u); g_ran_out = 0.
   bC is the resource bound after the three parses; the last hypothesis says how the three tree frees
   close it into cno_mid. *)
Definition cno_KC : Prop :=
  forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md Lam3 pk q1 q2 q3 one two nul u D1 D2 D0 bC,
  cj B API L0 A0 regs0 mem0 md0 L A m md ->
  spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1 = Z_to_bv 64 0x139d8 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 = Z_to_bv 64 one -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 two -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 = Z_to_bv 64 nul ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19 = Z_to_bv 64 0 ->
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 (spZ regs0 - 240 + 112) ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  Mem.bytes_at (ms_segs B) m G_RAN_OUT (Mem.le1 (Z_to_bv 64 0)) ->
  frm_zero (@fp_csr fx) ->
  ledger B L A m Lam3 pk (cnt + 3 * Z.of_nat (ncalls jr_strtod (zb x))) (2 ^ 64 - 1) -> peak <= pk ->
  Permutation Lam3 (D0 ++ D2 ++ D1 ++ Lam) ->
  pj_node (ms_segs B) m (lin Lam3) (spZ regs0 - 240 + 112) u D1 ->
  pj_node (ms_segs B) m (lin Lam3) (spZ regs0 - 240 + 56) u D2 ->
  pj_node (ms_segs B) m (lin Lam3) (spZ regs0 - 240) u D0 ->
  (depth u <= 32)%nat ->
  (forall a k, In (a, k) (D1 ++ D2 ++ D0) ->
     ~ In (a - 16, k + 16) (blocks L0 A0) /\ (a - 16, k + 16) <> (one, Z.of_nat (length x) + 16) /\
     (a - 16, k + 16) <> (two, Z.of_nat (length x) + 16) /\ (a - 16, k + 16) <> (nul, Z.of_nat (length x) + 16)) ->
  In (q1, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q1 = one ->
  In (q2, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q2 = two ->
  In (q3, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q3 = nul ->
  (forall q k, In (q, k) (user_blocks A0) -> q <> q1 /\ q <> q2 /\ q <> q3) ->
  q1 <> q2 -> q1 <> q3 -> q2 <> q3 ->
  st_init_done A = true ->
  rf_ok F A bC ->
  (forall D1' D2' D3', Permutation D1 D1' -> Permutation D2 D2' -> Permutation D0 D3' ->
     exists E1 E2 E3, cno_dl (cno_tr x) E1 /\ cno_dl (cno_tr x) E2 /\ cno_dl (cno_tr x) E3 /\
       rf_frees F (rf_frees F (rf_frees F bC D1') D2') D3' =
       cno_mid F b (Z.of_nat (length x)) (cno_tr x) (cno_ok x) E1 E2 E3) ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x16340) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md)
    (cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x).

(* The state at the first parse_noting call (0x13a38, ra 0x1392c): s0, s1, s2 hold the three copies one, two, nul
   (blocks q1, q2, q3 of n + 16 bytes holding x), s4 = n, s3 = 1 (ran_out until the compares), s7 = CNO_S7
   (g_own_ran_out + 0x6ac), a0 = one, a1 = n, a2 = sp + 0x70. *)
Definition cno_KB : Prop :=
  forall (fx : OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.FPState) L A regs m md q1 q2 q3 one two nul,
  cj B API L0 A0 regs0 mem0 md0 L A m md ->
  spZ regs = spZ regs0 - 240 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 1 = Z_to_bv 64 0x1392c ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 3 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 3 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 4 = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 4 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 8 = Z_to_bv 64 one -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 9 = Z_to_bv 64 two -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 18 = Z_to_bv 64 nul ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 20 = Z_to_bv 64 (Z.of_nat (length x)) -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 19 = Z_to_bv 64 1 ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 23 = Z_to_bv 64 CNO_S7 ->
  (forall r, 24 <= r <= 27 -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs (Z_to_bv 5 r) = OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs0 (Z_to_bv 5 r)) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 10 = Z_to_bv 64 one -> OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 11 = Z_to_bv 64 (Z.of_nat (length x)) ->
  OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.getr regs 12 = Z_to_bv 64 (spZ regs0 - 240 + 112) ->
  bytes_at rsegs m (spZ regs0 - 72) (cno_saved regs0) ->
  frm_zero (@fp_csr fx) ->
  ledger B L A m Lam peak cnt (2 ^ 64 - 1) ->
  rf_ok F A (cno_b3 F b (Z.of_nat (length x))) ->
  In (q1, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q1 = one -> Mem.bytes_at (ms_segs B) m one x ->
  In (q2, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q2 = two -> Mem.bytes_at (ms_segs B) m two x ->
  In (q3, Z.of_nat (length x) + 16) (user_blocks A) -> ptr_addr L q3 = nul -> Mem.bytes_at (ms_segs B) m nul x ->
  ~ In (one, Z.of_nat (length x) + 16) (blocks L0 A0) -> ~ In (two, Z.of_nat (length x) + 16) (blocks L0 A0) ->
  ~ In (nul, Z.of_nat (length x) + 16) (blocks L0 A0) ->
  (forall q k, In (q, k) (user_blocks A0) -> q <> q1 /\ q <> q2 /\ q <> q3) ->
  q1 <> q2 -> q1 <> q3 -> q2 <> q3 ->
  st_init_done A = true ->
  SR (ms_segs B) (mkCfg (@OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.mkst fx regs (Z_to_bv 64 0x13a38) m (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YK11.seg_rom (ms_segs B))) md)
    (cno_Q B API F L0 A0 regs0 mem0 md0 Lam peak cnt b data x).

End S.
