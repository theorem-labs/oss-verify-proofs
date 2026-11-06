(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of rec_canonical on the ASan build of
   plugin-hostd/fuzz_command, in the shape of cgif_file_fuzzer's walks (lib/A/AC8b.v: a loop walked by the
   symbolic executor over the position-abstract listing, its inline shadow checks removed by tok_load/tok_branch)
   and of this unit's xstrdup walk (the malloc call through amalloc04_sub of PaCall.v).
   The walk is cut at six points: the malloc return (0x89338: the null check, decided by the executor, and the
   empty-line check), the outer head (0x89354), the word-scan head (0x89364), the word start (0x893a0), the copy
   head (0x893e8) and the tail (0x89474); the model of the output is lib/Prog/RecFacts.v's
   canon T = join_sp (words T), and the word lemmas below are the Words section of fuzz_command's own released
   plain proof lib/Prog/rec_canonical.v, copied so that the walk stands on RecFacts alone. The walk's hypotheses are
   the statement's AMALLOC4 and TL (CmdPaLib.v: the malloc trampoline is the rule's entry, the GOT shadow cell). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/rec_canonical.v, with its module paths and module names changed; 696 of its 835 lines of code are new or changed and 2224 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/rec_canonical.v; 1022 of its 1119 lines of code are new or changed and 738 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/chain_words.v, with its module paths and module names changed; 183 of its 219 lines of code are new or changed and 1083 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/CF/verbs_receive_br.v; 267 of its 352 lines of code are new or changed and 134 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_call.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import verbs_receive_br sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecKindB reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma resp_kli : forall (J J' : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (J = 0x17a88 /\ J' = 0x17a8c) \/ (J = 0x178a4 /\ J' = 0x178a8) ->
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-902)) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 J') fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 J) fc None m (seg_rom rsegs)).
Proof.
  intros J J' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m [[-> ->]|[-> ->]]; zstep; apply evt_done; reflexivity.
Qed.

Lemma resp_kjal : forall (J J' : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (J = 0x17a8c /\ J' = 0x17a90) \/ (J = 0x178a8 /\ J' = 0x178ac) \/ (J = 0x176c0 /\ J' = 0x176c4) ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 J') sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 SUP_RESP) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 J) fc None m (seg_rom rsegs)).
Proof.
  intros J J' ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m [[-> ->]|[[-> ->]|[-> ->]]]; zstep; apply evt_done; reflexivity.
Qed.

Section B3.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation VS f := (@vr_state f _ B API S).

Definition ans_ret_ns (K : Z) (Rt : rstate * list byte) (sz : list byte -> list Z) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    Rt = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    CF.RecKindB.fp_kept fx fx' /\
    CF.RecKindB.call_post_rec B MR K L A regs mem md CF.RecKindB.rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ CF.RecKindB.owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    CF.RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ CF.RecKindB.f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    CF.RecKindB.sb_le (CF.RecKindB.sb_shift b A A') (CF.RecKindB.sb_mallocs b (sz t)) /\
    res_ok_slots A' (CF.RecKindB.sb_shift b A A').

Lemma ans_of_ns : forall K Rt sz L A rg mem md O b c',
  ans_ret_ns K Rt sz L A rg mem md O b c' ->
  sb_live (CF.RecKindB.sb_mallocs b (sz (snd Rt))) <= sb_cap (CF.RecKindB.sb_mallocs b (sz (snd Rt))) ->
  ans_post B API K L A rg mem md O b (sz (snd Rt)) Rt c'.
Proof.
  intros K Rt sz L A rg mem md O b c'
    (fx' & L' & A' & rg' & mem' & md' & R' & O' & t & q & -> & E & FPK & POST & A0 & REC & OWN & BLK & INB & FRESH
     & NOQ & BQ & OK & APART & RO & _ & INIT & RLEN & LE & RS) CAP.
  pose proof (vf_segs B API HF) as SEGS. rewrite SEGS in E. cbn [fst snd] in *.
  exists fx', L', A', rg', mem', md', O', q.
  split; [exact E|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A0|]. split; [exact REC|].
  split; [exact OWN|]. split; [exact BLK|]. split; [exact INB|]. split; [exact FRESH|]. split; [exact NOQ|].
  split; [exact BQ|]. split; [exact OK|]. split; [exact APART|]. split; [exact RO|]. split; [exact INIT|].
  split; [exact RLEN|]. exact (CF.RecKindB.res_ok_slots_le A' _ _ LE CAP RS).
Qed.

Definition ans_ret_rm (K : Z) (Rt : rstate * list byte) (sz : list byte -> list Z) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    Rt = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    CF.RecKindB.fp_kept fx fx' /\
    CF.RecKindB.call_post_rec B MR K L A regs mem md CF.RecKindB.rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ CF.RecKindB.owns_new L A O O' /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    CF.RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    ro_agree (ms_segs B) mem' /\ CF.RecKindB.f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    CF.RecKindB.sb_le (CF.RecKindB.sb_shift b A A') (CF.RecKindB.sb_mallocs b (sz t)) /\
    res_ok_slots A' (CF.RecKindB.sb_shift b A A').

Lemma ans_of_rm : forall K Rt sz L A rg mem md O b c',
  ans_ret_rm K Rt sz L A rg mem md O b c' ->
  sb_live (CF.RecKindB.sb_mallocs b (sz (snd Rt))) <= sb_cap (CF.RecKindB.sb_mallocs b (sz (snd Rt))) ->
  ans_post B API K L A rg mem md O b (sz (snd Rt)) Rt c'.
Proof.
  intros K Rt sz L A rg mem md O b c'
    (fx' & L' & A' & rg' & mem' & md' & R' & O' & t & q & -> & E & FPK & POST & A0 & REC & OWN & INB & FRESH
     & NOQ & BQ & OK & BLK & APART & RO & _ & INIT & RLEN & LE & RS) CAP.
  pose proof (vf_segs B API HF) as SEGS. rewrite SEGS in E. cbn [fst snd] in *.
  exists fx', L', A', rg', mem', md', O', q.
  split; [exact E|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A0|]. split; [exact REC|].
  split; [exact OWN|]. split; [exact BLK|]. split; [exact INB|]. split; [exact FRESH|]. split; [exact NOQ|].
  split; [exact BQ|]. split; [exact OK|]. split; [exact APART|]. split; [exact RO|]. split; [exact INIT|].
  split; [exact RLEN|]. exact (CF.RecKindB.res_ok_slots_le A' _ _ LE CAP RS).
Qed.

Lemma post_rec_of_k : forall K L A rg mem md L' A' rg' mem' md' (E excl : Z -> Prop),
  call_post_k B MR K L A rg mem md (fun _ => False) L' A' rg' mem' md' ->
  CF.RecKindB.call_post_rec B MR K L A rg mem md E excl L' A' rg' mem' md'.
Proof.
  intros K L A rg mem md L' A' rg' mem' md' E excl (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|].
  split; [intros a Ha N1 N2 N3 _; exact (H8 a Ha N1 N2 N3 (fun x => x))|].
  split; [intros p n i X1 X2 _ Hi; exact (H9 p n i X1 X2 Hi)|].
  exact H10.
Qed.

Definition resp_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (code : Z) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' q,
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    CF.RecKindB.fp_kept fx fx' /\
    call_post_k B MR SUP_RESP_K L A regs mem md (fun _ => False) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\ q <> 0 /\ q mod 16 = 0 /\
    fresh_block B q (Z.of_nat (length (resp code)) + 1) /\
    (exists b1 b2, blocks L' A' = b1 ++ (q, Z.of_nat (length (resp code)) + 1) :: b2 /\ blocks L A = b1 ++ b2) /\
    blocks_kept B L A mem mem' (fun _ => False) /\
    (forall p k, In (p, k) (user_blocks A) -> In (p, k) (user_blocks A')) /\
    Mem.bytes_at (ms_segs B) mem' q (resp code ++ [Z_to_bv 8 0]) /\
    (forall R O, g_rec_rep (ms_segs B) L A mem R O -> g_rec_rep (ms_segs B) L' A' mem' (fst (sup_resp_m R code)) O) /\
    ro_agree (ms_segs B) mem' /\ CF.RecKindB.f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (sb_malloc b (Z.of_nat (length (resp code)) + 1)).

Lemma resp_of : forall L A rg mem md R O code b c',
  g_rec_rep (ms_segs B) L A mem R O -> resp_ret L A rg mem md code b c' ->
  ans_post B API SUP_RESP_K L A rg mem md O b [Z.of_nat (length (resp code)) + 1] (sup_resp_m R code) c'.
Proof.
  intros L A rg mem md R O code b c' REC
    (fx' & L' & A' & rg' & mem' & md' & q & E & FPK & POST & A0 & _ & _ & FRESH & (b1 & b2 & E1 & E2) & _ & UB
     & BQ & RT & RO & _ & INIT & RLEN & RES).
  pose proof (vf_segs B API HF) as SEGS. pose proof (aa_laws API) as LAWS.
  pose proof POST as (HM' & _ & _ & _ & HPA & _ & _ & _ & HUB & _).
  assert (DJ : forall a k, In (a, k) (blocks L A) ->
                 a + k <= q \/ q + (Z.of_nat (length (resp code)) + 1) <= a).
  { intros a k Hin. rewrite E2 in Hin.
    exact (CF.RecKindB.blocks_mid_disjoint B MR LAWS L' A' mem' md' b1 b2 q _ a k HM' E1 Hin). }
  rewrite SEGS in E. pose proof (RT R O REC) as REC'.
  unfold sup_resp_m in *. cbn [fst snd] in *.
  exists fx', L', A', rg', mem', md', O, q. cbn [fst snd].
  split; [exact E|]. split; [exact FPK|]. split; [exact (post_rec_of_k _ _ _ _ _ _ _ _ _ _ _ _ _ POST)|].
  split; [exact A0|]. split; [exact REC'|].
  split; [intros pn Hpn; left; exact Hpn|].
  split.
  { intros pn Hin. rewrite E1 in Hin. apply in_app_or in Hin. destruct Hin as [Hin|[Hin|Hin]].
    - destruct (in_dec CF.RecTail.pair_dec pn O) as [Ho|Ho]; [right; left; exact Ho|].
      left. split; [rewrite E2; apply in_or_app; left; exact Hin | exact Ho].
    - right; right. symmetry. exact Hin.
    - destruct (in_dec CF.RecTail.pair_dec pn O) as [Ho|Ho]; [right; left; exact Ho|].
      left. split; [rewrite E2; apply in_or_app; right; exact Hin | exact Ho]. }
  split; [rewrite E1; apply in_or_app; right; left; reflexivity|].
  split; [exact FRESH|].
  split.
  { intros Hin. apply in_map_iff in Hin as ([a k] & Ea & Hk). cbn [fst] in Ea. subst a.
    destruct (CF.reply.rec_rep_O _ _ _ _ _ _ _ _ REC (q, k) Hk) as [Hb Hk1].
    destruct (DJ q k Hb) as [D1|D1]; cbn [snd] in Hk1; lia. }
  split; [exact BQ|].
  split.
  { intros p k Hp _. split; [exact (UB p k Hp)|]. split; [exact (HPA p k Hp (UB p k Hp))|].
    intros i Hi. exact (HUB p k i Hp (UB p k Hp) Hi). }
  split.
  { intros p k Hp _. destruct (DJ (ptr_addr L p) k (CF.RecTail.user_in_blocks L A p k Hp)); lia. }
  split; [exact RO|]. split; [exact INIT|]. split; [exact RLEN|]. exact RES.
Qed.

Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.

Lemma call_resp : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c ret code P,
  VS fx rg SUP_RESP mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  getr rg 10 = Z_to_bv 64 code -> -2 ^ 31 <= code < 2 ^ 31 -> (k1 + 1 <= 32)%nat ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' q c',
     VS fx' rg' ret mem' md' L' A' R1 O' (k1 + 1) qv
       (Some (q, Z.of_nat (length (resp code)) + 1, resp code)) jk c' ->
     getr rg' 10 = Z_to_bv 64 q -> regs_preserved rg rg' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS SRESP.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c ret code P HST E1 RET E10 HC HK KONT.
  pose proof (vf_segs B API HF) as SEGS.
  assert (KR : 0 <= SUP_RESP_K <= 14336) by (split; apply Z.leb_le; vm_compute; reflexivity).
  destruct (vs_pre B API HF S HS rg SUP_RESP mem1 md1 L1 A1 R1 O1 k1 qv None jk c SUP_RESP_K ret HST E1 RET KR)
    as (PRE & SPR & FZ & F18 & RO & REC & HM & _).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST))))) as (RES & _).
  pose proof (resp_length code HC) as RL.
  assert (HSZ : Forall (fun n => 0 <= n <= 8194) [Z.of_nat (length (resp code)) + 1])
    by (apply Forall_cons; [lia | apply Forall_nil]).
  assert (HKS : (k1 + length [(Z.of_nat (length (resp code)) + 1)%Z] <= 32)%nat) by (cbn [length]; lia).
  pose proof (st_room B API S HS k1 _ (Z.of_nat (length (resp code)) + 1) HKS HSZ ltac:(lia)) as ROOM.
  pose proof HST as (EC & _). subst c.
  apply (call_ans B API HF S HS rg SUP_RESP mem1 md1 L1 A1 R1 O1 k1 qv jk _ SUP_RESP_K ret
           [Z.of_nat (length (resp code)) + 1] (sup_resp_m R1 code) P HST E1 KR HKS HSZ).
  - rewrite <- SEGS. eapply SR_mono.
    + exact (SRESP fx L1 A1 rg mem1 md1 code (sb_n (s_b S) k1) PRE E10 HC RO FZ F18 RES ROOM).
    + intros c'' HR. exact (resp_of L1 A1 rg mem1 md1 R1 O1 code (sb_n (s_b S) k1) c'' REC HR).
  - intros f' rg' mem' md' L' A' O' q c' HST2 E10' HP2. exact (KONT f' rg' mem' md' L' A' O' q c' HST2 E10' HP2).
Qed.

End B3.

Section B4.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma resp_join : forall rg0 R0 k0 qv (qt : bool) J J' rg mem md L A R O k jk c code P,
  (J = 0x17a8c /\ J' = 0x17a90) \/ (J = 0x178a8 /\ J' = 0x178ac) \/ (J = 0x176c0 /\ J' = 0x176c4) ->
  VS fx rg J mem md L A R O k (if qt then 1 else qv) None jk c ->
  getr rg 10 = Z_to_bv 64 code -> -2 ^ 31 <= code < 2 ^ 31 ->
  getr rg 18 = getr rg0 18 -> (J = 0x17a8c -> getr rg 21 = getr rg0 21) ->
  VerbsRun.run_step sup_reply_code_c.reply_code R0
    (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, resp code, qt) ->
  (k0 <= k)%nat -> (k + 1 <= k0 + 8)%nat -> (k0 + 8 <= 32)%nat ->
  join_k B API S J' 10 rg0 R0 k0 qv P ->
  SR rsegs c P.
Proof using HF HS SRESP.
  intros rg0 R0 k0 qv qt J J' rg mem md L A R O k jk c code P HJ HST E10 HC E18 E21 RUN HK1 HK2 HK8 JOIN.
  pose proof HST as (_ & _ & VR & _).
  eapply (@ka_nw fx rc B API HF S HS rg J mem md L A R O k (if qt then 1 else qv) None jk c _ P HST).
  { unfold Regs6ss.mkR_of. apply (resp_kjal J J'). exact HJ. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK SUP_RESP eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  assert (E1' : getr rg' 1 = Z_to_bv 64 J') by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
  assert (E10' : getr rg' 10 = Z_to_bv 64 code) by (rewrite (getr_of_eqv _ _ 10 X eq_refl); exact E10).
  assert (RET : YK0s.ret_ok (Z_to_bv 64 J'))
    by (destruct HJ as [[_ ->]|[[_ ->]|[_ ->]]]; apply bv_eq; vm_compute; reflexivity).
  apply (call_resp B API HF S HS SRESP rg' mem2 md L A R O k (if qt then 1 else qv) jk _ J' code P HST1 E1' RET E10' HC
           ltac:(lia)).
  intros f' rg'' mem' md' L' A' O' q c' HST2 E10'' HP2.
  eapply JOIN. exists qt.
  split; [exact HST2|]. split; [exact E10''|].
  split; [exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (eq_trans (PR 18 ltac:(unfold callee_saved; lia)) E18))|].
  split.
  { intros HJ'. assert (EJ : J = 0x17a8c) by (destruct HJ as [[-> ->]|[[-> ->]|[-> ->]]]; lia).
    exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (eq_trans (PR 21 ltac:(unfold callee_saved; lia)) (E21 EJ))). }
  split; [exact RUN | lia].
Qed.

Lemma rej_join : forall rg0 R0 k0 qv J J' rg mem md L A O k jk c P,
  (J = 0x17a88 /\ J' = 0x17a90) \/ (J = 0x178a4 /\ J' = 0x178ac) ->
  vr_rej B API S fx J rg0 R0 k0 qv rg mem md L A O k jk c ->
  (k0 + 8 <= 32)%nat -> join_k B API S J' 10 rg0 R0 k0 qv P ->
  SR rsegs c P.
Proof using HF HS SRESP.
  intros rg0 R0 k0 qv J J' rg mem md L A O k jk c P HJ (HST & E18 & E21 & PL & ->) HK8 JOIN.
  pose proof HST as (_ & _ & VR & _).
  set (J1 := J + 4).
  assert (HJ1 : (J = 0x17a88 /\ J1 = 0x17a8c) \/ (J = 0x178a4 /\ J1 = 0x178a8))
    by (unfold J1; destruct HJ as [[-> _]|[-> _]]; [left | right]; split; reflexivity).
  eapply (@ka_nw fx rc B API HF S HS rg J mem md L A R0 O k0 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. apply (resp_kli J J1). exact HJ1. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK J1 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (resp_join rg0 R0 k0 qv false J1 J' rg' mem2 md L A R0 O k0 jk _ (-902) P).
  - destruct HJ as [[-> ->]|[-> ->]]; [left | right; left]; split; reflexivity.
  - exact HST1.
  - rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity.
  - lia.
  - exact (eq_trans (PR 18 ltac:(unfold callee_saved; lia)) E18).
  - intros _. exact (eq_trans (PR 21 ltac:(unfold callee_saved; lia)) E21).
  - rewrite PL. reflexivity.
  - lia.
  - lia.
  - exact HK8.
  - exact JOIN.
Qed.

End B4.

Section B5.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation VS f := (@vr_state f _ B API S).

Lemma ka_w : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c (W : list (Z * Z)) (QQ : machine_state -> Prop) P,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  (forall x, 0 <= x < 2 ^ 64 -> ~ (spZ (s_regs S) - VR_K <= x < s_spf S) -> Frame.outside W x) ->
  evt rsegs (fun ms' => QQ ms' /\ exists R' pc' m', ms' = MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs) /\
                 munch W (normalize rsegs mem1) m' /\ wmono rsegs (normalize rsegs mem1) m')
    (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' pc' m' rg' mem2, QQ (MS R' fp_regs pc' fp_csr None m' (seg_rom rsegs)) -> Regs6ss.xregs_eqv R' rg' ->
     (forall pz, pc' = Z_to_bv 64 pz -> vregs S rg' ->
        VS fx rg' pz mem2 md1 L1 A1 R1 O1 k1 qv xq jk (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1)) ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof using HF HS.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P HST WO EVT K.
  pose proof HST as (_ & FPK & _ & _ & FR & GQ & GW).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  apply (ka_bridge B API HF S HS rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c W QQ P HST).
  - intros x Hx H1 _. apply WO; [exact Hx|]. unfold s_spf. lia.
  - exact EVT.
  - intros R' pc' m' mem2 rg' HQ X _ MU _ H2.
    apply (K R' pc' m' rg' mem2 HQ X). intros pz Epz VR'. subst pc'.
    assert (KP : forall a, s_spf S <= a < s_spf S + 608 \/ G_QUIT <= a < G_QUIT + 4 ->
              mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha. assert (Ra : 0 <= a < 2 ^ 64) by (unfold s_spf, G_QUIT, VR_K in *; lia).
      assert (Oa : Frame.outside W a) by (apply WO; [exact Ra | unfold s_spf, G_QUIT, VR_K in *; lia]).
      split; [exact (munch_mbyte rsegs W mem1 mem2 a MU Ra Oa) | exact (munch_writable rsegs W mem1 mem2 a MU Ra Oa)]. }
    split; [reflexivity|]. split; [exact FPK|]. split; [exact VR'|]. split; [exact H2|].
    split.
    + apply (vfr_keep B API S HS mem1 mem2 jk); [|exact FR]. intros a Ha. apply KP. left. exact Ha.
    + apply (gq_transfer mem1 mem2 qv); [|exact GQ|exact GW]. intros i Hi. apply KP. right. lia.
Qed.

End B5.
