(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module paths, addresses and numbers changed; 2641 of its 2742 lines of code are new or changed and 1015 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/Prog/sup_host_setting.v, with its module paths, module names, addresses and numbers changed; 447 of its 509 lines of code are new or changed and 2680 lines of the source are left out. *)
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP Image.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0 AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c RecKindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM06 YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require RecAns.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecSeq RecStep RecGlue RecAnsB RecTail RecStubU.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c record_c arg_s_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import rec_shape_of_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require sup_remove.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import SupChainUA sup_chain_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma scb_no0 : forall ids, no0 (dec_list ids).
Proof.
  intros [|i r]; cbn [dec_list]; [intros H; destruct H|].
  apply no0_app; [apply dec_no0|].
  induction r as [|v r IH]; cbn [map concat]; [intros H; destruct H|].
  apply no0_app; [|exact IH].
  change (SPACE :: dec v) with ([SPACE] ++ dec v).
  apply no0_app; [apply no0_nz; vm_compute; reflexivity | apply dec_no0].
Qed.

Lemma scb_verb : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x104fc (str_bytes "chain"%string).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | cbn; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma scb_shape : shape_find shape_rows (str_bytes "chain"%string) = 0x10417.
Proof. vm_compute. reflexivity. Qed.

Lemma scb_run0 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 e : word),
  rw_cells rsegs m (bv_unsigned sp0 + -128) [C8 e] -> 128 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16f58) (Z_to_bv 64 (bv_unsigned sp0 + -128)) gp tp t0 t1 t2 e s1 e s3
                                      a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x161c4) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -128)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f48) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 e FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 4 step.
  apply evt_done. reflexivity.
Qed.

Lemma scb_run1 :
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x16f60) sp gp tp t0 t1 t2 s0 s1 s3 a1 a2 a3 a4 a5 a6 a7
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                 F (Z_to_bv 64 0x18ad0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f58) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 2 step.
  apply evt_done. reflexivity.
Qed.

Lemma scb_run2 : rec_shape_of_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 64 <= bv_unsigned sp -> 0x34100 <= lo ->
  bytes_at rsegs m G_SHAPES g_shapes_bytes -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m' (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       ms' = MS (mkR (Z_to_bv 64 0x16f80) sp gp tp t0' t1' t2' s0 s1 s0 (Z_to_bv 64 0x10417) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 0x16310) fc None m' (seg_rom rsegs)
       /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f60) fc None m (seg_rom rsegs)).
Proof.
  intros RSO ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo ST LO LO2 GS MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  do 4 step.
  eapply evt_cut.
  { eapply RSO with (lo := lo) (v := str_bytes "chain"%string).
    - exact MI.
    - exact ST.
    - unfold REC_SHAPE_OF_FRAME. lia.
    - exact GS.
    - left. unfold REC_SHAPE_OF_FRAME, G_SHAPES. lia.
    - rewrite unsigned_lit by lia. reflexivity.
    - intros _. rewrite unsigned_lit by lia. split; [exact (scb_verb m MI)|].
      left. unfold REC_SHAPE_OF_FRAME. rewrite ?unsigned_lit by lia. lia. }
  intros ms2 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2
    & MI2 & ST2).
  unfold REC_SHAPE_OF_FRAME in MU2.
  rewrite (ret_pc_even 0x16f70) by lia. rewrite scb_shape.
  do 4 step.
  apply evt_done.
  exists m2, t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6'.
  split; [reflexivity|]. split; [exact MU2 | exact WM2].
Qed.

Lemma scb_run3 :
  forall ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (sp0 q27 q26 q25 q24 q23 q22 q21 q20 q19 q18 q9 q8 q1 : word),
  rw_cells rsegs m (bv_unsigned sp0 + -104)
    [C8 q27; C8 q26; C8 q25; C8 q24; C8 q23; C8 q22; C8 q21; C8 q20; C8 q19; C8 q18; C8 q9; C8 q8; C8 q1] ->
  128 <= bv_unsigned sp0 ->
  evt rsegs (fun ms' => ms' = MS (mkR q1 sp0 gp tp t0 t1 t2 q8 q9 a0 a1 a2 a3 a4 a5 a6 a7
                                      q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
                                 F (ret_pc q1) fc None m (seg_rom rsegs))
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp0 + -128)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16f80) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp0 q27 q26 q25 q24 q23 q22 q21 q20 q19 q18 q9 q8 q1 FR SPR.
  pose proof (bv_unsigned_in_range 64 sp0) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  do 15 step.
  replace (Z_to_bv 64 (bv_unsigned sp0 + -128 + 128)) with sp0
    by (replace (bv_unsigned sp0 + -128 + 128) with (bv_unsigned sp0) by ring; symmetry; apply Z_to_bv_bv_unsigned).
  apply evt_done. reflexivity.
Qed.

Section Back.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GFACT : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis GOWN : forall L A mem md a, aa_MR API L A mem md -> in_globals frame_G a -> ~ owned B L A a.
Hypothesis RIMG : forall a, in_globals frame_RELRO a ->
  in_img B a /\ ~ static_owned B a /\ ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\
  ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : AllocExtra B (aa_MR API).
Hypothesis CTX : ctx_owned B API.
Hypothesis SLACK : block_slack_present B API.
Hypothesis GOTG : ms_got_guard B = 0x22d40.
Hypothesis GRD : ms_guard B = 0x54730.
Hypothesis FREE_PC : ms_free B = 0x18ad0.
Hypothesis FREE : forall fx0 : YK11.FPState, free_contract (fx := fx0) B API.
Hypothesis ARGS : forall fx0 : YK11.FPState, @arg_s_contract fx0 rc B API.
Hypothesis RSO : rec_shape_of_contract.
Hypothesis ANS : forall fx0 : YK11.FPState, @answer_contract fx0 rc B API.

Definition scu_ret (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (id : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    sup_chain_m R id ids = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    fp_kept fx fx' /\
    call_post_rec B (aa_MR API) SUP_CHAIN_K L A regs mem md rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ owns_new L A O O' /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    Mem.bytes_at (ms_segs B) mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    ro_agree (ms_segs B) mem' /\ f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    sb_le (sb_shift b A A') (sb_mallocs b (sup_chain_sizes id ids t)) /\
    res_ok_slots A' (sb_shift b A A').

Lemma scb_relro : forall i, 0 <= i < 448 -> in_globals frame_RELRO (G_SHAPES + i).
Proof. intros i Hi. exists 0x226b0, 1680. split; [left; reflexivity | unfold G_SHAPES; lia]. Qed.

Lemma scb_rjr_shapes : forall K S O L A mem md Lc Ac mc mdc,
  rjr B (aa_MR API) K S rec_area (fun pn => In pn O) L A mem md Lc Ac mc mdc ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes ->
  bytes_at rsegs mc G_SHAPES g_shapes_bytes.
Proof using SEGS RIMG.
  intros K S O L A mem md Lc Ac mc mdc RJ BS. pose proof alloc_ceiling_val as AC.
  destruct (rjr_bounds B _ K S rec_area _ L A mem md Lc Ac mc mdc RJ) as (HK1 & HK2 & HK3).
  destruct RJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _).
  assert (GL : length g_shapes_bytes = 448%nat) by (vm_compute; reflexivity).
  apply (bytes_at_transfer rsegs mem); [exact BS|]. intros i Hi. rewrite GL in Hi.
  pose proof (scb_relro i ltac:(lia)) as RL.
  destruct (RIMG _ RL) as (I1 & I2 & I3 & I4).
  pose proof (in_img_low B SEGS _ I1) as IL.
  assert (NS : ~ (S - K <= G_SHAPES + i < S)) by lia.
  assert (NR : ~ rec_area (G_SHAPES + i))
    by (unfold rec_area, REC_SC, SC_SIZE, G_REC, REC_SIZE, G_SHAPES; lia).
  rewrite <- SEGS. exact (proj1 (HF _ (or_intror (conj I1 (conj I2 I3))) NS I4 NR)).
Qed.

Lemma scu_back : forall L A regs mem md (id : Z) (ids : list Z) (R : rstate) (O : list (Z * Z)) b
    (fx' : YK11.FPState) R' m' Lc Ac mdc Oc lp b1,
  call_pre_t B API SUP_CHAIN_K L A regs mem md ->
  (1 <= length ids <= 62)%nat -> Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
  bytes_at rsegs mem G_SHAPES g_shapes_bytes -> g_rec_rep rsegs L A mem R O ->
  room_slots (sb_mallocs b (sup_chain_sizes id ids (snd (sup_chain_m R id ids)))) 745 ->
  fp_kept fx fx' ->
  sinvx B API SUP_CHAIN_K (spZ regs) L A mem md O Lc Ac m' mdc
    (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids))]) Oc b (lp, 12 * Z.of_nat (length ids) + 1) ->
  bytes_at rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0]) ->
  getr R' 2 = Z_to_bv 64 (spZ regs - 128) -> getr R' 3 = getr regs 3 -> getr R' 4 = getr regs 4 ->
  getr R' 19 = Z_to_bv 64 lp ->
  st_init_done Ac = true ->
  sb_le b1 b ->
  sb_shift b A Ac = sb_malloc (sb_malloc (sb_malloc b1 (12 * Z.of_nat (length ids) + 1))
                      (Z.of_nat (length (dec id)) + 1)) (Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1) ->
  rw_cells rsegs m' (spZ regs - 128) [C8 (Z_to_bv 64 (rec_entry G_REC REC_SC R))] ->
  rw_cells rsegs m' (spZ regs - 104) [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24);
    C8 (getr regs 23); C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
    C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)] ->
  SR rsegs (mkCfg (@mkst fx' R' (Z_to_bv 64 0x16f48) m' (seg_rom rsegs)) mdc)
    (scu_ret L A regs mem md id ids R O b).
Proof using SEGS ERRNO_LOW GFACT GOWN RIMG AX CTX SLACK GOTG GRD FREE_PC FREE ARGS RSO ANS.
  intros L A regs mem md id ids R O b fx' R' m' Lc Ac mdc Oc lp b1 PRE HN HF GS GR ROOM FK SI BX E2 E3 E4 E19 INI
    BLE1 EQB FR0 FR1.
  pose proof (aa_laws API) as LAWS. pose proof alloc_ceiling_val as AC. pose proof wx_apart_rsegs as WX.
  pose proof ERRNO_LOW as EL.
  pose proof PRE as (PRK & HTS).
  pose proof PRK as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  change SUP_CHAIN_K with 12512 in *.
  pose proof GR as (Q0 & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HCODE & _) & _) & _).
  pose proof (rec_rep_calls_le _ _ _ _ _ _ _ _ GR) as H16.
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  assert (NE : ids <> []) by (intros E; rewrite E in HN; cbn in HN; lia).
  pose proof (sc_dec_list_len ids NE HF) as DLL.
  change (snd (sup_chain_m R id ids)) with
    (snd (rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
      (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true)) in ROOM.
  rewrite sch_mallocs_split in ROOM.
  assert (LT : (length (snd (rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
                  (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true)) <= 16)%nat).
  { pose proof (sup_remove.srm_stub_len R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids]
                  (daemon_shape "chain") true HCODE) as H.
    assert (LX : (length (daemon_shape "chain") <= 16)%nat) by (apply Nat.leb_le; vm_compute; reflexivity).
    lia. }
  set (z := 12 * Z.of_nat (length ids) + 1) in *.
  set (e := rec_entry G_REC REC_SC R) in *.
  assert (ZX : Z.of_nat (length (dec_list ids)) + 1 <= z) by (unfold z; lia).
  pose proof SI as (RJ & GRc & ON & B1 & B2 & RA & F18 & RS & LIN & LNO & LOC).
  pose proof RJ as (HM & _).
  destruct (mr_model B _ LAWS Lc Ac m' mdc HM) as (Hh & Hl & _).
  destruct (rjr_bounds B _ 12512 (bv_unsigned sp) rec_area _ L A mem md Lc Ac m' mdc RJ) as (HK1 & HK2 & HK3).
  destruct (block_facts B _ LAWS Lc Ac m' mdc lp z 0 HM LIN ltac:(unfold z; lia)) as (_ & LP4 & LPC & _).
  replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) in FR0 by ring.
  replace (bv_unsigned sp - 128) with (bv_unsigned sp + -128) in E2 by ring.
  replace (bv_unsigned sp - 104) with (bv_unsigned sp + -104) in FR1 by ring.
  set (cs := [C8 (getr regs 27); C8 (getr regs 26); C8 (getr regs 25); C8 (getr regs 24); C8 (getr regs 23);
              C8 (getr regs 22); C8 (getr regs 21); C8 (getr regs 20); C8 (getr regs 19); C8 (getr regs 18);
              C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]) in FR1.
  assert (CS : Z.of_nat (cells_size cs) = 104) by reflexivity.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp - 128)
    by (rewrite unsigned_lit by lia; ring).
  assert (MOD : (bv_unsigned sp - 128) mod 16 = 0).
  { replace (bv_unsigned sp - 128) with (bv_unsigned sp + (-8) * 16) by ring. rewrite Z.mod_add by lia. exact HAL. }
  assert (Q2 : reg_get R' 2 = Z_to_bv 64 (bv_unsigned sp + -128)) by exact E2.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q2.
    eapply scb_run0; [exact FR0 | lia]. }
  intros ms1 (can1 & Q1 & EQ1). subst can1.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ1 eq_refl eq_refl) as (R1 & -> & X1). clear EQ1.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x16f58) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_3 : getr R1 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X1 eq_refl); simp_regs; exact E3).
  assert (E1_4 : getr R1 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; exact E4).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_11 : getr R1 11 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 11 X1 eq_refl); simp_regs; exact E19).
  assert (E1_19 : getr R1 19 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 19 X1 eq_refl); simp_regs; exact E19).
  assert (SP1 : spZ R1 = bv_unsigned sp - 128) by (unfold spZ; rewrite E1_2; exact SPU).
  assert (SRC : arg_s_src B Lc Ac (spZ R1) m' lp (Some (dec_list ids))).
  { rewrite SP1. cbn [arg_s_src]. rewrite SEGS.
    set (pad := (- (lp + Z.of_nat (length (dec_list ids)) + 1)) mod 8).
    assert (PADR : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
    assert (PADA : (lp + Z.of_nat (length (dec_list ids)) + 1 + pad) mod 8 = 0).
    { unfold pad. rewrite Zplus_mod_idemp_r.
      replace (lp + Z.of_nat (length (dec_list ids)) + 1 + - (lp + Z.of_nat (length (dec_list ids)) + 1)) with 0
        by ring.
      reflexivity. }
    assert (LX1 : Z.of_nat (length (dec_list ids ++ [Z_to_bv 8 0])) = Z.of_nat (length (dec_list ids)) + 1)
      by (rewrite length_app; cbn [length]; lia).
    destruct (rs_bytes_pad rsegs m' lp (dec_list ids ++ [Z_to_bv 8 0]) (Z.to_nat pad) BX) as (sl & SL & BS').
    { rewrite LX1, Z2Nat.id by lia. lia. }
    { intros j Hj. rewrite LX1.
      assert (Hj' : Z.of_nat j < pad) by lia.
      assert (PRc : present m' (lp + (Z.of_nat (length (dec_list ids)) + 1) + Z.of_nat j)).
      { destruct (Z_lt_ge_dec (Z.of_nat (length (dec_list ids)) + 1 + Z.of_nat j) z) as [Hlt|Hge].
        - replace (lp + (Z.of_nat (length (dec_list ids)) + 1) + Z.of_nat j)
            with (lp + (Z.of_nat (length (dec_list ids)) + 1 + Z.of_nat j)) by ring.
          exact (proj1 (block_facts B _ LAWS Lc Ac m' mdc lp z (Z.of_nat (length (dec_list ids)) + 1 + Z.of_nat j)
                          HM LIN ltac:(lia))).
        - apply (SLACK Lc Ac m' mdc lp z _ HM LIN). split; [lia|].
          clear -PADA Hj' Hge PADR ZX. Z.div_mod_to_equations. lia. }
      destruct PRc as [bb E]. unfold mbyte. rewrite E. discriminate. }
    rewrite <- app_assoc in BS'. cbn [app] in BS'.
    split; [lia|]. split; [apply scb_no0|]. split; [unfold LMAX; lia|]. exists sl.
    split; [exact BS'|].
    split; [rewrite SL, Z2Nat.id by lia; lia|].
    split; [left; rewrite length_app; cbn [length]; rewrite SL; unfold ARG_S_K, XMALLOC_K, ALLOC_STACK; lia|].
    right. left. exists lp, z. split; [exact LIN | lia]. }
  assert (ROOM1 : room_slots (sb_malloc (sb_shift b A Ac) (Z.of_nat (length (dec_list ids)) + 1))
                    (Z.of_nat (length (dec_list ids)) + 1)).
  { eapply room_slots_mono; [| | exact ROOM].
    - eapply sb_le_trans; [|apply sb_le_malloc; lia]. eapply sb_le_trans; [|apply sb_le_malloc; lia].
      rewrite EQB. unfold sb_mallocs. cbn [fold_left]. repeat apply sb_malloc_mono. exact BLE1.
    - lia. }
  apply (sinvx_arg_sn (fx := fx') B API SEGS ERRNO_LOW GFACT GOWN AX (ARGS fx') 12512 (bv_unsigned sp) L A mem md O
           Lc Ac m' mdc R REC_CHAIN [dec id; dec (Z.of_nat (length ids))] Oc b (lp, z) R1 lp (Some (dec_list ids)) _
           SI ltac:(cbn; lia)).
  { rewrite E1_1. apply bv_eq. vm_compute. reflexivity. }
  { rewrite SP1. exact MOD. }
  { rewrite SP1. unfold ARG_S_K, XMALLOC_K, ALLOC_STACK. lia. }
  { rewrite SP1. lia. }
  { rewrite E1_4. exact HTP. }
  { exact E1_10. }
  { exact E1_11. }
  { exact SRC. }
  { exact ROOM1. }
  intros L2 A2 R2 m2 md2 p SI2 EQB2 INI2 PR2 KST2.
  rewrite E1_1.
  cbn [app sarg] in SI2, EQB2.
  pose proof SI2 as (RJ2 & _ & _ & _ & _ & RA2 & _ & _ & LIN2 & _).
  pose proof RJ2 as (HM2 & _).
  destruct (mr_model B _ LAWS L2 A2 m2 md2 HM2) as (Hh2 & Hl2 & _).
  assert (E2_2 : getr R2 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by exact (eq_trans (PR2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_3 : getr R2 3 = getr regs 3) by exact (eq_trans (PR2 3 ltac:(unfold callee_saved; lia)) E1_3).
  assert (E2_4 : getr R2 4 = getr regs 4) by exact (eq_trans (PR2 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : getr R2 8 = Z_to_bv 64 e) by exact (eq_trans (PR2 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_19 : getr R2 19 = Z_to_bv 64 lp) by exact (eq_trans (PR2 19 ltac:(unfold callee_saved; lia)) E1_19).
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. eapply scb_run1. }
  intros ms3 (can3 & Q3 & EQ3). subst can3.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ3 eq_refl eq_refl) as (R3 & -> & X3). clear EQ3.
  assert (E3_1 : getr R3 1 = Z_to_bv 64 0x16f60) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); simp_regs; reflexivity).
  assert (E3_2 : getr R3 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by (rewrite (getr_of_eqv _ _ 2 X3 eq_refl); simp_regs; exact E2_2).
  assert (E3_3 : getr R3 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X3 eq_refl); simp_regs; exact E2_3).
  assert (E3_4 : getr R3 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X3 eq_refl); simp_regs; exact E2_4).
  assert (E3_8 : getr R3 8 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 8 X3 eq_refl); simp_regs; exact E2_8).
  assert (E3_10 : getr R3 10 = Z_to_bv 64 lp) by (rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; exact E2_19).
  assert (SP3 : spZ R3 = bv_unsigned sp - 128) by (unfold spZ; rewrite E3_2; exact SPU).
  pose proof LIN2 as LIN'. unfold blocks in LIN'. apply in_map_iff in LIN' as ([q z'] & Eq & HQ).
  cbn in Eq. injection Eq as HLP HZ'. subst z'.
  assert (CP3 : call_pre B (aa_MR API) L2 A2 R3 m2 md2).
  { apply (proj2 (call_pre_k_alloc B (aa_MR API) L2 A2 R3 m2 md2)).
    apply (call_pre_k_of_rjr B _ 12512 (bv_unsigned sp) rec_area _ L A mem md L2 A2 m2 md2 ALLOC_STACK R3 RJ2).
    - rewrite E3_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP3. exact MOD.
    - unfold ALLOC_STACK. lia.
    - rewrite SP3. unfold ALLOC_STACK. lia.
    - rewrite SP3. lia.
    - rewrite E3_4. exact HTP. }
  apply (sch_free (fx := fx') B API SEGS ERRNO_LOW GFACT GOWN AX GOTG GRD FREE_PC (FREE fx') 12512 (bv_unsigned sp) L A
           mem md O L2 A2 m2 md2 _ _ b q lp z R3 _ SI2 CP3
           ltac:(rewrite SP3; unfold ALLOC_STACK; lia) ltac:(rewrite SP3; lia) ltac:(unfold z; lia) HQ HLP E3_10 INI2).
  intros L3 A3 R4 m3 md3 SI3 POST3 EQ3.
  rewrite E3_1.
  pose proof POST3 as (PM3 & _ & _ & _ & _ & PR3 & _ & PF3 & _).
  rewrite SEGS in PF3.
  pose proof SI3 as (RJ3 & _ & _ & _ & _ & RA3 & _ & _).
  pose proof RJ3 as (HM3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSC3 & _).
  rewrite SEGS in HSC3.
  destruct (mr_model B _ LAWS L3 A3 m3 md3 HM3) as (Hh3 & Hl3 & _).
  assert (E4_2 : getr R4 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_3 : getr R4 3 = getr regs 3) by exact (eq_trans (PR3 3 ltac:(unfold callee_saved; lia)) E3_3).
  assert (E4_4 : getr R4 4 = getr regs 4) by exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (E4_8 : getr R4 8 = Z_to_bv 64 e) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E3_8).
  pose proof (scb_rjr_shapes 12512 (bv_unsigned sp) O L A mem md L3 A3 m3 md3 RJ3 GS) as GS3.
  assert (Q4 : reg_get R4 2 = Z_to_bv 64 (bv_unsigned sp + -128)) by exact E4_2.
  eapply evt_SR_canon; [ | exact Hh3 | exact Hl3 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q4.
    eapply (evt_normalize rsegs); [exact WX | exact RA3 |].
    eapply (scb_run2 RSO) with (lo := bv_unsigned sp - 12512).
    - apply stk_norm; [lia | rewrite SPU; lia |]. intros a Ha. rewrite SPU in Ha. apply HSC3. left. lia.
    - rewrite SPU. lia.
    - lia.
    - exact (bytes_at_normalize rsegs m3 _ _ RA3 GS3).
    - apply mem_inv_normalize. }
  intros ms4 (can4 & (s4 & Q4' & REL4 & RO4) & EQ4).
  destruct Q4' as (m4n & t0' & t1' & t2' & c3 & c4 & c5 & c6 & c7 & t3' & t4' & t5' & t6' & -> & MU4n & WM4n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL4) as [EC4 MR4r].
  revert EC4 MR4r RO4 EQ4. generalize (ms_mem can4) as m4. intros m4 EC4 MR4r RO4 EQ4. subst can4.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 MU4n) as MU4.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m3 RA3) MR4r RO4 WM4n) as WM4.
  clear MU4n WM4n MR4r.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ4 eq_refl eq_refl) as (R5 & -> & X5).
  rewrite SPU in MU4.
  pose proof (sinv_stack B API SEGS GOWN AX 12512 (bv_unsigned sp) L A mem md O L3 A3 m3 md3 _ _ b m4 _ SI3 MU4 WM4
                ltac:(intros a Ra Hm; cbn in Hm; lia)) as SI4.
  pose proof SI4 as (_ & _ & _ & _ & _ & RA4 & _).
  assert (E5_1 : getr R5 1 = Z_to_bv 64 0x16f80) by (rewrite (getr_of_eqv _ _ 1 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_2 : getr R5 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by (rewrite (getr_of_eqv _ _ 2 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_3 : getr R5 3 = getr regs 3) by (rewrite (getr_of_eqv _ _ 3 X5 eq_refl); simp_regs; exact E4_3).
  assert (E5_4 : getr R5 4 = getr regs 4) by (rewrite (getr_of_eqv _ _ 4 X5 eq_refl); simp_regs; exact E4_4).
  assert (E5_10 : getr R5 10 = Z_to_bv 64 e) by (rewrite (getr_of_eqv _ _ 10 X5 eq_refl); simp_regs; exact E4_8).
  assert (E5_11 : getr R5 11 = Z_to_bv 64 0x10417)
    by (rewrite (getr_of_eqv _ _ 11 X5 eq_refl); simp_regs; reflexivity).
  assert (E5_12 : getr R5 12 = Z_to_bv 64 1) by (rewrite (getr_of_eqv _ _ 12 X5 eq_refl); simp_regs; reflexivity).
  assert (SP5 : spZ R5 = bv_unsigned sp - 128) by (unfold spZ; rewrite E5_2; exact SPU).
  assert (BLE3 : sb_le (sb_shift b A A3) (sb_mallocs b [z; Z.of_nat (length (dec id)) + 1;
                   Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1; Z.of_nat (length (dec_list ids)) + 1])).
  { rewrite EQ3, EQB2, EQB. apply sch_bpre; [exact BLE1 | unfold z; lia]. }
  eapply SR_bind.
  { apply (sup_remove.answer_call (fx := fx') B API SEGS AX ERRNO_LOW (ANS fx') SLACK 12512 (bv_unsigned sp) L A mem md
             O L3 A3 R5 m4 md3 (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
             (Oc ++ [(p, Z.of_nat (length (dec_list ids)) + 1)]) b
             (sb_mallocs b [z; Z.of_nat (length (dec id)) + 1; Z.of_nat (length (dec (Z.of_nat (length ids)))) + 1;
                            Z.of_nat (length (dec_list ids)) + 1])
             e 0x10417 (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true SI4).
    - rewrite E5_1. apply bv_eq. vm_compute. reflexivity.
    - rewrite SP5. exact MOD.
    - rewrite SP5. assert (AK : ANSWER_K = 12384) by reflexivity. rewrite AK. lia.
    - rewrite SP5. lia.
    - rewrite SP5. lia.
    - rewrite E5_4. exact HTP.
    - exact E5_10.
    - exact E5_11.
    - rewrite E5_12. reflexivity.
    - intros _. replace (daemon_shape "chain") with REC_MOD_HOST_SHAPE by (vm_compute; reflexivity).
      apply sup_remove.srm_host_shape. exact RA4.
    - intros _ _. exact (ans_entry_record R REC_CHAIN _ H16).
    - exact (proj1 FK).
    - exact BLE3.
    - eapply room_slots_mono; [| | exact ROOM].
      + apply sb_malloc_mono, sb_malloc_mono. exact BLE3.
      + lia. }
  intros cf6 MID. unfold sup_remove.ans_mid in MID.
  destruct MID as (fx'' & L' & A' & R6 & m5 & md5 & O' & q' & -> & FPK & RJ5 & PR5 & KST5 & A05 & GR5 & ON5 & BL5 & INq
    & FRq & NIq & BYq & OK5 & AP5 & RA5 & F185 & INIT5 & RG5 & SB5 & RS5).
  pose proof RJ5 as (HM5 & _).
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -104) cs).
  { apply (rw_cells_transfer rsegs m'); [exact FR1|]. intros i Hi. rewrite CS in Hi.
    destruct (KST2 (bv_unsigned sp + -104 + i)) as [Ea Eb]; [rewrite SP1; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -104) cs).
  { apply (rw_cells_transfer rsegs m2); [exact FR2|]. intros i Hi. rewrite CS in Hi.
    destruct (PF3 (bv_unsigned sp + -104 + i)) as [Ea Eb].
    - left. lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L2 A2 m2 md2 _ HM2 Ho). lia.
    - intros Ho. pose proof (mr_owned_low B _ LAWS L3 A3 m3 md3 _ PM3 Ho). lia.
    - unfold scratch_k. rewrite SP3. unfold ALLOC_STACK. intros [H|H]; lia.
    - cbv beta. lia.
    - split; [exact Ea | exact (proj1 Eb)]. }
  assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -104) cs).
  { apply (rw_out rsegs _ m3 m4 _ _ FR3 MU4). intros i Hi. rewrite CS in Hi. split; [lia|]. cbn [outside].
    split; [lia | exact I]. }
  assert (FR5 : rw_cells rsegs m5 (bv_unsigned sp + -104) cs).
  { apply (rw_cells_transfer rsegs m4); [exact FR4|]. intros i Hi. rewrite CS in Hi.
    destruct (KST5 (bv_unsigned sp + -104 + i)) as [Ea Eb]; [rewrite SP5; lia|]. split; [exact Ea | exact (proj1 Eb)]. }
  unfold cs in FR5.
  assert (Q6 : reg_get R6 2 = Z_to_bv 64 (bv_unsigned sp + -128))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E5_2).
  assert (E6_3 : getr R6 3 = getr regs 3) by exact (eq_trans (PR5 3 ltac:(unfold callee_saved; lia)) E5_3).
  assert (E6_4 : getr R6 4 = getr regs 4) by exact (eq_trans (PR5 4 ltac:(unfold callee_saved; lia)) E5_4).
  rewrite E5_1.
  eapply evt_SR_canon; [ | exact Hh5 | exact Hl5 | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. rewrite Q6. eapply scb_run3; [exact FR5 | lia]. }
  intros ms7 (can7 & Q7 & EQ7). subst can7.
  destruct (eqv_mkst _ _ _ _ _ _ _ EQ7 eq_refl eq_refl) as (R7 & -> & X7). clear EQ7.
  assert (RP : regs_preserved regs R7).
  { intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct C as [->|[->|[->|C]]].
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 2) X7 eq_refl); simp_regs. reflexivity.
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 3) X7 eq_refl); simp_regs. exact E6_3.
    - rewrite (getr_of_eqv _ _ (Z_to_bv 5 4) X7 eq_refl); simp_regs. exact E6_4.
    - repeat (destruct C as [C|C];
              [subst r; match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
                 rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X7 eq_refl); simp_regs; reflexivity end|]).
      subst r. match goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
        rewrite (getr_of_eqv _ _ (Z_to_bv 5 k) X7 eq_refl); simp_regs; reflexivity end. }
  assert (RPC : ret_pc (getr regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  apply SR_ret. unfold scu_ret.
  exists fx'', L', A', R7, m5, md5, (fst (sup_chain_m R id ids)), O', (snd (sup_chain_m R id ids)), q'.
  split; [apply surjective_pairing|].
  split; [rewrite RPC, SEGS; reflexivity|].
  split.
  { destruct FK as [_ K1]. destruct FPK as [Z2 K2]. split; [exact Z2|]. intros r Hr. rewrite (K2 r Hr). exact (K1 r Hr). }
  split.
  { apply (rjr_final B (aa_MR API) CTX 12512 rec_area (fun pn => In pn O) (fun a => In a (map fst O)) L A regs mem md
             L' A' R7 m5 md5 PRK RJ5 RP).
    intros a0 k0 G. exact (in_map fst O (a0, k0) G). }
  split; [rewrite (getr_of_eqv _ _ 10 X7 eq_refl); simp_regs; exact A05|].
  split; [rewrite SEGS; exact GR5|]. split; [exact ON5|]. split; [exact INq|]. split; [exact FRq|].
  split; [exact NIq|]. split; [rewrite SEGS; exact BYq|]. split; [rewrite SEGS; exact OK5|]. split; [exact BL5|].
  split.
  { change (snd (sup_chain_m R id ids)) with
      (snd (rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
        (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (daemon_shape "chain") true)).
    intros p0 k0 H1 H2. pose proof (AP5 p0 k0 H1 H2). lia. }
  split; [rewrite SEGS; exact (scb_rjr_shapes 12512 (bv_unsigned sp) O L A mem md L' A' m5 md5 RJ5 GS)|].
  split; [rewrite SEGS; exact RA5|]. split; [rewrite SEGS; exact F185|]. split; [exact INIT5|]. split; [exact RG5|].
  split; [rewrite sch_mallocs_split; exact SB5 | exact RS5].
Qed.

End Back.
