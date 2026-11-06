(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths, module names and numbers changed; 505 of its 555 lines of code are new or changed and 1016 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes FP.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import printf_facts_c snprintf_c strlen_c memcpy_c
  RecAns.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition sr_mid (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo code : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' slack,
    ms' = MS (mkR (Z_to_bv 64 0x15f70) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2
                  (Z_to_bv 64 (Z.of_nat (length (resp code)) + 1)) s1 (Z_to_bv 64 (Z.of_nat (length (resp code)) + 1))
                  a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 0x15a88) fc' None m' (seg_rom rsegs)
    /\ munch [(lo, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10%Z -> reg_get F' k = reg_get F k)
    /\ length slack = (31 - length (resp code))%nat
    /\ bytes_at rsegs m' (bv_unsigned sp + -56)%Z (resp code ++ Z_to_bv 8 0 :: slack)
    /\ rw_cells rsegs m' (bv_unsigned sp + -24)%Z [C8 s1; C8 s0; C8 ra].

Lemma sr_run1 : snprintf_contract -> strlen_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo code : Z) (canary : word),
  (-2^31 <= code < 2^31)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 64 + SNPRINTF_K <= bv_unsigned sp)%Z -> (2 ^ 21 <= lo)%Z ->
  (bv_unsigned sp < 2^63)%Z ->
  frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> (bv_unsigned sp <= TASK_SIZE)%Z ->
  bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
  evt rsegs (sr_mid ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo code m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 code) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x15f34) fc None m (seg_rom rsegs)).
Proof.
  intros SNP SLEN ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo code canary HC ST LO IE S63 FRM MI TM HTS GG GW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  unfold SNPRINTF_K, IMG_END, GOT_GUARD, GUARD in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 24%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 24%nat junk [] [8; 8; 8]%nat) in FR; [|reflexivity].
  cbn [mk_CB_cells app firstn skipn] in FR.
  rename FR into FRS.
  carve_frame 32%nat ST.
  carve_frame 8%nat ST.
  clear FR0.
  do 10 step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (mw := mm) in *; clearbody mw end.
  try replace (bv_unsigned sp + -64 + 8)%Z with (bv_unsigned sp + -56)%Z by ring.
  pose proof (resp_len code HC) as RL.
  pose proof (rw_cells_bound _ _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
  assert (BJ : bytes_at rsegs mw (bv_unsigned sp + -56)%Z junk0).
  { destruct FR as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  pose proof (bytes_at_bound _ _ _ _ BJ) as BJL.
  eapply evt_cut.
  { eapply (SNP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo canary RESP_FMT RESP_PS
              [AInt code] (RESP_HEAD ++ pf_dec code) junk0).
    - rewrite unsigned_lit by lia. apply resp_fmt_at. exact MI.
    - rewrite unsigned_lit by lia. unfold RO_LO. lia.
    - rewrite unsigned_lit by lia. unfold RO_END, RESP_FMT. cbn [length]. lia.
    - exact resp_parse.
    - cbn [pf_args_ok pf_arg_ok]. split; [|exact I]. split; [exact HC | apply lit_mod32].
    - exact (resp_text code).
    - rewrite !unsigned_lit by lia. exact FR.
    - rewrite unsigned_lit by lia. lia.
    - lia.
    - rewrite unsigned_lit by lia. lia.
    - rewrite !unsigned_lit by lia. right. lia.
    - rewrite !unsigned_lit by lia. apply pf_img_free_hi. lia.
    - rewrite unsigned_lit by lia. exact ST.
    - rewrite unsigned_lit by lia. unfold SNPRINTF_K. lia.
    - unfold IMG_END. lia.
    - rewrite unsigned_lit by lia. lia.
    - exact FRM.
    - exact MI.
    - exact (task_mem_munch1 m mw lo (bv_unsigned sp) TM MU HTS).
    - exact GG.
    - exact GW. }
  intros ms' PO. unfold printf_post in PO.
  destruct PO as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & Ft & fc' & m2
    & -> & MU2 & WM2 & MI2 & TM2 & FRM2 & FK & ST2 & BT).
  rewrite !unsigned_lit in MU2, BT by lia.
  change (Z.to_nat (32 - 1)) with 31%nat in BT, MU2.
  rewrite (firstn_all2 (n := 31%nat)) in MU2, BT by lia.
  replace (ret_pc (Z_to_bv 64 0x15f5c)) with (Z_to_bv 64 0x15f5c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  assert (JL : length junk0 = 32%nat) by (destruct FR as [[[HJ _] _] _]; exact HJ).
  assert (FRS2 : rw_cells rsegs m2 (bv_unsigned sp + -24)%Z [C8 s1; C8 s0; C8 ra]).
  { apply (rw_cells_transport rsegs _ mw m2 _ _ FRS MU2 WM2). cbn [disjoint_from cells_size csize Nat.add].
    split; [lia | split; [lia | exact I]]. }
  destruct (bytes_at_firstn_skipn _ _ _ _ (S (length (RESP_HEAD ++ pf_dec code))) BJ) as [_ BJT].
  rewrite firstn_length_le in BJT by lia.
  assert (BJT2 : bytes_at rsegs m2 (bv_unsigned sp + -56 + Z.of_nat (S (length (RESP_HEAD ++ pf_dec code))))%Z
                   (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { apply (bytes_at_transport rsegs _ mw m2 _ _ BJT MU2). cbn [disjoint_from]. rewrite length_skipn.
    split; [lia | split; [lia | exact I]]. }
  assert (PB : pf_bytes ((RESP_HEAD ++ pf_dec code) ++ [0%Z]) = resp code ++ [Z_to_bv 8 0]).
  { unfold pf_bytes. rewrite map_app. change (map (Z_to_bv 8) (RESP_HEAD ++ pf_dec code)) with
      (pf_bytes (RESP_HEAD ++ pf_dec code)). rewrite pf_resp by exact HC. reflexivity. }
  assert (LR : length (resp code) = length (RESP_HEAD ++ pf_dec code)).
  { rewrite <- (pf_resp code HC). unfold pf_bytes. apply length_map. }
  rewrite PB in BT.
  assert (BUF : bytes_at rsegs m2 (bv_unsigned sp + -56)%Z
                  (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)).
  { replace (resp code ++ Z_to_bv 8 0 :: skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) with
      ((resp code ++ [Z_to_bv 8 0]) ++ skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0)
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BT|]. rewrite length_app, LR. cbn [length].
    replace (Z.of_nat (length (RESP_HEAD ++ pf_dec code) + 1))
      with (Z.of_nat (S (length (RESP_HEAD ++ pf_dec code)))) by lia. exact BJT2. }
  assert (SLL : length (skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) = (31 - length (resp code))%nat)
    by (rewrite length_skipn, JL, LR; lia).
  assert (MU12 : munch [(lo, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU2].
    unfold sub_fp. cbn [outside]. intros x [Hx _]. split; [lia | split; [lia | exact I]]. }
  assert (WM12 : wmono rsegs m m2) by (eapply wmono_trans; [exact WM | exact WM2]).
  clear BT BJT BJT2 BJ BJL FR MU MU2 WM WM2.
  set (slack := skipn (S (length (RESP_HEAD ++ pf_dec code))) junk0) in *. clearbody slack.
  assert (UL : bv_unsigned (Z_to_bv 64 (Z.of_nat (length (resp code)))) = Z.of_nat (length (resp code)))
    by (apply unsigned_lit; lia).
  do 2 step.
  try replace (bv_unsigned sp + -64 + 8)%Z with (bv_unsigned sp + -56)%Z by ring.
  call (SLEN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (resp code) slack).
  1: rewrite unsigned_lit by lia; exact BUF.
  1: exact (resp_no0 code).
  1: rewrite unsigned_lit by lia; rewrite SLL;
     match goal with |- (?x mod 8 <= _)%Z => pose proof (Z.mod_pos_bound x 8 ltac:(lia)) end; lia.
  1: exact MI2.
  cbv delta [mkR].
  do 3 step.
  rewrite ?UL.
  apply evt_done. unfold sr_mid.
  do 17 eexists. exists slack. split; [reflexivity|].
  split; [exact MU12|]. split; [exact WM12|]. split; [eassumption|].
  split; [exact FRM2|]. split; [exact FK|]. split; [exact SLL|]. split; [exact BUF | exact FRS2].
Qed.

Definition sr_fin (ra0 sp r3 r4 s0v s1v r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : word) (F : bvmap 5 word)
    (fc : bv 32) (p n : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + 64)) r3 r4 t0 t1 t2 s0v s1v (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
                  r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 t3 t4 t5 t6) F (ret_pc ra0) fc None m' (seg_rom rsegs)
    /\ munch [(p, p + n)]%Z m m' /\ wmono rsegs m m'
    /\ rw_cells rsegs m' p [CB (length src) src].

Lemma sr_run2 : memcpy_contract ->
  forall r1 r3 r4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31
    (F : bvmap 5 word) fc (m : word -> option byte) (sp ra0 s0v s1v : word) (p n : Z) (src junk : list byte),
  rw_cells rsegs m (bv_unsigned sp + 40)%Z [C8 s1v; C8 s0v; C8 ra0] ->
  bytes_at rsegs m (bv_unsigned sp + 8)%Z src ->
  Z.of_nat (length src) = n ->
  rw_cells rsegs m p [CB (length src) junk] ->
  (0 < p)%Z -> (p + n <= bv_unsigned sp)%Z -> (bv_unsigned sp + 64 < 2 ^ 64)%Z ->
  mem_inv rsegs m ->
  evt rsegs (sr_fin ra0 sp r3 r4 s0v s1v r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 F fc p n src m)
    (MS (mkR r1 sp r3 r4 x5 x6 x7 (Z_to_bv 64 n) x9 (Z_to_bv 64 p)
             x11 x12 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x15f70) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY r1 r3 r4 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 x28 x29 x30 x31
    F fc m sp ra0 s0v s1v p n src junk FR SRC LN DST P0 PS SPH MI.
  subst n.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (US : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + 8)) = (bv_unsigned sp + 8)%Z) by (apply unsigned_lit; lia).
  assert (UD : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 (Z.of_nat (length src))) = Z.of_nat (length src)) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(p, p + Z.of_nat (length src))]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  do 4 step.
  call (MCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ src junk).
  1: rewrite US; exact SRC.
  1: rewrite UN, Nat2Z.id; reflexivity.
  1: rewrite UD, UN, Nat2Z.id; exact DST.
  1: rewrite US, UD, UN; lia.
  1: exact MI.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m3 := mm) in *; clearbody m3 end.
  rewrite ?UD, ?UN, ?Nat2Z.id in *.
  match goal with H : rw_cells rsegs m3 p _ |- _ => rename H into DST3 end.
  do 6 step.
  apply evt_done. unfold sr_fin. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM | exact DST3].
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import RecInv RecInvU RecKindB RecAnsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import xmalloc_c sup_resp_c.
Local Open Scope Z_scope.

Lemma sr_in_fG : forall a, 0x33ff0 <= a < 0x33ff0 + 1020 -> in_globals frame_G a.
Proof. intros a Ha. exists 0x33ff0, 1020. split; [left; reflexivity | exact Ha]. Qed.

Lemma sr_got_seg : forall i, 0 <= i < 8 -> find_segment rsegs (0x22d40 + i) 1 <> None.
Proof.
  intros i Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  destruct C as [C | [C | [C | [C | [C | [C | [C | C]]]]]]]; subst i; intro F; vm_compute in F; discriminate F.
Qed.

Section SR.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis SEGS : ms_segs B = rsegs.
Hypothesis ERRNO_LOW : errno_addr B + 4 <= alloc_ceiling.
Hypothesis GOTG : ms_got_guard B = snprintf_c.GOT_GUARD.
Hypothesis GUARDG : ms_guard B = snprintf_c.GUARD.
Hypothesis GLOB : forall a, in_globals frame_G a -> in_img B a /\ ~ static_owned B a /\
  ~ (ms_ctx B <= a < ms_ctx B + CTX_SIZE) /\ ~ (errno_addr B <= a < errno_addr B + 4).
Hypothesis AX : YL01.AllocExtra B (aa_MR API).
Hypothesis SNP : snprintf_contract.
Hypothesis SLEN : strlen_contract.
Hypothesis MCPY : memcpy_contract.
Hypothesis XM : forall fx' : YK11.FPState, @xmalloc_contract fx' rc B API.

Theorem sup_resp_holds : sup_resp_contract B API.
Proof using SEGS ERRNO_LOW GOTG GUARDG GLOB AX SNP SLEN MCPY XM.
  unfold sup_resp_contract.
  intros L A regs mem md code b PRE A0 HC RA FZ F18 RES ROOM.
  destruct PRE as [PRE HTS].
  pose proof (aa_laws API) as LAWS.
  pose proof alloc_ceiling_val as AC.
  pose proof wx_apart_rsegs as WX.
  assert (GOTG0 : ms_got_guard B = 0x22d40) by exact GOTG.
  assert (KV : SUP_RESP_K = 8272) by reflexivity.
  assert (XK : XMALLOC_K = 8208) by reflexivity.
  rewrite KV in PRE |- *.
  destruct PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  set (sp := reg_get regs 2) in *.
  change (spZ regs) with (bv_unsigned sp) in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (resp_length code HC) as RL.
  rewrite SEGS in RA, HWS, HERR, F18.
  pose proof F18 as (GG & canary & GW).
  assert (GGb : bytes_at rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD))).
  { destruct GG as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (GWb : bytes_at rsegs mem snprintf_c.GUARD (Mem.le8 canary)).
  { destruct GW as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  assert (ST0 : stk rsegs (normalize_cj rsegs mem) (bv_unsigned sp - 8272) (bv_unsigned sp))
    by (apply stk_normalize_cj; [lia | exact HTS | intros a Ha; apply HWS; lia]).
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GOT_GUARD (Mem.le8 (Z_to_bv 64 snprintf_c.GUARD)) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GOT_GUARD, TASK_SIZE; lia) GGb) as GGn.
  pose proof (bytes_at_normalize_cj_low rsegs mem snprintf_c.GUARD (Mem.le8 canary) RA
    ltac:(rewrite Mem.length_le8; unfold snprintf_c.GUARD, TASK_SIZE; lia) GWb) as GWn.
  rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. unfold Regs6ss.mkR_of. fold sp.
    assert (R10 : reg_get regs 10 = Z_to_bv 64 code) by exact A0. rewrite R10.
    eapply (evt_normalize_cj rsegs); [exact WX | exact RA |].
    eapply (sr_run1 SNP SLEN) with (lo := bv_unsigned sp - 8272) (canary := canary);
      [exact HC | exact ST0 | unfold SNPRINTF_K; lia | lia | lia | exact FZ
      | exact (mem_inv_cj_inv rsegs _ (mem_inv_cj_normalize rsegs mem))
      | exact (mem_inv_cj_task rsegs _ (mem_inv_cj_normalize rsegs mem)) | exact HTS
      | exact GGn | exact GWn]. }
  intros ms1 (can1 & (s1n & Q1 & REL1 & RO1) & EQ1).
  destruct Q1 as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & F1 & fc1 & m1n
    & slack & -> & MU1n & WM1n & MI1n & FRM1 & FK1 & SL & BUF1n & FRS1n).
  destruct (ms_rel_cj_MS _ _ _ _ _ _ _ _ REL1) as [EC1 MR1r].
  revert EC1 MR1r RO1 EQ1. generalize (ms_mem can1) as m1. intros m1 EC1 MR1r RO1 EQ1. subst can1.
  pose proof (munch_rel_cj rsegs _ _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 MU1n) as MU1.
  pose proof (wmono_rel_cj rsegs _ _ _ _ (mem_rel_cj_normalize rsegs mem RA) MR1r RO1 WM1n) as WM1.
  pose proof (ro_agree_same_cj rsegs _ _ RA RO1) as RA1.
  pose proof (rw_cells_rel_cj rsegs _ _ _ _ MR1r FRS1n) as FRS1.
  pose proof (bytes_at_rel_cj rsegs _ _ _ _ MR1r BUF1n) as BUF1.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ1) as (R1 & -> & X1).
  clear MU1n WM1n MI1n FRS1n BUF1n EQ1 MR1r.
  assert (LB : 6 <= Z.of_nat (length (resp code)) <= 16) by lia.
  set (l := Z.of_nat (length (resp code))) in *.
  assert (E1_1 : getr R1 1 = Z_to_bv 64 0x15f70) by (rewrite (getr_of_eqv _ _ 1 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_2 : getr R1 2 = Z_to_bv 64 (bv_unsigned sp + -64))
    by (rewrite (getr_of_eqv _ _ 2 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_4 : getr R1 4 = reg_get regs 4) by (rewrite (getr_of_eqv _ _ 4 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_8 : getr R1 8 = Z_to_bv 64 (l + 1)) by (rewrite (getr_of_eqv _ _ 8 X1 eq_refl); simp_regs; reflexivity).
  assert (E1_10 : getr R1 10 = Z_to_bv 64 (l + 1))
    by (rewrite (getr_of_eqv _ _ 10 X1 eq_refl); simp_regs; reflexivity).
  assert (SP1 : spZ R1 = bv_unsigned sp - 64) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp) ->
            outside [(bv_unsigned sp - 8272, bv_unsigned sp)] a) by (intros a _ Ha; cbn; split; [exact Ha | exact I]).
  assert (MR1 : aa_MR API L A m1 md).
  { eapply (mr_frame B _ LAWS L A mem m1 md md HMR).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU1 | lia | apply OUT1; lia].
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - intros p n i Hin Hi. destruct (mr_blocks B _ LAWS L A mem md p n i HMR Hin Hi) as (Hp & H4 & Hc & _).
      eapply munch_present; [exact MU1 | lia | apply OUT1; lia | exact Hp].
    - reflexivity.
    - exact Hh.
    - exact Hl.
    - exact Hmat. }
  pose proof (XM (mkFP F1 fc1)) as XMC. unfold xmalloc_contract in XMC. rewrite SEGS in XMC.
  assert (XS : xmalloc_size (l + 1) = l + 1) by (unfold xmalloc_size; destruct (Z.eqb_spec (l + 1) 0); lia).
  eapply SR_bind.
  { eapply (XMC L A R1 m1 md (l + 1) b);
      [ | exact E1_10 | unfold LMAX; lia | exact RES | rewrite XS; exact ROOM | exact RA1].
    rewrite XK.
    split; [exact MR1|]. split; [exact HWF|]. split; [exact HBD|].
    split; [rewrite E1_1; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite SP1; replace (bv_unsigned sp - 64) with (bv_unsigned sp + (-4) * 16) by ring;
            rewrite Z.mod_add by lia; exact HAL|].
    split; [rewrite SP1; lia|].
    split; [rewrite SP1; lia|].
    split; [intros a Ha; rewrite SP1 in Ha; rewrite SEGS; apply WM1; apply HWS; lia|].
    split; [rewrite E1_4; exact HTP|].
    split; [intros a Ha; rewrite SEGS; apply WM1; apply HERR; exact Ha|].
    intros HI. specialize (HAUX HI). rewrite SP1.
    destruct HAUX as (av & ar & W1 & W2 & W3 & W4 & B1 & B2 & B3 & B4 & L1 & L2).
    exists av, ar.
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W1]. intros k Hk.
      assert (SO : owned B L A (ms_libc B + 8 + Z.of_nat k)) by (right; unfold static_owned; lia).
      destruct (owned_low B _ LAWS _ _ _ _ _ HMR SO). split; [lia | apply OUT1; lia]. }
    split.
    { intros k Hk. eapply word_mem_munch; [exact MU1 | | exact (W2 k Hk)]. intros k' Hk'.
      split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W3]. intros k Hk. split; [lia | apply OUT1; lia]. }
    split.
    { eapply word_mem_munch; [exact MU1 | | exact W4]. intros k Hk. split; [lia | apply OUT1; lia]. }
    lia. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & p & -> & POST2 & A0' & NZ & AL & FRESH & (b1 & b2 & BL2 & BL1)
    & KEPT & RA2 & GK2 & UB & INIT2 & REG2 & RES2).
  rewrite XS in *.
  try rewrite SEGS in RA2.
  destruct POST2 as (HMR2 & HWF2 & HBD2 & HLE2 & HSTAB2 & HP2 & HVM2 & HFR2 & HBLKS2 & HSCR2).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR2) as (Hh2 & Hl2 & Hmat2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (INB : In (p, l + 1) (blocks L2 A2)) by (rewrite BL2; apply in_or_app; right; left; reflexivity).
  assert (NOWN : forall a, alloc_ceiling <= a -> ~ owned B L A a /\ ~ owned B L2 A2 a).
  { intros a Ha. split; intros Ho;
      [destruct (owned_low B _ LAWS _ _ _ _ _ HMR Ho) | destruct (owned_low B _ LAWS _ _ _ _ _ HMR2 Ho)]; lia. }
  assert (OWNG : forall a, in_globals frame_G a -> forall L0 A0 m0 md0, aa_MR API L0 A0 m0 md0 -> ~ owned B L0 A0 a).
  { intros a Ga La Aa m0 md0 HM. destruct (GLOB a Ga) as (Hi & Hs & Hc & He). intros [Ho|Ho]; [|exact (Hs Ho)].
    exact (Hc (YL01.ax_img AX _ _ _ _ a HM Hi Ho)). }
  assert (HF12 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (bv_unsigned sp - 8272 <= a < bv_unsigned sp - 64) ->
     mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
     (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
  { intros a Ha Hs. destruct (NOWN a (proj1 Ha)) as [N1 N2].
    apply HFR2; [left; exact Ha | exact N1 | exact N2 | | intros F; exact F].
    unfold scratch_k. rewrite SP1, XK. intros [H|H]; lia. }
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (bv_unsigned sp + -64))
    by exact (eq_trans (HP2 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 (l + 1))
    by exact (eq_trans (HP2 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 p) by exact A0'.
  assert (FR2 : rw_cells rsegs m2 (bv_unsigned sp + -24)
                  [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply (rw_cells_transfer rsegs m1); [exact FRS1|]. intros i Hi. cbn in Hi. rewrite <- SEGS.
    destruct (HF12 (bv_unsigned sp + -24 + i) ltac:(lia) ltac:(lia)) as [E W].
    split; [exact E | apply W]. }
  assert (LSRC : Z.of_nat (length (resp code ++ [Z_to_bv 8 0])) = l + 1) by (rewrite length_app; cbn [length]; lia).
  assert (BS1' : bytes_at rsegs m1 (bv_unsigned sp + -56) (resp code ++ [Z_to_bv 8 0])).
  { replace (resp code ++ Z_to_bv 8 0 :: slack) with ((resp code ++ [Z_to_bv 8 0]) ++ slack) in BUF1
      by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app in BUF1. exact (proj1 BUF1). }
  assert (SRC2 : bytes_at rsegs m2 (bv_unsigned sp + -56) (resp code ++ [Z_to_bv 8 0])).
  { apply (bytes_at_transfer rsegs m1); [exact BS1'|]. intros i Hi. rewrite LSRC in Hi. rewrite <- SEGS.
    exact (proj1 (HF12 (bv_unsigned sp + -56 + i) ltac:(lia) ltac:(lia))). }
  destruct (present_rw_cells rsegs (normalize rsegs m2) p (length (resp code ++ [Z_to_bv 8 0]))) as [junk2 DST2];
    [lia | rewrite LSRC; lia | |].
  { intros i Hi. rewrite LSRC in Hi. destruct (proj1 (block_facts B _ LAWS _ _ _ _ _ _ i HMR2 INB Hi)) as [bb E].
    exists bb. rewrite normalize_rw; [exact E|]. apply (ro_addr_out B SEGS); [lia | apply FR_img; lia]. }
  assert (FR2n : rw_cells rsegs (normalize rsegs m2) (bv_unsigned sp + -24)
                   [C8 (reg_get regs 9); C8 (reg_get regs 8); C8 (reg_get regs 1)]).
  { apply rw_cells_normalize; [exact RA2 | exact FR2 |]. intros i Hi. cbn in Hi. unfold wa. apply ro_addr_hi. lia. }
  pose proof (bytes_at_normalize rsegs m2 _ _ RA2 SRC2) as SRC2n.
  rewrite E1_1. try rewrite SEGS.
  eapply evt_SR_canon; [ | exact Hh2 | exact Hl2 | ].
  { rewrite canon_mkst. cbn [fp_regs fp_csr]. unfold Regs6ss.mkR_of. rewrite E2_2, E2_8, E2_10.
    eapply (evt_normalize rsegs); [exact WX | exact RA2 |].
    eapply (sr_run2 MCPY) with (src := resp code ++ [Z_to_bv 8 0]);
      [ rewrite unsigned_lit by lia; replace (bv_unsigned sp + -64 + 40) with (bv_unsigned sp + -24) by ring;
        exact FR2n
      | rewrite unsigned_lit by lia; replace (bv_unsigned sp + -64 + 8) with (bv_unsigned sp + -56) by ring;
        exact SRC2n
      | exact LSRC | exact DST2 | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
      | apply mem_inv_normalize ]. }
  intros ms3 (can3 & (s3n & Q3 & REL3 & RO3) & EQ3). unfold sr_fin in Q3.
  destruct Q3 as (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m3n
    & -> & MU3n & WM3n & DST3n).
  destruct (ms_rel_MS rsegs _ _ _ _ _ _ _ _ REL3) as [EC3 MR3r].
  revert EC3 MR3r RO3 EQ3. generalize (ms_mem can3) as m3. intros m3 EC3 MR3r RO3 EQ3. subst can3.
  pose proof (munch_rel rsegs _ _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 MU3n) as MU3.
  pose proof (wmono_rel rsegs _ _ _ _ (mem_rel_normalize rsegs m2 RA2) MR3r RO3 WM3n) as WM3.
  pose proof (ro_agree_same rsegs _ _ RA2 RO3) as RA3.
  pose proof (rw_cells_rel rsegs _ _ _ _ MR3r DST3n) as DST3.
  destruct (eqv_mkst_fx _ _ _ _ _ _ _ EQ3) as (R3 & -> & X3).
  clear MU3n WM3n DST3n EQ3 MR3r.
  assert (RP : ret_pc (reg_get regs 1) = getr regs 1) by exact (ret_pc_of_ok _ HRA).
  rewrite RP.
  assert (OUT3 : forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + (l + 1)) -> outside [(p, p + (l + 1))] a)
    by (intros a _ H1; cbn [outside]; split; [exact H1 | exact I]).
  assert (MR3 : aa_MR API L2 A2 m3 md2).
  { eapply (mr_frame B _ LAWS L2 A2 m2 m3 md2 md2 HMR2).
    - intros a Ho. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      eapply munch_mbyte; [exact MU3 | lia | apply OUT3; [lia |]].
      intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p) HMR2 INB ltac:(lia))))).
      replace (p + (a - p)) with a by ring. exact Ho.
    - intros a Ho Hp. destruct (owned_low B _ LAWS _ _ _ _ a HMR2 Ho) as [Ha1 Ha2].
      eapply munch_present; [exact MU3 | lia | apply OUT3; [lia |] | exact Hp].
      intros Hin. apply (proj2 (proj2 (proj2 (block_facts B _ LAWS _ _ _ _ _ _ (a - p) HMR2 INB ltac:(lia))))).
      replace (p + (a - p)) with a by ring. exact Ho.
    - intros q n i Hin Hi. destruct (mr_blocks B _ LAWS L2 A2 m2 md2 q n i HMR2 Hin Hi) as (Hp & H4 & Hc & _).
      destruct (Z_le_gt_dec p (ptr_addr L2 q + i)) as [D1|D1];
        [destruct (Z_lt_ge_dec (ptr_addr L2 q + i) (p + (l + 1))) as [D2|D2]|].
      + apply (present_of_writable_out B SEGS m3 (ptr_addr L2 q + i) ltac:(lia)).
        * replace (ptr_addr L2 q + i) with (p + (ptr_addr L2 q + i - p)) by ring. apply FR_img. lia.
        * pose proof DST3 as [_ (_ & _ & W)].
          assert (Hb : 0 <= ptr_addr L2 q + i - p <
                       Z.of_nat (cells_size [CB (length (resp code ++ [Z_to_bv 8 0])) (resp code ++ [Z_to_bv 8 0])]))
            by (cbn [cells_size csize]; rewrite Nat.add_0_r, LSRC; lia).
          specialize (W (ptr_addr L2 q + i - p) Hb).
          replace (p + (ptr_addr L2 q + i - p)) with (ptr_addr L2 q + i) in W by ring. exact W.
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
      + eapply munch_present; [exact MU3 | lia | apply OUT3; lia | exact Hp].
    - reflexivity.
    - exact Hh2.
    - exact Hl2.
    - exact Hmat2. }
  assert (GK3 : forall i, 0 <= i < 8 -> mbyte rsegs m3 (0x22d40 + i) = mbyte rsegs mem (0x22d40 + i)).
  { intros i Hi.
    rewrite (munch_mbyte _ _ _ _ (0x22d40 + i) MU3 ltac:(lia)).
    2: { apply OUT3; [lia |]. intros Hin. apply (FR_img (0x22d40 + i - p)); [lia|].
         replace (p + (0x22d40 + i - p)) with (0x22d40 + i) by ring.
         apply (in_img_found B SEGS); [lia | apply sr_got_seg; lia]. }
    pose proof (GK2 i Hi) as G. rewrite GOTG0, SEGS in G. rewrite G.
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  apply SR_ret. cbv beta zeta.
  exists (mkFP F1 fc1), L2, A2, R3, m3, md2, p.
  split; [reflexivity|].
  split.
  { unfold fp_kept. cbn [fp_regs fp_csr]. split; [exact FRM1|].
    intros r Hr. apply FK1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    unfold fs_saved in Hr. rewrite Z.mod_small by lia. lia. }
  split.
  { split; [exact MR3|]. split; [exact HWF2|]. split; [exact HBD2|].
    split; [exact HLE2|].
    split; [exact HSTAB2|].
    split.
    { eapply (preserved_chain (fun r => (r =? 2) || (r =? 8) || (r =? 9)) regs R1 R2 R3 _ _ X1 HP2 X3).
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | split; reflexivity]|]).
        subst r. split; reflexivity.
      - intros r Hr O. unfold callee_saved in Hr.
        assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        destruct C as [C|C].
        { subst r. simp_regs. rewrite unsigned_lit by lia.
          replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by ring. exact (Z_to_bv_lit_self sp). }
        repeat (destruct C as [C|C]; [subst r; first [discriminate O | reflexivity]|]).
        subst r. discriminate O. }
    split; [exact HVM2|].
    split.
    { intros a Hd N1 N2 NS _. unfold scratch_k, spZ in NS. change (getr regs 2) with sp in NS.
      assert (AR : 0 <= a < 2 ^ 64) by (destruct Hd as [Hd|Hd]; [lia | pose proof (in_img_low B SEGS a Hd); lia]).
      assert (NF : ~ (p <= a < p + (l + 1))).
      { intros Hin. destruct Hd as [Hd|Hd]; [lia|]. apply (FR_img (a - p)); [lia|].
        replace (p + (a - p)) with a by ring. exact Hd. }
      assert (E01 : mbyte (ms_segs B) m1 a = mbyte (ms_segs B) mem a)
        by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; [lia | intro H; apply NS; left; exact H]]).
      assert (W01 : writable_at (ms_segs B) mem a <-> writable_at (ms_segs B) m1 a)
        by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; [lia | intro H; apply NS; left; exact H]]).
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFR2; [exact Hd | exact N1 | exact N2 | | intros F; exact F].
        unfold scratch_k. rewrite SP1, XK. intros [H|H]; apply NS; [left; lia | right; exact H]. }
      destruct H12 as [E12 W12].
      assert (E23 : mbyte (ms_segs B) m3 a = mbyte (ms_segs B) m2 a)
        by (apply (munch_mbyte _ _ _ _ _ MU3); [lia | apply OUT3; [lia | exact NF]]).
      assert (W23 : writable_at (ms_segs B) m2 a <-> writable_at (ms_segs B) m3 a)
        by (apply (munch_writable _ _ _ _ _ MU3); [lia | apply OUT3; [lia | exact NF]]).
      split; [rewrite E23, E12, E01; reflexivity | tauto]. }
    split.
    { intros q n i Hin Hin' Hi.
      destruct (mr_blocks B _ LAWS L A mem md q n i HMR Hin Hi) as (_ & Hlo & Hhi & _).
      assert (INA : In (ptr_addr L q, n) (b1 ++ b2)).
      { rewrite <- BL1. unfold blocks. exact (in_map (fun b => (ptr_addr L (fst b), snd b)) _ _ Hin). }
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2 INA) as Dj.
      rewrite (munch_mbyte _ _ _ _ (ptr_addr L q + i) MU3 ltac:(lia)).
      2: { apply OUT3; lia. }
      rewrite (HBLKS2 q n i Hin Hin' Hi).
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
    intros a Ha. unfold scratch_k, spZ in Ha. change (getr regs 2) with sp in Ha.
    rewrite SEGS. apply WM3. rewrite <- SEGS.
    destruct Ha as [Ha|Ha].
    - destruct (Z_lt_ge_dec a (bv_unsigned sp - 64)) as [D|D].
      + apply HSCR2. unfold scratch_k. rewrite SP1, XK. left. lia.
      + apply (proj1 (proj2 (HF12 a ltac:(lia) ltac:(lia)))). rewrite SEGS. apply WM1. apply HWS. lia.
    - apply HSCR2. right. exact Ha. }
  split; [rewrite (getr_of_eqv _ _ 10 X3 eq_refl); simp_regs; reflexivity|].
  split; [exact NZ|]. split; [exact AL|]. split; [exact FRESH|].
  split; [exists b1, b2; split; [exact BL2 | exact BL1]|].
  split.
  { intros q k i Hq _ Hi.
    destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hq Hi) as (_ & Hlo & Hhi & _).
    assert (Hq' : In (q, k) (b1 ++ b2)) by (rewrite <- BL1; exact Hq).
    pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2 Hq') as Dj.
    rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia)).
    2: { apply OUT3; lia. }
    rewrite (KEPT q k i Hq (fun F => F) Hi).
    apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]. }
  split; [exact UB|].
  split.
  { pose proof DST3 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb. }
  split.
  { intros R O REP. change (fst (sup_resp_m R code)) with R.
    unfold g_rec_rep in REP |- *. eapply (rec_rep_frame _ _ _ L A mem R O L2 A2 m3 REP).
    - intros a Ha.
      assert (GA : in_globals frame_G a)
        by (apply sr_in_fG; unfold G_REC, REC_SC, REC_SIZE, SC_SIZE in Ha; lia).
      destruct (GLOB a GA) as (Ii & _ & _ & NEr).
      pose proof (in_img_low B SEGS a Ii) as Hlo.
      assert (NF : ~ (p <= a < p + (l + 1))).
      { intros H. apply (FR_img (a - p)); [lia|]. replace (p + (a - p)) with a by ring. exact Ii. }
      assert (E01 : mbyte rsegs m1 a = mbyte rsegs mem a)
        by (apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
      assert (W01 : writable_at rsegs mem a <-> writable_at rsegs m1 a)
        by (apply (munch_writable _ _ _ _ _ MU1); [lia | apply OUT1; lia]).
      assert (H12 : mbyte (ms_segs B) m2 a = mbyte (ms_segs B) m1 a /\
                    (writable_at (ms_segs B) m1 a <-> writable_at (ms_segs B) m2 a)).
      { apply HFR2; [right; exact Ii | exact (OWNG a GA _ _ _ _ MR1) | exact (OWNG a GA _ _ _ _ HMR2) | |
                     intros F; exact F].
        unfold scratch_k. rewrite SP1, XK. intros [H|H]; [lia | exact (NEr H)]. }
      rewrite SEGS in H12. destruct H12 as [E12 W12].
      assert (E23 : mbyte rsegs m3 a = mbyte rsegs m2 a)
        by (apply (munch_mbyte _ _ _ _ _ MU3); [lia | apply OUT3; [lia | exact NF]]).
      assert (W23 : writable_at rsegs m2 a <-> writable_at rsegs m3 a)
        by (apply (munch_writable _ _ _ _ _ MU3); [lia | apply OUT3; [lia | exact NF]]).
      split; [rewrite E23, E12, E01; reflexivity | tauto].
    - intros q k i Hin Hi. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb.
      destruct (block_facts B _ LAWS _ _ _ _ _ _ i HMR Hb Hi) as (_ & Hlo & Hhi & _).
      assert (Hq' : In (q, k) (b1 ++ b2)) by (rewrite <- BL1; exact Hb).
      pose proof (blocks_mid_disjoint B _ LAWS _ _ _ _ _ _ _ _ _ _ HMR2 BL2 Hq') as Dj.
      rewrite (munch_mbyte _ _ _ _ (q + i) MU3 ltac:(lia)).
      2: { apply OUT3; lia. }
      pose proof (KEPT q k i Hb (fun F => F) Hi) as KE. rewrite SEGS in KE. rewrite KE.
      apply (munch_mbyte _ _ _ _ _ MU1); [lia | apply OUT1; lia].
    - intros pn Hin. pose proof (rec_rep_O_blocks _ _ _ _ _ _ _ _ _ REP Hin) as Hb. rewrite BL2.
      rewrite BL1 in Hb. apply in_mid_inv. exact Hb. }
  split; [exact RA3|].
  split.
  { destruct (YL01.ax_statics AX L2 A2 m3 md2 MR3) as (_ & (g & Hg & HGW) & _).
    apply (f18_words_after mem m3 g F18); [| exact Hg | rewrite SEGS, GUARDG in HGW; exact HGW].
    intros i Hi. exact (GK3 i Hi). }
  split; [exact INIT2|].
  split; [exact REG2|].
  exact RES2.
Qed.

End SR.
