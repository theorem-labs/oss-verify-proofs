(* Segment M02 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput (plain, ELF 8dec0b814e6f): piece C of its inner walk,
   0x13c00 .. 0x13c64, the probe loop
   for (i = 0; i < m->n; i++) { snprintf(probe, 18, "%sx", m->seg[i].name);
                                 if (!m_find(m, probe, strlen(probe))) check_absent(c, probe); }
   as M02D.M02_C_stmt from the contracts of snprintf, strlen, m_find and check_absent.
   The code: `lw a0,0(s10)` (m->n, M02Bridge.mb_mconf_n), `blez` to 0x13c64; s1 = i = 0, s3 = 0x108cd ("%sx" in
   .rodata), s4 = m. Turn i (0x13c18, [c_turn]): a0 = probe = sp + 0x40, a1 = 18, a2 = s3, a3 = s4 = m + 256 i (the
   name of m->seg[i]: M02Bridge.mb_mname), `jal snprintf` ([c_snp]: the probe holds T = name ++ "x", c_T); a0 =
   probe, `jal strlen` ([c_strlen]: the slack after the NUL is main's frame, M02K.m02_bytes); a2 = |T|, a1 = probe,
   a0 = s0 = m, `jal m_find` ([c_mfind]); `bnez a0` to 0x13c54 (m_find_ptr is m + 256 j > 0 for a hit); else a1 =
   probe, a0 = s8 = c, `jal check_absent` ([c_absent]; absent rc T from M02_model's probe check, T being
   snprintf_s 18 F_probe [AS name] by M02Bridge.mb_probe_s). Latch 0x13c54 ([c_loop]): `lw a0,0(s10)`, s1 += 1,
   s4 += 0x100, `blt s1,a0` to 0x13c18. Each callee's writes lie in M02_W (M02K.m02_inv_step / m02_inv_step_tm);
   s0, s3, s4, s6 = cap, s8, s10 and sp are callee-saved through the calls. The image-free lemmas (the probe text
   c_T, c_pf_zs, c_T_nz, c_name_rng, c_T_rng, the name slack c_pad16) and m_find's index bound mb_mfind_lt are in
   M02Bridge, shared with the UBSan walk; `blt` on small words is M02K.m02_lts, the bounds M02K.m02_bnds.
   Part of the proof of LLVMFuzzerTestOneInput: piece C of segment M02 of its walk; no released proof of
   fuzz_segconf's LLVMFuzzerTestOneInput exists, written new (segment piece). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge FP.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require MemNorm.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_env printf_facts_c
  snprintf_c strlen_c m_find_c check_absent_c reac_segconf_find_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require check_segments.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require Import Tac_slot M02D M02K.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog.Seg Require M02_bridge.
Import M02_bridge.M02Bridge.
Import ListNotations.
Open Scope Z_scope.

(* ---- The probe's bytes (plain printf_facts_c.pf_bytes) ---- *)
Lemma c_zs_pf : forall l, Forall (fun x => 0 < x < 256) l -> zs (pf_bytes l) = l.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  inversion H as [|? ? Hx Hl]; subst. cbv beta in Hx.
  specialize (IH Hl). unfold zs, pf_bytes in *. cbn [map]. f_equal; [|exact IH].
  rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
Qed.

Lemma c_pf_len : forall l, length (pf_bytes l) = length l.
Proof. intros l. unfold pf_bytes. apply length_map. Qed.

Lemma c_nonul : forall l, Forall (fun x => 0 < x < 256) l -> ~ In ZERO (pf_bytes l).
Proof.
  intros l H Hin. apply (in_map (@bv_unsigned 8)) in Hin.
  change (map (@bv_unsigned 8) (pf_bytes l)) with (zs (pf_bytes l)) in Hin.
  rewrite (c_zs_pf l H) in Hin.
  rewrite Forall_forall in H. specialize (H _ Hin). cbv beta in H.
  assert (E0 : bv_unsigned ZERO = 0) by reflexivity. lia.
Qed.

(* ---- Image and memory facts of the plain build ---- *)
(* No reserved segment of the image reaches SL_TOP: a printf destination above it is image-free. *)
Lemma c_img_free : forall D n, SL_TOP <= D -> pf_img_free D n.
Proof.
  intros D n HD i Hi s Hs. unfold segments_reserved in Hs. apply in_map_iff in Hs as (seg & <- & Hseg).
  destruct (sl_rsegs_seg seg Hseg) as (_ & _ & R3).
  pose proof (bv_unsigned_in_range _ (snd (segment_reservation seg))) as R. lia.
Qed.

Lemma c_ba_eq : forall m a a' bs, bytes_at rsegs m a bs -> a = a' -> bytes_at rsegs m a' bs.
Proof. intros m a a' bs H <-. exact H. Qed.

(* "%sx" and its NUL at 0x108cd in .rodata. *)
Lemma c_fmt_ro : ro_bytes_b rsegs 0x108cd (pf_bytes ([37; 115; 120] ++ [0])) = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- Tactics ---- *)
Ltac c_reg := first [ rewrite unsigned_lit by lia; lia | reflexivity ].
Ltac c_kprep K :=
  try (rewrite m02_lts in K by lia);
  zify_cond K;
  try (rewrite ?andb_false_iff, ?orb_true_iff, ?Z.ltb_lt, ?Z.ltb_ge, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq,
         ?Z.eqb_neq in K).
(* A branch the facts force (taken) or refute (not taken). *)
Ltac c_tkn := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ clear K | exfalso; c_kprep K; first [ lia | Z.div_mod_to_equations; lia ] ]
  | _ => idtac end.
Ltac c_ntk := lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K;
      [ exfalso; c_kprep K; first [ lia | Z.div_mod_to_equations; lia ] | clear K ]
  | _ => idtac end.
(* A callee's write set inside M02_W S, and below 2^47 (all of it lies below hi = main's sp). *)
Ltac c_subfp := let x := fresh "x" in let Hx := fresh "Hx" in
  unfold sub_fp, M02_W, M02_FRAME; intros x Hx; cbn [outside] in *;
  destruct Hx as (?H1 & ?H2 & _); repeat split; lia.
Ltac c_low hi := let x := fresh "x" in let Hx := fresh "Hx" in let O := fresh "O" in
  intros x Hx O; cbn [outside] in O;
  destruct (Z_lt_le_dec x hi); [lia | exfalso; apply O; repeat split; lia].

(* ---- The four calls, each from main's frame (sp = S - 208) with the probe at sp + 0x40 = S - 144 ---- *)
(* snprintf(probe, 18, "%sx", m->seg[i].name): the probe holds T = name ++ "x" and its NUL. *)
Lemma c_snp : snprintf_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf)
         (mc : mconf) (i : nat),
  M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m -> frm0 fc -> (i < length (mc_seg mc))%nat ->
  bv_unsigned sp = S - 208 -> bv_unsigned a0 = S - 144 -> bv_unsigned a1 = 18 -> bv_unsigned a2 = 0x108cd ->
  bv_unsigned a3 = mm + 256 * Z.of_nat i ->
  evt rsegs (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F' : bvmap 5 word)
                         (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (Z.of_nat (length (c_T mc i)))) x11 x12 x13 x14 x15
                       x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F' (ret_pc ra) fc' None m'
                  (seg_rom rsegs) /\
         frm0 fc' /\ M02_inv S m0 m' /\ bytes_at rsegs m' (S - 144) (pf_bytes (c_T mc i) ++ [ZERO]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SNPRINTF) fc None m (seg_rom rsegs)).
Proof.
  intros SN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc i HM HI FRM Hi Esp Ea0 Ea1 Ea2 Ea3.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MI : mem_inv rsegs m) by (eapply m02_mem_inv; eassumption).
  assert (TM : MemNorm.task_mem rsegs m) by (eapply m02_task_mem; eassumption).
  assert (SSP : ssp_ok m) by (eapply m02_ssp; eassumption).
  destruct SSP as (GG & g & GQ).
  assert (ST : stk rsegs m (S - 65536) S) by (eapply m02_stk; eassumption).
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mconf_n rsegs m mm mc MC) as (_ & L32).
  destruct (mb_mname rsegs m mm mc i MC Hm16 Hi) as (_ & _ & (sx & sl & Bn & Zx & _ & Ln) & NF & L16).
  assert (Lsx : length sx = length (ms_name (nth i (mc_seg mc) mseg_d)))
    by (rewrite <- Zx; unfold zs; rewrite length_map; reflexivity).
  rewrite length_app in Ln. cbn [length] in Ln.
  assert (TL : (length (c_T mc i) <= 16)%nat) by (unfold c_T; rewrite length_app; cbn [length]; lia).
  assert (JK : exists junk, rw_cells rsegs m (S - 144) [CB (Z.to_nat 18) junk])
    by (eapply m02_cells; try eassumption; lia).
  destruct JK as (junk & JK).
  pose proof (SN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                (S - 65536) g [37; 115; 120] [Ps; PLit 120] [APtr (ms_name (nth i (mc_seg mc) mseg_d))] (c_T mc i)
                junk) as C.
  cbv zeta in C. rewrite Esp, Ea0, Ea1, Ea2 in C.
  assert (P1 : bytes_at rsegs m 0x108cd (pf_bytes ([37; 115; 120] ++ [0]))).
  { apply (ro_bytes_at rsegs m); [exact MI | lia | apply Z.leb_le; reflexivity |].
    exact (ro_bytes_b_sound rsegs _ _ c_fmt_ro). }
  assert (P2 : RO_LO <= 0x108cd) by (apply Z.leb_le; reflexivity).
  assert (P3 : 0x108cd + Z.of_nat (length [37; 115; 120]) + 1 <= RO_END) by (apply Z.leb_le; reflexivity).
  assert (P4 : pf_parse [37; 115; 120] = Some [Ps; PLit 120]) by reflexivity.
  assert (PA : pf_args_ok m (S - 208) (S - 65536) (S - 144) 18 [a3; a4; a5; a6; a7]
                 [APtr (ms_name (nth i (mc_seg mc) mseg_d))]).
  { cbn [pf_args_ok pf_arg_ok]. rewrite Ea3. split; [|exact I]. split; [exact (c_name_rng sx _ Zx NF)|].
    exists sl. split; [|split; [|split; [lia | split; [left | left]]]].
    - replace (pf_bytes (ms_name (nth i (mc_seg mc) mseg_d) ++ [0]) ++ sl) with (sx ++ ZERO :: sl); [exact Bn|].
      unfold pf_bytes. rewrite map_app, <- Zx, c_pf_zs, <- app_assoc. reflexivity.
    - apply c_pad16; [exact Hm16 | lia | lia | lia | lia].
    - lia.
    - lia. }
  assert (P6 : pf_text [Ps; PLit 120] [APtr (ms_name (nth i (mc_seg mc) mseg_d))] = Some (c_T mc i))
    by reflexivity.
  assert (P8 : 1 <= 18 < 2 ^ 31) by lia.
  assert (P9 : Z.of_nat (length (c_T mc i)) < 2 ^ 31 - 1) by lia.
  assert (P10 : 0 < S - 144) by lia.
  assert (P11 : S - 144 + 18 <= S - 65536 \/ S - 208 <= S - 144) by (right; lia).
  assert (P12 : pf_img_free (S - 144) 18) by (apply c_img_free; unfold SL_TOP; lia).
  assert (P13 : stk rsegs m (S - 65536) (S - 208))
    by exact (proj1 (stk_split rsegs m (S - 65536) (S - 208) S ST ltac:(lia))).
  assert (P14 : S - 65536 <= S - 208 - SNPRINTF_K) by (unfold SNPRINTF_K; lia).
  assert (P15 : IMG_END <= S - 65536) by (unfold IMG_END; lia).
  assert (P16 : S - 208 < 2 ^ 63) by lia.
  specialize (C P1 P2 P3 P4 PA P6 JK P8 P9 P10 P11 P12 P13 P14 P15 P16 FRM MI TM GG GQ).
  eapply evt_mono; [exact C|].
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & Ft & fc' & m' & E &
              MU & WM & MI' & TM' & FR' & _ & _ & BY).
  assert (E17 : firstn (Z.to_nat (18 - 1)) (c_T mc i) = c_T mc i)
    by (apply firstn_all2; change (Z.to_nat (18 - 1)) with 17%nat; lia).
  rewrite E17 in MU, BY. rewrite Esp in MU.
  hnf. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, Ft, fc', m'.
  split; [exact E|]. split; [exact FR'|]. split.
  - eapply m02_inv_step_tm; [exact HI | exact MU | exact WM | exact MI' | exact TM' | c_subfp].
  - unfold pf_bytes in BY |- *. rewrite map_app in BY. exact BY.
Qed.

(* strlen(probe) = |T|: the bytes after the NUL up to the next 8-byte boundary are main's frame. *)
Lemma c_strlen : strlen_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf)
         (mc : mconf) (T : list Z),
  M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m -> Forall (fun x => 0 < x < 256) T -> (length T <= 16)%nat ->
  bv_unsigned a0 = S - 144 -> bytes_at rsegs m (S - 144) (pf_bytes T ++ [ZERO]) ->
  evt rsegs (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                               (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (Z.of_nat (length T))) x11 x12 x13 x14 x15 x16 x17
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         M02_inv S m0 m' /\ bytes_at rsegs m' (S - 144) (pf_bytes T ++ [ZERO]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros SL ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc T HM HI TR TL Ea0 BY.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MI : mem_inv rsegs m) by (eapply m02_mem_inv; eassumption).
  pose proof (c_pf_len T) as LP.
  destruct (Z.mod_pos_bound (- (S - 144 + Z.of_nat (length T) + 1)) 8 ltac:(lia)) as [P0 P8].
  remember ((- (S - 144 + Z.of_nat (length T) + 1)) mod 8) as P eqn:EP.
  assert (SLe : exists sl, length sl = Z.to_nat P /\ bytes_at rsegs m (S - 144 + Z.of_nat (length T) + 1) sl)
    by (eapply m02_bytes; try eassumption; lia).
  destruct SLe as (sl & Lsl & Bsl).
  assert (B2 : bytes_at rsegs m (bv_unsigned a0) (pf_bytes T ++ ZERO :: sl)).
  { rewrite Ea0.
    replace (pf_bytes T ++ ZERO :: sl) with ((pf_bytes T ++ [ZERO]) ++ sl) by (rewrite <- app_assoc; reflexivity).
    apply bytes_at_app. split; [exact BY|].
    eapply c_ba_eq; [exact Bsl|]. rewrite length_app, LP. cbn [length]. lia. }
  eapply evt_mono.
  { eapply SL with (str := pf_bytes T) (slack := sl);
      [exact B2 | exact (c_nonul T TR) | rewrite Ea0, LP, Lsl, <- EP; lia | exact MI]. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & E & MU & WM &
              MI' & BY').
  rewrite LP in E. rewrite Ea0 in BY'.
  replace (pf_bytes T ++ Z_to_bv 8 0 :: sl) with ((pf_bytes T ++ [ZERO]) ++ sl) in BY'
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in BY' as [BY'' _].
  hnf. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'.
  split; [exact E|]. split; [|exact BY''].
  eapply m02_inv_step; [exact HI | exact MU | exact WM | exact MI' | c_subfp | c_low (S - 208)].
Qed.

(* m_find(m, probe, |T|): a0 = m_find_ptr m mc T. *)
Lemma c_mfind : m_find_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf)
         (mc : mconf) (T : list Z),
  M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m -> Forall (fun x => 0 < x < 256) T -> (length T <= 16)%nat ->
  bv_unsigned sp = S - 208 -> bv_unsigned a0 = mm -> bv_unsigned a1 = S - 144 ->
  bv_unsigned a2 = Z.of_nat (length T) -> bytes_at rsegs m (S - 144) (pf_bytes T ++ [ZERO]) ->
  evt rsegs (fun ms' => exists (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                               (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 (m_find_ptr mm mc T)) x11 x12 x13 x14 x15 x16 x17
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         M02_inv S m0 m' /\ bytes_at rsegs m' (S - 144) (pf_bytes T ++ [ZERO]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 M_FIND) fc None m (seg_rom rsegs)).
Proof.
  intros MF ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc T HM HI TR TL Esp Ea0 Ea1 Ea2 BY.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MI : mem_inv rsegs m) by (eapply m02_mem_inv; eassumption).
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  assert (SO : stack_ok rsegs m (S - 65536) (S - 208) M_FIND_STACK)
    by (eapply m02_stack_ok; try eassumption; cbv [M_FIND_STACK M02_FRAME]; lia).
  pose proof (c_pf_len T) as LP.
  eapply evt_mono.
  { eapply MF with (lo := S - 65536) (mc := mc) (l := pf_bytes T).
    rewrite Esp, Ea0, Ea1, Ea2. unfold m_find_pre.
    split; [lia|]. split; [exact Hm16|]. split; [exact MC|]. split; [unfold apart, SEG_M_SIZE; left; lia|].
    split; [apply bytes_at_app in BY as [BY1 _]; exact BY1|].
    split; [rewrite LP; reflexivity|]. split; [unfold apart; right; lia|]. split; [exact SO | exact MI]. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & E & MU & WM &
              MI' & _ & _).
  rewrite Ea0, (c_zs_pf T TR) in E. rewrite Esp in MU. change M_FIND_STACK with 48 in MU.
  hnf. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'.
  split; [exact E|]. split.
  - eapply m02_inv_step; [exact HI | exact MU | exact WM | exact MI' | c_subfp | c_low (S - 208)].
  - eapply bytes_at_transport; [exact BY | exact MU |]. cbn [disjoint_from]. split; [right; lia | exact I].
Qed.

(* check_absent(c, probe) when m_find found no entry: the probe is absent from the reader's state. *)
Lemma c_absent : check_absent_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (S c mm cap : Z) (rc : rconf)
         (mc : mconf) (T : list Z),
  M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m -> Forall (fun x => 0 < x < 256) T -> (length T <= 16)%nat ->
  absent rc T = true ->
  bv_unsigned sp = S - 208 -> bv_unsigned a0 = c -> bv_unsigned a1 = S - 144 ->
  bytes_at rsegs m (S - 144) (pf_bytes T ++ [ZERO]) ->
  evt rsegs (fun ms' => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         M02_inv S m0 m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 CHECK_ABSENT) fc None m (seg_rom rsegs)).
Proof.
  intros CA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc T HM HI TR TL AB Esp Ea0 Ea1 BY.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MI : mem_inv rsegs m) by (eapply m02_mem_inv; eassumption).
  assert (RC : rconf_at rsegs m c rc) by (eapply m02_rconf; eassumption).
  assert (SO : stack_ok rsegs m (S - 65536) (S - 208) CHECK_ABSENT_STACK).
  { eapply m02_stack_ok; try eassumption. change CHECK_ABSENT_STACK with 80. cbv [M02_FRAME]. lia. }
  eapply evt_mono.
  { eapply CA with (lo := S - 65536) (rc := rc) (nm := T).
    rewrite Esp, Ea0, Ea1. unfold check_absent_pre, query_pre. split; [|exact AB].
    split; [lia|]. split; [exact Hc16|]. split; [exact RC|]. split; [unfold apart, SEG_C_SIZE; left; lia|].
    split; [lia|].
    split; [exists (pf_bytes T); split; [exact BY | split; [exact (c_zs_pf T TR) | exact (c_T_nz T TR)]]|].
    split; [unfold apart; right; lia|]. split; [exact SO | exact MI]. }
  intros ms' (x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & E & MU &
              WM & MI' & _ & _).
  rewrite Esp in MU. change CHECK_ABSENT_STACK with 80 in MU.
  hnf. exists x5, x6, x7, x10, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m'.
  split; [exact E|].
  eapply m02_inv_step; [exact HI | exact MU | exact WM | exact MI' | c_subfp | c_low (S - 208)].
Qed.

(* ---- One turn: 0x13c18 .. 0x13c54 ---- *)
(** The state at the latch 0x13c54 of turn i: s1 = i, s3 = "%sx", s4 = m + 256 i and the other callee-saved
    registers as at the head; the memory an M02_inv successor of m0. *)
Definition c_at54 (S c mm : Z) (i : nat) (gp tp w2 w5 w6 w7 w9 w11 : word) (m0 : word -> option byte)
    : machine_state -> Prop :=
  fun ms => exists (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F' : bvmap 5 word)
                   (fc' : bv 32) (m' : word -> option byte),
    ms = MS (mkR x1 (Z_to_bv 64 (S - 208)) gp tp x5 x6 x7 (Z_to_bv 64 mm) (Z_to_bv 64 (Z.of_nat i)) x10 x11 x12 x13
                 x14 x15 x16 x17 w2 (Z_to_bv 64 0x108cd) (Z_to_bv 64 (mm + 256 * Z.of_nat i)) w5 w6 w7
                 (Z_to_bv 64 c) w9 (Z_to_bv 64 (mm + 8192)) w11 x28 x29 x30 x31)
            F' (Z_to_bv 64 0x13c54) fc' None m' (seg_rom rsegs) /\
    frm0 fc' /\ M02_inv S m0 m'.

Lemma c_turn : snprintf_contract -> strlen_contract -> m_find_contract -> check_absent_contract ->
  forall (S c mm cap : Z) (rc : rconf) (mc : mconf) (ret : bool) (m0 : word -> option byte) (i : nat)
         (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 gp tp w2 w5 w6 w7 w9 w11 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 -> M02_inv S m0 m -> frm0 fc ->
  (i < length (mc_seg mc))%nat ->
  evt rsegs (c_at54 S c mm i gp tp w2 w5 w6 w7 w9 w11 m0)
    (MS (mkR x1 (Z_to_bv 64 (S - 208)) gp tp x5 x6 x7 (Z_to_bv 64 mm) (Z_to_bv 64 (Z.of_nat i)) x10 x11 x12 x13
             x14 x15 x16 x17 w2 (Z_to_bv 64 0x108cd) (Z_to_bv 64 (mm + 256 * Z.of_nat i)) w5 w6 w7
             (Z_to_bv 64 c) w9 (Z_to_bv 64 (mm + 8192)) w11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c18) fc None m (seg_rom rsegs)).
Proof.
  intros SN SL MF CA S c mm cap rc mc ret m0 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
    gp tp w2 w5 w6 w7 w9 w11 F fc m HMOD HM HI FRM Hi.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mconf_n rsegs m mm mc MC) as (_ & L32).
  destruct (mb_mname rsegs m mm mc i MC Hm16 Hi) as (_ & _ & (sx & sl & _ & Zx & _ & _) & NF & L16).
  pose proof (c_T_rng mc i sx Zx NF) as TR.
  assert (TL : (length (c_T mc i) <= 16)%nat) by (unfold c_T; rewrite length_app; cbn [length]; lia).
  assert (AB : m_find mc (c_T mc i) = None -> absent rc (c_T mc i) = true).
  { intros EF. destruct HMOD as (_ & _ & _ & _ & HP & _). rewrite forallb_forall in HP.
    specialize (HP (nth i (mc_seg mc) mseg_d) ltac:(apply nth_In; exact Hi)). cbv beta in HP.
    rewrite mb_probe_s in HP by (first [exact NF | lia]).
    unfold probe_ok in HP. unfold c_T in EF |- *. rewrite EF in HP. exact HP. }
  clear HMOD.
  (* 0x13c18 addi a0,sp,0x40; 0x13c1c li a1,18; 0x13c20 mv a2,s3; 0x13c24 mv a3,s4; 0x13c28 jal snprintf *)
  do 5 step.
  eapply evt_cut.
  { eapply (c_snp SN) with (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (m0 := m0) (i := i);
      [exact HM | exact HI | exact FRM | exact Hi | c_reg | c_reg | c_reg | c_reg | c_reg]. }
  intros ms' (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F1 & fc1 & m1 & -> &
              FR1 & HI1 & BY1).
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13c2c addi a0,sp,0x40; 0x13c30 jal strlen *)
  do 2 step.
  eapply evt_cut.
  { eapply (c_strlen SL) with (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (m0 := m0)
      (T := c_T mc i); [exact HM | exact HI1 | exact TR | exact TL | c_reg | exact BY1]. }
  intros ms' (z5 & z6 & z7 & z11 & z12 & z13 & z14 & z15 & z16 & z17 & z28 & z29 & z30 & z31 & m2 & -> & HI2 & BY2).
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13c34 mv a2,a0; 0x13c38 addi a1,sp,0x40; 0x13c3c mv a0,s0; 0x13c40 jal m_find *)
  do 4 step.
  eapply evt_cut.
  { eapply (c_mfind MF) with (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (m0 := m0)
      (T := c_T mc i); [exact HM | exact HI2 | exact TR | exact TL | c_reg | c_reg | c_reg | c_reg | exact BY2]. }
  intros ms' (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m3 & -> & HI3 & BY3).
  rewrite ret_pc_even by (try lia; reflexivity).
  (* 0x13c44 bnez a0 *)
  destruct (m_find mc (c_T mc i)) as [j|] eqn:EF.
  - pose proof (mb_mfind_lt mc _ j EF) as Hj.
    assert (EP : m_find_ptr mm mc (c_T mc i) = mm + 256 * Z.of_nat j)
      by (unfold m_find_ptr; rewrite EF; reflexivity).
    rewrite EP.
    step. c_tkn.
    apply evt_done. unfold c_at54. hnf. do 19 eexists. split; [reflexivity|]. split; [exact FR1 | exact HI3].
  - assert (EP : m_find_ptr mm mc (c_T mc i) = 0) by (unfold m_find_ptr; rewrite EF; reflexivity).
    rewrite EP.
    step. c_ntk.
    (* 0x13c48 addi a1,sp,0x40; 0x13c4c mv a0,s8; 0x13c50 jal check_absent *)
    do 3 step.
    eapply evt_cut.
    { eapply (c_absent CA) with (S := S) (c := c) (mm := mm) (cap := cap) (rc := rc) (mc := mc) (m0 := m0)
        (T := c_T mc i); [exact HM | exact HI3 | exact TR | exact TL | exact (AB eq_refl) | c_reg | c_reg | c_reg |
                          exact BY3]. }
    intros ms' (v5 & v6 & v7 & v10 & v11 & v12 & v13 & v14 & v15 & v16 & v17 & v28 & v29 & v30 & v31 & m4 & -> &
                HI4).
    rewrite ret_pc_even by (try lia; reflexivity).
    apply evt_done. unfold c_at54. hnf. do 19 eexists. split; [reflexivity|]. split; [exact FR1 | exact HI4].
Qed.

(* ---- The loop: turn i at 0x13c18 with k turns left, to 0x13c64 ---- *)
Lemma c_loop : snprintf_contract -> strlen_contract -> m_find_contract -> check_absent_contract ->
  forall (S c mm cap : Z) (rc : rconf) (mc : mconf) (ret : bool) (m0 : word -> option byte)
         (gp tp v2 v5 v7 v9 v11 : word),
  M02_model rc mc ret -> M02_mem S c mm cap rc mc m0 ->
  forall (k i : nat) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w9 w20 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  (i + k = length (mc_seg mc))%nat -> (0 < k)%nat ->
  w9 = Z_to_bv 64 (Z.of_nat i) -> w20 = Z_to_bv 64 (mm + 256 * Z.of_nat i) ->
  frm0 fc -> M02_inv S m0 m ->
  evt rsegs (M02_mid 0x13c64 S c mm (fun w => w = Z_to_bv 64 cap) gp tp m0)
    (MS (mkR x1 (Z_to_bv 64 (S - 208)) gp tp x5 x6 x7 (Z_to_bv 64 mm) w9 x10 x11 x12 x13 x14 x15 x16 x17
             v2 (Z_to_bv 64 0x108cd) w20 v5 (Z_to_bv 64 cap) v7 (Z_to_bv 64 c) v9 (Z_to_bv 64 (mm + 8192)) v11
             x28 x29 x30 x31)
        F (Z_to_bv 64 0x13c18) fc None m (seg_rom rsegs)).
Proof.
  intros SN SL MF CA S c mm cap rc mc ret m0 gp tp v2 v5 v7 v9 v11 HMOD HM.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  induction k as [|k IH]; intros i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w9 w20 F fc m
    Hik Hk E9 E20 FRM HI; [lia|].
  subst w9 w20.
  eapply evt_cut.
  { eapply (c_turn SN SL MF CA) with (cap := cap) (rc := rc) (mc := mc) (ret := ret) (m0 := m0);
      [exact HMOD | exact HM | exact HI | exact FRM | lia]. }
  intros ms' (y1 & y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & F' & fc' &
              m' & -> & FR' & HI').
  assert (MC' : mconf_at rsegs m' mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mconf_n rsegs m' mm mc MC') as (RD & L32). unfold MC_N in RD.
  (* 0x13c54 lw a0,0(s10) *)
  step.
  rewrite (check_segments.CsPure.sx32_small (Z.of_nat (length (mc_seg mc)))) by lia.
  (* 0x13c58 addi s1,s1,1; 0x13c5c addi s4,s4,0x100; 0x13c60 blt s1,a0 *)
  do 3 step.
  destruct k as [|k].
  - c_ntk.
    apply evt_done. unfold M02_mid. hnf. do 28 eexists. split; [reflexivity|].
    split; [exact FR'|]. split; [exact HI' | reflexivity].
  - c_tkn.
    eapply (IH (Datatypes.S i)); [lia | lia | f_equal; lia | f_equal; lia | exact FR' | exact HI'].
Qed.

(* ---- Piece C: 0x13c00 .. 0x13c64 ---- *)
Theorem m02_C : snprintf_c.snprintf_contract -> strlen_c.strlen_contract -> m_find_c.m_find_contract ->
  check_absent_c.check_absent_contract -> M02D.M02_C_stmt.
Proof.
  intros SN SL MF CA. unfold M02_C_stmt.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m
    S c mm cap rc mc ret Esp Es0 Es8 Es10 Es6 FRM HMOD HM HI.
  subst sp s0 s8 s10 s6.
  unfold M02_FRAME, MC_N.
  destruct (m02_bnds S c mm cap rc mc m0 HM) as (H16 & HT & H47 & Hc0 & Hc16 & Hc & Hm0 & Hm16 & Hm).
  unfold SEG_C_SIZE in Hc. unfold SEG_M_SIZE in Hm.
  assert (MC : mconf_at rsegs m mm mc) by (eapply m02_mconf; eassumption).
  destruct (mb_mconf_n rsegs m mm mc MC) as (RD & L32). unfold MC_N in RD.
  (* 0x13c00 lw a0,0(s10) *)
  step.
  rewrite (check_segments.CsPure.sx32_small (Z.of_nat (length (mc_seg mc)))) by lia.
  (* 0x13c04 blez a0 *)
  step.
  destruct (Nat.eq_dec (length (mc_seg mc)) 0) as [N0|N0].
  - c_tkn.
    apply evt_done. unfold M02_mid. hnf. do 28 eexists. split; [reflexivity|].
    split; [exact FRM|]. split; [exact HI | reflexivity].
  - c_ntk.
    (* 0x13c08 li s1,0; 0x13c0c auipc a0; 0x13c10 addi s3,a0,-0x33f ("%sx"); 0x13c14 mv s4,s0 *)
    do 4 step.
    eapply (c_loop SN SL MF CA) with (rc := rc) (mc := mc) (ret := ret) (k := length (mc_seg mc)) (i := 0%nat);
      [exact HMOD | exact HM | lia | lia | f_equal; lia | f_equal; lia | exact FRM | exact HI].
Qed.
