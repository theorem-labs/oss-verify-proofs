(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v; 310 of its 361 lines of code are new or changed and 164 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 pins_clear_c lv2_refusals_forget_c sup_resp_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pinclr_code_range : forall R uri, -2^31 <= r_code R < 2^31 -> -2^31 <= snd (pins_clear_m R uri) < 2^31.
Proof.
  intros R uri HC. cbv beta zeta delta [pins_clear_m rec_stub_code rec_answer_code].
  assert (E : r_code (rec_record R REC_PINS_CLEAR [sarg uri]) = r_code R)
    by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  destruct (r_refuse (rec_record R REC_PINS_CLEAR [sarg uri]) =? 0); cbn [snd]; [lia | rewrite E; exact HC].
Qed.

Section V.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Definition pinclr_vpost (K : Z) (L : layout) (A : astate) (rg : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (O : list (Z * Z)) (b : sbound) (sizes : list Z) (R' : rstate) (Q : bvmap 5 word -> Prop) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' rg' mem' md' O',
    c' = mkCfg (@mkst fx' rg' (getr rg 1) mem' (seg_rom rsegs)) md' /\
    RecKindB.fp_kept fx fx' /\
    RecKindB.call_post_rec B MR K L A rg mem md RecKindB.rec_area (fun a => In a (map fst O)) L' A' rg' mem' md' /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ RecKindB.owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') -> (In pn (blocks L A) /\ ~ In pn O) \/ In pn O') /\
    RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    ro_agree (ms_segs B) mem' /\ st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    res_ok_slots A' (RecKindB.sb_mallocs b sizes) /\ Q rg'.

Lemma pinclr_call_v : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret sizes R' Q P,
  @vr_state fx _ B API S rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  getr rg 1 = Z_to_bv 64 ret -> 0 <= K <= 14336 ->
  (k1 + length sizes <= 32)%nat -> Forall (fun n => 0 <= n <= 8194) sizes ->
  SR rsegs c (pinclr_vpost K L1 A1 rg mem1 md1 O1 (sb_n (s_b S) k1) sizes R' Q) ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' c',
     @vr_state fx' _ B API S rg' ret mem' md' L' A' R' O' (k1 + length sizes) qv xq jk c' ->
     Q rg' -> regs_preserved rg rg' -> SR rsegs c' P) ->
  SR rsegs c P.
Proof.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c K ret sizes R' Q P HST E1 HK HKS HSZ HSR KONT.
  pose proof (vf_segs B API HF) as SEGS.
  eapply SR_bind; [exact HSR|].
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & -> & FPK & POST & REC & OWN & BLK & OK & RO & INIT & RLEN
    & RES & HQ).
  pose proof HST as (_ & FPK0 & VR & H & FR & GQ & GW).
  pose proof POST as (HM' & _ & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _).
  pose proof (vregs_sp B API S HS rg VR) as SPR.
  pose proof (frame_keep B API HF S HS K rg mem1 mem' L1 A1 L' A' md1 md' RecKindB.rec_area HM1 HM' SPR
    rec_area_low HFR) as KP.
  pose proof (gq_keep B API HF S HS K rg mem1 mem' L1 A1 L' A' md1 md' RecKindB.rec_area HM1 HM' SPR HK
    rec_area_gq HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  assert (HQX : match xq with
                | Some (q, nq, t) => bytes_at rsegs mem' q (t ++ [Z_to_bv 8 0]) /\ Z.of_nat (length t) + 1 <= nq
                | None => True
                end).
  { pose proof (h_q B API S _ _ _ _ _ _ _ _ H) as HQ1.
    pose proof (h_t B API S _ _ _ _ _ _ _ _ H) as T.
    destruct xq as [[[q nq] t]|]; [|exact I].
    destruct HQ1 as [Hb Hl]. split; [|exact Hl].
    destruct (t_x B API S _ _ _ _ _ _ _ _ T (q, nq) (or_intror (or_intror (or_introl eq_refl)))) as [Hin Hno].
    assert (Hno' : ~ In (q, nq) O1) by (intros Ho; apply Hno; apply in_map_iff; exists (q, nq); split; [reflexivity | exact Ho]).
    destruct (ok_surv B L1 A1 mem1 L' A' mem' O1 q nq OK Hin Hno') as [_ KB].
    apply (bytes_at_transfer rsegs mem1); [exact Hb|]. intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite <- SEGS. apply KB. lia. }
  apply (KONT fx' rg' mem' md' L' A' O'); [| exact HQ | exact HPR].
  split; [rewrite E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { apply (heap_step_stub B API HF S HS rg mem1 md1 L1 A1 R1 O1 k1 xq K L' A' rg' mem' md' R' O' [] xq
      (k1 + length sizes) H SPR HK POST REC OWN).
    - intros pn Hin. destruct (BLK pn Hin) as [X|X]; [left; exact X | right; left; exact X].
    - exact OK.
    - exact RO.
    - exact INIT.
    - exact RLEN.
    - exact (st_res B API S HS A' k1 sizes HKS HSZ RES).
    - exact HKS.
    - rewrite app_nil_r. reflexivity.
    - intros pn [].
    - constructor.
    - exact HQX. }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

Lemma pinclr_of_pc : forall L A rg mem md uri R O b c',
  pins_clear_ret B API L A rg mem md uri R O b c' ->
  sb_live (RecKindB.sb_mallocs b (pins_clear_sizes uri (snd (pins_clear_m R uri)))) <=
    sb_cap (RecKindB.sb_mallocs b (pins_clear_sizes uri (snd (pins_clear_m R uri)))) ->
  pinclr_vpost PINS_CLEAR_K L A rg mem md O b (pins_clear_sizes uri (snd (pins_clear_m R uri)))
    (fst (pins_clear_m R uri)) (fun rg' => getr rg' 10 = Z_to_bv 64 (snd (pins_clear_m R uri))) c'.
Proof.
  intros L A rg mem md uri R O b c'
    (fx' & L' & A' & rg' & mem' & md' & R' & O' & r & EM & E & FPK & POST & A0 & REC & OWN & BLK & OK & RO & _
     & INIT & RLEN & LE & RS) CAP.
  pose proof (vf_segs B API HF) as SEGS. rewrite SEGS in E. rewrite EM in *. cbn [fst snd] in *.
  exists fx', L', A', rg', mem', md', O'.
  split; [exact E|]. split; [exact FPK|]. split; [exact POST|]. split; [exact REC|]. split; [exact OWN|].
  split; [exact BLK|]. split; [exact OK|]. split; [exact RO|]. split; [exact INIT|]. split; [exact RLEN|].
  split; [exact (RecKindB.res_ok_slots_le A' _ _ LE CAP RS) | exact A0].
Qed.

End V.

Lemma pinclr_k1 : forall (tk : list (list byte)) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p1 : word),
  s5 = verbs_receive_disp.ntokw tk -> (length tk <= 64)%nat -> bv_unsigned sp < 2^63 ->
  (length tk = 2%nat -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1)) ->
  evt rsegs (fun ms' =>
      (length tk = 2%nat /\
       ms' = MS (mkR (Z_to_bv 64 0x17a78) sp gp tp t0 t1 t2 s0 s1 p1 (Z_to_bv 64 (-9)) a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x171b0) fc None m (seg_rom rsegs)) \/
      (length tk <> 2%nat /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a88) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17a5c) fc None m (seg_rom rsegs)).
Proof.
  intros tk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 E5 HL HSP HB. subst s5.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
  destruct (Z.of_nat (length tk) =? 2) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. assert (L2 : length tk = 2%nat) by lia.
    pose proof (verbs_receive_disp.read_all _ _ _ (HB L2)) as RD. rewrite length_le8 in RD.
    do 3 zstep. cond_by false.
    do 2 zstep. apply evt_done. left. split; [exact L2 | reflexivity].
  - apply Z.eqb_neq in E. apply evt_done. right. split; [lia | reflexivity].
Qed.

Lemma pinclr_k2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : Z),
  a0 = Z_to_bv 64 r -> -2^31 <= r < 2^31 ->
  evt rsegs (fun ms' =>
      (r <> 0 /\
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a8c) fc None m (seg_rom rsegs)) \/
      (r = 0 /\
       ms' = MS (mkR (Z_to_bv 64 0x17a80) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x1731c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17a78) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m r E0 HR. subst a0.
  zstep. rewrite (rec_shape_of.eqb_lit_signed r 0) by lia.
  destruct (r =? 0) eqn:E; cbv beta iota delta [negb].
  - apply Z.eqb_eq in E. zstep. apply evt_done. right. split; [exact E | reflexivity].
  - apply Z.eqb_neq in E. apply evt_done. left. split; [exact E | reflexivity].
Qed.

Lemma pinclr_k3 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x17a8c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17a80) fc None m (seg_rom rsegs)).
Proof. intros. do 2 zstep. apply evt_done. reflexivity. Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis SRESP : forall f : YK11.FPState, @sup_resp_contract f rc B API.
Hypothesis DP : forall f : YK11.FPState, @pins_clear_contract f rc B API.
Hypothesis DL : forall f : YK11.FPState, @lv2_refusals_forget_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_pinclr : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RPinclr) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RPinclr -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  join_k B API S 0x17a90 10 rg R1 k1 qv P ->
  rej_k B API S f 0x17a88 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK JOIN REJ.
  pose proof (vf_segs B API HF) as SEGS.
  pose proof HST as (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as LPT.
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO1. rewrite SEGS in RO1.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (SPB : bv_unsigned (reg_get rg 2) < 2^63) by (rewrite SP2; unfold s_spf, VR_K in *; lia).
  assert (R21 : reg_get rg 21 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N21; reflexivity).
  assert (NL : (length (toks D) <= 64)%nat) by lia.
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (HB : length (toks D) = 2%nat -> bytes_at rsegs (normalize rsegs mem1) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { intros L2. rewrite SP2. apply bytes_at_normalize; [exact RO1|].
    assert (E : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
    pose proof (frame_tok S mem1 jk 1 p1 FR E) as FT.
    replace (s_spf S + 16) with (s_spf S + 8 + 8 * Z.of_nat 1) by lia. exact FT. }
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RPinclr) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply (pinclr_k1 (toks D)) with (p1 := p1); [exact R21 | exact NL | exact SPB | exact HB]. }
  { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
  intros R' pc' rg' mem2 HQ X MK.
  destruct HQ as [(L2 & EQ)|(L2 & EQ)]; injection EQ as ER EP; subst R' pc'.
  2:{ assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
    eapply REJ. split; [exact (MK 0x17a88 eq_refl (vregs_pres S rg rg' VR PR))|].
    split; [rewrite (getr_of_eqv _ _ 18 X eq_refl); reflexivity|].
    split; [rewrite (getr_of_eqv _ _ 21 X eq_refl); reflexivity|].
    split; [|lia].
    rewrite RT. destruct (toks D) as [|v [|a [|b r]]] eqn:TK'; cbn [plan_at]; try reflexivity.
    exfalso. apply L2. rewrite ?TK'. reflexivity. }
  destruct (len2 (toks D) L2) as (v & a & TK).
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK 0x171b0 eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  assert (E1 : getr rg' 1 = Z_to_bv 64 0x17a78) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
  assert (E10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)).
  { rewrite Z_to_bv_bv_unsigned. rewrite (getr_of_eqv _ _ 10 X eq_refl). reflexivity. }
  assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17a78)) by (apply bv_eq; vm_compute; reflexivity).
  assert (KB : 0 <= PINS_CLEAR_K <= 14336) by (unfold PINS_CLEAR_K; lia).
  destruct (vs_pre B API HF S HS rg' 0x171b0 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ PINS_CLEAR_K 0x17a78
              HST1 E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
  assert (EP1 : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
  assert (EA : nth_error (toks D) 1 = Some a) by (rewrite TK; reflexivity).
  pose proof (st_tok_arg B API HF S HS rg' 0x171b0 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ PINS_CLEAR_K 1 p1 a
                HST1 KB EP1 EA) as SA.
  assert (LA : Z.of_nat (length a) <= 8192).
  { assert (IA : In a (toks D)) by (rewrite TK; right; left; reflexivity).
    pose proof (verbs_receive_route.toks_len D a IA) as LW.
    pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia. }
  pose proof (pinclr_code_range R1 (Some a) (rep_code _ _ _ _ _ _ REC)) as CR.
  pose proof (resp_length _ CR) as RL.
  assert (HSZ : Forall (fun n => 0 <= n <= 8194) (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a))))).
  { unfold pins_clear_sizes, sarg. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. }
  assert (HKS : (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))) <= 32)%nat) by (unfold pins_clear_sizes; cbn [length]; lia).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST1))))) as (RES & _).
  pose proof (st_room B API S HS k1 _ (LMAX + 1) HKS HSZ ltac:(unfold LMAX; lia)) as ROOM.
  assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k1) (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a))))) <=
                sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k1) (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))))).
  { destruct (sb_mallocs_fields (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))) (sb_n (s_b S) k1)) as (F1 & _ & F3).
    rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
    unfold sb_n. cbn [sb_live sb_cap] in *. unfold pins_clear_sizes. cbn [length]. lia. }
  apply (pinclr_call_v B API HF S HS rg' 0x171b0 mem2 md1 L1 A1 R1 O1 k1 qv None jk _ PINS_CLEAR_K 0x17a78 (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a))))
           (fst (pins_clear_m R1 (Some a))) (fun rg2 => getr rg2 10 = Z_to_bv 64 (snd (pins_clear_m R1 (Some a)))) P HST1 E1 KB HKS HSZ).
  { eapply SR_mono.
    { pose proof (DP f L1 A1 rg' mem2 md1 (bv_unsigned p1) (Some a) R1 O1 (sb_n (s_b S) k1) PRE E10
                    ltac:(rewrite SPR; exact SA) REC RO FZ F18 RES ROOM) as C.
      rewrite SEGS in C. unfold PINS_CLEAR in C. exact C. }
    intros c'' HR. exact (pinclr_of_pc B API HF L1 A1 rg' mem2 md1 (Some a) R1 O1 (sb_n (s_b S) k1) c'' HR CAP). }
  intros f2 rg2 mem3 md3 La2 Aa2 O2 c2 HST2 Q2 HP2.
  pose proof HST2 as (_ & _ & VR2 & _).
  eapply (ka_nw B API HF S HS rg2 0x17a78 mem3 md3 La2 Aa2 _ O2 _ qv None jk c2 _ P HST2).
  { unfold Regs6ss.mkR_of. apply (pinclr_k2) with (r := snd (pins_clear_m R1 (Some a))); [exact Q2 | exact CR]. }
  { intros ms' [(_ & E)|(_ & E)]; subst ms'; do 2 eexists; reflexivity. }
  intros R3 pc3 rg3 mem4 HQ3 X3 MK3.
  destruct HQ3 as [(NZ & EQ)|(Z0 & EQ)]; injection EQ as ER EP; subst R3 pc3.
  - assert (PR3 : regs_preserved rg2 rg3) by (apply (pres_of rg2 _ rg3 X3); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK3 0x17a8c eq_refl (vregs_pres S rg2 rg3 VR2 PR3)) as HST3.
    eapply (resp_join B API HF S HS SRESP rg R1 k1 qv false 0x17a8c 0x17a90 rg3 mem4 md3 La2 Aa2 _ O2 _ jk _ (snd (pins_clear_m R1 (Some a))) P).
    + left. split; reflexivity.
    + exact HST3.
    + rewrite (getr_of_eqv _ _ 10 X3 eq_refl). exact Q2.
    + exact CR.
    + exact (eq_trans (PR3 18 ltac:(unfold callee_saved; lia))
               (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia)))).
    + intros _. exact (eq_trans (PR3 21 ltac:(unfold callee_saved; lia))
               (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia)))).
    + rewrite RT, TK. cbn [plan_at]. revert NZ. unfold VerbsRun.run_step.
      destruct (pins_clear_m R1 (Some a)) as [Rp r']. cbv beta iota zeta delta [VerbsRun.pins_follow fst snd].
      intros NZ. apply Z.eqb_neq in NZ. rewrite NZ. reflexivity.
    + unfold pins_clear_sizes. cbn [length]. lia.
    + unfold pins_clear_sizes. cbn [length]. lia.
    + exact HK.
    + exact JOIN.
  - assert (PR3 : regs_preserved rg2 rg3) by (apply (pres_of rg2 _ rg3 X3); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK3 0x1731c eq_refl (vregs_pres S rg2 rg3 VR2 PR3)) as HST3.
    assert (E1' : getr rg3 1 = Z_to_bv 64 0x17a80) by (rewrite (getr_of_eqv _ _ 1 X3 eq_refl); reflexivity).
    assert (E10' : getr rg3 10 = Z_to_bv 64 0).
    { rewrite (getr_of_eqv _ _ 10 X3 eq_refl). transitivity (Z_to_bv 64 (snd (pins_clear_m R1 (Some a)))); [exact Q2 | rewrite Z0; reflexivity]. }
    assert (RET' : YK0s.ret_ok (Z_to_bv 64 0x17a80)) by (apply bv_eq; vm_compute; reflexivity).
    assert (KB' : 0 <= LV2_REFUSALS_FORGET_K <= 14336) by (unfold LV2_REFUSALS_FORGET_K; lia).
    destruct (vs_pre B API HF S HS rg3 0x1731c mem4 md3 La2 Aa2 _ O2 _ qv None jk _ LV2_REFUSALS_FORGET_K 0x17a80
                HST3 E1' RET' KB') as (PRE' & SPR' & FZ' & F18' & RO' & REC' & HM' & SH').
    assert (LZ : (lv2_refusals_forget_size None) = 2) by reflexivity.
    assert (HSZ' : Forall (fun n => 0 <= n <= 8194) [(lv2_refusals_forget_size None)]) by (rewrite LZ; repeat constructor; lia).
    assert (HKS' : (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))) + length [(lv2_refusals_forget_size None)] <= 32)%nat) by (unfold pins_clear_sizes; cbn [length]; lia).
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST3))))) as (RES' & _).
    pose proof (st_room B API S HS (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a))))) _ (LMAX + 1) HKS' HSZ' ltac:(unfold LMAX; lia)) as ROOM'.
    assert (CAP' : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))))) [(lv2_refusals_forget_size None)]) <=
                   sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))))) [(lv2_refusals_forget_size None)])).
    { destruct (sb_mallocs_fields [(lv2_refusals_forget_size None)] (sb_n (s_b S) (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a))))))) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RC & _).
      unfold sb_n. cbn [sb_live sb_cap] in *. unfold pins_clear_sizes. cbn [length]. lia. }
    apply (pinclr_call_v B API HF S HS rg3 0x1731c mem4 md3 La2 Aa2 _ O2 _ qv None jk _ LV2_REFUSALS_FORGET_K 0x17a80
             [(lv2_refusals_forget_size None)] (lv2_refusals_forget_m (fst (pins_clear_m R1 (Some a))) None) (fun _ => True) P HST3 E1' KB' HKS' HSZ').
    { eapply SR_mono.
      { pose proof (DL f2 La2 Aa2 rg3 mem4 md3 0 None (fst (pins_clear_m R1 (Some a))) O2 (sb_n (s_b S) (k1 + length (pins_clear_sizes (Some a) (snd (pins_clear_m R1 (Some a)))))) (proj1 PRE') E10'
                      eq_refl REC' RO' F18' RES' ROOM') as C.
        rewrite SEGS in C. unfold LV2_REFUSALS_FORGET in C. exact C. }
      intros c'' HR. rewrite <- SEGS in HR.
      destruct HR as (La3 & Aa3 & rg4 & mem5 & md5 & O3 & E & POST & REC3 & OWN & OK & BLK & RO3 & _ & INIT & RLEN & LE & RS).
      exists f2, La3, Aa3, rg4, mem5, md5, O3.
      split; [rewrite SEGS in E; exact E|].
      split; [split; [exact FZ' | intros r _; reflexivity]|].
      split; [exact POST|]. split; [exact REC3|]. split; [exact OWN|]. split; [exact BLK|]. split; [exact OK|].
      split; [exact RO3|]. split; [exact INIT|]. split; [exact RLEN|].
      split; [exact (RecKindB.res_ok_slots_le Aa3 _ _ LE CAP' RS) | exact I]. }
    intros f3 rg4 mem5 md5 La3 Aa3 O3 c3 HST4 _ HP4.
    pose proof HST4 as (_ & _ & VR4 & _).
    eapply (ka_nw B API HF S HS rg4 0x17a80 mem5 md5 La3 Aa3 _ O3 _ qv None jk c3 _ P HST4).
    { unfold Regs6ss.mkR_of. apply pinclr_k3. }
    { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
    intros R5 pc5 rg5 mem6 HQ5 X5 MK5. cbv beta in HQ5. injection HQ5 as ER EP. subst R5 pc5.
    assert (PR5 : regs_preserved rg4 rg5) by (apply (pres_of rg4 _ rg5 X5); intros r Hr; cs_cases r Hr; reflexivity).
    pose proof (MK5 0x17a8c eq_refl (vregs_pres S rg4 rg5 VR4 PR5)) as HST5.
    eapply (resp_join B API HF S HS SRESP rg R1 k1 qv false 0x17a8c 0x17a90 rg5 mem6 md5 La3 Aa3 _ O3 _ jk _ 0 P).
    + left. split; reflexivity.
    + exact HST5.
    + rewrite (getr_of_eqv _ _ 10 X5 eq_refl). reflexivity.
    + lia.
    + exact (eq_trans (PR5 18 ltac:(unfold callee_saved; lia)) (eq_trans (HP4 18 ltac:(unfold callee_saved; lia))
             (eq_trans (PR3 18 ltac:(unfold callee_saved; lia)) (eq_trans (HP2 18 ltac:(unfold callee_saved; lia))
             (PR 18 ltac:(unfold callee_saved; lia)))))).
    + intros _. exact (eq_trans (PR5 21 ltac:(unfold callee_saved; lia)) (eq_trans (HP4 21 ltac:(unfold callee_saved; lia))
             (eq_trans (PR3 21 ltac:(unfold callee_saved; lia)) (eq_trans (HP2 21 ltac:(unfold callee_saved; lia))
             (PR 21 ltac:(unfold callee_saved; lia)))))).
    + rewrite RT, TK. cbn [plan_at]. revert Z0. unfold VerbsRun.run_step.
      destruct (pins_clear_m R1 (Some a)) as [Rp r']. cbv beta iota zeta delta [VerbsRun.pins_follow fst snd].
      intros Z0. subst r'. reflexivity.
    + unfold pins_clear_sizes. cbn [length]. lia.
    + unfold pins_clear_sizes. cbn [length]. lia.
    + exact HK.
    + exact JOIN.
Qed.

End R.
