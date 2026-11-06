(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v, with its module names changed; 234 of its 285 lines of code are new or changed and 164 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br3 chain_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply RecTail.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Lemma chain_k1 : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x179f4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_unsigned sp + 8)) s3
                                       a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0x17d0c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x179e8) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m.
  do 3 zstep. apply evt_done. reflexivity.
Qed.

Lemma k_j178f8 : forall (R F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x17a90) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x179f4) fc None m (seg_rom rsegs)).
Proof. intros R F fc m. zstep. apply evt_done. reflexivity. Qed.

Lemma route_chain : forall tk, route tk = RChain -> exists args, tk = verb_chain :: args.
Proof.
  intros [|v args] H; [discriminate H|]. exists args. f_equal.
  unfold route, route_mid, route_tail, route_conn, route_cd in H.
  repeat match type of H with
  | context [if ?b then _ else _] =>
      let Eb := fresh "Eb" in
      destruct b eqn:Eb; cbv beta iota in H; [first [discriminate H | apply list_eqb_eq; exact Eb] |]
  end.
  destruct (ledger_of v instance_info_verbs); [discriminate H|].
  destruct args as [|a [|b [|c r]]]; try discriminate H.
  all: cbv beta iota in H;
    repeat match type of H with context [if ?b then _ else _] => destruct b; cbv beta iota in H end;
    discriminate H.
Qed.

Lemma run_chain : forall (rcode : list byte -> Z) R args Rc xc, VerbsRun.chain_run R args = (Rc, xc) ->
  VerbsRun.run_step rcode R (chain_words_m args) = (Rc, xc, false).
Proof.
  intros rcode R args Rc xc E. unfold VerbsRun.chain_run in E.
  assert (C : (exists c, chain_words_m args = SCall c) \/ chain_words_m args = reject).
  { unfold chain_words_m. destruct args as [|a [|b rest]]; [right; reflexivity | right; reflexivity |].
    destruct (number_m a); [|right; reflexivity].
    destruct (numbers_m (b :: rest)); [left; eexists; reflexivity | right; reflexivity]. }
  destruct C as [(c0 & C)|C]; rewrite C in E |- *.
  - cbv beta iota in E. cbn [VerbsRun.run_step]. rewrite E. reflexivity.
  - unfold reject in E |- *. cbv beta iota in E. cbn [VerbsRun.run_step]. unfold sup_resp_m in E.
    injection E as <- <-. reflexivity.
Qed.

Section C.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis CW : forall f : YK11.FPState, @chain_words_contract f rc B API.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma post_cw : forall K L A rg mem md excl L' A' rg' mem' md',
  RecKindB.call_post_rec B MR K L A rg mem md cw_writes excl L' A' rg' mem' md' ->
  RecKindB.call_post_rec B MR K L A rg mem md RecKindB.rec_area excl L' A' rg' mem' md'.
Proof.
  intros K L A rg mem md excl L' A' rg' mem' md' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
  split; [exact H6|]. split; [exact H7|].
  split; [|split; [exact H9 | exact H10]].
  intros a Ha N1 N2 N3 N4. apply (H8 a Ha N1 N2 N3). intros Hc. apply N4.
  unfold cw_writes, RecKindB.rec_area in *. tauto.
Qed.

Lemma errno_img4 : in_img B (errno_addr B) -> forall j, 0 <= j < 4 -> in_img B (errno_addr B + j).
Proof using HF.
  intros EI j Hj. pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR.
  destruct EI as (NE & s & Hs & H1 & H2). split; [exact NE|]. exists s. split; [exact Hs|].
  rewrite ERR in *. rewrite SEGS in Hs.
  assert (T : forallb (fun s => negb ((bv_unsigned (fst s) <=? 0x3441c) &&
                                      (0x3441c <? bv_unsigned (fst s) + bv_unsigned (snd s))) ||
                                (0x34420 <=? bv_unsigned (fst s) + bv_unsigned (snd s)))
                (segments_reserved rsegs) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) T s Hs) as Ts. cbv beta in Ts.
  apply orb_true_iff in Ts. destruct Ts as [Ts|Ts].
  - apply negb_true_iff, andb_false_iff in Ts. destruct Ts as [Ts|Ts]; [apply Z.leb_gt in Ts | apply Z.ltb_ge in Ts]; lia.
  - apply Z.leb_le in Ts. lia.
Qed.

Lemma errno_fresh : forall q k, in_img B (errno_addr B) -> fresh_block B q k -> 1 <= k ->
  errno_addr B + 4 <= q \/ q + k <= errno_addr B.
Proof using HF.
  intros q k EI (H4 & Hc & HN) Hk.
  destruct (Z_le_gt_dec (errno_addr B + 4) q) as [E|E]; [left; exact E|].
  destruct (Z_le_gt_dec (q + k) (errno_addr B)) as [E'|E']; [right; exact E'|]. exfalso.
  destruct (Z_le_gt_dec q (errno_addr B)) as [E''|E''].
  - apply (HN (errno_addr B - q)); [lia|]. replace (q + (errno_addr B - q)) with (errno_addr B) by ring. exact EI.
  - apply (HN 0); [lia|]. replace (q + 0) with (errno_addr B + (q - errno_addr B)) by ring.
    apply errno_img4; [exact EI | lia].
Qed.

Lemma call_chain : forall rg mem1 md1 L1 A1 R1 O1 k1 qv jk c ret Rc xc P,
  VS fx rg CHAIN_WORDS mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  getr rg 1 = Z_to_bv 64 ret -> YK0s.ret_ok (Z_to_bv 64 ret) ->
  getr rg 10 = Z_to_bv 64 (s_spf S + 8) -> getr rg 11 = verbs_receive_disp.ntokw (toks D) ->
  nth_error (toks D) 0 = Some verb_chain -> (k1 + 6 <= 32)%nat ->
  (r_refuse R1 <> 0 -> declared (r_code R1) = true) ->
  VerbsRun.chain_run R1 (tl (toks D)) = (Rc, xc) ->
  (forall (fx' : YK11.FPState) rg' mem' md' L' A' O' k' p n c',
     VS fx' rg' ret mem' md' L' A' Rc O' k' qv (Some (p, n, xc)) jk c' ->
     getr rg' 10 = Z_to_bv 64 p -> Z.of_nat (length xc) + 1 <= n -> regs_preserved rg rg' ->
     (k1 <= k' <= k1 + 6)%nat -> SR rsegs c' P) ->
  SR rsegs c P.
Proof using HF HS CW.
  intros rg mem1 md1 L1 A1 R1 O1 k1 qv jk c ret Rc xc P HST E1 RET E10 E11 V0 HK DECL ECH KONT.
  pose proof (vf_segs B API HF) as SEGS. pose proof (vf_errno B API HF) as ERR. pose proof (aa_laws API) as LAWS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & SP16 & _). pose proof alloc_ceiling_val as ACV.
  assert (KC : 0 <= CW_K <= 14336) by (unfold CW_K; lia).
  destruct (vs_pre B API HF S HS rg CHAIN_WORDS mem1 md1 L1 A1 R1 O1 k1 qv None jk c CW_K ret HST E1 RET KC)
    as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
  pose proof HST as (EC & FPK0 & VR & H & FR & GQ & GW).
  pose proof (h_res B API S _ _ _ _ _ _ _ _ H) as (RES & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (h_x B API S _ _ _ _ _ _ _ _ H (s_cb S, s_ncb S) (or_intror (or_introl eq_refl))) as [INC NOC].
  destruct (st_f18 B API HF _ _ _ _ HM) as (_ & cn & SSP).
  pose proof (ok_cbf B API S HS) as FCB. pose proof (ok_eimg B API S HS) as EIMG.
  pose proof (ok_n8 B API S HS) as N8. pose proof (ok_nD B API S HS) as ND.
  assert (LPT : length (s_ps S) = length (toks D)) by exact (Forall2_length TOK).
  assert (NT : 1 <= Z.of_nat (length (toks D)) <= 64).
  { pose proof (Verbs.toks_length D). destruct (toks D); [discriminate V0 | cbn [length] in *; lia]. }
  assert (SPZ : spZ rg = s_spf S) by exact SPR.
  unfold spZ in SPZ.
  assert (TA : toks_at B mem1 (s_spf S + 8) (map (fun w : word => bv_unsigned w) (s_ps S)) (toks D)
                 (s_cb S) (s_ncb S)).
  { split; [unfold s_spf in *; lia|].
    split; [rewrite length_map; exact LPT|].
    split.
    { rewrite map_map.
      assert (EM : map (fun x : word => Mem.le8 (Z_to_bv 64 (bv_unsigned x))) (s_ps S) = map le8 (s_ps S))
        by (apply map_ext; intros w; rewrite Z_to_bv_bv_unsigned; reflexivity).
      rewrite EM. apply reply.bytes_le_at. rewrite SEGS. exact (proj2 (proj2 FR)). }
    intros i p w Ep Ew.
    rewrite nth_error_map in Ep. destruct (nth_error (s_ps S) i) as [pw|] eqn:Epw; [|discriminate Ep].
    injection Ep as <-.
    destruct (Forall2_nth _ _ _ i pw w TOK Epw Ew) as ((Hb & Hnz) & H1 & H2).
    assert (LW : Z.of_nat (length w) <= 8192).
    { pose proof (verbs_receive_route.toks_len D w (nth_error_In _ _ Ew)). lia. }
    split; [apply reply.bytes_le_at; rewrite SEGS; exact Hb|].
    split; [exact Hnz|]. split; [exact LW|]. split; [exact H1|]. split; [exact H2|].
    left. destruct FCB as (_ & FC2 & _). unfold s_spf, s_ncb, VR_K in *. lia. }
  assert (OUTS : outside B L1 A1 CW_K rg (s_spf S + 8) (8 * Z.of_nat (length (toks D)))).
  { intros i Hi. split.
    - intros Ho. pose proof (owned_low B _ LAWS _ _ _ _ _ HM Ho). unfold s_spf, VR_K in *. lia.
    - unfold scratch_k. unfold spZ. rewrite SPZ, ERR. unfold s_spf, CW_K, VR_K in *. lia. }
  assert (NOC' : ~ In (s_cb S, s_ncb S) O1).
  { intros Hin. apply NOC. apply in_map_iff. exists (s_cb S, s_ncb S). split; [reflexivity | exact Hin]. }
  assert (ERRCB : errno_addr B + 4 <= s_cb S \/ s_cb S + s_ncb S <= errno_addr B)
    by (apply errno_fresh; [exact EIMG | exact FCB | unfold s_ncb; lia]).
  assert (ERRSSP : errno_addr B + 4 <= SSP_GUARD_B \/ SSP_GUARD_B + 8 <= errno_addr B)
    by (rewrite ERR; unfold SSP_GUARD_B; lia).
  assert (ROOM : room_slots (sb_n (sb_n (s_b S) k1) CW_MALLOCS) CW_REQ).
  { refine (RecKindB.room_slots_mono _ _ CW_REQ VR_REQ _ _ (ok_room B API S HS)); [|unfold CW_REQ, VR_REQ; lia].
    unfold RecKindB.sb_le, sb_n, SB_REQ, CW_MALLOCS. cbn [sb_live sb_bytes sb_cap]. lia. }
  pose proof (CW fx L1 A1 rg mem1 md1 (sb_n (s_b S) k1) R1 O1 (s_spf S + 8) (s_cb S) (s_ncb S)
                (Z.of_nat (length (toks D))) (map (fun w : word => bv_unsigned w) (s_ps S)) (toks D) cn
                PRE RO FZ E10 E11 INC NOC' TA eq_refl NT V0 ltac:(lia) ltac:(unfold s_spf, VR_K in *; lia) OUTS
                ERRCB ERRSSP REC DECL SSP SH RES ROOM) as C.
  subst c. eapply SR_bind; [rewrite SEGS in C; exact C|].
  intros c' (fx' & L' & A' & rg' & mem' & md' & O' & k & p & n & -> & FPK & POST & RO' & MODEL & A0' & INB & NOB
    & APART & TOKS' & SURV & BLK & NO2 & RLEN & BK & SSP' & SHP' & KLE & RES').
  rewrite ECH in MODEL. destruct MODEL as (REC' & BX & LX).
  rewrite <- SEGS in REC', RO'.
  pose proof POST as (HM' & HWF' & _ & _ & _ & HPR & _ & HFR & _ & _).
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM1 & _).
  assert (CWL : forall a, cw_writes a -> a < alloc_ceiling)
    by (intros a Ha; unfold cw_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE in Ha; lia).
  assert (CWQ : forall i, 0 <= i < 4 -> ~ cw_writes (G_QUIT + i))
    by (intros i Hi Ha; unfold cw_writes, G_REC, REC_SIZE, REC_SC, SC_SIZE, G_QUIT in Ha; lia).
  pose proof (frame_keep B API HF S HS CW_K rg mem1 mem' L1 A1 L' A' md1 md' cw_writes HM1 HM' SPR CWL HFR) as KP.
  pose proof (gq_keep B API HF S HS CW_K rg mem1 mem' L1 A1 L' A' md1 md' cw_writes HM1 HM' SPR KC CWQ HFR) as KQ.
  destruct (gq_transfer mem1 mem' qv KQ GQ GW) as [GQ' GW'].
  destruct (blk_low B API HF L' A' mem' md' p n 0 HM' INB ltac:(lia)) as (P4 & Pc & _).
  assert (EB : sb_n (sb_n (s_b S) k1) k = sb_n (s_b S) (k1 + k)%nat)
    by (unfold sb_n; cbn [sb_live sb_bytes sb_cap]; f_equal; lia).
  apply (KONT fx' rg' mem' md' L' A' O' (k1 + k)%nat p n); [| exact A0' | exact LX | exact HPR |
    unfold CW_MALLOCS in KLE; lia].
  split; [rewrite E1; reflexivity|].
  split; [exact (fp_kept_trans _ _ _ FPK0 FPK)|].
  split; [exact (vregs_pres S rg rg' VR HPR)|].
  split.
  { apply (heap_step_sv B API HF S HS rg mem1 md1 L1 A1 R1 O1 k1 None CW_K L' A' rg' mem' md' Rc O' [(p, n)]
             (Some (p, n, xc)) (k1 + k)%nat H SPR KC (post_cw _ _ _ _ _ _ _ _ _ _ _ _ POST) REC').
    - intros pn Ho. destruct (in_dec RecTail.pair_dec pn O1) as [Hi|Hi]; [left; exact Hi|].
      right. intros Hb. exact (NO2 pn Hb Hi Ho).
    - intros pn Hin. destruct (BLK pn Hin) as [X|[X|X]];
        [left; exact X | right; left; exact X | right; right; left; symmetry; exact X].
    - intros [a k0] Hin Hno. split; [exact (SURV _ Hin Hno)|]. intros i Hi. cbn [fst snd] in *.
      apply (BK a k0 i Hin); [|exact Hi].
      intros (j & Hj). destruct (reply.rec_rep_O _ _ _ _ _ _ _ _ REC (a, j) Hj) as [Hb Hj1]. cbn [snd] in Hj1.
      pose proof (mr_blocks_disjoint B _ LAWS _ _ _ _ HM1) as PD.
      assert (Ejk : j = k0) by exact (reply.same_start _ a j k0 PD Hb Hin ltac:(lia) ltac:(lia)).
      subst j. exact (Hno Hj).
    - exact RO'.
    - apply YI04.blocks_In in INB as (q & _ & Hq). exact (YI04.init_done_of_block A' (q, n) HWF' Hq).
    - exact RLEN.
    - rewrite <- EB. exact RES'.
    - unfold CW_MALLOCS in KLE. lia.
    - reflexivity.
    - intros pn [<-|[]]. cbn [fst snd]. split; [exact INB|].
      split; [exact (addr_notin B API L' A' mem' md' Rc O' p n HM' REC' INB ltac:(lia) NOB)|].
      split; [lia|]. intros pn' Hin' Hno'. destruct (APART pn' Hin' Hno'); lia.
    - constructor; [intros []|constructor].
    - split; [|exact LX]. rewrite <- SEGS. apply reply.le_at_bytes; [exact BX | lia |].
      rewrite length_app. cbn [length]. lia. }
  split; [exact (vfr_keep B API S HS mem1 mem' jk KP FR)|].
  split; [exact GQ' | exact GW'].
Qed.

End C.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Hypothesis CW : forall f : YK11.FPState, @chain_words_contract f rc B API.

Local Notation D := (s_D S).

Lemma vr_br_chain : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  @vr_state f _ B API S rg (route_pc RChain) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RChain -> getr rg 19 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  (r_refuse R1 <> 0 -> declared (r_code R1) = true) ->
  join_k_ge B API S 0x17a90 10 rg R1 k1 qv P ->
  SR rsegs c P.
Proof using HF HS CW.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N19 HK DECL JOIN.
  destruct (route_chain (toks D) RT) as (args & TK).
  destruct (VerbsRun.chain_run R1 (tl (toks D))) as [Rc xc] eqn:ECH.
  pose proof HST as (_ & _ & VR & _).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  assert (R19 : reg_get rg 19 = verbs_receive_disp.ntokw (toks D)) by (rewrite <- N19; reflexivity).
  eapply (@ka_nw f _ B API HF S HS rg (route_pc RChain) mem1 md1 L1 A1 R1 O1 k1 qv None jk c _ P HST).
  { unfold Regs6ss.mkR_of. cbn [route_pc]. apply chain_k1. }
  { intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity. }
  intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as ER EP. subst R' pc'.
  assert (PR : regs_preserved rg rg') by (apply (pres_of rg _ rg' X); intros r Hr; cs_cases r Hr; reflexivity).
  pose proof (MK CHAIN_WORDS eq_refl (vregs_pres S rg rg' VR PR)) as HST1.
  apply (@call_chain f _ B API HF S HS CW rg' mem2 md1 L1 A1 R1 O1 k1 qv jk _ 0x179f4 Rc xc P HST1).
  - rewrite (getr_of_eqv _ _ 1 X eq_refl). reflexivity.
  - apply bv_eq; vm_compute; reflexivity.
  - rewrite (getr_of_eqv _ _ 10 X eq_refl).
    transitivity (Z_to_bv 64 (bv_unsigned (reg_get rg 2) + 8)); [reflexivity | rewrite SP2; reflexivity].
  - rewrite (getr_of_eqv _ _ 11 X eq_refl). transitivity (reg_get rg 19); [reflexivity | exact R19].
  - rewrite TK. reflexivity.
  - lia.
  - exact DECL.
  - exact ECH.
  - intros f' rg'' mem' md' L' A' O' k' p n c' HST2 E10' LX HP2 HKk.
    apply (join_jump_ge B API HF S HS f' rg R1 k1 qv rg'' 0x179f4 0x17a90 mem' md' L' A' Rc O' k' p n xc jk c' P
             HST2 LX k_j178f8).
    + exact E10'.
    + exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) (PR 18 ltac:(unfold callee_saved; lia))).
    + exact (eq_trans (HP2 21 ltac:(unfold callee_saved; lia)) (PR 21 ltac:(unfold callee_saved; lia))).
    + rewrite RT, TK. cbn [plan_at]. apply run_chain. rewrite TK in ECH. exact ECH.
    + lia.
    + exact JOIN.
Qed.

End R.
