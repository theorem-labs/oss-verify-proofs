(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

Ltac cond_by b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with b;
      [ cbv iota
      | symmetry; unfold bv_eqb, bv_ltu, bv_leu; fold_lit_ux; rewrite ?unsigned_lit_wrap;
        change 7%Z with (Z.ones 3); rewrite ?Z.land_ones by lia;
        repeat match goal with
               | |- context [Z.ltb ?x ?y] => destruct (Z.ltb_spec x y)
               | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
               end;
        cbn [negb]; first [reflexivity | exfalso; Z.div_mod_to_equations; lia] ]
  end.

Lemma rep_code : forall segs L A mem R O, g_rec_rep segs L A mem R O -> -2^31 <= r_code R < 2^31.
Proof. intros segs L A mem R O (Q & (_ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & HC & _) & _) & _). exact HC. Qed.

Lemma stub_text_len : forall R fn As v ch, -2^31 <= r_code R < 2^31 ->
  (length (snd (rec_stub R fn As (shape_of v) ch)) <= 28)%nat.
Proof.
  intros R fn As v ch HC. unfold rec_stub. rewrite rec_answer_text.
  assert (E : r_code (rec_record R fn As) = r_code R) by (unfold rec_record; destruct (Nat.ltb _ _); reflexivity).
  destruct (r_refuse (rec_record R fn As) =? 0).
  - exact (proj1 (proj2 (shape_of_facts v))).
  - rewrite E. pose proof (resp_length (r_code R) HC). lia.
Qed.

Lemma len2 : forall {X : Type} (l : list X), length l = 2%nat -> exists v a, l = [v; a].
Proof. intros X [|v [|a [|b r]]] H; cbn [length] in H; try lia. exists v, a. reflexivity. Qed.

Lemma frame_tok : forall (S : vstart) mem jk i p, vfr S mem jk -> nth_error (s_ps S) i = Some p ->
  bytes_at rsegs mem (s_spf S + 8 + 8 * Z.of_nat i) (le8 p).
Proof.
  intros S mem jk i p (_ & _ & FB) E.
  destruct (nth_error_split (s_ps S) i p E) as (l1 & l2 & EQ & LEN).
  rewrite EQ, map_app, concat_app in FB. cbn [map concat] in FB.
  apply Mem.bytes_at_app in FB. destruct FB as [_ FB]. apply Mem.bytes_at_app in FB. destruct FB as [FB _].
  rewrite length_concat_le8, LEN in FB.
  replace (s_spf S + 8 + 8 * Z.of_nat i) with (s_spf S + 8 + Z.of_nat (8 * i)) by lia. exact FB.
Qed.

Lemma getr_eqv_of : forall rg rg', Regs6ss.xregs_eqv (Regs6ss.mkR_of rg) rg' -> forall r, getr rg' r = getr rg r.
Proof.
  intros rg rg' X r. unfold getr. destruct (bv_eqb r 0) eqn:E; [reflexivity|].
  rewrite <- (X r E). symmetry. exact (Regs6ss.mkR_of_eqv rg r E).
Qed.

Ltac cs_cases r Hr :=
  unfold callee_saved in Hr;
  let Hc := fresh "Hc" in
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].

Lemma pres_of : forall rg R' rg', Regs6ss.xregs_eqv R' rg' ->
  (forall r, callee_saved r -> reg_get R' (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)) -> regs_preserved rg rg'.
Proof.
  intros rg R' rg' X H r Hr. pose proof (H r Hr) as E. cs_cases r Hr;
    match goal with |- getr _ ?k = _ => rewrite (getr_of_eqv R' rg' k X eq_refl), E; reflexivity end.
Qed.

Section B1.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation VS f := (@vr_state f _ B API S).

Definition ans_ret (K : Z) (Rt : rstate * list byte) (sz : list byte -> list Z) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (O : list (Z * Z)) (b : sbound) (c' : config) : Prop :=
  exists (fx' : YK11.FPState) L' A' regs' mem' md' R' O' t q,
    Rt = (R', t) /\
    c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom (ms_segs B))) md' /\
    RecKindB.fp_kept fx fx' /\
    RecKindB.call_post_rec B MR K L A regs mem md RecKindB.rec_area (fun a => In a (map fst O)) L' A' regs' mem' md' /\
    getr regs' 10 = Z_to_bv 64 q /\
    g_rec_rep (ms_segs B) L' A' mem' R' O' /\ RecKindB.owns_new L A O O' /\
    (forall pn, In pn (blocks L' A') ->
       (In pn (blocks L A) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
    In (q, Z.of_nat (length t) + 1) (blocks L' A') /\ fresh_block B q (Z.of_nat (length t) + 1) /\
    ~ In q (map fst O') /\
    Mem.bytes_at (ms_segs B) mem' q (t ++ [Z_to_bv 8 0]) /\
    RecKindB.others_kept (ms_segs B) L A mem L' A' mem' O /\
    (forall p k, In (p, k) (user_blocks A) -> ~ In (ptr_addr L p, k) O ->
       ptr_addr L p + k <= q \/ q + Z.of_nat (length t) + 1 <= ptr_addr L p) /\
    Mem.bytes_at (ms_segs B) mem' rec_shape_of_c.G_SHAPES rec_shape_of_c.g_shapes_bytes /\
    ro_agree (ms_segs B) mem' /\ RecKindB.f18_words (ms_segs B) mem' /\
    st_init_done A' = true /\
    (length (st_regions A) <= length (st_regions A'))%nat /\
    RecKindB.sb_le (RecKindB.sb_shift b A A') (RecKindB.sb_mallocs b (sz t)) /\
    res_ok_slots A' (RecKindB.sb_shift b A A').

Lemma ans_of : forall K Rt sz L A rg mem md O b c',
  ans_ret K Rt sz L A rg mem md O b c' ->
  sb_live (RecKindB.sb_mallocs b (sz (snd Rt))) <= sb_cap (RecKindB.sb_mallocs b (sz (snd Rt))) ->
  ans_post B API K L A rg mem md O b (sz (snd Rt)) Rt c'.
Proof.
  intros K Rt sz L A rg mem md O b c'
    (fx' & L' & A' & rg' & mem' & md' & R' & O' & t & q & -> & E & FPK & POST & A0 & REC & OWN & BLK & INB & FRESH
     & NOQ & BQ & OK & APART & _ & RO & _ & INIT & RLEN & LE & RS) CAP.
  pose proof (vf_segs B API HF) as SEGS. rewrite SEGS in E. cbn [fst snd] in *.
  exists fx', L', A', rg', mem', md', O', q.
  split; [exact E|]. split; [exact FPK|]. split; [exact POST|]. split; [exact A0|]. split; [exact REC|].
  split; [exact OWN|]. split; [exact BLK|]. split; [exact INB|]. split; [exact FRESH|]. split; [exact NOQ|].
  split; [exact BQ|]. split; [exact OK|]. split; [exact APART|]. split; [exact RO|]. split; [exact INIT|].
  split; [exact RLEN|]. exact (RecKindB.res_ok_slots_le A' _ _ LE CAP RS).
Qed.

Lemma ka_nw : forall rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c (QQ : machine_state -> Prop) P,
  VS fx rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c ->
  evt rsegs QQ (MS (Regs6ss.mkR_of rg) fp_regs (Z_to_bv 64 pc) fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall ms', QQ ms' -> exists R' pc', ms' = MS R' fp_regs pc' fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
  (forall R' (pc' : word) rg' mem2, QQ (MS R' fp_regs pc' fp_csr None (normalize rsegs mem1) (seg_rom rsegs)) ->
     Regs6ss.xregs_eqv R' rg' ->
     (forall pz, pc' = Z_to_bv 64 pz -> vregs S rg' ->
        VS fx rg' pz mem2 md1 L1 A1 R1 O1 k1 qv xq jk (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1)) ->
     SR rsegs (mkCfg (mkst rg' pc' mem2 (seg_rom rsegs)) md1) P) ->
  SR rsegs c P.
Proof.
  intros rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c QQ P HST EVT SHP K.
  pose proof HST as (_ & FPK & _ & _ & FR & GQ & GW).
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _ & _). pose proof alloc_ceiling_val as ACV.
  apply (ka_bridge B API HF S HS rg pc mem1 md1 L1 A1 R1 O1 k1 qv xq jk c []
    (fun ms' => QQ ms' /\ exists R' pc', ms' = MS R' fp_regs pc' fp_csr None (normalize rsegs mem1) (seg_rom rsegs))
    P HST).
  - intros x _ _ _. exact I.
  - eapply evt_mono; [exact EVT|]. intros ms' HQ. destruct (SHP ms' HQ) as (R' & pc' & E).
    split; [split; [exact HQ | exists R', pc'; exact E]|].
    exists R', pc', (normalize rsegs mem1). split; [exact E|]. split; [apply munch_refl | apply wmono_refl].
  - intros R' pc' m' mem2 rg' (HQ & R'' & pc'' & E) X RL MU WM H2.
    injection E as E1 E2 E3. subst R'' pc'' m'.
    apply (K R' pc' rg' mem2 HQ X). intros pz Epz VR'. subst pc'.
    assert (KP : forall a, 0 <= a < 2 ^ 64 ->
      mbyte rsegs mem2 a = mbyte rsegs mem1 a /\ (writable_at rsegs mem1 a <-> writable_at rsegs mem2 a)).
    { intros a Ha. split; [exact (munch_mbyte rsegs [] mem1 mem2 a MU Ha I)
                          | exact (munch_writable rsegs [] mem1 mem2 a MU Ha I)]. }
    split; [reflexivity|]. split; [exact FPK|]. split; [exact VR'|]. split; [exact H2|].
    split.
    + apply (vfr_keep B API S HS mem1 mem2 jk); [|exact FR]. intros a Ha. apply KP. unfold s_spf, VR_K in *. lia.
    + apply (gq_transfer mem1 mem2 qv); [|exact GQ|exact GW]. intros i Hi. apply KP. unfold G_QUIT. lia.
Qed.

End B1.

Section B2.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.

Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Definition vr_join (f : YK11.FPState) (J ar : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z)
    (rg : bvmap 5 word) (mem : word -> option byte) (md : Model) (L : layout) (A : astate) (R : rstate)
    (O : list (Z * Z)) (k : nat) (q : Z) (x jk : list byte) (c : config) : Prop :=
  exists qt : bool,
    VS f rg J mem md L A R O k (if qt then 1 else qv) (Some (q, Z.of_nat (length x) + 1, x)) jk c /\
    getr rg (Z_to_bv 5 ar) = Z_to_bv 64 q /\ getr rg 18 = getr rg0 18 /\
    (J = 0x17a90 \/ J = 0x17a94 -> getr rg 21 = getr rg0 21) /\
    VerbsRun.run_step sup_reply_code_c.reply_code R0
      (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, qt) /\
    (k0 <= k <= k0 + 8)%nat.

Definition vr_rej (f : YK11.FPState) (J : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z)
    (rg : bvmap 5 word) (mem : word -> option byte) (md : Model) (L : layout) (A : astate)
    (O : list (Z * Z)) (k : nat) (jk : list byte) (c : config) : Prop :=
  VS f rg J mem md L A R0 O k qv None jk c /\
  getr rg 18 = getr rg0 18 /\ getr rg 21 = getr rg0 21 /\
  plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D) = reject /\
  k = k0.

Definition join_k (J ar : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z) (P : config -> Prop) : Prop :=
  forall (f : YK11.FPState) rg mem md L A R O k q x jk c,
    vr_join f J ar rg0 R0 k0 qv rg mem md L A R O k q x jk c -> SR rsegs c P.

Definition rej_k (f : YK11.FPState) (J : Z) (rg0 : bvmap 5 word) (R0 : rstate) (k0 : nat) (qv : Z)
    (P : config -> Prop) : Prop :=
  forall rg mem md L A O k jk c, vr_rej f J rg0 R0 k0 qv rg mem md L A O k jk c -> SR rsegs c P.

Lemma join_jump : forall (f : YK11.FPState) rg0 R0 k0 qv rg pc J mem md L A R O k q x jk c P,
  VS f rg pc mem md L A R O k qv (Some (q, Z.of_nat (length x) + 1, x)) jk c ->
  (forall (Rm Fm : bvmap 5 word) (fcm : bv 32) (m : word -> option byte),
     evt rsegs (fun ms' => ms' = MS Rm Fm (Z_to_bv 64 J) fcm None m (seg_rom rsegs))
       (MS Rm Fm (Z_to_bv 64 pc) fcm None m (seg_rom rsegs))) ->
  getr rg 10 = Z_to_bv 64 q -> getr rg 18 = getr rg0 18 -> getr rg 21 = getr rg0 21 ->
  VerbsRun.run_step sup_reply_code_c.reply_code R0
    (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) = (R, x, false) ->
  (k0 <= k <= k0 + 8)%nat ->
  join_k J 10 rg0 R0 k0 qv P ->
  SR rsegs c P.
Proof.
  intros f rg0 R0 k0 qv rg pc J mem md L A R O k q x jk c P HST JMP E10 E18 E21 RUN HK JOIN.
  apply (@ka_nw f _ B API HF S HS rg pc mem md L A R O k qv _ jk c _ P HST (JMP _ _ _ _)).
  - intros ms' E. cbv beta in E. subst ms'. do 2 eexists. reflexivity.
  - intros R' pc' rg' mem2 EQ X MK. cbv beta in EQ. injection EQ as E1 E2. subst R' pc'.
    pose proof (getr_eqv_of rg rg' X) as GE.
    pose proof HST as (_ & _ & VR & _).
    eapply JOIN. exists false.
    split; [apply MK; [reflexivity | apply (vregs_pres S rg rg' VR); intros r _; apply GE]|].
    rewrite !GE. split; [exact E10|]. split; [exact E18|]. split; [intros _; exact E21|].
    split; [exact RUN | exact HK].
Qed.

End B2.
