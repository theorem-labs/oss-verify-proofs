(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/boost-beast/http_request/lib/Lib/Tac.v; 237 of its 261 lines of code are new or changed and 298 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/Prog/mread.v, with its module paths and numbers changed; 1088 of its 1116 lines of code are new or changed and 233 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/chain_words.v, with its module names changed; 179 of its 215 lines of code are new or changed and 1080 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/U/Prog/verbs_receive_br.v; 353 of its 396 lines of code are new or changed and 172 lines of the source are left out. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 sup_pool_config_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br_pool verbs_receive_br_broad strcmp_c strncmp_c sup_add_c descriptors_add_c.
Local Open Scope Z_scope.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br_add0.
Local Open Scope Z_scope.

Lemma add_vregs_of : forall S rg R rg', vregs S rg -> Regs6ss.xregs_eqv R rg' ->
  (forall r, In r [2;3;4;8;9;25;26;27] -> reg_get R (Z_to_bv 5 r) = reg_get rg (Z_to_bv 5 r)) -> vregs S rg'.
Proof.
  intros S rg R rg' (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27) X KP.
  unfold vregs. repeat split;
    match goal with |- getr _ ?r = _ => rewrite (getr_of_eqv _ _ r X eq_refl) end.
  all: match goal with |- reg_get _ ?r = _ =>
    let z := eval vm_compute in (bv_unsigned r) in
    let E := fresh in pose proof (KP z ltac:(cbn; tauto)) as E;
    replace (Z_to_bv 5 z) with r in E by (apply bv_eq; reflexivity); rewrite E end; assumption.
Qed.

Lemma add_get_keep : forall rg R rg', Regs6ss.xregs_eqv R rg' -> add_keep (Regs6ss.mkR_of rg) R ->
  forall r, In r [2;3;4;8;9;18;21;25;26;27] -> getr rg' (Z_to_bv 5 r) = getr rg (Z_to_bv 5 r).
Proof.
  intros rg R rg' X KP r HR. cbn [In] in HR.
  destruct HR as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
    match goal with |- getr _ ?r = _ => rewrite (getr_of_eqv _ _ r X eq_refl) end;
    match goal with |- reg_get _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      let E := fresh in pose proof (KP z ltac:(cbn; tauto)) as E;
      replace (Z_to_bv 5 z) with r in E by (apply bv_eq; reflexivity); rewrite E end; reflexivity.
Qed.

Lemma add_vregs_keep : forall S rg R rg', vregs S rg -> Regs6ss.xregs_eqv R rg' ->
  add_keep (Regs6ss.mkR_of rg) R -> vregs S rg'.
Proof.
  intros S rg R rg' (V2 & V3 & V4 & V8 & V9 & V25 & V26 & V27) X KP.
  unfold vregs. repeat split;
    match goal with |- getr _ ?r = _ =>
      let z := eval vm_compute in (bv_unsigned r) in
      let E := fresh in pose proof (add_get_keep _ _ _ X KP z ltac:(cbn; tauto)) as E;
      replace (Z_to_bv 5 z) with r in E by (apply bv_eq; reflexivity); rewrite E end; assumption.
Qed.

Section R.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Hypothesis HF : vframe B API.
Variable S : vstart.
Hypothesis HS : vok B API S.
Local Notation D := (s_D S).
Local Notation VS f := (@vr_state f _ B API S).

Lemma add_reads : forall (f : YK11.FPState) rg pc mem md L A R O k qv xq jk c,
  VS f rg pc mem md L A R O k qv xq jk c ->
  bv_unsigned (reg_get rg 2) = s_spf S /\ length (s_ps S) = length (toks D) /\
  (forall j, (j < length (s_ps S))%nat ->
    bytes_at rsegs (normalize rsegs mem) (bv_unsigned (reg_get rg 2) + 8 + 8 * Z.of_nat j)
      (le8 (nth j (s_ps S) (Z_to_bv 64 0)))) /\
  (forall j, (j < length (toks D))%nat ->
    VerbsMem.cstr0_at (normalize rsegs mem) (bv_unsigned (nth j (s_ps S) (Z_to_bv 64 0))) (nth j (toks D) [])).
Proof.
  intros f rg pc mem md L A R O k qv xq jk c (_ & _ & VR & H & FR & _).
  pose proof (h_tok B API S _ _ _ _ _ _ _ _ H) as TOK.
  pose proof (Forall2_length TOK) as PL.
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO. rewrite (vf_segs B API HF) in RO.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _). pose proof alloc_ceiling_val as ACV.
  assert (SP2 : bv_unsigned (reg_get rg 2) = s_spf S).
  { destruct VR as (V2 & _). change (reg_get rg 2) with (getr rg 2). rewrite V2. apply unsigned_lit.
    unfold s_spf, VR_K in *. lia. }
  split; [exact SP2|]. split; [exact PL|]. split.
  - intros j HJ. rewrite SP2. apply bytes_at_normalize; [exact RO|]. apply (frame_tok S mem jk); [exact FR|].
    apply nth_error_nth'; exact HJ.
  - intros j HJ.
    assert (EP : nth_error (s_ps S) j = Some (nth j (s_ps S) (Z_to_bv 64 0))) by (apply nth_error_nth'; lia).
    assert (EW : nth_error (toks D) j = Some (nth j (toks D) [])) by (apply nth_error_nth'; exact HJ).
    destruct (Forall2_nth _ _ _ _ _ _ TOK EP EW) as ((HB & NZ) & _).
    split; [apply bytes_at_normalize; assumption|exact NZ].
Qed.

Lemma add_tok_arg : forall (f : YK11.FPState) rg pc mem md L A R O k qv xq jk c K p w,
  VS f rg pc mem md L A R O k qv xq jk c -> 0 <= K <= 14336 ->
  add_tokptr (toks D) (s_ps S) p w ->
  RecKindB.str_arg B L A O (s_spf S) K mem (bv_unsigned p) w.
Proof.
  intros f rg pc mem md L A R O k qv xq jk c K p w HST HK [(-> & ->)|(j & x & EP & EX & ->)].
  - reflexivity.
  - exact (st_tok_arg B API HF S HS rg pc mem md L A R O k qv xq jk c K j p x HST HK EP EX).
Qed.

Lemma add_tok_len : forall p w, add_tokptr (toks D) (s_ps S) p w ->
  Z.of_nat (length (darg w [Z_to_bv 8 45])) <= 8192.
Proof.
  intros p w [(-> & ->)|(j & x & EP & EX & ->)]; [cbv; discriminate|].
  change (Z.of_nat (length x) <= 8192).
  pose proof (verbs_receive_route.toks_len D x (nth_error_In _ _ EX)).
  pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS). lia.
Qed.

Hypothesis DA : forall f : YK11.FPState, @descriptors_add_contract f rc B API.

Lemma add_call_desc : forall (f : YK11.FPState) rg mem md L A R O k qv xq jk c u p P,
  VS f rg 0x1721c mem md L A R O k qv xq jk c ->
  getr rg 1 = Z_to_bv 64 0x17890 -> getr rg 10 = Z_to_bv 64 (bv_unsigned p) ->
  nth_error (s_ps S) 1 = Some p -> nth_error (toks D) 1 = Some u -> (k + 1 <= 32)%nat ->
  (forall (f' : YK11.FPState) rg' mem' md' L' A' O' c',
    VS f' rg' 0x17890 mem' md' L' A' (descriptors_add_m R (Some u)) O' (k + 1) qv xq jk c' ->
    regs_preserved rg rg' -> SR rsegs c' P) -> SR rsegs c P.
Proof.
  intros f rg mem md L A R O k qv xq jk c u p P HST E1 E10 EP EU HK KONT.
  pose proof (vf_segs B API HF) as SEGS.
  assert (KB : 0 <= DESCRIPTORS_ADD_K <= 14336) by (unfold DESCRIPTORS_ADD_K; lia).
  assert (RET : YK0s.ret_ok (Z_to_bv 64 0x17890)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (vs_pre B API HF S HS rg 0x1721c mem md L A R O k qv xq jk c DESCRIPTORS_ADD_K 0x17890
    HST E1 RET KB) as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
  pose proof (st_tok_arg B API HF S HS rg 0x1721c mem md L A R O k qv xq jk c DESCRIPTORS_ADD_K 1 p u HST KB EP EU) as SU.
  pose proof (verbs_receive_route.toks_len D u (nth_error_In _ _ EU)) as UL.
  pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS).
  assert (SZ : Forall (fun n => 0 <= n <= 8194) (descriptors_add_sizes (Some u))).
  { unfold descriptors_add_sizes, sarg. constructor; [lia|constructor]. }
  assert (KS : (k + length (descriptors_add_sizes (Some u)) <= 32)%nat) by exact HK.
  pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 HST))))) as (RES & _).
  pose proof (st_room B API S HS k _ (LMAX + 1) KS SZ ltac:(unfold LMAX; lia)) as ROOM.
  assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k) (descriptors_add_sizes (Some u))) <=
    sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k) (descriptors_add_sizes (Some u)))).
  { destruct (sb_mallocs_fields (descriptors_add_sizes (Some u)) (sb_n (s_b S) k)) as (F1 & _ & F3).
    rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RCAP & _).
    unfold sb_n in *. cbn [sb_live sb_cap] in *. unfold descriptors_add_sizes. cbn [length]. lia. }
  apply (broad_call_v B API HF S HS rg 0x1721c mem md L A R O k qv xq jk c DESCRIPTORS_ADD_K 0x17890
    (descriptors_add_sizes (Some u)) (descriptors_add_m R (Some u)) (fun _ => True) P HST E1 KB KS SZ).
  - eapply SR_mono.
    { pose proof (DA f L A rg mem md (bv_unsigned p) (Some u) R O (sb_n (s_b S) k)
        (proj1 PRE) E10 ltac:(rewrite SPR; exact SU) REC RO F18 RES ROOM) as C.
      rewrite SEGS in C. unfold DESCRIPTORS_ADD in C. rewrite (proj1 HST). exact C. }
    intros c' (L' & A' & rg' & mem' & md' & O' & E & POST & REC' & OWN & BLK & OK & RO' & _ & INIT & RLEN & LE & RS).
    exists f, L', A', rg', mem', md', O'.
    split; [rewrite SEGS in E; exact E|]. split; [split; [exact FZ|intros; reflexivity]|].
    split; [exact POST|]. split; [exact REC'|]. split; [exact OWN|]. split; [exact BLK|].
    split; [exact OK|]. split; [exact RO'|]. split; [exact INIT|]. split; [exact RLEN|].
    split; [exact (RecKindB.res_ok_slots_le A' _ _ LE CAP RS)|exact I].
  - intros f' rg' mem' md' L' A' O' c' ST _ HP. exact (KONT f' rg' mem' md' L' A' O' c' ST HP).
Qed.

Hypothesis RC : sup_reply_code_c.sup_reply_code_contract.

Lemma add_finish : forall (f : YK11.FPState) rg0 R0 k0 rg mem md L A R O k qv q x jk c u P,
  VS f rg 0x1786c mem md L A R O k qv (Some (q, Z.of_nat (length x) + 1, x)) jk c ->
  getr rg 10 = Z_to_bv 64 q -> getr rg 18 = getr rg0 18 -> no0 x ->
  nth_error (toks D) 1 = Some u -> (k0 <= k /\ k + 1 <= k0 + 8 /\ k + 1 <= 32)%nat ->
  VerbsRun.run_step sup_reply_code_c.reply_code R0 (plan_at (route (toks D)) atoi_c.atoi_val (line D) (toks D)) =
    (if 0 <=? sup_reply_code_c.reply_code x then descriptors_add_m R (Some u) else R, x, false) ->
  join_k B API S 0x178b0 19 rg0 R0 k0 qv P -> SR rsegs c P.
Proof.
  intros f rg0 R0 k0 rg mem md L A R O k qv q x jk c u P HST E10 E18 NX EU HK RUN JOIN.
  pose proof HST as (_ & _ & VR & H & _).
  destruct (add_reads f rg 0x1786c mem md L A R O k qv _ jk c HST) as (SP2 & PL & HB & _).
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _). pose proof alloc_ceiling_val as ACV.
  pose proof (h_rel B API S _ _ _ _ _ _ _ _ H) as (HM & _ & _ & _ & _ & _ & _ & _ & SW).
  pose proof (h_ro B API S _ _ _ _ _ _ _ _ H) as RO. rewrite SEGS in RO.
  destruct (h_q B API S _ _ _ _ _ _ _ _ H) as [QBY _].
  destruct (h_x B API S _ _ _ _ _ _ _ _ H (q, Z.of_nat (length x) + 1)
    (or_intror (or_intror (or_introl eq_refl)))) as [QI _].
  destruct (blk_low B API HF L A mem md q (Z.of_nat (length x) + 1) 0 HM QI ltac:(lia)) as (Q4 & QC & _).
  assert (U10 : bv_unsigned (reg_get rg 10) = q).
  { change (reg_get rg 10) with (getr rg 10). rewrite E10. apply unsigned_lit. lia. }
  assert (ST : stk rsegs (normalize rsegs mem) (s_spf S - 32) (s_spf S)).
  { apply stk_normalize; [|unfold s_spf, VR_K in *; lia]. split; [unfold s_spf, VR_K in *; lia|].
    split; [unfold s_spf, VR_K in *; lia|]. intros a HA.
    assert (W : writable_at rsegs mem a).
    { rewrite <- SEGS. apply SW. left. unfold s_spf, VR_K in *; lia. }
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(unfold s_spf, VR_K in *; lia) W) as [b EB].
    exists b. unfold mrd, wa. rewrite EB. reflexivity. }
  assert (LEN : (1 < length (toks D))%nat) by (apply nth_error_Some; rewrite EU; discriminate).
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  assert (EP : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
  eapply (@ka_w f _ B API HF S HS rg 0x1786c mem md L A R O k qv _ jk c [(s_spf S - 32, s_spf S)] _ P HST).
  - intros a HA HOUT. cbn [Frame.outside]. split; [unfold s_spf, VR_K in *; lia|exact I].
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of. eapply add_kreply with (lo := s_spf S - 32) (p1 := p1) (x := x).
      - exact RC.
      - rewrite SP2. unfold s_spf, VR_K in *. lia.
      - apply mem_inv_normalize.
      - rewrite SP2. exact ST.
      - rewrite SP2. lia.
      - unfold s_spf, VR_K in *. lia.
      - rewrite U10. lia.
      - rewrite U10. apply bytes_at_normalize; assumption.
      - exact NX.
      - rewrite U10. unfold s_spf, VR_K in *. lia.
      - replace (bv_unsigned (reg_get rg 2) + 16) with (bv_unsigned (reg_get rg 2) + 8 + 8 * Z.of_nat 1) by lia.
        apply HB. lia. }
    intros ms HQ. split; [exact HQ|]. destruct HQ as (RR & pc & mm & E & MU & WM & _).
    exists RR, (Z_to_bv 64 pc), mm. split; [exact E|]. rewrite SP2 in MU. split; assumption.
  - intros R' pc' m' rg' mem' HQ X MK.
    destruct HQ as (RR & pc & mm & EE & MU & WM & KP & Q19 & RESULT).
    injection EE as ER EPC EM. subst R' pc' m'.
    pose proof (add_vregs_keep S rg RR rg' VR X KP) as VR'.
    assert (G18 : getr rg' 18 = getr rg0 18).
    { transitivity (getr rg 18); [exact (add_get_keep _ _ _ X KP 18 ltac:(cbn; tauto))|exact E18]. }
    assert (G19 : getr rg' 19 = Z_to_bv 64 q).
    { rewrite (getr_of_eqv _ _ 19 X eq_refl), Q19. exact E10. }
    destruct RESULT as [(-> & NEG)|(-> & POS & G1 & G10)].
    + eapply JOIN. exists false. split; [exact (MK 0x178b0 eq_refl VR')|].
      split; [exact G19|]. split; [exact G18|]. split; [intros [E|E]; discriminate|].
      split; [rewrite RUN, (proj2 (Z.leb_gt _ _) NEG); reflexivity|lia].
    + pose proof (MK 0x1721c eq_refl VR') as ST1.
      assert (E1' : getr rg' 1 = Z_to_bv 64 0x17890) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); exact G1).
      assert (E10' : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)).
      { rewrite Z_to_bv_bv_unsigned, (getr_of_eqv _ _ 10 X eq_refl). exact G10. }
      eapply (add_call_desc f rg' mem' md L A R O k qv _ jk _ u p1 P ST1 E1' E10' EP EU ltac:(lia)).
      intros f2 rg2 mem2 md2 L2 A2 O2 c2 ST2 HP2.
      pose proof ST2 as (_ & _ & VR2 & _).
      eapply (@ka_nw f2 _ B API HF S HS rg2 0x17890 mem2 md2 L2 A2 _ O2 (k + 1) qv _ jk c2 _ P ST2 (add_kjump _ _ _ _)).
      { intros ms E. subst ms. do 2 eexists. reflexivity. }
      intros RR2 pc2 rg3 mem3 HQ3 X3 MK3. injection HQ3 as ER3 EP3. subst RR2 pc2.
      pose proof (getr_eqv_of rg2 rg3 X3) as GE.
      eapply JOIN. exists false.
      split; [apply MK3; [reflexivity|apply (vregs_pres S rg2 rg3 VR2); intros r _; apply GE]|].
      split; [exact (eq_trans (GE _) (eq_trans (HP2 19 ltac:(unfold callee_saved; lia)) G19))|].
      split; [exact (eq_trans (GE _) (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) G18))|].
      split; [intros [E|E]; discriminate|]. split.
      * rewrite RUN, (proj2 (Z.leb_le _ _) POS). reflexivity.
      * lia.
Qed.

Lemma add_text_no0 : forall R u i pl cl, no0 (snd (sup_add_m R u i pl cl)).
Proof.
  intros. unfold sup_add_m.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; apply resp_no0.
Qed.

Lemma add_text_len : forall R u i pl cl, -2^31 <= r_code R < 2^31 -> -2^31 <= i < 2^31 ->
  (length (snd (sup_add_m R u i pl cl)) <= 28)%nat.
Proof.
  intros R u i pl cl CR IR.
  assert (RCODE : forall fn args, r_code (rec_record R fn args) = r_code R).
  { intros. unfold rec_record. destruct (Nat.ltb _ _); reflexivity. }
  pose proof (resp_length (-1) ltac:(lia)) as L1.
  pose proof (resp_length (r_code R) CR) as LR.
  pose proof (resp_length i IR) as LI.
  unfold sup_add_m. repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [hand_back snd]; rewrite ?RCODE; lia.
Qed.

Hypothesis AT : atoi_c.atoi_contract.
Hypothesis SA : forall f : YK11.FPState, @sup_add_contract f rc B API.

Lemma add_run : forall (f : YK11.FPState) rg0 rg mem md L A R O k qv jk c P,
  VS f rg 0x17834 mem md L A R O k qv None jk c ->
  route (toks D) = RAdd -> getr rg 18 = getr rg0 18 -> (k + 8 <= 32)%nat ->
  add_inputs (toks D) (s_ps S) (getr rg 20) (getr rg 19) ->
  join_k B API S 0x178b0 19 rg0 R k qv P -> SR rsegs c P.
Proof.
  intros f rg0 rg mem md L A R O k qv jk c P HST RT E18 HK (pl & cl & PLAN & PP & CP) JOIN.
  pose proof HST as (_ & _ & VR & H & _).
  destruct (add_reads f rg 0x17834 mem md L A R O k qv None jk c HST) as (SP2 & PL & HB & HW).
  pose proof (vf_segs B API HF) as SEGS.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _).
  assert (HSP : bv_unsigned (reg_get rg 2) < 2^63) by (rewrite SP2; unfold s_spf, VR_K in *; lia).
  assert (LEN : (3 <= length (toks D))%nat).
  { destruct (toks D) as [|v [|u [|i rest]]]; cbn [tl add_m] in PLAN; try discriminate; cbn [length]; lia. }
  set (p1 := nth 1 (s_ps S) (Z_to_bv 64 0)).
  set (p2 := nth 2 (s_ps S) (Z_to_bv 64 0)).
  set (u := nth 1 (toks D) []). set (i := atoi_c.atoi_val (nth 2 (toks D) [])).
  assert (EP : nth_error (s_ps S) 1 = Some p1) by (unfold p1; apply nth_error_nth'; lia).
  assert (EU : nth_error (toks D) 1 = Some u) by (unfold u; apply nth_error_nth'; lia).
  assert (HB1 : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (reg_get rg 2) + 16) (le8 p1)).
  { replace (bv_unsigned (reg_get rg 2) + 16) with (bv_unsigned (reg_get rg 2) + 8 + 8 * Z.of_nat 1) by lia. apply HB; lia. }
  assert (HB2 : bytes_at rsegs (normalize rsegs mem) (bv_unsigned (reg_get rg 2) + 24) (le8 p2)).
  { replace (bv_unsigned (reg_get rg 2) + 24) with (bv_unsigned (reg_get rg 2) + 8 + 8 * Z.of_nat 2) by lia. apply HB; lia. }
  eapply (@ka_w f _ B API HF S HS rg 0x17834 mem md L A R O k qv None jk c [] _ P HST).
  - intros; exact I.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of. eapply add_katoi with (p1 := p1) (p2 := p2) (w := nth 2 (toks D) []);
      [exact AT|exact HSP|apply mem_inv_normalize|exact HB1|exact HB2|exact (proj1 (HW 2%nat ltac:(lia)))]. }
    intros ms HQ. split; [exact HQ|].
    destruct HQ as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & mm & -> & MU & WM).
    do 3 eexists. split; [reflexivity|]. split; assumption.
  - intros R' pc' m' rg' mem' HQ X MK.
    destruct HQ as (x5 & x6 & x7 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & mm & E & _).
    injection E as ER EPC EM. subst R' pc' m'.
    assert (VR' : vregs S rg').
    { eapply add_vregs_of; [exact VR|exact X|]. intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity. }
    pose proof (MK 0x16000 eq_refl VR') as ST1.
    assert (G1 : getr rg' 1 = Z_to_bv 64 0x1786c) by (rewrite (getr_of_eqv _ _ 1 X eq_refl); reflexivity).
    assert (G10 : getr rg' 10 = Z_to_bv 64 (bv_unsigned p1)) by (rewrite Z_to_bv_bv_unsigned, (getr_of_eqv _ _ 10 X eq_refl); reflexivity).
    assert (G11 : getr rg' 11 = Z_to_bv 64 i) by (rewrite (getr_of_eqv _ _ 11 X eq_refl); reflexivity).
    assert (G12 : getr rg' 12 = Z_to_bv 64 (bv_unsigned (getr rg 20))) by (rewrite Z_to_bv_bv_unsigned, (getr_of_eqv _ _ 12 X eq_refl); reflexivity).
    assert (G13 : getr rg' 13 = Z_to_bv 64 (bv_unsigned (getr rg 19))) by (rewrite Z_to_bv_bv_unsigned, (getr_of_eqv _ _ 13 X eq_refl); reflexivity).
    assert (G18 : getr rg' 18 = getr rg0 18) by (rewrite (getr_of_eqv _ _ 18 X eq_refl); exact E18).
    assert (KB : 0 <= SUP_ADD_K <= 14336) by (unfold SUP_ADD_K; lia).
    assert (RET : YK0s.ret_ok (Z_to_bv 64 0x1786c)) by (apply bv_eq; vm_compute; reflexivity).
    destruct (vs_pre B API HF S HS rg' 0x16000 mem' md L A R O k qv None jk _ SUP_ADD_K 0x1786c ST1 G1 RET KB)
      as (PRE & SPR & FZ & F18 & RO & REC & HM & SH).
    pose proof (st_tok_arg B API HF S HS rg' 0x16000 mem' md L A R O k qv None jk _ SUP_ADD_K 1 p1 u ST1 KB EP EU) as SU.
    pose proof (add_tok_arg f rg' 0x16000 mem' md L A R O k qv None jk _ SUP_ADD_K _ _ ST1 KB PP) as SP.
    pose proof (add_tok_arg f rg' 0x16000 mem' md L A R O k qv None jk _ SUP_ADD_K _ _ ST1 KB CP) as SC.
    pose proof (add_tok_len _ _ PP) as LP. pose proof (add_tok_len _ _ CP) as LC.
    pose proof (verbs_receive_route.toks_len D u (nth_error_In _ _ EU)) as UL.
    pose proof (ok_nD B API S HS). pose proof (ok_n8 B API S HS).
    pose proof (pool_atoi_range (nth 2 (toks D) [])) as IR. fold i in IR.
    pose proof (dec_length i IR) as DL.
    assert (LT : (length (snd (sup_add_m R (Some u) i pl cl)) <= 28)%nat).
    { apply add_text_len; [exact (rep_code _ _ _ _ _ _ REC)|exact IR]. }
    assert (SZ : Forall (fun n => 0 <= n <= 8194) (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl)))).
    { change (Forall (fun n => 0 <= n <= 8194)
        [Z.of_nat (length u) + 1; Z.of_nat (length (dec i)) + 1;
         Z.of_nat (length (darg pl [Z_to_bv 8 45])) + 1; Z.of_nat (length (darg cl [Z_to_bv 8 45])) + 1;
         Z.of_nat (length (snd (sup_add_m R (Some u) i pl cl))) + 1;
         Z.of_nat (length (snd (sup_add_m R (Some u) i pl cl))) + 1]).
      repeat (apply Forall_cons; [cbv beta; lia|]). constructor. }
    assert (KS : (k + length (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl))) <= 32)%nat).
    { unfold sup_add_sizes. cbn [length]. lia. }
    pose proof (h_res B API S _ _ _ _ _ _ _ _ (proj1 (proj2 (proj2 (proj2 ST1))))) as (RES & _).
    pose proof (st_room B API S HS k _ (LMAX + 1) KS SZ ltac:(unfold LMAX; lia)) as ROOM.
    assert (CAP : sb_live (RecKindB.sb_mallocs (sb_n (s_b S) k) (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl)))) <=
      sb_cap (RecKindB.sb_mallocs (sb_n (s_b S) k) (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl))))).
    { destruct (sb_mallocs_fields (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl))) (sb_n (s_b S) k)) as (F1 & _ & F3).
      rewrite F1, F3. pose proof (ok_room B API S HS) as (_ & RCAP & _).
      unfold sb_n in *. cbn [sb_live sb_cap] in *. unfold sup_add_sizes. cbn [length]. lia. }
    apply (call_ans B API HF S HS rg' 0x16000 mem' md L A R O k qv jk _ SUP_ADD_K 0x1786c
      (sup_add_sizes (Some u) i pl cl (snd (sup_add_m R (Some u) i pl cl))) (sup_add_m R (Some u) i pl cl) P ST1 G1 KB KS SZ).
    + eapply SR_mono.
      { pose proof (SA f L A rg' mem' md (bv_unsigned p1) (bv_unsigned (getr rg 20)) (bv_unsigned (getr rg 19))
          (Some u) i pl cl R O (sb_n (s_b S) k) PRE G10 G11 IR G12 G13
          ltac:(rewrite SPR; exact SU) ltac:(rewrite SPR; exact SP) ltac:(rewrite SPR; exact SC) REC RO FZ F18 RES ROOM) as C.
        rewrite SEGS in C. unfold SUP_ADD in C. exact C. }
      intros c' HR. exact (ans_of_ns B API HF SUP_ADD_K (sup_add_m R (Some u) i pl cl) (sup_add_sizes (Some u) i pl cl)
        L A rg' mem' md O (sb_n (s_b S) k) c' HR CAP).
    + intros f2 rg2 mem2 md2 L2 A2 O2 q c2 ST2 E10' HP2.
      eapply (add_finish f2 rg0 R k rg2 mem2 md2 L2 A2 _ O2 _ qv q _ jk c2 u P ST2 E10').
      * exact (eq_trans (HP2 18 ltac:(unfold callee_saved; lia)) G18).
      * apply add_text_no0.
      * exact EU.
      * unfold sup_add_sizes. cbn [length]. lia.
      * rewrite RT. destruct (toks D) as [|v rest] eqn:TK; [cbn [length] in LEN; lia|].
        change (plan_at RAdd atoi_c.atoi_val (line D) (v :: rest)) with (add_m atoi_c.atoi_val rest).
        cbn [tl] in PLAN. rewrite PLAN. fold u i. cbn [VerbsRun.run_step].
        destruct (sup_add_m R (Some u) i pl cl); reflexivity.
      * exact JOIN.
Qed.

Hypothesis SCMP : strcmp_contract.
Hypothesis NCMP : strncmp_contract.

Lemma vr_br_add : forall (f : YK11.FPState) rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P,
  VS f rg (route_pc RAdd) mem1 md1 L1 A1 R1 O1 k1 qv None jk c ->
  route (toks D) = RAdd -> getr rg 21 = verbs_receive_disp.ntokw (toks D) -> (k1 + 8 <= 32)%nat ->
  getr rg 19 = verbs_receive_disp.ntokw (toks D) ->
  getr rg 22 = Z_to_bv 64 (Z.of_nat (length (toks D)) - 1) ->
  join_k B API S 0x178b0 19 rg R1 k1 qv P ->
  rej_k B API S f 0x17a88 rg R1 k1 qv P ->
  rej_k B API S f 0x178a4 rg R1 k1 qv P ->
  SR rsegs c P.
Proof.
  intros f rg mem1 md1 L1 A1 R1 O1 k1 qv jk c P HST RT N21 HK N19 N22 JOIN REJ1 REJ2.
  pose proof HST as (_ & _ & VR & _).
  destruct (add_reads f rg (route_pc RAdd) mem1 md1 L1 A1 R1 O1 k1 qv None jk c HST) as (SP2 & PL & HB & HW).
  pose proof (ok_psl B API S HS) as PSL.
  pose proof (sp_facts B API S HS) as (SPC & SP63 & _).
  assert (HSP : bv_unsigned (reg_get rg 2) < 2^63) by (rewrite SP2; unfold s_spf, VR_K in *; lia).
  assert (NE : toks D <> []) by (intros E; rewrite E in RT; discriminate).
  assert (NL : (1 <= length (toks D) <= 64)%nat).
  { split; [destruct (toks D); [contradiction|cbn [length]; lia]|lia]. }
  eapply (@ka_w f _ B API HF S HS rg (route_pc RAdd) mem1 md1 L1 A1 R1 O1 k1 qv None jk c [] _ P HST).
  - intros; exact I.
  - eapply evt_mono.
    { unfold Regs6ss.mkR_of. cbn [route_pc]. eapply (add_kparse SCMP NCMP (toks D) (s_ps S));
      [exact N19|exact N21|exact N22|exact NL|exact PL|exact HSP|apply mem_inv_normalize|exact HB|exact HW]. }
    intros ms HQ. split; [exact HQ|]. destruct HQ as (RR & pc & mm & E & MU & WM & _).
    exists RR, (Z_to_bv 64 pc), mm. split; [exact E|]. split; assumption.
  - intros R' pc' m' rg' mem2 HQ X MK.
    destruct HQ as (RR & pc & mm & E & _ & _ & KP & RESULT).
    injection E as ER EPC EM. subst R' pc' m'.
    pose proof (add_vregs_keep S rg RR rg' VR X KP) as VR'.
    assert (G18 : getr rg' 18 = getr rg 18) by exact (add_get_keep _ _ _ X KP 18 ltac:(cbn; tauto)).
    assert (G21 : getr rg' 21 = getr rg 21) by exact (add_get_keep _ _ _ X KP 21 ltac:(cbn; tauto)).
    destruct RESULT as [(-> & INPUT)|([EPC | EPC] & BAD)].
    + eapply (add_run f rg rg' mem2 md1 L1 A1 R1 O1 k1 qv jk _ P (MK 0x17834 eq_refl VR') RT G18 HK); [|exact JOIN].
      rewrite (getr_of_eqv _ _ 20 X eq_refl), (getr_of_eqv _ _ 19 X eq_refl). exact INPUT.
    + subst pc. eapply REJ1. split; [exact (MK 0x17a88 eq_refl VR')|].
      split; [exact G18|]. split; [exact G21|]. split; [|reflexivity].
      rewrite RT. destruct (toks D) as [|v rest]; [contradiction|exact BAD].
    + subst pc. eapply REJ2. split; [exact (MK 0x178a4 eq_refl VR')|].
      split; [exact G18|]. split; [exact G21|]. split; [|reflexivity].
      rewrite RT. destruct (toks D) as [|v rest]; [contradiction|exact BAD].
Qed.

End R.
