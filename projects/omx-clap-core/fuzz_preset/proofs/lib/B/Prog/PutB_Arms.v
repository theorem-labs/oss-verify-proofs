(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B' (asan-ubsan #102 pin d663f82d7f48), the walk of put: THE
   TWO ARMS. Arm 1 (failed = 1): the entry run to the return (index 28 `bnez` taken). Arm 0 (failed = 0): the entry
   run to the need test (index 44, `bgeu cap, n + 1 + len`); FAST (cap >= need) to the seat at the join (index 65)
   and the shared tail (PutB_Tail.putb_tail); GROW (cap < need) through the grow head and the doubling loop
   (PutB_Loop.putb_loop), fuzz_realloc (index 56, the text through PutB_Base.put_realloc_call), then the NULL arm
   (index 116: failed := 1, the return) or the SUCCESS arm (indices 58 .. 64: buf := res, cap := newcap, o + 8 back
   from the spill at 0(sp)) to the seat and the tail.
   Texts: the batch kit's cut 7cdbb61b5fa0 (PRH_FnWriter d89d3c67b78, PRH_FnAlloc
   4d8aeba047e, PRH_Base ef7c8ca9852). The two gaps the f97c walk met by a _FIX twin are CLOSED BY THE BATCH KIT'S TEXT, so the
   walk proves the text itself:
   (1) REFUSED-RET: the text now takes the consumer window prh_cons_from over put's own all-granted events and
   states the refusal arm DEAD (DEAD-PUT: `exists ok, prhWriter_ret_ok .. /\ prh_granted ..`). At the grow, the
   leaf's batch-kit outcome clause gives res <> 0 at cnt <> fail (PutB_Base.put_realloc_cases), so a NULL is the allocation
   set to fail only, and the twin's added premise putb_k0_refused and its lemma putb_ret_refused are deleted.
   (2) NULL-HIST: the text's grow-NULL conjunct is `f' = 1 -> exists hist', ..`, the twin's form, met by
   PutB_Base.putb_null_pos.
   The live room is the text's per-event prh_live_evs; its first event is fuzz_realloc's guarded per-call premise
   (PutB_Kit.putb_live_first). FRM0-ENTRY: fpre's `frm_zero (fp_csr fx)` is threaded to fuzz_realloc's fpre
   (put_realloc_call); put's post is fpostWm, with no exit frm_zero conjunct.
   Port of the A walk S7a_put.v (sha256 f576f7636d50; internal record) put_arm1 / put_arm0 (its success tail was never built).
   THE RE-HIDING MOVE AND THE HULL (the texts' current form): put's text concludes SRr' segs RZ_cf (the grow's
   fuzz_realloc frees the old buffer) with its post fpostWmR at wle' segs RZ_cf, and takes `(length rp_os <= 4)%nat`.
   Arm 0 concludes in that form: its run up to the call is plain SRr, lifted once at its entry
   (YGcfRhLift.ra_rh_of_SRr); the call is PutB_Base.put_realloc_call (the rule over R at wle'), its hull budget the
   env's pe_hull at put's run position; the runs after it use the runners over R, and the shared tail is
   PutB_Tail.putb_tail at wle' (the no-grow arm lifts its plain journal there). Arm 1 makes no call, so it stays plain
   SRr and PutB.v lifts it.
   Numerals: indices DERIVED (PutB_Base.PK); 112 (LENGTH: put's frame); 64 / 65 / 66 / 70 (after-stretch / after-call
   atom indices, DERIVED); 4096, 2 ^ 28, 2 ^ 32, 2 ^ 46, 2 ^ 47, 2 ^ 64 (DERIVED bounds). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC81.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YK06 YImgTop YK1g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YCbqG YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YGcallMx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive YG0dcf YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PresetRoomPos PresetLiveBounds PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterSpec WriterSpecFacts WriterApp WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PutB_Kit PutB_Base PutB_Loop PutB_Tail.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* SCOPED LIA (22:58Z: PutB_Arms took 2052 s, 99.6% in lia over the grow arm's whole context). Each lia
   of the grow arm runs as `(clear - <the facts it needs>; lia) || slia_fb`: the fallback is the old full-context lia,
   and it prints PUTB-SLIA-FALLBACK, so a log with no such line has every lia of the arm scoped. *)
Ltac slia_fb := idtac "PUTB-SLIA-FALLBACK"; lia.

(* a register of a symbolic state read through its sv, the sv computed *)
Ltac putb_greg GR :=
  rewrite GR; match goal with |- context [sv_denot ?EE (sr_get ?L ?r)] =>
    let v := eval vm_compute in (sr_get L r) in change (sr_get L r) with v end.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs rc B_prog_listing PA).
#[local] Notation VAL := (@pa_val rc B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma rc B_prog_listing PA).
#[local] Notation BASE := (@pa_val rc B_prog_listing PA A_TEXT).

Section h.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis PE : putb_env (SK := SK) B ARx.
Let LAWS : AR_laws_x SEGS B ARx cf_head := pe_laws B ARx PE.
Let TL : PALib B := pe_tl B ARx PE.
Let RUN := paj_run_x (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS.
Let BR := paj_branch (PI := PA).
Let RET := paj_ret_at (PL := PL_prog_B) (PI := PA).
#[local] Notation RZ := YGcfRehidePost.RZ_cf.
(* the branch over R at wle' segs RZ_cf, for the runs after fuzz_realloc *)
Let BRR := paj_branchR (PI := PA) (wle' SEGS RZ).
Variable CTX0 : list (list Z).

Section rp.
Variable rp_sm : list Z -> Z * Z.
Variable rp_x : list Z.
Variable rp_os : list (option nat * option nat * option nat).
Variable rp_H0 : list Z.

(* the post of the text tput_specX, by its name in the text's projection layer, PRH_FnWriter.tputP_Q (tputP_Q_check
   fails to build if that body and the text's post ever differ); this name only puts the arguments in the walk's
   order. The arms build it conjunct by conjunct after unfolding both names. *)
Definition putb_post (rp_i : nat) (rp_hist : list YG00.chunk) ly S Lam peak ran most own o buf (st : WriterApp.wst)
  (bs : list Z) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  tputP_Q B rp_sm rp_x rp_os rp_i rp_H0 rp_hist most own ly S o buf st bs Lam peak ran.
(* with the segment's memory invariant P on the end memory (the generic-P form) *)
Definition putb_postP (P : (word -> option byte) -> Prop) (rp_i : nat) (rp_hist : list YG00.chunk) ly S Lam peak ran
  most own o buf (st : WriterApp.wst) (bs : list Z) :
  alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    putb_post rp_i rp_hist ly S Lam peak ran most own o buf st bs ly' S' Hp' W' regs' mem' md' /\ P mem'.

(* ---- ARM 1: failed = 1 - the run from the entry to the return: nothing written but the frame, so the model run of
   [bs] is empty, the ledger and the blocks are the entry's ---- *)
Lemma putb_arm1 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall ly S Hp W regs mem md ch o d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran most own
    (rp_i : nat) rp_hist,
  fpre B ARx STK_put ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  getr regs 10 = w64 o -> fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  WriterApp.w_failed st = 1 -> P mem ->
  SRr SEGS W (cfg_at SEGS (SIGMA AS_put) regs mem md)
    (fpostW B ARx SK STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (putb_postP P rp_i rp_hist ly S Lam peak ran most own o buf st bs)).
Proof.
intros P PLAW.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
intros ly S Hp W regs mem md ch o d buf st bs Lam peak ran most own rp_i rp_hist HPRE HROOM HPOS H10 HWIN Hol Hoh HOUT
  HLED Hf1 HPM.
pose proof HPRE as (HAP & HRO & HSTKTOP & HRAZ & HFRM).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : 112 + 4096 + 16 <= STK_put) by (vm_compute; discriminate).
pose proof HOUT as (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
set (len := Z.of_nat (length (WriterApp.w_text st))) in *.
assert (Hlen : 0 <= len < 2 ^ 64).
{ destruct Harm as [(Hc & _ & Ht) | (_ & _ & Hl & _)]; subst len; [rewrite Ht; cbn; lia | lia]. }
rewrite Hf1 in V24.
destruct (put_entry B ARx PE ly S Hp W regs mem md ch o d buf len (WriterApp.w_cap st) 1 HAP H10 HWIN Hol Hoh Ho8
  V0 Hbr V8 Hlen V16 Hcr V24 ltac:(lia)) as (HS & SHOK).
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (ajournal_x_init_W (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := put_E regs buf len (WriterApp.w_cap st)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len (WriterApp.w_cap st))) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Uo : bv_unsigned (ew E 10) = o) by (rewrite E10; apply unsigned_lit_small; lia).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (WriterApp.w_cap st)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
unfold cfg_at. rewrite (pe_ent B ARx PE).
change (w64 (BASE + PUT_K)) with (Z_to_bv 64 (BASE + PUT_K)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
(* the return at index 115: every callee-saved register and ra are back at their entry atoms *)
try rewrite wvb_collapse in HJ.
apply (RET W E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat1.
assert (HAG : env_agree 32 (Ereg regs (put_extra buf len (WriterApp.w_cap st))) E).
{ split; [intros k Hk; apply EL; unfold A_TEXT; lia | reflexivity]. }
assert (HP : aregs_preserved regs (ms_regs ms)).
{ pose proof HS as HS'. unfold st_ok_pi in HS'.
  eapply (aregs_preserved_of_st_ok SEGS); [exact HS' | exact HAG | vm_compute; reflexivity]. }
assert (Hra1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W) E _ ms 1%bv HS).
  match goal with |- sv_denot E ?e = _ => let v := eval vm_compute in e in change e with v end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
(* only the frame [sp - 112, sp) and the struct [o, o + 32) are write windows of the run *)
assert (NOW : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout Hos. apply aview_eq_of. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
  unfold put_ss, put_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | []]]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi stack_region got_regionP bcell_regionP put_struct base_val] in Hra';
    rewrite ?HKf, ?Usp, ?Uo in Hra'; lia. }
(* the struct's four fields at the end, from the final state's struct region *)
put_region HS 3%nat (put_struct 1) HRS.
assert (VF : forall od (w : N) e v, In (YP09.mkChunk od (CVal w e)) (YP09.r_chunks (put_struct 1)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (o + od) (N.to_nat w) v).
{ intros od w e v Hin He Hv Hw. exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 od w e v HRS Uo Hin He Hv Hw). }
assert (DEN : forall (k : nat) z, ew E k = Z_to_bv 64 z -> sv_denot E (SOff k 0) = Z_to_bv 64 z).
{ intros k z Hk. cbn [sv_denot]. rewrite Hk, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (VF 0 8%N (SOff 33 0) buf ltac:(cbn; tauto) (DEN _ _ E33) ltac:(cbn; lia) ltac:(cbn; lia)) as W0.
pose proof (VF 8 8%N (SOff 34 0) len ltac:(cbn; tauto) (DEN _ _ E34) ltac:(cbn; lia) ltac:(cbn; lia)) as W8.
pose proof (VF 16 8%N (SOff 35 0) (WriterApp.w_cap st) ltac:(cbn; tauto) (DEN _ _ E35) ltac:(cbn; lia) ltac:(cbn; lia)) as W16.
pose proof (VF 24 4%N (SLit 1) 1 ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as W24.
rewrite Z.add_0_r in W0. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in W0, W8, W16, W24.
exists ly, S, Hp, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat1 md), 0.
split.
{ rewrite wvb_collapse, Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ pose proof (ajournal_x_materialize (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low rc B_prog_listing PA)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat1 HJ) as HJ1.
  rewrite wvb_collapse in HJ1. exact HJ1. }
split.
{ intros a Ha Hn. apply NOW; [lia | lia |]. intros Ho. apply Hn. exists (o, o + 32). split; [left; reflexivity | cbn; lia]. }
split; [exact HP|].
unfold putb_postP. split; [|exact HPM].
unfold putb_post, tputP_Q. split; [exact HROOM|].
split; [intros _; exact HPOS|].
split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; apply andb_prop in Hg; destruct Hg as (Hg & _);
  apply Z.eqb_eq in Hg; lia|].
assert (Hf1' : WriterApp.w_failed st <> 0) by lia.
(* the outcomes: none (k = 0) *)
exists []. split.
2: { intros i Hi. rewrite (prhW_k_failed [] st [bs] Hf1') in Hi. clear - Hi; lia. }
unfold prhWriter_ret_ok. exists ran, buf, Lam, peak. cbv zeta.
rewrite (prhW_putN_failed [bs] [] st Hf1'), (prhW_k_failed [] st [bs] Hf1').
(* prh_oks at k = 0, ns := prhWriter_reqs [] st [bs], most := most (the ledger's g_most), ran := ran, ran' := ran *)
split; [split; [intros i Hi; clear - Hi; lia|]; split; [left; reflexivity | intros i Hi; clear - Hi; lia]|].
split.
{ apply (put_out_kept W mem (ms_mem ms) Lam o buf st st); try reflexivity.
  - intros a Ha. apply NOW; lia.
  - intros Hc. destruct (put_buf_low B ARx PE ly S Hp W mem md Lam peak _ _ ran most own o buf st HAR HLED HOUT Hc) as (Hb1 & Hb2 & _).
    pose proof (@cf_head_nonneg cp). lia.
  - right. exact Hf1.
  - intros H0. lia.
  - exact W0.
  - exact W8.
  - exact W16.
  - rewrite Hf1. exact W24.
  - exact HOUT. }
split.
{ apply (put_ledger_kept0 B ARx PE ly S Hp W mem (ms_mem ms) md); [exact HAR | intros a Ha; apply NOW; lia | exact HLED]. }
left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | apply Permutation_refl].
Qed.

(* ---- ARM 0: failed = 0 - the entry run to the need test (index 44); FAST (cap >= need) to the seat at the join
   (index 65) and the shared tail; GROW (cap < need) through the grow head, the doubling loop and fuzz_realloc ---- *)
Lemma putb_arm0 : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P -> srr_inv_call SEGS P ->
  forall ly S Hp W regs mem md ch o s n d buf (st : WriterApp.wst) (bs : list Z) Lam peak ran most own
    (rp_i : nat) rp_hist,
  fpre B ARx STK_put ly S Hp W regs mem md ch -> room_live_cf S ->
  PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S -> (length rp_os <= 4)%nat ->
  (* The batch kit: the consumer window over put's own all-granted events, then the closure without a run-word list *)
  PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhWriter_evs [] st [bs])) ->
  prh_univ_closure B CTX0 ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  (spZ regs + 16 <= o \/ o = spZ regs + 8) ->
  (spZ regs + 16 <= o ->
     exists ra, rdword (aview SEGS (w_H W) mem) (o - 8) = Some ra /\
       exists nfp, rdword (aview SEGS (w_H W) mem) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling) ->
  fwin ly W regs mem d -> spZ regs <= o -> o + 32 <= spZ regs + d ->
  prhWriter_out (PA := PA) W mem Lam o buf st ->
  prh_ledger B ly S Hp W mem Lam peak (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own ->
  src_rd (PA := PA) W mem s bs -> Z.of_nat (length bs) = n ->
  prhWriter_src_home B ly S Lam buf (WriterApp.w_cap st) s n ->
  (prhWriter_grows st bs = true -> WriterApp.w_cnt st <> WriterApp.w_fail st ->
     nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i = Some (prhWriter_ev st bs)) ->
  Z.of_nat (length (WriterApp.w_text st)) + n + 1 <= prhWriter_WMAX ->
  prhWriter_WMAX + cf_head < cf_malloc_max ->
  prh_live_evs S (prhWriter_evs [] st [bs]) ->
  WriterApp.w_failed st = 0 -> P mem ->
  SRr' SEGS RZ W (cfg_at SEGS (SIGMA AS_put) regs mem md)
    (fpostWR B ARx SK (wle' SEGS RZ) STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st)) regs ly S Hp W mem md
       (putb_postP P rp_i rp_hist ly S Lam peak ran most own o buf st bs)).
Proof.
intros P PLAW PCALL.
pose (RUNI := paj_run_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
pose (RUNTOI := paj_run_to_x_inv (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW).
intros ly S Hp W regs mem md ch o s n d buf st bs Lam peak ran most own rp_i rp_hist HPRE HROOM HPOS HLEN HCONS HUNIV H10
  H11 H12 HCASE HREC HWIN Hol Hoh HOUT HLED HSRC Hn HHOME HEV HWMAX HMAX HLIVE Hf0 HPM.
(* the run up to the call is plain SRr: lifted once, here, into SRr' segs RZ_cf *)
apply (YGcfRhLift.ra_rh_of_SRr SEGS RZ).
change (put_hide (spZ regs + 16 <= o \/ o = spZ regs + 8)) in HCASE.
pose proof HPRE as (HAP & HRO & HSTKTOP & HRAZ & HFRM).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HWIN as (Hd0 & Hd16 & Hdtop & Hdpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@alloc_ceiling_value rc) as HCV.
assert (HKf : pi_frame F_put = 112) by (vm_compute; reflexivity).
assert (HKs : 112 + 4096 + 16 <= STK_put) by (vm_compute; discriminate).
(* two bounds the scoped lias of the grow arm name (they keep each lia's context to a few facts) *)
assert (HCSP : YM05.alloc_ceiling + 112 <= spZ regs) by lia.
assert (HSPD : spZ regs + d <= 2 ^ 64) by lia.
pose proof HOUT as (Ho8 & Hbr & Hcr & V0 & V8 & V16 & V24 & Hf01 & Hbok & Harm).
set (len := Z.of_nat (length (WriterApp.w_text st))) in *.
assert (Hlen : 0 <= len < 2 ^ 64).
{ destruct Harm as [(Hc & _ & Ht) | (_ & _ & Hl & _)]; subst len; [rewrite Ht; cbn; lia | lia]. }
rewrite Hf0 in V24.
destruct (put_entry B ARx PE ly S Hp W regs mem md ch o d buf len (WriterApp.w_cap st) 0 HAP H10 HWIN Hol Hoh Ho8
  V0 Hbr V8 Hlen V16 Hcr V24 ltac:(lia)) as (HS & SHOK).
assert (HWINx : fwin_x SEGS ly W regs mem d) by (split; [exact Hd0|]; split; [exact Hd16|]; split; [exact Hdtop | exact Hdpres]).
pose proof (ajournal_x_init_W (SK := SK) SEGS B (@prh_pst prh_img_B) ARx STK_put d (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly S Hp W regs mem md ch HAP HWINx) as HJ.
set (E := put_E regs buf len (WriterApp.w_cap st)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs (put_extra buf len (WriterApp.w_cap st))) k)
  by (intros k Hk; subst E; unfold put_E; apply Eimg_low; exact Hk).
assert (EG : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r)
  by (intros kk r Hk Hr; rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ kk r Hr)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EG 2%nat 2%bv) by (lia || reflexivity); reflexivity).
assert (Uo : bv_unsigned (ew E 10) = o)
  by (rewrite (EG 10%nat 10%bv) by (lia || reflexivity); rewrite H10; apply unsigned_lit_small; lia).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (rewrite (EG 10%nat 10%bv) by (lia || reflexivity); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 (WriterApp.w_cap st)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
pose proof (eq_refl : len = Z.of_nat (length (WriterApp.w_text st))) as Hlen_def.
assert (Hn0 : 0 <= n) by lia.
unfold prhWriter_WMAX in HWMAX.
assert (U12 : bv_unsigned (ew E 12) = n)
  by (rewrite (EG 12%nat 12%bv) by (lia || reflexivity); rewrite H12; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = len) by (rewrite E34; apply unsigned_lit_small; lia).
(* the three registers the tail reads as functions of o (s3, s6, s8), at any later env that keeps atoms 10 and 32 *)
assert (DS3 : forall EE, ew EE 10 = Z_to_bv 64 o -> sv_denot EE (SAlu ALU_SRL (SOff 10 0) (SLit 3)) = Z_to_bv 64 (o / 8))
  by (intros EE HE10; apply (put_denot_srl3 EE 10 o HE10); lia).
assert (DS6 : forall EE, ew EE 10 = Z_to_bv 64 o -> sv_denot EE (SOff 10 8) = Z_to_bv 64 (o + 8))
  by (intros EE HE10; apply (put_denot_off EE 10 o 8 HE10); lia).
assert (DS8 : forall EE, ew EE 10 = Z_to_bv 64 o -> ew EE 32 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot EE (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) = Z_to_bv 64 (SHADOW_OFF + (o + 8) / 8))
  by (intros EE HE10 HE32; apply (put_denot_shx EE 10 32 8 o SHADOW_OFF HE10 HE32); unfold SHADOW_OFF; lia).
(* the entry facts of the source, and of the buffer when there is one *)
pose proof HSRC as (Sba & S4096 & Sceil & Samr & Sra & Shull).
rewrite Hn in Sceil, Samr, Sra, Shull.
destruct HHOME as (Hkept & Hdisj0).
unfold cfg_at. rewrite (pe_ent B ARx PE).
change (w64 (BASE + PUT_K)) with (Z_to_bv 64 (BASE + PUT_K)).
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
{ put_awr. }
psrr_branch_tok RUN BR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
all: rewrite branch_geu_U, (U_atom E 35 (WriterApp.w_cap st) E35 Hcr), U_add_off_atom in Hc
  by (unfold M64; rewrite ?U12, ?U34; lia).
all: rewrite U12, U34 in Hc.
(* ---- FAST: len + n + 1 <= cap, no call ---- *)
1: { apply negb_true_iff, Z.ltb_ge in Hc.
  assert (Hcap0 : WriterApp.w_cap st <> 0) by lia.
  destruct (put_buf_low B ARx PE ly S Hp W mem md Lam peak _ _ ran most own o buf st HAR HLED HOUT Hcap0) as (Hb1 & Hb2 & Hb16 & Hinb).
  destruct Harm as [(Hz & _) | (Hgrid & HinL & Hlt & (rest & Hrl & Hba) & Hsh)]; [contradiction|].
  destruct (Hsh Hf0) as (Bra & Bhull).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hinb) as (_ & _ & _ & Happ & _).
  pose proof (@cf_head_nonneg cp) as Hch0.
  assert (Hreq : req_size (WriterApp.w_cap st + cf_head) = WriterApp.w_cap st + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (WriterApp.w_cap st + cf_head) 0); cbv iota; lia).
  rewrite Hreq in Happ.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 65).
  all: try solve [put_awr].
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => set (R1 := ms_regs X) in *; set (M1 := ms_mem X) in * end.
  (* the run writes the frame only: every byte outside the frame and the struct is the entry's *)
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
    aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hout Hos. apply aview_eq_of.
    rewrite (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | |];
    rewrite unsigned_lit_small by lia; intros (r & Hr & Hra');
    match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp, ?Uo in Hra'; lia | ]);
    destruct Hr. }
  assert (KLOW : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a)
    by (intros a Ha; apply KEEP; lia).
  try rewrite wvb_collapse in HJ.
  (* the registers at the join *)
  assert (GR : forall rr : bv 5, getr R1 rr = sv_denot E (sr_get (ss_regs _) rr))
    by (intros rr; exact (st_ok_pi_restrict_reg (w_H W) E _ _ rr HS)).
  assert (D0 : forall (kx : nat) (wx : word), ew E kx = wx -> sv_denot E (SOff kx 0) = wx)
    by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (R8 : getr R1 8 = Z_to_bv 64 o) by (putb_greg GR; apply D0; exact E10).
  assert (R9 : getr R1 9 = Z_to_bv 64 n)
    by (putb_greg GR; apply D0; rewrite (EG 12%nat 12%bv) by (lia || reflexivity); exact H12).
  assert (R18 : getr R1 18 = Z_to_bv 64 s)
    by (putb_greg GR; apply D0; rewrite (EG 11%nat 11%bv) by (lia || reflexivity); exact H11).
  assert (R23 : getr R1 23 = Z_to_bv 64 SHADOW_OFF) by (putb_greg GR; apply D0; exact E32).
  assert (R19 : getr R1 19 = Z_to_bv 64 (o / 8)) by (putb_greg GR; exact (DS3 E E10)).
  assert (R22 : getr R1 22 = Z_to_bv 64 (o + 8)) by (putb_greg GR; exact (DS6 E E10)).
  assert (R24 : getr R1 24 = Z_to_bv 64 (SHADOW_OFF + (o + 8) / 8)) by (putb_greg GR; exact (DS8 E E10 E32)).
  assert (R3 : getr R1 3 = getr regs 3) by (putb_greg GR; apply D0; apply EG; [lia | reflexivity]).
  assert (R4 : getr R1 4 = getr regs 4) by (putb_greg GR; apply D0; apply EG; [lia | reflexivity]).
  assert (Hsp1 : spZ R1 = spZ regs - 112)
    by (unfold spZ at 1; putb_greg GR; cbn [sv_denot]; rewrite Usp; apply unsigned_lit_small; lia).
  (* the frame: the thirteen saved registers *)
  put_region_auto HS 0%nat HRF.
  assert (Hsv : forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W) M1) (spZ regs - 8 - 8 * Z.of_nat j) 8
     (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
  { intros j Hj.
    lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
      assert (FR : forall (k : nat) (r : bv 5) od, (k < 32)%nat -> Z.of_nat k = bv_unsigned r ->
        In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
        val_mem SEGS (mrestrict (w_H W) M1) (spZ regs + od) 8 (bv_unsigned (getr regs r)))
      by (intros k r od Hk Hr Hin;
          eapply (field_of_region SEGS E _ 2 (spZ regs) cs _ _ _ _ od 8%N (SOff k 0) (bv_unsigned (getr regs r)) HRF Usp Hin);
          [ apply D0; rewrite (EG k r Hk Hr); symmetry; apply Z_to_bv_bv_unsigned
          | pose proof (u64_range (getr regs r)); cbn; lia | cbn; lia ])
    end.
    replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by lia.
    do 13 (destruct j as [|j];
      [ cbn [nth put_saved];
        match goal with |- val_mem _ _ (spZ regs + ?od) _ (bv_unsigned (getr regs ?r)) =>
          let od' := eval vm_compute in od in let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
          change od with od'; apply (FR k r od'); [lia | reflexivity | cbn; tauto] end
      | ]).
    lia. }
  (* the struct: buf, len, cap, failed = 0 *)
  put_region_auto HS 3%nat HRS.
  assert (W0 : val_mem SEGS (mrestrict (w_H W) M1) o 8 buf).
  { pose proof (field_of_region SEGS E _ 10 o _ 0 32 0 32 0 8%N (SOff 33 0) buf HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E33) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
  assert (W8 : val_mem SEGS (mrestrict (w_H W) M1) (o + 8) 8 len)
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E34) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W16 : val_mem SEGS (mrestrict (w_H W) M1) (o + 16) 8 (WriterApp.w_cap st))
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 16 8%N (SOff 35 0) (WriterApp.w_cap st) HRS Uo ltac:(cbn; tauto)
      (D0 _ _ E35) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W24 : val_mem SEGS (mrestrict (w_H W) M1) (o + 24) 4 0)
    by exact (field_of_region SEGS E _ 10 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS Uo ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  (* the caller window outside the struct, and the struct in the footprint *)
  assert (HWK : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
    aview SEGS (w_H W) M1 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hnf. apply KEEP; [lia | lia |]. intros Ho. apply Hnf. exists (o, o + 32).
    split; [left; reflexivity | cbn; lia]. }
  assert (HFPo : forall a, o <= a < o + 32 -> inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a)
    by (intros a Ha; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
  (* the destination [buf + len, buf + len + n]: in the buffer block, addressable *)
  assert (Hamr_d : amem_range (buf + len) (n + 1)).
  { apply (put_app_amem (buf - cf_head) (WriterApp.w_cap st + cf_head)); [exact Happ | lia | lia | lia]. }
  assert (Hawr_d : forall a, buf + len <= a <= buf + len + n ->
    awr_byte (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) (ablocks B ly S) (ablocks B ly S)
      ly [] a).
  { intros a Ha. right; left. split.
    - exists (buf - cf_head, buf - cf_head + req_size (WriterApp.w_cap st + cf_head)). split; [|cbn; rewrite Hreq; lia].
      right. unfold prhWriter_fp. rewrite (proj2 (Z.eqb_neq _ _) Hcap0). unfold ablocks_fp. cbn. left; reflexivity.
    - exists (buf - cf_head), (WriterApp.w_cap st + cf_head). split; [exact Hinb | rewrite Hreq; lia]. }
  assert (Hra_d : range_addressable (aview SEGS (w_H W) M1) SHADOW_OFF (buf + len) (n + 1)).
  { eapply (range_addressable_agree (aview SEGS (w_H W) mem)).
    { intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity. }
    apply (range_addressable_sub _ _ buf (WriterApp.w_cap st)); [exact Bra | lia | lia]. }
  assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) M1) (buf + len) n).
  { intros Hn1 s0 Hs0. pose proof (put_hull_low (buf + len) n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
    rewrite KLOW by lia. exact (put_hull_sub _ buf (WriterApp.w_cap st) (buf + len) n Bhull ltac:(lia) ltac:(lia) Hn1 s0 Hs0). }
  (* the source [s, s + n): read-only, addressable, apart from the destination *)
  assert (Hsc : s + n <= YM05.alloc_ceiling) by lia.
  assert (Hsvis : forall a, s <= a < s + n -> aview SEGS (w_H W) M1 a <> None).
  { intros a Ha. rewrite KLOW by lia. replace a with (s + Z.of_nat (Z.to_nat (a - s))) by lia.
    rewrite (put_garr8_aview W mem s bs (Z.to_nat (a - s)) Sba ltac:(lia)). discriminate. }
  assert (Hdisj : buf + len + n <= s \/ s + n <= buf + len) by lia.
  assert (Hra_s : range_addressable (aview SEGS (w_H W) M1) SHADOW_OFF s n).
  { eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Sra].
    intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity. }
  assert (Hhull_s : 0 < n -> shadow_hull_vis (aview SEGS (w_H W) M1) s n).
  { intros Hn1 s0 Hs0. pose proof (put_hull_low s n s0 ltac:(lia) Hn1 ltac:(lia) Hs0).
    rewrite KLOW by lia. exact (Shull Hn1 s0 Hs0). }
  (* the tail at wle' segs RZ_cf: the plain journal lifted (wle_wle') *)
  pose proof (ajournal_xwR_mono (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (@wle SEGS) (wle' SEGS RZ)
    (wle_wle' SEGS RZ) _ _ _ _ _ Hp _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJR.
  apply (SRr_ret SEGS). cbv beta.
  apply (putb_tail B ARx PE P PLAW PCALL ly S Hp W regs mem md d o s n buf len (WriterApp.w_cap st)
    (prhWriter_cfp o buf (WriterApp.w_cap st))
    ly S Hp W R1 M1 _ _ _ HJR HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8 Hsp1 R8 R9 R18 R23 R19 R22 R24 R3 R4 Hsv
    W0 W8 W16 W24 Hcr ltac:(lia) HWK HFPo ltac:(lia) ltac:(lia) ltac:(lia) Hamr_d Hawr_d Hra_d Hhull_d S4096 Hsc Samr
    Hsvis Hdisj Hra_s Hhull_s).
  (* the post: the capacity is unchanged, the text grows by bs, the ledger is the entry's over the new bytes *)
  intros regs' mem' md' k' HJ' HPM' Hkeep' Hcopy' Hnul' V0' V8' V16' V24'.
  unfold putb_postP. split; [|exact HPM'].
  unfold putb_post, tputP_Q. split; [exact HROOM|].
  split; [intros _; exact HPOS|].
  split; [intros Hg; exfalso; unfold prhWriter_grows, prhWriter_need in Hg; apply andb_prop in Hg;
    destruct Hg as (_ & Hg); apply Z.ltb_lt in Hg; rewrite <- Hlen_def, Hn in Hg; lia|].
  assert (EPUT : prhWriter_putN [] st [bs] = WriterApp.mkW 0 (WriterApp.w_text st ++ bs) (WriterApp.w_cap st)
     (WriterApp.w_cnt st) (WriterApp.w_fail st) (WriterApp.w_calls st)).
  { cbn [prhWriter_putN]. unfold prhWriter_grows, prhWriter_need. rewrite Hf0.
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [Z.eqb andb]. cbn [prhWriter_putN].
    unfold WriterApp.put1. rewrite Hf0. cbn [Z.eqb negb]. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  assert (EK : prhWriter_k [] st [bs] = 0%nat) by (unfold prhWriter_k; rewrite EPUT; cbn [WriterApp.w_calls]; lia).
  (* the outcomes: none (k = 0) *)
  exists []. split; [|rewrite EK; intros i Hi; clear - Hi; lia].
  unfold prhWriter_ret_ok. exists ran, buf, Lam, peak. cbv zeta. rewrite EPUT.
  rewrite EK. cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
  (* prh_oks at k = 0, ns := prhWriter_reqs [] st [bs], most := most (the ledger's g_most), ran := ran, ran' := ran *)
  split; [split; [intros i Hi; clear - Hi; lia|]; split; [left; reflexivity | intros i Hi; clear - Hi; lia]|].
  split.
  { apply (put_out_put W M1 mem' Lam o buf (WriterApp.w_cap st) (WriterApp.w_text st) bs 0 rest s); try assumption.
    - lia.
    - exact (put_app_band buf (WriterApp.w_cap st) cf_head Happ Hch0).
    - apply (put_bytes_keep W mem M1 buf _ Hba). intros j Hj. apply KLOW. lia.
    - eapply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact Bra].
      intros x Hx. pose proof (put_shadow_low x ltac:(lia)). rewrite KLOW by lia. reflexivity.
    - intros s0 Hs0. pose proof (put_hull_low buf (WriterApp.w_cap st) s0 ltac:(lia) ltac:(lia) ltac:(lia) Hs0).
      rewrite KLOW by lia. exact (Bhull s0 Hs0).
    - apply (put_bytes_keep W mem M1 s bs Sba). intros j Hj. apply KLOW. lia.
    - lia.
    - rewrite <- Hlen_def, Hn. exact Hkeep'.
    - rewrite <- Hlen_def, Hn. exact Hcopy'.
    - rewrite <- Hlen_def, Hn. exact Hnul'.
    - rewrite <- Hlen_def, Hn. exact V8'. }
  split.
  { apply (put_ledger_copy B ARx PE ly S Hp W mem mem' md Lam peak _ _ ran most own buf (WriterApp.w_cap st) HAR HLED HinL).
    intros a Ha Hab. rewrite Hkeep' by lia. apply KLOW. exact Ha. }
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | apply Permutation_refl]. }
(* ---- GROW: cap < len + n + 1: the spill of o + 8 at index 45, the grow head and the doubling loop, fuzz_realloc ---- *)
apply negb_false_iff, Z.ltb_lt in Hc.
(* every disjunction in the context goes behind put_hide: lia splits on each one it sees, and this arm carries a dozen *)
put_hide_all.
paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HPM put_Bspan (PK 46).
all: try solve [put_awr].
pmkst HS.
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => set (R1 := ms_regs X) in *; set (M1 := ms_mem X) in * end.
try rewrite wvb_collapse in HJ.
assert (GR : forall rr : bv 5, getr R1 rr = sv_denot E (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W) E _ _ rr HS)).
assert (R11 : getr R1 11 = Z_to_bv 64 (WriterApp.w_cap st)).
{ putb_greg GR. cbn [sv_denot]. rewrite E35, Z.add_0_r, unsigned_lit_small by lia. reflexivity. }
assert (R10 : getr R1 10 = Z_to_bv 64 (n + 1 + len)).
{ putb_greg GR. apply bv_eq. rewrite unsigned_lit_small by lia.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)))) with (U E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0))).
  rewrite U_add_off_atom by (unfold M64; rewrite ?U12, ?U34; lia). rewrite U12, U34. lia. }
apply (putb_loop B ARx PE P PLAW W R1 M1 _ (WriterApp.w_cap st) (n + 1 + len) _ _ _ ly S Hp W mem md ly S Hp _ _ HJ HPM
  R11 R10 ltac:(lia) ltac:(lia)).
intros regs3 mem3 md3 HJ3 HPM3 HM3 L22 L11 HO3.
(* the loop changed a1 and s6 only: the symbolic state at index 51, a1 and s6 fresh atoms 64 / 65 *)
let v := eval vm_compute in (PK 51) in
jafter_stretch_pi HS 64%nat regs3 (mrestrict (w_H W) mem3) ([11%bv; 22%bv] : list (bv 5)) v HSY.
lazymatch type of HSY with ?T -> _ => assert (HRY : T) end.
{ intros r Hr. apply HO3; intros ->; vm_compute in Hr; discriminate Hr. }
specialize (HSY HRY). clear HRY.
lazymatch type of HSY with ?T -> _ => assert (HKY : T) end.
{ apply Forall_forall. intros r _. split.
  - intros a _. unfold mbyte. cbn [ms_mem restrict]. rewrite HM3. reflexivity.
  - intros a _ Hw. unfold writable_at in *. cbn [ms_mem restrict] in Hw. unfold wview in *. rewrite HM3. exact Hw. }
specialize (HSY HKY). clear HKY. rewrite <- restrict_mkst_fx in HSY.
remember (havoc E 64 (map (getr regs3) [11%bv; 22%bv])) as E2 eqn:HE2 in HSY.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall kk, (kk < 64)%nat -> ew E2 kk = ew E kk) by (intros kk Hk; rewrite HE2; apply ew_havoc_old; exact Hk).
assert (E264 : ew E2 64 = getr regs3 11) by (rewrite HE2; reflexivity).
assert (E265 : ew E2 65 = getr regs3 22) by (rewrite HE2; reflexivity).
pose proof HJ3 as (HAR3 & _).
assert (SHOK2 : sh_ok SEGS put_Bx put_SH E2 (mrestrict (w_H W) mem3)).
{ apply (put_shok B ARx PE E2 ly S Hp W mem3 md3 o HAR3); [rewrite OLD2 by lia; exact E32 | | lia | lia | lia | lia].
  rewrite OLD2 by lia. exact E10. }
clear HS SHOK HJ HEI HPM. rename HSY into HS. rename SHOK2 into SHOK. rename HJ3 into HJ. rename HEI2 into HEI.
rename HPM3 into HPM.
clear GR R11 R10. subst R1 M1.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
assert (Uo2 : bv_unsigned (ew E2 10) = o) by (rewrite OLD2 by lia; exact Uo).
(* ---- indices 51 .. 56: s11 := the shadow of o, its load check, buf into a0, newcap into a1, the call ---- *)
paj_run_tok_x_inv RUNI HS HJ SHOK HPM put_Bspan.
all: try solve [put_awr].
lazymatch type of HS with st_ok _ _ _ (restrict _ ?X) => rename X into MSC end.
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2.
prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
(* the call's memory is the entry's but for the frame and the struct (the loop wrote nothing) *)
assert (KEEPC : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W) (ms_mem MSC) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hout Hos. apply aview_eq_of.
  rewrite (HFr1 (Z_to_bv 64 a)), HM3, (HFr0 (Z_to_bv 64 a)), (HFr (Z_to_bv 64 a)); [reflexivity | | |];
  rewrite unsigned_lit_small by ((clear - Ha; lia) || slia_fb); intros (r & Hr & Hra');
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp, ?Uo, ?Usp2, ?Uo2 in Hra';
     ((clear - Hra' Hout Hos; lia) || slia_fb) | ]);
  destruct Hr. }
assert (KLOWC : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W) (ms_mem MSC) a = aview SEGS (w_H W) mem a)
  by (intros a Ha; apply KEEPC; ((clear - Ha HCSP C1 Hol; lia) || slia_fb)).
assert (HPCsp : spZ (ms_regs MSC) = spZ regs + d + - (112 + d))
  by (unfold spZ at 1; rewrite Q2, Usp2, unsigned_lit_small by lia; lia).
destruct (pe_cnt B ARx PE _ _ _ _ _ _ _ HPOS) as (HSEC & H24).
assert (Hs0c : s0Z (ms_regs MSC) = o) by (unfold s0Z; rewrite Q8, OLD2 by lia; exact Uo).
(* the record from o at the call: case 1 by tput_specX's record premise (both words lie at or above sp, outside put's
   frame and the struct), case 2 (o = sp + 8) by the caller window's presence at sp and put's own saved ra at sp - 8,
   below the ceiling by fpre's raZ bound *)
assert (HREC1 : exists ra nfp, rdword (aview SEGS (w_H W) (ms_mem MSC)) (o - 8) = Some ra /\
  rdword (aview SEGS (w_H W) (ms_mem MSC)) (o - 16) = Some nfp /\ nfp < YM05.alloc_ceiling).
{ unfold put_hide in HCASE. destruct HCASE as [Hc1 | Hc2].
  - destruct (HREC Hc1) as (ra & Hra8 & nfp & Hnfp & Hnc). exists ra, nfp.
    rewrite (put_rdword_ext (aview SEGS (w_H W) mem) _ (o - 8)) by (intros k Hk; apply KEEPC; lia).
    rewrite (put_rdword_ext (aview SEGS (w_H W) mem) _ (o - 16)) by (intros k Hk; apply KEEPC; lia).
    split; [exact Hra8|]. split; [exact Hnfp | exact Hnc].
  - destruct (put_rdword_some (aview SEGS (w_H W) (ms_mem MSC)) (o - 8)) as (ra & Hra8).
    { intros k Hk. rewrite KEEPC by lia. apply put_apresent_aview. apply Hdpres. lia. }
    put_region_auto_st HS 0%nat HRF.
    assert (DR : sv_denot E2 (SOff 1 0) = Z_to_bv 64 (raZ regs)).
    { cbn [sv_denot]. rewrite OLD2 by lia. rewrite (EG 1%nat 1%bv) by (lia || reflexivity).
      unfold raZ. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. reflexivity. }
    assert (Hr64 : 0 <= raZ regs < 2 ^ (8 * Z.of_N 8))
      by (unfold raZ; pose proof (u64_range (getr regs 1)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia).
    pose proof (field_of_region SEGS E2 _ 2 (spZ regs) _ (-112) 0 (-112) 0 (-8) 8%N (SOff 1 0) (raZ regs) HRF Usp2
      ltac:(cbn; tauto) DR Hr64 ltac:(cbn; lia)) as Hv.
    exists ra, (raZ regs). split; [exact Hra8|]. split; [|exact HRAZ].
    replace (o - 16) with (spZ regs + -8) by lia.
    exact (put_rdword_of_val_mem (w_H W) (ms_mem MSC) _ _ Hv (u64_range (getr regs 1))). }
destruct HREC1 as (ra & nfp & Hra8 & Hnfp & Hnc).
assert (HCO1 : YM05.alloc_ceiling <= o) by lia.
assert (HCO2 : spZ regs - 112 + 16 <= o) by lia.
assert (HCO3 : o < ly_top ly - 16) by lia.
destruct (put_chain_one ly (aview SEGS (w_H W) (ms_mem MSC)) (spZ regs - 112) o ra nfp HCO1 Ho8 HCO2 HCO3 Hra8
  (put_rdword_nonneg _ _ _ _ Hra8) Hnfp Hnc) as (ch1 & Hch1).
destruct (prh_univ_closure_realloc B CTX0 HUNIV) as (HU1 & HU2); [vm_compute; discriminate|].
assert (HMU : prh_malloc_univ B) by (apply (prh_univ_closure_malloc B CTX0 HUNIV); vm_compute; discriminate).
assert (Hcgrid : WriterApp.w_cap st = 0 \/ exists j, 0 <= j <= 51 /\ WriterApp.w_cap st = 4096 * 2 ^ j)
  by (destruct Harm as [(Hz & _) | (Hg & _)]; [left; exact Hz | right; exact Hg]).
destruct (put_newcap_grid (WriterApp.w_cap st) (n + 1 + len) Hcgrid ltac:(lia)) as (Hgrid' & Hneed' & H28' & Hge').
set (nc := WriterSpec.newcap (WriterApp.w_cap st) (n + 1 + len)) in *.
(* the model's need and grow facts of this arm *)
assert (Hneedlt : WriterApp.w_cap st < prhWriter_need st bs)
  by (unfold prhWriter_need; rewrite <- Hlen_def, Hn; ((clear - Hc; lia) || slia_fb)).
assert (Enc : WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs) = nc)
  by (unfold prhWriter_need, nc; rewrite <- Hlen_def, Hn; f_equal; ((clear - Hn; lia) || slia_fb)).
assert (Hgr : prhWriter_grows st bs = true)
  by (unfold prhWriter_grows; rewrite Hf0; cbn [Z.eqb andb]; apply Z.ltb_lt; exact Hneedlt).
(* The batch kit's per-event live room at put's one event (the all-granted run of [bs] is [prhWriter_ev st bs] when the call is
   not the allocation set to fail) is fuzz_realloc's guarded per-call premise *)
assert (HLIVE' : WriterApp.w_cnt st <> WriterApp.w_fail st -> blocks_bytes S + (nc + cf_head) <= LIVE_MAX).
{ intros Hcf. pose proof HLIVE as HL1. rewrite (prhW_evs_grow st bs Hgr Hcf) in HL1.
  pose proof (putb_live_first S _ [] HL1) as H1.
  assert (Hreq : prh_ev_req (prhWriter_ev st bs) = nc + cf_head)
    by (unfold prhWriter_ev; rewrite Enc; destruct (WriterApp.w_cap st =? 0); reflexivity).
  rewrite Hreq in H1. exact H1. }
(* the consumer window and the run premise at the leaf's one event (DEAD-PUT, PutB_Base.put_realloc_cases) *)
assert (HCONS1 : WriterApp.w_cnt st <> WriterApp.w_fail st -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i 1).
{ intros Hcf. pose proof HCONS as HC1. rewrite (prhW_evs_grow st bs Hgr Hcf) in HC1. exact HC1. }
assert (HRUN : WriterApp.w_cnt st <> WriterApp.w_fail st -> nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i =
  Some (if WriterApp.w_cap st =? 0 then PresetReqAt.HMal (nc + cf_head)
        else PresetReqAt.HRe (WriterApp.w_cap st + cf_head) (nc + cf_head))).
{ intros Hcf. rewrite (HEV Hgr Hcf). unfold prhWriter_ev. rewrite Enc. reflexivity. }
assert (Hal' : - (112 + d) mod 16 = 0).
{ replace (- (112 + d)) with ((- 7 - d / 16) * 16) by (pose proof (Z.div_mod d 16 ltac:(lia)); lia). apply Z_mod_mult. }
assert (Hbud : STK_fuzz_realloc - - (112 + d) <= STK_put + d).
{ assert (STK_fuzz_realloc + 112 <= STK_put) by (vm_compute; discriminate). lia. }
assert (Hgp' : getr (ms_regs MSC) 3 = w64 (as_gp B))
  by (rewrite Q3, OLD2 by lia; rewrite (EG 3%nat 3%bv) by (lia || reflexivity); exact Hgp).
assert (Htp' : getr (ms_regs MSC) 4 = w64 (as_tp B))
  by (rewrite Q4, OLD2 by lia; rewrite (EG 4%nat 4%bv) by (lia || reflexivity); exact Htp).
assert (Hraw : YK0s.ret_ok (getr (ms_regs MSC) 1))
  by (rewrite Q1; apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity]).
assert (Hra4' : 4096 <= bv_unsigned (getr (ms_regs MSC) 1))
  by (pose proof (@pa_B_ok _ _ PA) as HB; rewrite Q1, unsigned_lit_small by lia; lia).
assert (Hch' : achain ly (aview SEGS (w_H W) (ms_mem MSC)) (spZ regs + d + - (112 + d)) (s0Z (ms_regs MSC)) ch1)
  by (replace (spZ regs + d + - (112 + d)) with (spZ regs - 112) by lia; rewrite Hs0c; exact Hch1).
(* the return pc of the jal is a listing slot, below the ceiling (the closed lemma put_ret_slot_ceil) *)
assert (HRAZc : raZ (ms_regs MSC) < YM05.alloc_ceiling).
{ pose proof (@pa_B_ok _ _ PA) as HB. unfold raZ. rewrite Q1, unsigned_lit_small by lia.
  match goal with |- _ + ?k < _ => assert (HK57 : PK 57 = k) by (vm_compute; reflexivity) end.
  rewrite <- HK57. exact put_ret_slot_ceil. }
assert (HTOP' : spZ (ms_regs MSC) + 64 <= ly_stk_hi ly) by (rewrite HPCsp; lia).
assert (H10' : getr (ms_regs MSC) 10 = w64 buf) by (rewrite Q10, OLD2 by lia; exact E33).
assert (H11' : getr (ms_regs MSC) 11 = w64 nc) by (rewrite Q11, E265; exact L22).
assert (Hnmax : nc + cf_head < cf_malloc_max) by (unfold prhWriter_WMAX in HMAX; lia).
pose proof (put_ledger_kept0 B ARx PE ly S Hp W mem (ms_mem MSC) md Lam peak _ _ ran most own HAR KLOWC HLED) as HLED'.
(* the old block: none (cap = 0, buf = 0) or the buffer with its cap bytes *)
assert (HOX : exists OLD : list Z,
  (buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] /\ WriterApp.w_text st = []) \/
  (buf <> 0 /\ WriterApp.w_cap st <> 0 /\ (exists j, 0 <= j <= 51 /\ WriterApp.w_cap st = 4096 * 2 ^ j) /\
   In (buf, WriterApp.w_cap st) Lam /\ len < WriterApp.w_cap st /\
   (exists rest, OLD = WriterApp.w_text st ++ 0 :: rest) /\ Z.of_nat (length OLD) = WriterApp.w_cap st /\
   bytes_at W (ms_mem MSC) buf OLD /\
   cf_head <= buf - 4096 /\ buf + WriterApp.w_cap st <= YM05.alloc_ceiling /\ buf mod 16 = 0 /\
   In (buf - cf_head, WriterApp.w_cap st + cf_head) (ablocks B ly S))).
{ destruct Harm as [(Hz & Hb0 & Ht0) | (Hg & HinL & Hlt & (rest & Hrl & Hba) & Hsh)].
  - exists []. left. split; [exact Hb0|]. split; [exact Hz|]. split; [reflexivity | exact Ht0].
  - assert (Hcap0 : WriterApp.w_cap st <> 0)
      by (destruct Hg as (j & Hj & ->); assert (0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia); lia).
    destruct (put_buf_low B ARx PE ly S Hp W mem md Lam peak _ _ ran most own o buf st HAR HLED HOUT Hcap0)
      as (Hb1 & Hb2 & Hb16 & Hinb).
    pose proof (@cf_head_nonneg cp).
    exists (WriterApp.w_text st ++ 0 :: rest). right. split; [lia|]. split; [exact Hcap0|]. split; [exact Hg|].
    split; [exact HinL|]. split; [lia|]. split; [exists rest; reflexivity|]. split; [exact Hrl|].
    split; [apply (put_bytes_keep W mem (ms_mem MSC) buf _ Hba); intros j Hj; apply KLOWC; lia|].
    split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb16 | exact Hinb]. }
destruct HOX as (OLD & HOX).
assert (HOLD : buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] \/
  In (buf, WriterApp.w_cap st) Lam /\ bytes_at W (ms_mem MSC) buf OLD /\ Z.of_nat (length OLD) = WriterApp.w_cap st)
  by (destruct HOX as [(Hb0 & Hz & Ho0 & _) | (_ & _ & _ & HinL & _ & _ & Hrl & Hba & _)];
      [left; split; [exact Hb0 | split; [exact Hz | exact Ho0]] | right; split; [exact HinL | split; [exact Hba | exact Hrl]]]).
assert (HFP1 : fp_sub_x B (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st))
  (if buf =? 0 then [] else ablocks_fp [(buf - cf_head, WriterApp.w_cap st + cf_head)]) ly S [] ly S).
{ intros a Ha. destruct HOX as [(Hb0 & _) | (Hb0 & Hcap0 & _)].
  - rewrite Hb0 in Ha. destruct Ha as (r & [] & _).
  - left. rewrite (proj2 (Z.eqb_neq _ _) Hb0) in Ha. destruct Ha as (r & Hr & Hra'). exists r. split; [|exact Hra'].
    right. unfold prhWriter_fp. rewrite (proj2 (Z.eqb_neq _ _) Hcap0). exact Hr. }
assert (HRO' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) (ms_mem MSC))).
{ apply (put_arodata_kept B ARx PE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); [|exact HRO].
  pose proof (@cf_head_nonneg cp).
  apply sink_closed_cons; [cbn; lia|]. unfold prhWriter_fp.
  destruct HOX as [(_ & Hz & _) | (_ & Hcap0 & _ & _ & _ & _ & _ & _ & Hb1 & _)].
  - rewrite Hz. cbn. intros (r & [] & _).
  - rewrite (proj2 (Z.eqb_neq _ _) Hcap0). apply sink_closed_pos. constructor; [cbn; lia | constructor]. }
assert (Hbc : buf = 0 /\ WriterApp.w_cap st = 0 /\ OLD = [] \/ buf <> 0 /\ WriterApp.w_cap st <> 0)
  by (destruct HOX as [(Hb0 & Hz & Ho0 & _) | (Hb0 & Hcap0 & _)]; [left; auto | right; auto]).
put_hide_all.
(* the hull budget of the call: pe_hull at put's run position (the state is the entry's; at most 4 calls) *)
pose proof (@cf_head_nonneg cp) as Hchc.
assert (Hrq : 0 <= nc + cf_head < cf_malloc_max)
  by (split; [((clear - Hneed' Hn0 Hlen Hchc; lia) || slia_fb) | exact Hnmax]).
assert (HHULL : PresetHullBudget.hull_budget S
  (if buf =? 0 then [PresetReqAt.HMal (nc + cf_head)]
   else [PresetReqAt.HRe (WriterApp.w_cap st + cf_head) (nc + cf_head)])).
{ destruct (pe_hull B ARx PE rp_sm rp_x rp_os rp_i rp_H0 rp_hist S (WriterApp.w_cap st + cf_head) (nc + cf_head)
    HLEN HPOS Hrq) as (HHM & HHR).
  destruct (buf =? 0); [exact HHM | exact HHR]. }
(* ---- THE CALL: the cut before it leaves the plain run (SRr_ret); the call and everything after it are at
   wle' segs RZ_cf ---- *)
apply (SRr_ret SEGS). cbv beta.
eapply (SRr'_bind SEGS RZ); [ apply (put_realloc_call B ARx PE W E2 _ MSC (STK_put + d) (spZ regs + d)
    (prhWriter_cfp o buf (WriterApp.w_cap st))
    ly S Hp W mem md ly S Hp _ _ (- (112 + d)) (getr (ms_regs MSC) 1) ch1 buf (WriterApp.w_cap st) nc OLD Lam peak
    (WriterApp.w_cnt st) (WriterApp.w_fail st) ran most own HS eq_refl eq_refl HJ HPCsp Hal' ltac:(lia) Hbud Hgp' Htp' eq_refl
    Hraw Hra4' Hch' HRO' HTOP' HRAZc HFRM HROOM HMU HSEC H24 HHULL HU1 HU2 H10' H11' ltac:(lia) Hnmax HLED' HOLD HLIVE'
    HFP1) | ].
cbv beta; intros W2 c2 HW2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJin & HP2 & (HQ2 & HMN2)).
unfold SRr'.
(* the runners over R at wle' segs RZ_cf, for the runs after the call *)
pose (RUNIR := paj_run_x_invR (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
pose (RUNTOIR := paj_run_to_x_invR (SK := SK) (PL := PL_prog_B) (PI := PA) B (@prh_pst prh_img_B) ARx LAWS P PLAW
  (wle' SEGS RZ) (wle'_refl SEGS RZ) (wle'_trans SEGS RZ)).
(* P crosses the call by the text's memnorm keep (fpostm's fQmn conjunct) *)
pose proof (PCALL _ _ HMN2 HPM) as HPM2; clear HPM HMN2; rename HPM2 into HPM.
(* ---- back at index 57: the frame and the struct kept (both above the callee's window), the caller-saved registers
   fresh atoms from 66 (the stretch used 64 / 65) ---- *)
rewrite Q1.
try rewrite wvb_collapse in HJ2.
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
jafter_call_keep_pi HS 66%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 3]%nat HSX.
lazymatch type of HSX with ?T -> _ => assert (HRKX : T) by
  (constructor; [|constructor; [|apply Forall_nil]]; cbn [ms_mem restrict];
   [ eapply (region_kept_stack_sub_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ) E2 STK_fuzz_realloc _ _
       ly S Hp W
       (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 2%nat (-112) 0 (-112) 0 _ (spZ regs) (STK_put + d) (spZ regs + d) _
       ly S Hp W mem md [] _ HJin HJ2 Usp2); lia
   | eapply (region_kept_stack_sub_xR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (wle' SEGS RZ) E2 STK_fuzz_realloc _ _
       ly S Hp W
       (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 10%nat 0 32 0 32 _ o (STK_put + d) (spZ regs + d) _
       ly S Hp W mem md [] _ HJin HJ2 Uo2); lia ]) end.
specialize (HSX HRKX); clear HRKX; rewrite <- restrict_mkst_fx in HSX.
remember (havoc E2 66 (map (getr regs2) CLOB)) as E3 eqn:HE3 in HSX.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall kk, (kk < 66)%nat -> ew E3 kk = ew E2 kk) by (intros kk Hk; rewrite HE3; apply ew_havoc_old; exact Hk).
assert (SHOK3 : sh_ok SEGS put_Bx put_SH E3 (mrestrict (w_H W2) mem2))
  by (apply (put_shok B ARx PE E3 ly2 S2 Hp2 W2 mem2 md2 o HAR2);
      [ rewrite OLD3, OLD2 by lia; exact E32
      | rewrite OLD3, OLD2 by lia; exact E10
      | rewrite ?Eslo2; lia | rewrite ?Eshi2; lia | lia | lia ]).
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
assert (Uo3 : bv_unsigned (ew E3 10) = o) by (rewrite OLD3 by lia; exact Uo2).
clear HS SHOK HJ HEI. rename HSX into HS. rename SHOK3 into SHOK. rename HJ2 into HJ.
rename HEI3 into HEI.
destruct (put_realloc_cases B ARx PE rp_sm rp_x rp_os rp_H0 rp_i rp_hist buf (WriterApp.w_cap st) nc OLD Lam peak _ _ ran
  most own ly S Hp W ly2 S2 Hp2 W2 regs2 mem2 md2 HAR2 Hbc ltac:(lia) HPOS HRUN HCONS1 HQ2) as (HROOM2 & [HNULL | HSUCC]).
all: psrr_branch_tok RUNIR BRR HS SHOK put_Bspan.
all: match goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc0 end.
all: assert (E370 : ew E3 70 = getr regs2 10) by (rewrite HE3; reflexivity).
all: rewrite branch_eq_U, U_SOff, (U_lit E3 0 ltac:(lia)), E370, Z.add_0_r, zcanon_id in Hc0
  by (unfold M64; apply u64_range).
all: try solve [ destruct HNULL as (U0 & _); rewrite U0 in Hc0; discriminate Hc0
              | destruct HSUCC as (res & Ur & _ & Hr4 & _); rewrite Ur in Hc0; apply Z.eqb_eq in Hc0;
                pose proof (@cf_head_nonneg cp); lia ].
(* ---- NULL: indices 116 .. 120 (the store check of o + 24, failed = 1), the epilogue, the return ---- *)
1: { destruct HNULL as (U0 & PHp & Ebl & Hbkeep & Hcf & HL2 & HPN).
  put_hide_all.
  paj_run_tok_x_inv RUNIR HS HJ SHOK HPM put_Bspan.
  all: try solve [put_awr].
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => rename X into MSN end.
  try rewrite wvb_collapse in HJ.
  apply (SRr_SRrG SEGS (wle' SEGS RZ) (wle_wle' SEGS RZ)).
  apply (RET W2 E3 _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros matR.
  assert (HAG : env_agree 32 (Ereg regs (put_extra buf len (WriterApp.w_cap st))) E3).
  { split; [intros kk Hk; rewrite OLD3, OLD2 by lia; apply EL; unfold A_TEXT; lia | rewrite HE3, HE2; reflexivity]. }
  assert (HP : aregs_preserved regs (ms_regs MSN)).
  { pose proof HS as HS'. unfold st_ok_pi in HS'.
    eapply (aregs_preserved_of_st_ok SEGS); [exact HS' | exact HAG | vm_compute; reflexivity]. }
  assert (Hra1 : getr (ms_regs MSN) 1 = getr regs 1).
  { rewrite (st_ok_pi_restrict_reg (w_H W2) E3 _ MSN 1%bv HS).
    match goal with |- sv_denot E3 ?e = _ => let v := eval vm_compute in e in change e with v end.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite OLD3, OLD2 by lia.
    rewrite EL by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ 1 1%bv eq_refl). }
  (* the run after the call writes the frame and struct windows only *)
  assert (KEEPN : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
    aview SEGS (w_H W2) (ms_mem MSN) a = aview SEGS (w_H W2) mem2 a).
  { intros a Ha Hout Hos. apply aview_eq_of.
    match goal with HF' : frame_of E3 _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem MSN)) |- _ =>
      rewrite (HF' (Z_to_bv 64 a)); [reflexivity|] end.
    rewrite unsigned_lit_small by lia. intros (r & Hr & Hra').
    match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
    repeat (destruct Hr as [<- | Hr];
      [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp3, ?Uo3 in Hra'; lia | ]).
    destruct Hr. }
  pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & GIN & _).
  (* the struct's fields at the end *)
  put_region_auto HS 1%nat HRS.
  assert (D0 : forall (kx : nat) (wx : word), ew E3 kx = wx -> sv_denot E3 (SOff kx 0) = wx)
    by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
  assert (W0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) o 8 buf).
  { pose proof (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 0 8%N (SOff 33 0) buf HRS Uo3 ltac:(cbn; tauto)
      ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E33) ltac:(cbn; lia) ltac:(cbn; lia)) as Hv.
    rewrite Z.add_0_r in Hv. exact Hv. }
  assert (W8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 8) 8 len)
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo3 ltac:(cbn; tauto)
      ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E34) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W16 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 16) 8 (WriterApp.w_cap st))
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 16 8%N (SOff 35 0) (WriterApp.w_cap st) HRS Uo3
      ltac:(cbn; tauto) ltac:(apply D0; rewrite OLD3, OLD2 by lia; exact E35) ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (W24 : val_mem SEGS (mrestrict (w_H W2) (ms_mem MSN)) (o + 24) 4 1)
    by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 24 4%N (SLit 1) 1 HRS Uo3 ltac:(cbn; tauto)
      eq_refl ltac:(cbn; lia) ltac:(cbn; lia)).
  assert (KLOWN : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem MSN) a = aview SEGS (w_H W2) mem2 a)
    by (intros a Ha; apply KEEPN; lia).
  (* the post: failed, text and capacity kept, the ledger counts the call *)
  exists ly2, S2, Hp2, (ms_regs MSN), (ms_mem MSN). eexists. exists (0 + k1).
  split.
  { rewrite ?wvb_collapse, Hra1. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
  split.
  { pose proof (ajournal_x_materializeR (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS
      (@pa_segs_low rc B_prog_listing PA) (wle' SEGS RZ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ matR HJ) as HJ1.
    rewrite ?wvb_collapse in HJ1. exact HJ1. }
  split.
  { intros a Ha Hnf.
    assert (Hos : ~ (o <= a < o + 32)) by (intros Ho; apply Hnf; exists (o, o + 32); split; [left; reflexivity | cbn; lia]).
    rewrite KEEPN by lia. rewrite GIN by lia. apply KEEPC; lia. }
  split; [exact HP|].
  unfold putb_postP. split; [|exact HPM].
  unfold putb_post, tputP_Q. split; [exact HROOM2|].
  (* the position: grows (cap < need), fuzz_realloc returned NULL, the stored failed is 1: kept at rp_i *)
  split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; rewrite (proj2 (Z.eqb_eq _ _) Hf0) in Hg;
    cbn [andb] in Hg; apply Z.ltb_ge in Hg; lia|].
  split; [intros _ f' Hf'; split; [intros Ef'; exfalso; exact (put_val_mem_1 _ _ _ Hf' W24 Ef') |
    intros _; exact HPN]|].
  destruct (put_null_model st bs Hf0 Hneedlt) as (EPUT & EK).
  assert (HOUTN : forall fl', prhWriter_out (PA := PA) W2 (ms_mem MSN) Lam o buf
    (WriterApp.mkW 1 (WriterApp.w_text st) (WriterApp.w_cap st) ((WriterApp.w_cnt st + 1) mod 2 ^ 64) fl'
      (WriterApp.w_calls st ++ [WriterSpec.newcap (WriterApp.w_cap st) (prhWriter_need st bs)]))).
  { intros fl'. unfold prhWriter_out. cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap].
    split; [exact Ho8|]. split; [exact Hbr|]. split; [exact Hcr|]. split; [exact W0|]. split; [exact W8|].
    split; [exact W16|]. split; [exact W24|]. split; [right; reflexivity|]. split; [exact Hbok|].
    destruct HOX as [(Hb0 & Hz & Ho0 & Ht0) | (Hb0 & Hcap0 & Hg & HinL & Hlt & (rest & Erest) & Hrl & Hba & _ & Hb2 & _)].
    - left. split; [exact Hz|]. split; [exact Hb0 | exact Ht0].
    - right. split; [exact Hg|]. split; [exact HinL|]. split; [lia|]. split.
      + exists rest. rewrite <- Erest. split; [exact Hrl|].
        apply (put_bytes_keep W2 mem2 (ms_mem MSN) buf OLD (Hbkeep Hb0)). intros j Hj. apply KEEPN; lia.
      + intros Hf; discriminate Hf. }
  (* the outcome: [false], the allocation set to fail (cnt = fail; DEAD-PUT: no refusal, PutB_Base.put_realloc_cases) *)
  exists [false]. split.
  2: { rewrite EK. intros i Hi _. assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb). subst i.
       cbn [Z.of_nat]. rewrite Z.add_0_r. exact Hcf. }
  unfold prhWriter_ret_ok. exists ran, buf, Lam, peak. cbv zeta. rewrite EPUT, EK.
  rewrite (proj2 (Z.eqb_eq _ _) Hcf). cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
  (* prh_oks at k = 1, ns := prhWriter_reqs [false] st [bs], most := most (the ledger's g_most), ran := ran,
     ran' := ran: the one call is the chosen failure, not a refusal *)
  split.
  { split; [intros i Hi Hci; assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb); subst i; reflexivity|].
    split; [left; reflexivity|].
    intros i Hi Hr _. exfalso. assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb). subst i.
    unfold prh_refused in Hr. cbn [nth negb andb Z.of_nat] in Hr. rewrite Z.add_0_r, Hcf, Z.eqb_refl in Hr.
    cbn [negb] in Hr. discriminate Hr. }
  split; [exact (HOUTN _)|].
  split.
  { change SIZE_MAXZ with (2 ^ 64 - 1) in HL2.
    exact (put_ledger_kept0 B ARx PE ly2 S2 Hp2 W2 mem2 (ms_mem MSN) md2 Lam peak _ _ ran most own HAR2 KLOWN HL2). }
  left. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  rewrite Ebl. apply Permutation_refl. }
(* ---- SUCCESS: indices 58 .. 64 (the store checks of o and o + 16, buf := res, cap := newcap, s6 := o + 8 from the
   spill), the seat at the join and the shared tail ---- *)
destruct HSUCC as (res & Ures & Hcf & Hr4 & Hr16 & Hrc & l1 & l2 & b1 & b2 & Harm2 & Pb & (rest' & HbrN & Hlr) &
  Hra2 & Hhv2 & Hnin & HL2 & HPS).
pose proof (@cf_head_nonneg cp) as Hch0.
assert (Hnc0 : 0 < nc) by ((clear - Hneed' Hn0 Hlen; lia) || slia_fb).
put_hide_all.
assert (HinN : In (res - cf_head, nc + cf_head) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Pb)); left; reflexivity).
paj_run_to_tok_x_inv RUNTOIR HS HJ SHOK HPM put_Bspan (PK 65).
all: try solve [put_awr].
lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?X) => rename X into M68S end.
try rewrite wvb_collapse in HJ.
pmkst HS.
assert (KEEP68 : forall a, 0 <= a < 2 ^ 64 -> (a < spZ regs - 112 \/ spZ regs <= a) -> ~ (o <= a < o + 32) ->
  aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hout Hos. apply aview_eq_of.
  match goal with HF' : frame_of E3 _ (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem M68S)) |- _ =>
    rewrite (HF' (Z_to_bv 64 a)); [reflexivity|] end.
  rewrite unsigned_lit_small by ((clear - Ha; lia) || slia_fb). intros (r & Hr & Hra').
  match type of Hr with In _ ?rs => let v := eval vm_compute in rs in change rs with v in Hr end.
  repeat (destruct Hr as [<- | Hr];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hra'; rewrite ?Usp3, ?Uo3 in Hra';
     ((clear - Hra' Hout Hos; lia) || slia_fb) | ]).
  destruct Hr. }
assert (KLOW68 : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply KEEP68; ((clear - Ha HCSP C1 Hol; lia) || slia_fb)).
pose proof HJin as (_ & _ & _ & _ & _ & _ & _ & _ & GIN & _).
(* the registers at the join *)
assert (EG3 : forall (kk : nat) (r : bv 5), (kk < 32)%nat -> Z.of_nat kk = bv_unsigned r -> ew E3 kk = getr regs r)
  by (intros kk r Hk Hr; rewrite OLD3, OLD2 by ((clear - Hk; lia) || slia_fb); apply EG; [exact Hk | exact Hr]).
assert (E3_10 : ew E3 10 = Z_to_bv 64 o) by (rewrite OLD3, OLD2 by ((clear - Hch0; lia) || slia_fb); exact E10).
assert (E3_32 : ew E3 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLD3, OLD2 by ((clear - Hch0; lia) || slia_fb); exact E32).
assert (GR : forall rr : bv 5, getr (ms_regs M68S) rr = sv_denot E3 (sr_get (ss_regs _) rr))
  by (intros rr; exact (st_ok_pi_restrict_reg (w_H W2) E3 _ _ rr HS)).
assert (D0 : forall (kx : nat) (wx : word), ew E3 kx = wx -> sv_denot E3 (SOff kx 0) = wx)
  by (intros kx wx Hk; cbn [sv_denot]; rewrite Hk, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (R8 : getr (ms_regs M68S) 8 = Z_to_bv 64 o) by (putb_greg GR; apply D0; exact E3_10).
assert (R9 : getr (ms_regs M68S) 9 = Z_to_bv 64 n)
  by (putb_greg GR; apply D0; rewrite (EG3 12%nat 12%bv) by (reflexivity || ((clear - Hch0; lia) || slia_fb)); exact H12).
assert (R18 : getr (ms_regs M68S) 18 = Z_to_bv 64 s)
  by (putb_greg GR; apply D0; rewrite (EG3 11%nat 11%bv) by (reflexivity || ((clear - Hch0; lia) || slia_fb)); exact H11).
assert (R23 : getr (ms_regs M68S) 23 = Z_to_bv 64 SHADOW_OFF) by (putb_greg GR; apply D0; exact E3_32).
assert (R19 : getr (ms_regs M68S) 19 = Z_to_bv 64 (o / 8)) by (putb_greg GR; exact (DS3 E3 E3_10)).
assert (R22 : getr (ms_regs M68S) 22 = Z_to_bv 64 (o + 8)) by (putb_greg GR; exact (DS6 E3 E3_10)).
assert (R24 : getr (ms_regs M68S) 24 = Z_to_bv 64 (SHADOW_OFF + (o + 8) / 8)) by (putb_greg GR; exact (DS8 E3 E3_10 E3_32)).
assert (R3 : getr (ms_regs M68S) 3 = getr regs 3)
  by (putb_greg GR; apply D0; apply EG3; [((clear - Hch0; lia) || slia_fb) | reflexivity]).
assert (R4 : getr (ms_regs M68S) 4 = getr regs 4)
  by (putb_greg GR; apply D0; apply EG3; [((clear - Hch0; lia) || slia_fb) | reflexivity]).
assert (Hsp1 : spZ (ms_regs M68S) = spZ regs - 112)
  by (unfold spZ at 1; putb_greg GR; cbn [sv_denot]; rewrite Usp3; apply unsigned_lit_small;
      ((clear - HCSP C1 HSPD Hd0; lia) || slia_fb)).
(* the frame: the thirteen saved registers *)
put_region_auto HS 0%nat HRF.
assert (Hsv : forall j, (j < 13)%nat -> val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (spZ regs - 8 - 8 * Z.of_nat j) 8
   (bv_unsigned (nth j (put_saved regs) (Z_to_bv 64 0)))).
{ intros j Hj.
  lazymatch type of HRF with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
    assert (FR : forall (k : nat) (r : bv 5) od, (k < 32)%nat -> Z.of_nat k = bv_unsigned r ->
      In (YP09.mkChunk od (CVal 8 (SOff k 0))) cs ->
      val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (spZ regs + od) 8 (bv_unsigned (getr regs r)))
    by (intros k r od Hk Hr Hin;
        eapply (field_of_region SEGS E3 _ 2 (spZ regs) cs _ _ _ _ od 8%N (SOff k 0) (bv_unsigned (getr regs r)) HRF Usp3 Hin);
        [ apply D0; rewrite (EG3 k r Hk Hr); symmetry; apply Z_to_bv_bv_unsigned
        | pose proof (u64_range (getr regs r)) as Hu; cbn; ((clear - Hu; lia) || slia_fb)
        | cbn; ((clear - Hch0; lia) || slia_fb) ])
  end.
  replace (spZ regs - 8 - 8 * Z.of_nat j) with (spZ regs + (-8 - 8 * Z.of_nat j)) by ((clear - Hj; lia) || slia_fb).
  do 13 (destruct j as [|j];
    [ cbn [nth put_saved];
      match goal with |- val_mem _ _ (spZ regs + ?od) _ (bv_unsigned (getr regs ?r)) =>
        let od' := eval vm_compute in od in let k := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
        change od with od'; apply (FR k r od'); [((clear - Hch0; lia) || slia_fb) | reflexivity | cbn; tauto] end
    | ]).
  ((clear - Hj; lia) || slia_fb). }
(* the struct: res, len, newcap, failed = 0 *)
assert (E370' : ew E3 70 = Z_to_bv 64 res) by (rewrite E370, <- Ures; symmetry; apply Z_to_bv_bv_unsigned).
assert (E365 : ew E3 65 = Z_to_bv 64 nc) by (rewrite OLD3 by ((clear - Hch0; lia) || slia_fb); rewrite E265; exact L22).
put_region_auto HS 1%nat HRS.
assert (W0 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) o 8 res).
{ pose proof (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 0 8%N (SOff 70 0) res HRS Uo3 ltac:(cbn; tauto)
    (D0 _ _ E370') ltac:(cbn; ((clear - Hr4 Hch0 Hrc Hnc0 HCSP HSPD Hd0; lia) || slia_fb))
    ltac:(cbn; ((clear - Hch0; lia) || slia_fb))) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
assert (W8 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 8) 8 len)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 8 8%N (SOff 34 0) len HRS Uo3 ltac:(cbn; tauto)
    ltac:(apply D0; rewrite OLD3, OLD2 by ((clear - Hch0; lia) || slia_fb); exact E34)
    ltac:(cbn; ((clear - Hlen; lia) || slia_fb)) ltac:(cbn; ((clear - Hch0; lia) || slia_fb))).
assert (Hnc64 : 0 <= nc < 2 ^ (8 * Z.of_N 8))
  by (change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); ((clear - H28' Hnc0; lia) || slia_fb)).
assert (W16 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 16) 8 nc)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 16 8%N (SOff 65 0) nc HRS Uo3 ltac:(cbn; tauto)
    (D0 _ _ E365) Hnc64 ltac:(cbn; ((clear - Hch0; lia) || slia_fb))).
assert (W24 : val_mem SEGS (mrestrict (w_H W2) (ms_mem M68S)) (o + 24) 4 0)
  by exact (field_of_region SEGS E3 _ 10 o _ 0 32 0 32 24 4%N (SLit 0) 0 HRS Uo3 ltac:(cbn; tauto)
    eq_refl ltac:(cbn; ((clear - Hch0; lia) || slia_fb)) ltac:(cbn; ((clear - Hch0; lia) || slia_fb))).
(* the caller window outside the struct, and the struct in the footprint *)
assert (HWK : forall a, spZ regs <= a < spZ regs + d -> ~ inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a ->
  aview SEGS (w_H W2) (ms_mem M68S) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hnf.
  assert (Hos : ~ (o <= a < o + 32))
    by (intros Ho; apply Hnf; exists (o, o + 32); split; [left; reflexivity | cbn; ((clear - Ho; lia) || slia_fb)]).
  rewrite KEEP68 by ((clear - Ha Hos HSPD HCSP C1; lia) || slia_fb).
  rewrite GIN by ((clear - Ha Hos HSPD HCSP C1 Hd0; lia) || slia_fb).
  apply KEEPC; ((clear - Ha Hos HSPD HCSP C1; lia) || slia_fb). }
assert (HFPo : forall a, o <= a < o + 32 -> inFP (prhWriter_cfp o buf (WriterApp.w_cap st)) a)
  by (intros a Ha; exists (o, o + 32); split; [left; reflexivity | cbn; ((clear - Ha; lia) || slia_fb)]).
(* the new block: not an entry block; its range and shadow *)
assert (Harm' : WriterApp.w_cap st = 0 /\ buf = 0 /\ l1 = [] /\ l2 = Lam \/
  WriterApp.w_cap st <> 0 /\ Lam = l1 ++ (buf, WriterApp.w_cap st) :: l2).
{ unfold put_hide in Harm2, HOX.
  destruct Harm2 as [(Hzz & Ea1 & Ea2 & _ & _) | (Hzz & ELm & _)]; [left | right; split; [exact Hzz | exact ELm]].
  split; [exact Hzz|]. split; [|split; [exact Ea1 | exact Ea2]].
  destruct HOX as [(Hbz & _) | (_ & Hcz & _)]; [exact Hbz | contradiction]. }
assert (HnotN : ~ In (res - cf_head, nc + cf_head) (ablocks B ly S)).
{ unfold put_hide in Harm2.
  assert (Hsnd : 0 < snd (res - cf_head, nc + cf_head))
    by (change (snd (res - cf_head, nc + cf_head)) with (nc + cf_head); ((clear - Hnc0 Hch0; lia) || slia_fb)).
  apply (put_newblk B ARx PE ly2 S2 Hp2 W2 mem2 md2 (ablocks B ly S) b1 b2 (res - cf_head, nc + cf_head)
    (buf - cf_head, WriterApp.w_cap st + cf_head) HAR2 Hsnd Pb).
  destruct Harm2 as [(Hzz & Ea1 & Ea2 & Ea3 & Ea4) | (Hzz & ELm & Eb)]; [left; split; [exact (eq_sym Ea4) | exact Ea3] |].
  right. split; [exact Eb|]. intros Eq'. injection Eq' as Eq1 Eq2. ((clear - Eq2 Hc Hneed'; lia) || slia_fb). }
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 HinN) as (_ & _ & _ & HappN & _).
assert (Hreqn : req_size (nc + cf_head) = nc + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (nc + cf_head) 0) as [Hz | Hz]; cbv iota;
      ((clear - Hz Hnc0 Hch0; lia) || slia_fb)).
rewrite Hreqn in HappN.
(* the source after the call *)
destruct (put_src_after B ARx PE (wle' SEGS RZ) ly S Hp W mem md (ms_mem MSC) _ ly2 S2 Hp2 W2 mem2 md2 k1 _ Lam peak _ _ ran
  most own buf
  (WriterApp.w_cap st) s bs n res nc l1 l2 _ _ _ _ _ _ HAR HLED HSRC Hn (conj Hkept Hdisj0) KLOWC HJin Harm' HinN HnotN HL2 Hnc0)
  as (SBa2 & Svis2 & Sra2 & Shull2 & Sdisj2).
put_hide_all.
(* the destination [res + len, res + len + n]: in the new block, addressable *)
assert (Hamr_d : amem_range (res + len) (n + 1)).
{ apply (put_app_amem (res - cf_head) (nc + cf_head));
    [exact HappN | ((clear - Hch0 Hlen; lia) || slia_fb) | ((clear - Hn0; lia) || slia_fb)
    | ((clear - Hch0 Hlen Hn0 Hneed'; lia) || slia_fb)]. }
assert (Hawr_d : forall a, res + len <= a <= res + len + n ->
  awr_byte (STK_put + d) (spZ regs + d) (prhWriter_cfp o buf (WriterApp.w_cap st)) (ablocks B ly S) (ablocks B ly2 S2)
    ly2 [] a).
{ intros a Ha. right; right; left. exists (res - cf_head), (nc + cf_head).
  split; [exact HinN|]. split; [exact HnotN | rewrite Hreqn; ((clear - Ha Hch0 Hlen Hn0 Hneed'; lia) || slia_fb)]. }
assert (Hra_d : range_addressable (aview SEGS (w_H W2) (ms_mem M68S)) SHADOW_OFF (res + len) (n + 1)).
{ eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)).
  { intros x Hx. pose proof (put_shadow_low x ltac:((clear - Hx Hr4 Hch0 Hlen Hn0 Hrc Hneed' C1; lia) || slia_fb)) as Hsl.
    rewrite KLOW68 by ((clear - Hsl C1; lia) || slia_fb). reflexivity. }
  apply (range_addressable_sub _ _ res nc);
    [exact Hra2 | ((clear - Hlen; lia) || slia_fb) | ((clear - Hlen Hn0 Hneed'; lia) || slia_fb)]. }
assert (Hhull_d : 0 < n -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem M68S)) (res + len) n).
{ intros Hn1 s0 Hs0.
  pose proof (put_hull_low (res + len) n s0 ltac:((clear - Hr4 Hch0 Hlen; lia) || slia_fb) Hn1
    ltac:((clear - Hr4 Hch0 Hlen Hn0 Hrc Hneed' C1; lia) || slia_fb) Hs0) as Hhl.
  rewrite KLOW68 by ((clear - Hhl C1; lia) || slia_fb).
  exact (put_hull_sub _ res nc (res + len) n (Hhv2 Hnc0) ltac:((clear - Hlen; lia) || slia_fb)
    ltac:((clear - Hlen Hn0 Hneed'; lia) || slia_fb) Hn1 s0 Hs0). }
(* the source at the join *)
assert (Hsc : s + n <= YM05.alloc_ceiling) by ((clear - Sceil; lia) || slia_fb).
assert (Hsvis : forall a, s <= a < s + n -> aview SEGS (w_H W2) (ms_mem M68S) a <> None)
  by (intros a Ha; rewrite KLOW68 by ((clear - Ha S4096 Hsc; lia) || slia_fb); exact (Svis2 a Ha)).
assert (Hdisj : res + len + n <= s \/ s + n <= res + len)
  by (unfold put_hide in Sdisj2; ((clear - Sdisj2 Hneed' Hlen Hn0; lia) || slia_fb)).
put_hide_all.
assert (Hra_s : range_addressable (aview SEGS (w_H W2) (ms_mem M68S)) SHADOW_OFF s n).
{ eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)); [|exact Sra2].
  intros x Hx. pose proof (put_shadow_low x ltac:((clear - Hx S4096 Hsc C1; lia) || slia_fb)) as Hsl.
  rewrite KLOW68 by ((clear - Hsl C1; lia) || slia_fb). reflexivity. }
assert (Hhull_s : 0 < n -> shadow_hull_vis (aview SEGS (w_H W2) (ms_mem M68S)) s n).
{ intros Hn1 s0 Hs0.
  pose proof (put_hull_low s n s0 ltac:((clear - S4096; lia) || slia_fb) Hn1
    ltac:((clear - Hsc C1; lia) || slia_fb) Hs0) as Hhl.
  rewrite KLOW68 by ((clear - Hhl C1; lia) || slia_fb). exact (Shull2 Hn1 s0 Hs0). }
apply (putb_tail B ARx PE P PLAW PCALL ly S Hp W regs mem md d o s n res len nc (prhWriter_cfp o buf (WriterApp.w_cap st))
  ly2 S2 Hp2 W2 (ms_regs M68S) (ms_mem M68S) _ _ _ HJ HPM Hra Hgp Htp Hal16 Hd0 Hd16 Hol Hoh Ho8 Hsp1 R8 R9 R18 R23
  R19 R22 R24 R3 R4 Hsv W0 W8 W16 W24
  ltac:((clear - H28' Hnc0; lia) || slia_fb) ltac:((clear - Hlen; lia) || slia_fb) HWK HFPo
  ltac:((clear - HWMAX Hlen Hn0; lia) || slia_fb) ltac:((clear - Hr4 Hch0; lia) || slia_fb)
  ltac:((clear - Hrc Hneed'; lia) || slia_fb) Hamr_d Hawr_d Hra_d
  Hhull_d S4096 Hsc Samr Hsvis Hdisj Hra_s Hhull_s).
(* the post: the buffer grew to the new block, the text by bs; the ledger is fuzz_realloc's over the new bytes *)
intros regs' mem' md' k' HJ' HPM' Hkeep' Hcopy' Hnul' V0' V8' V16' V24'.
unfold putb_postP. split; [|exact HPM'].
unfold putb_post, tputP_Q. split; [exact HROOM2|].
destruct (put_grow_model st bs Hf0 Hneedlt Hcf) as (EPUT & EK).
(* the position: grows, fuzz_realloc granted, the stored failed is 0: one event (the text's entry premise, HEV, is
   this call's, put_realloc_cases' HPS), the position advanced by one *)
split; [intros Hg; exfalso; unfold prhWriter_grows in Hg; rewrite (proj2 (Z.eqb_eq _ _) Hf0) in Hg;
  cbn [andb] in Hg; apply Z.ltb_ge in Hg; ((clear - Hg Hneedlt; lia) || slia_fb)|].
split.
{ intros Hg f' Hf'. split.
  - intros _. exact HPS.
  - (* f' = 1 against the stored 0 (one byte decides) *)
    intros Ef'. exfalso. exact (put_val_mem_0 _ _ _ Hf' V24' Ef'). }
(* the outcome: [true], one granted grow *)
assert (HGRT : prh_granted [true] (WriterApp.w_cnt st) (WriterApp.w_fail st) (prhWriter_k [true] st [bs])).
{ rewrite EK. intros i Hi Hn0'. assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb). subst i. discriminate Hn0'. }
(* no refusal, so the refusal term of the grow arm's peak is 0 (PRH_Base.prh_refused_peak_granted) *)
assert (ERPK : prhWriter_rpeak [true] Lam st [bs] = 0)
  by (unfold prhWriter_rpeak; exact (prh_refused_peak_granted _ _ _ _ _ HGRT)).
exists [true]. split; [|exact HGRT].
unfold prhWriter_ret_ok. exists ran, res, ((res, nc) :: l1 ++ l2), (Z.max peak (Ledger.lsum (l1 ++ l2) + nc)).
cbv zeta. rewrite EPUT, EK, Enc. cbn [WriterApp.w_cnt WriterApp.w_fail WriterApp.w_cap].
(* prh_oks at k = 1, ns := prhWriter_reqs [true] st [bs], most := most (the ledger's g_most), ran := ran,
   ran' := ran: the one call granted *)
split.
{ split; [intros i Hi Hci; assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb); subst i; cbn in Hci;
          ((clear - Hci Hcf; lia) || slia_fb)|].
  split; [left; reflexivity|].
  intros i Hi Hr _. exfalso. assert (i = 0%nat) by ((clear - Hi; lia) || slia_fb). subst i.
  unfold prh_refused in Hr. cbn [nth negb andb] in Hr. discriminate Hr. }
assert (HNB : exists r0 rest'', Z.of_nat (length (WriterApp.w_text st ++ r0 :: rest'')) = nc /\
  bytes_at (PA := PA) W2 mem2 res (WriterApp.w_text st ++ r0 :: rest'')).
{ unfold put_hide in HOX.
  destruct HOX as [(Hbz & Hzz & Hoz & Htz) | (Hbz & Hcapz & Hgz & HinLz & Hltz & (restz & Erz) & Hrlz & Hbaz & _)].
  - rewrite Hoz, firstn_nil in HbrN. cbn [app] in HbrN. rewrite Hzz in Hlr.
    destruct rest' as [|r0 rest'']; [cbn [length] in Hlr; ((clear - Hlr Hnc0; lia) || slia_fb)|].
    exists r0, rest''. rewrite Htz. cbn [app].
    split; [cbn [length] in Hlr |- *; ((clear - Hlr Hnc0; lia) || slia_fb) | exact HbrN].
  - rewrite Z.min_l in HbrN, Hlr by ((clear - Hge'; lia) || slia_fb).
    rewrite firstn_all2 in HbrN by ((clear - Hrlz; lia) || slia_fb). subst OLD. rewrite <- app_assoc in HbrN.
    cbn [app] in HbrN.
    exists 0, (restz ++ rest'). split; [|exact HbrN].
    rewrite length_app in Hrlz |- *. cbn [length] in Hrlz |- *. rewrite length_app.
    ((clear - Hrlz Hlr Hge'; lia) || slia_fb). }
destruct HNB as (r0 & rest'' & Hlen'' & Hba'').
assert (Hba68 : bytes_at (PA := PA) W2 (ms_mem M68S) res (WriterApp.w_text st ++ r0 :: rest''))
  by (apply (put_bytes_keep W2 mem2 (ms_mem M68S) res _ Hba''); intros j Hj; apply KLOW68;
      ((clear - Hj Hlen'' Hr4 Hch0 Hrc; lia) || slia_fb)).
split.
{ apply (put_out_put W2 (ms_mem M68S) mem' ((res, nc) :: l1 ++ l2) o res nc (WriterApp.w_text st) bs r0 rest'' s);
    try assumption.
  - ((clear - Hr4 Hch0; lia) || slia_fb).
  - exact (put_app_band res nc cf_head HappN Hch0).
  - left; reflexivity.
  - eapply (range_addressable_agree (aview SEGS (w_H W2) mem2)); [|exact Hra2].
    intros x Hx. pose proof (put_shadow_low x ltac:((clear - Hx Hr4 Hch0 Hrc C1; lia) || slia_fb)) as Hsl.
    rewrite KLOW68 by ((clear - Hsl C1; lia) || slia_fb). reflexivity.
  - intros s0 Hs0.
    pose proof (put_hull_low res nc s0 ltac:((clear - Hr4 Hch0; lia) || slia_fb) Hnc0
      ltac:((clear - Hrc C1; lia) || slia_fb) Hs0) as Hhl.
    rewrite KLOW68 by ((clear - Hhl C1; lia) || slia_fb). exact (Hhv2 Hnc0 s0 Hs0).
  - apply (put_bytes_keep W2 mem2 (ms_mem M68S) s bs SBa2). intros j Hj. apply KLOW68.
    ((clear - Hj Hn S4096 Hsc; lia) || slia_fb).
  - ((clear - Hn Hneed' Hlen_def; lia) || slia_fb).
  - rewrite <- Hlen_def, Hn. exact Hkeep'.
  - rewrite <- Hlen_def, Hn. exact Hcopy'.
  - rewrite <- Hlen_def, Hn. exact Hnul'.
  - rewrite <- Hlen_def, Hn. exact V8'. }
split.
{ apply (put_ledger_copy B ARx PE ly2 S2 Hp2 W2 mem2 mem' md2 ((res, nc) :: l1 ++ l2) _ _ _ ran most own res nc HAR2 HL2
    (or_introl eq_refl)).
  intros a Ha Hab. rewrite Hkeep' by ((clear - Ha Hab Hneed' Hlen Hn0; lia) || slia_fb). apply KLOW68. exact Ha. }
right. right. split; [((clear - Hc Hneed'; lia) || slia_fb)|].
exists l1, l2, b1, b2. split; [exact Harm2|]. split; [reflexivity|]. split; [|exact Pb].
(* peak' = max (max peak (lsum (l1 ++ l2) + nc)) (the refusal term, 0), and 0 <= peak by the entry ledger *)
rewrite ERPK. pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HPKZ & _).
((clear - HPKZ; lia) || slia_fb).
Qed.

End rp.
End h.
End W.
