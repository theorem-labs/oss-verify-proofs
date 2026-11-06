(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: segment S29 (REJ) of the walk of verbs_receive on the ASan build of
   plugin-hostd/fuzz_command: the refusal stubs that call sup_resp(code) (0x8da28, 0x8dacc, 0x8dc9c, 0x8dca0, 0x8dd34)
   and the stubs that move a handler's text into a join's register (0x8dc34, 0x8dc54, 0x8dc94, 0x8dca4, 0x8dd3c).
   Statement: vr_s29_stmt (lib/A/Prog/verbs_receive_iface.v). A refusal stub runs `li a0,-902; jal sup_resp` (0x8dca0:
   the jal alone, a0 = pin_set_words' code); sup_resp's contract (tsup_resp_spec, called with PaCall's cl_callS) gives
   a fresh block with the text; the stub at the return address moves a0 into the join's register. All names of this
   file carry the prefix v29_. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route verbs_receive_pre.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c arg_i_c socket_send_c reply_c sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import sup_resp_c verbs_receive_c verbs_receive_iface verbs_receive_live verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------
   Plain helpers *)
Lemma v29_atoks_atA_agree : forall (rd rd' : reader) tok ptrs tks cb ncb,
atoks_atA rd tok ptrs tks cb ncb ->
(forall k, 0 <= k < 8 * Z.of_nat (length ptrs) -> rd' (tok + k) = rd (tok + k)) ->
(forall k, 0 <= k < ncb -> rd' (cb + k) = rd (cb + k)) ->
atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb (Hal & Hlen & Hp & Ht) HT HC.
split; [exact Hal|]. split; [exact Hlen|].
split.
- intros i p Hi. assert (Hib : (i < length ptrs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  apply (aval_mem_agree rd rd' _ 8 _ (Hp i p Hi)). intros kk Hkk.
  replace (tok + 8 * Z.of_nat i + kk) with (tok + (8 * Z.of_nat i + kk)) by lia. apply HT. lia.
- intros i p w Hi Hw. destruct (Ht i p w Hi Hw) as (A1 & A2 & A3 & A4).
  split; [|split; [exact A2 | split; [exact A3 | exact A4]]].
  apply (astr_atR_agree rd rd' p w (Z.of_nat (length w) + 1) A1); [lia|].
  intros kk Hkk. replace (p + kk) with (cb + (p - cb + kk)) by lia. apply HC. lia.
Qed.

Ltac v29_inl := cbn [vr_base In app]; solve [ repeat first [left; reflexivity | right] ].

(* ------------------------------------------------------------------------------------------------------------
   Statement pass 4: sup_resp's post is FP-existential (CmdBase.v apost_baseF), so the code after its call runs at
   the FP state fx' the call returns. Section d0 holds everything that runs or holds after the call (the state at the
   return address, the move stubs to the joins) and the helpers; it is closed before the main section d, so its
   lemmas hold at every FP state. Section d (the end of the file) runs the refusal stubs at the entry's FP state,
   calls sup_resp (cl_callSF) and continues with d0's lemmas at fx'. *)
Section d0. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f0.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma v29_val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hb.
destruct (aview_byte SEGS (w_H W) mem _ _ Hb) as (b & Hm & Hbv & Hrange).
rewrite Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|]. change (bv_modulus 8) with 256. exact Hrange.
Qed.

Lemma v29_rdword_of_aval : forall (W : world SEGS) mem a v,
aval_mem (rdW W mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (rdW W mem) a = Some v.
Proof. intros W mem a v H Hv. apply rdword_of_val_mem; [apply v29_val_mem_of_aval; exact H | exact Hv]. Qed.

(* the one-word spill region at s1+8 (the shadow of the side-stack frame): read-only, so the symbolic runs below
   write nothing *)
Definition v29_spr : YP09.region := YP09.mkRegion (Some 9%nat) 8 16 8 8 [YP09.mkChunk 8 (CVal 8 (SOff 32 0))].
Definition v29_ss (pcoff : Z) : sstate := mkSS pcoff sr_atoms [v29_spr] None (mkFacts [] [] []).
(* the registers alone (the refusal stubs read no memory) *)
Definition v29_ssr (pcoff : Z) : sstate := mkSS pcoff sr_atoms [] None (mkFacts [] [] []).

Lemma v29_env_agree_Eimg : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma v29_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.

Section e0.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ------------------------------------------------------------------------------------------------------------
   The hypotheses the part after the call uses: the record facts with cgif's names and the interface's named
   premises (the same names and types as the main section's). *)
Hypothesis MTL : ameter_laws MT.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* ------------------------------------------------------------------------------------------------------------
   Reading a boundary state *)
Lemma v29_rv_in : forall regs l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma v29_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.

Lemma v29_rv_keep : forall e (regs regsc : bvmap 5 word) rl rl',
vr_rv regsc (vr_base B e ++ rl) ->
(forall r, In r [2; 3; 4; 8; 9] -> getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
(forall r v, In (r, v) rl' ->
  (In (r, v) rl /\ getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) \/ getr regs (Z_to_bv 5 r) = w64 v) ->
vr_rv regs (vr_base B e ++ rl').
Proof.
intros e regs regsc rl rl' Hrv Hb Hl. apply v29_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin|Hin].
- assert (Hr : In r [2; 3; 4; 8; 9]).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _; cbn; tauto. }
  rewrite (Hb r Hr). apply (v29_rv_in regsc _ _ _ Hrv). apply in_or_app; left; exact Hin.
- destruct (Hl r v Hin) as [[H1 H2] | H]; [|exact H].
  rewrite H2. apply (v29_rv_in regsc _ _ _ Hrv). apply in_or_app; right; exact H1.
Qed.

Lemma v29_core_regs : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc W mem md' k ->
vr_rv regs' (vr_base B e ++ rl') ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs' mem md'.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc W regs mem md regs' md'
  (HJ & Hk & Hm & Hnm & Hfr & Hrv & H) HJ' Hrv'.
split; [exact HJ'|]. split; [exact Hk|]. split; [exact Hm|]. split; [exact Hnm|]. split; [exact Hfr|].
split; [exact Hrv' | exact H].
Qed.

Lemma v29_frameF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
In (4, pos) (frames Sc) /\ AR SEGS B lyc Sc Wc memc mdc /\ 4096 <= F /\ F + 1024 <= alloc_ceiling.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc HC.
pose proof HC as (HJ & _ & _ & _ & (HF & _) & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (H1 & H2 & _).
change (fs_frame_bytes 4) with 1024 in H2. rewrite <- HF in H1, H2.
split; [exact Hin|]. split; [exact HAR|]. split; [exact H1 | exact H2].
Qed.

Lemma v29_stkF : forall {e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc},
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e).
Proof.
intros. pose proof H as (HJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact Hstk.
Qed.

Lemma v29_s1_bounds : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
4096 <= vr_s1 e /\ vr_s1 e + 224 <= vr_sp0 e + 32 /\ vr_sp0 e <= 2 ^ 47 /\ vr_s1 e + 16 <= 2 ^ 64 /\
vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia.
Qed.

Lemma v29_shadow_bounds : forall F, 4096 <= F -> F + 1024 <= alloc_ceiling ->
0 <= shadow_addr F /\ shadow_addr F + 4 < 2 ^ 64.
Proof.
intros F H1 H2. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
assert (Hp : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hu : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   Seeding a symbolic state at a stub: the registers, and the one spill word the move stubs read *)
Lemma v29_seed : forall (pcoff : Z) (regsc : bvmap 5 word) memc (W : world SEGS) (s1v shv : Z),
getr regsc (Z_to_bv 5 9) = w64 s1v -> 0 <= s1v -> s1v + 16 <= 2 ^ 64 -> 0 <= shv < 2 ^ 64 ->
aval_mem (rdW W memc) (s1v + 8) 8 shv ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc [w64 shv])) (v29_ss pcoff)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pcoff)) memc (seg_rom SEGS))).
Proof.
intros pcoff regsc memc W s1v shv H9 Hlo Hhi Hsh Hav.
set (E := Eimg (Ereg regsc [w64 shv])).
assert (E9 : bv_unsigned (ew E 9%nat) = s1v).
{ subst E. rewrite (ew_Eimg_Ereg_nat regsc [w64 shv] 9%nat (Z_to_bv 5 9) eq_refl), H9.
  unfold w64. apply unsigned_lit_small. lia. }
assert (E32 : ew E 32%nat = w64 shv).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  pose proof (ew_Ereg_extra regsc [w64 shv] 0%nat) as HE. cbn [Nat.add nth] in HE. exact HE. }
rewrite restrict_mkst_fx. unfold v29_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold v29_spr, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ s1v 8 8%N (SOff 32 0) shv).
  + cbn [sv_denot]. rewrite E32. unfold w64. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + cbn. lia.
  + apply v29_val_mem_of_aval. exact Hav.
- cbn. tauto.
- unfold facts_ok. cbn. repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma v29_seed_r : forall (pcoff : Z) (regsc : bvmap 5 word) memc (W : world SEGS),
st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) (v29_ssr pcoff)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pcoff)) memc (seg_rom SEGS))).
Proof.
intros pcoff regsc memc W. rewrite restrict_mkst_fx. unfold v29_ssr. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

Lemma v29_getr_ew : forall (regsc : bvmap 5 word) extra (n : nat) (r : bv 5) v,
Z.of_nat n = bv_unsigned r -> getr regsc r = w64 v -> ew (Ereg regsc extra) n = w64 v.
Proof. intros regsc extra n r v Hn Hg. rewrite (ew_Ereg_nat regsc extra n r Hn). exact Hg. Qed.

Ltac v29_rvgoal HS Hrv E32x :=
cbn [fst snd];
lazymatch goal with
| |- getr _ ?r = w64 _ =>
  let Hx := fresh "Hx" in
  prreg HS r Hx; cbv [A_TEXT A_LIM] in Hx; cbn [Nat.leb andb] in Hx; rewrite Hx; clear Hx;
  first [ exact E32x
        | lazymatch goal with
          | |- ew _ ?n = _ =>
            apply (v29_getr_ew _ _ n (Z_to_bv 5 (Z.of_nat n)) _ eq_refl);
            apply (v29_rv_in _ _ _ _ Hrv); apply in_or_app;
            first [ left; v29_inl | right; v29_inl ]
          end ]
end.

(* ------------------------------------------------------------------------------------------------------------
   vr_hd with the register list and the word count left open: the state at a stub's return address is of this
   shape too, and `vr_hd e pc` is this at the interface's list and count. *)
Definition v29_hdX (e : vrE) (pc : Z) (rlf : Z -> Z -> Z -> Z -> list (Z * Z)) (P : nat -> Prop)
  : world SEGS -> config -> Prop := fun Wc cf =>
exists tq O1 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
P (length (Verbs.toks (e_D e))) /\
4096 <= tq /\ astr_atR (rdW Wc memc) tq (vr_x (e_R e) (e_D e)) /\
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c]
  vr_sh2 (vr_sl3 F q c) (rlf F q c tq) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc Wc regsc memc mdc /\
vr_line B e q Wc memc /\ vr_copy B e F c tp Wc memc.

(* the move stubs: one or two register moves and a jump, no call and no store *)
Ltac v29_mv_tac srcpc srcoff tgtpc tgtoff :=
intros P e W cf H;
destruct H as (tq & O1 & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm & -> & Hnt & Htq & Hstr & HC & Hline & Hcopy);
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit);
destruct (v29_frameF HC) as (Hinf & HAR & HF1 & HF2);
pose proof (v29_stkF HC) as Hstk;
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e);
destruct (v29_shadow_bounds F HF1 HF2) as (Hsha & Hshb);
assert (H9 : getr regsc (Z_to_bv 5 9) = w64 (vr_s1 e))
  by (apply (v29_rv_in regsc _ 9 (vr_s1 e) Hrv); apply in_or_app; left; v29_inl);
assert (Hav : aval_mem (rdW W memc) (vr_s1 e + 8) 8 (shadow_addr F))
  by (unfold vr_spill in Hsp; rewrite Forall_forall in Hsp;
      exact (Hsp (8, shadow_addr F) ltac:(unfold vr_sl3; v29_inl)));
pose proof (v29_seed srcoff regsc memc W (vr_s1 e) (shadow_addr F) H9 ltac:(lia) ltac:(lia) ltac:(lia) Hav) as HS;
pose proof (Eimg_env (Ereg regsc [w64 (shadow_addr F)])) as HEI;
assert (E32 : ew (Ereg regsc [w64 (shadow_addr F)]) 32%nat = w64 (shadow_addr F))
  by (pose proof (ew_Ereg_extra regsc [w64 (shadow_addr F)] 0%nat) as HH; cbn [Nat.add nth] in HH; exact HH);
unfold cfg_at; change (w64 (vr_pc srcpc)) with (Z_to_bv 64 (BASE + srcoff));
paj_run_to_sh RUNTOP HS HJ tgtoff;
[ unfold v29_ss; cbn [ss_mem]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]
| assert (Hro : rs_read_only [v29_spr] = true) by (vm_compute; reflexivity);
  lazymatch goal with
  | Hfr : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let Hmem := fresh "Hmem" in
    pose proof (frame_of_read_only _ _ _ _ Hro Hfr) as Hmem;
    cbn [ms_mem mkst] in Hmem; rewrite Hmem in HJ; pmkst HS; rewrite Hmem
  end;
  apply SRr_ret;
  lazymatch goal with
  | |- v29_hdX _ _ _ _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) =>
    exists tq, O1, pos, F, q, c, tp, lyc, Sc, rg, mm, mdx, k, nm
  end;
  split; [unfold cfg_at; change (w64 (vr_pc tgtpc)) with (Z_to_bv 64 (BASE + tgtoff)); reflexivity|];
  split; [exact Hnt|];
  split; [exact Htq|]; split; [exact Hstr|];
  split; [| split; [exact Hline | exact Hcopy]];
  split; [exact HJ|]; split; [exact Hk|]; split; [exact Hmet|]; split; [exact Hnm|]; split; [exact Hfr|];
  split; [| split; [exact Hsv|]; split; [exact Hsp|]; split; [exact Henv|]; split; [exact Hrec|];
           split; [exact HnO|]; split; [exact Hperm | exact Hquit]];
  unfold vr_rv, vr_base; cbn [app];
  repeat apply Forall_cons; try apply Forall_nil; v29_rvgoal HS Hrv E32 ].

(* 0x8da30 mv s10,a0 -> JA 0x8da34 (after sup_resp at the stub 0x8da28) *)
Lemma v29_mv_a30 : forall P e W cf,
v29_hdX e 0x8da30 (fun F q c tq => [(10, tq); (18, q); (21, vr_ntok (e_D e)); (22, F + 32)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8da34 (fun F q c tq => [(26, tq); (18, q); (21, vr_ntok (e_D e)); (22, F + 32)]) P).
Proof. v29_mv_tac 0x8da30 30028 0x8da34 30032. Qed.

(* 0x8dc34 mv s9,a0; j 0x8dae4 *)
Lemma v29_mv_c34 : forall P e W cf,
v29_hdX e 0x8dc34 (fun F q c tq => [(10, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8dae4 (fun F q c tq => [(25, tq); (18, q); (19, c); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8dc34 30544 0x8dae4 30208. Qed.

(* 0x8dc54 mv s10,a0; j 0x8da44 *)
Lemma v29_mv_c54 : forall P e W cf,
v29_hdX e 0x8dc54 (fun F q c tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8da44 (fun F q c tq => [(26, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8dc54 30576 0x8da44 30048. Qed.

(* 0x8dc94 mv s9,a0; j 0x8dae0 *)
Lemma v29_mv_c94 : forall P e W cf,
v29_hdX e 0x8dc94 (fun F q c tq => [(10, tq); (18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8dae0 (fun F q c tq => [(25, tq); (18, q); (20, F); (22, F + 32); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8dc94 30640 0x8dae0 30204. Qed.

(* 0x8dca4 mv s10,a0; ld s9,8(s1); j 0x8da40 *)
Lemma v29_mv_ca4 : forall P e W cf,
v29_hdX e 0x8dca4 (fun F q c tq => [(10, tq); (18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8da40 (fun F q c tq => [(26, tq); (18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8dca4 30656 0x8da40 30044. Qed.

(* 0x8dd3c mv s10,a0; ld s9,8(s1); j 0x8da44 *)
Lemma v29_mv_d3c : forall P e W cf,
v29_hdX e 0x8dd3c (fun F q c tq => [(10, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]) P W cf ->
SRr SEGS W cf (v29_hdX e 0x8da44 (fun F q c tq => [(26, tq); (18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (25, shadow_addr F); (27, shadow_addr F + 4)]) P).
Proof. v29_mv_tac 0x8dd3c 30808 0x8da44 30048. Qed.

(* ------------------------------------------------------------------------------------------------------------
   The GOT words the walk needs are read-only bytes of the image *)
Lemma v29_abytes_aval8 : forall (rd : reader) a l v, (8 <= length l)%nat ->
(forall i, (i < 8)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) = le_byte v 8 i) ->
abytes_atR rd a l -> aval_mem rd a 8 v.
Proof. intros rd a l v Hl Hc Hb i Hi. rewrite (Hb i ltac:(lia)). f_equal. apply Hc. exact Hi. Qed.

Lemma v29_ro_got : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
repeat (lazymatch type of Hb with
        | abytes_atR rd 0xa7068 _ /\ _ => fail
        | _ /\ _ => apply proj2 in Hb
        end).
destruct Hb as (H1 & H2 & H3 & H4).
unfold cmd_got_ok. split; [|split; [|split]].
- exact (v29_abytes_aval8 rd 0xa7068 RO_ptr_a7068 A_G_REC ltac:(vm_compute; lia)
           ltac:(intros i Hi; do 8 (destruct i; [vm_compute; reflexivity|]); lia) H1).
- exact (v29_abytes_aval8 rd 0xa7070 RO_ptr_a7070 0x21cc0 ltac:(vm_compute; lia)
           ltac:(intros i Hi; do 8 (destruct i; [vm_compute; reflexivity|]); lia) H2).
- exact (v29_abytes_aval8 rd 0xa7078 RO_ptr_a7078 0x21ba0 ltac:(vm_compute; lia)
           ltac:(intros i Hi; do 8 (destruct i; [vm_compute; reflexivity|]); lia) H3).
- exact (v29_abytes_aval8 rd 0xa7080 RO_ptr_a7080 A_G_QUITTING ltac:(vm_compute; lia)
           ltac:(intros i Hi; do 8 (destruct i; [vm_compute; reflexivity|]); lia) H4).
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The entry's facts, the stack offset of the call, and the events and bytes sup_resp may spend *)
Lemma v29_ent_facts : forall e, vr_ent B MT e ->
afn_pre SEGS B VERBS_RECEIVE_STK (e_ly e) (e_S e) (e_W e) (e_regs e) (e_mem e) (e_md e) (e_ch e) /\
rec_repA B (e_ly e) (e_S e) (rdW (e_W e) (e_mem e)) (e_R e) (e_O e) /\
(0 <= e_n e <= 8192) /\ Z.of_nat (length (e_D e)) = e_n e /\
st_nev (e_S e) + ev_vr (e_R e) (e_D e) <= EV_MAX /\
blocks_bytes (e_S e) + LIVE_VERBS_RECEIVE <= LIVE_MAX /\
mo_ok MT (e_S e) (XM_VERBS_RECEIVE MT (e_R e) (e_D e)) /\
Z.of_nat (length (frames (e_S e))) <= 4 /\
r_calls (e_R e) = [] /\
Permutation (ablocks B (e_ly e) (e_S e)) (e_O e ++ e_rest e).
Proof.
intros e H. unfold vr_ent in H.
destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
  H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H28 & H29 & H30 & H31 & H32 & H33).
split; [exact H1|]. split; [exact H14|]. split; [exact H8|]. split; [exact H9|].
split; [exact H30|]. split; [exact H31|]. split; [exact H32|]. split; [exact H29|].
split; [exact H15 | exact H20].
Qed.

Lemma v29_s1_bounds2 : forall e, astk_ok VERBS_RECEIVE_STK (e_ly e) (vr_sp0 e) ->
alloc_ceiling <= vr_s1 e /\ (vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e mod 16 = 0 /\
SUP_RESP_STK - (vr_s1 e - vr_sp0 e) <= VERBS_RECEIVE_STK /\ 0 <= SUP_RESP_STK.
Proof.
intros e Hstk. pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HV : 16752 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HR : SUP_RESP_STK = 16528) by (vm_compute; reflexivity).
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as Hmb.
unfold vr_s1 in *.
split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [exact Hal|]. split; lia.
Qed.

Lemma v29_rec_spill_frees_nonneg : forall R, 0 <= rec_spill_frees R.
Proof. intros R. unfold rec_spill_frees. destruct (Nat.ltb (length (r_calls R)) 16); lia. Qed.
Lemma v29_ev_after_nonneg : forall R2 af, 0 <= ev_after R2 af.
Proof.
intros R2 af. unfold ev_after. destruct af as [p|]; [|lia].
unfold EV_SUP_AFTER_REPLY, EV_ARG_I, EV_XSTRDUP. pose proof (v29_rec_spill_frees_nonneg R2). lia.
Qed.
Lemma v29_k1_le_ev : forall R D, vr_k1 R D <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2. unfold EV_REPLY, EV_SOCKET_SEND.
pose proof (v29_ev_after_nonneg (vr_R2 R D) (vr_aft D)). lia.
Qed.

(* every byte of the entry's footprint is below the frame the prologue left *)
Lemma v29_fp_below : forall e, vr_ent B MT e -> forall a, vr_sp0 e <= a -> ~ inFP (vr_fp e) a.
Proof.
intros e He a Ha Hin. unfold vr_sp0 in Ha.
destruct (v29_ent_facts e He) as (HPRE & HREC0 & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HV : 16752 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
pose proof asan_consts as (C1 & _).
destruct Hin as (r & Hr & Hrr). unfold vr_fp in Hr. apply in_app_or in Hr as [Hr | Hr].
- unfold VERBS_RECEIVE_PG in Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hrr;
  cbv [A_G_REC A_REC_SPILL A_G_QUITTING REC_SIZE SC_SIZE] in Hrr; lia.
- destruct (inFP_ablocks_fp_inv (e_O e) a (ex_intro _ r (conj Hr Hrr))) as (p & n & Hpn & Hpr).
  pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn) as Hin2.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin2) as (_ & _ & Hce & _). lia.
Qed.

(* the frame chain at the call: verbs_receive keeps its frame pointer sp0 in s0 at every program call (class B of the
   s0 call-site survey), so the chain is achain_push on afn_pre's chain at the entry (vr_ent's 1st conjunct) with the
   ra and entry-s0 words the prologue stored at sp0 - 8 and sp0 - 16 (vr_saved, j = 0 and j = 1); the words from sp0
   up are the entry's (the journal's footprint lies below sp0); when sp0 >= ly_top - 16 the chain is achain's empty
   case (pass 5) *)
Lemma v29_achain : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc,
vr_ent B MT e ->
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
exists ch1, achain lyc (rdW Wc memc) (vr_s1 e) (vr_sp0 e) ch1.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc He HC.
pose proof HC as (HJ & _ & _ & _ & _ & _ & Hsv & _).
pose proof (v29_stkF HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (v29_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
destruct (v29_ent_facts e He) as (HPRE & _).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & _ & _ & Hch0 & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & _).
assert (Hkeep : forall a, vr_sp0 e <= a < 2 ^ 64 -> rdW Wc memc a = rdW (e_W e) (e_mem e) a).
{ intros a Ha. apply (aview_above_of_journal B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc Wc memc mdc k HJ a Ha).
  apply (v29_fp_below e He). lia. }
destruct (Z_le_gt_dec (ly_top lyc - 16) (vr_sp0 e)) as [Hle|Hgt].
- exists []. left. split; [right; left; lia | reflexivity].
- exists ((vr_sp0 e, raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 1)) as HRa;
  change (bv_modulus 64) with (2 ^ 64) in HRa.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs e) 8)) as HR8;
  change (bv_modulus 64) with (2 ^ 64) in HR8.
  assert (Hra8 : rdword (rdW Wc memc) (vr_sp0 e - 8) = Some (raZ (e_regs e))).
  { apply v29_rdword_of_aval; [| unfold raZ; lia].
    pose proof (Hsv 0%nat 1 eq_refl) as Hx.
    assert (E0 : vr_sp0 e - 8 - 8 * Z.of_nat 0 = vr_sp0 e - 8) by lia. rewrite E0 in Hx. exact Hx. }
  assert (Hs08 : rdword (rdW Wc memc) (vr_sp0 e - 16) = Some (s0Z (e_regs e))).
  { apply v29_rdword_of_aval; [| unfold s0Z; lia].
    pose proof (Hsv 1%nat 8 eq_refl) as Hx.
    assert (E1 : vr_sp0 e - 8 - 8 * Z.of_nat 1 = vr_sp0 e - 16) by lia. rewrite E1 in Hx. exact Hx. }
  apply (achain_push lyc (rdW (e_W e) (e_mem e)) (rdW Wc memc) (vr_sp0 e) (s0Z (e_regs e)) (raZ (e_regs e))
    (e_ch e) (vr_s1 e)).
  + apply (achain_ly_top (e_ly e) lyc); [exact Etop | exact Hch0].
  + lia.
  + exact Hkeep.
  + exact Hra8.
  + exact Hs08.
  + exact Hra4.
  + lia.
  + Z.div_mod_to_equations; lia.
  + lia.
  + lia.
Qed.

(* one message records at most two calls (the plain proof's step_frame, HarnessPropsProof.v:1363, at the ASan
   reply code and an already cleared table) *)
Lemma v29_calls_le2 : forall rcode R s, r_calls R = [] ->
(length (r_calls (fst (fst (VerbsRun.run_step rcode R s)))) <= 2)%nat.
Proof.
intros rcode R s H.
destruct s as [c0|c|u i p q|u f l v|u| |ln tk]; [|destruct c|..];
cbv [VerbsRun.run_step VerbsRun.run_call VerbsRun.pins_follow sup_add_m descriptors_get_m
  descriptors_panel_get_m sup_remove_m sup_remove_all_m sup_worker_list_m sup_instance_info_m sup_reset_m
  sup_quarantine_clear_m sup_policy_set_m sup_lv2_worker_set_m sup_pool_config_m sup_worker_env_m
  sup_chain_m sup_chain_clear_m sup_pin_accept_m sup_instance_verb_m sup_call_m sup_connect_m
  sup_broadcast_m sup_host_setting_m pins_set_m pins_clear_m lv2_refusals_forget_m descriptors_add_m
  rec_stub rec_answer hand_back rec_record rec_mix rec_mix_host rec_stub_code rec_answer_code
  rec_stub_mix set_calls set_spill set_answer set_state set_host set_reply];
rewrite ?H; cbn [fst snd r_calls length app Nat.ltb Nat.leb];
repeat (match goal with |- context [if ?cnd then _ else _] => destruct cnd end;
        cbn [fst snd r_calls length app Nat.ltb Nat.leb]; rewrite ?H; cbn [fst snd r_calls length app Nat.ltb Nat.leb]);
rewrite ?H; cbn [length app]; lia.
Qed.

(* the meter at sup_resp's call, the one call shape of S29: its account is one malloc of |resp code| + 1 <= 18 bytes
   (xstrdup's), so a = 1, b = 0, ev = EV_SUP_RESP = 1 for the interface's vri_meter_ok (the room before the call) and
   vri_meter_step (vr_meter after it). The meter reasoning of this segment lives in these three lemmas only. *)
Lemma v29_meter_xm : forall code, - 2 ^ 31 <= code < 2 ^ 31 ->
XM_SUP_RESP MT code <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof.
intros code Hcode. pose proof (resp_length code Hcode) as Hrl.
assert (HXM : XM_SUP_RESP MT code <= mo_malloc MT VERBS_RECEIVE_REQ).
{ unfold XM_SUP_RESP, XM_XSTRDUP. apply (mo_malloc_mono MT MTL). unfold VERBS_RECEIVE_REQ. lia. }
lia.
Qed.

Lemma v29_meter_pre : forall e Sc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> k <= vr_k1 (e_R e) (e_D e) - EV_SUP_RESP ->
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e Sc k nm code He Hcode Hmet Hk.
pose proof (v29_k1_le_ev (e_R e) (e_D e)) as Hkev.
apply vri_meter_ok with (B := B) (e := e) (k := k) (nm := nm) (a := 1) (b := 0) (ev := EV_SUP_RESP).
- exact MTL.
- exact He.
- exact Hmet.
- exact (v29_meter_xm code Hcode).
- unfold EV_SUP_RESP, EV_XSTRDUP. lia.
- unfold EV_SUP_RESP, EV_XSTRDUP. lia.
- lia.
Qed.

Lemma v29_meter_post : forall e Sc S2 k nm code,
- 2 ^ 31 <= code < 2 ^ 31 ->
vr_meter MT e Sc k nm -> mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_meter MT e S2 (k + EV_SUP_RESP) (nm + 1).
Proof.
intros e Sc S2 k nm code Hcode Hmet Hmo.
apply vri_meter_step with (Sc := Sc) (X := XM_SUP_RESP MT code) (b := 0).
- exact MTL.
- exact Hmet.
- exact Hmo.
- exact (v29_meter_xm code Hcode).
- unfold EV_SUP_RESP, EV_XSTRDUP. lia.
- unfold EV_SUP_RESP, EV_XSTRDUP. lia.
Qed.

(* the premises of tsup_resp_spec at a refusal stub *)
Lemma v29_call_pre : forall e pos F q c rlp Rx Ox lyc Sc (W : world SEGS) regsc memc mdc k nm code,
vr_ent B MT e -> - 2 ^ 31 <= code < 2 ^ 31 ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlp Rx Ox (e_q0 e)
  k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regsc memc mdc ->
Z.of_nat (length (frames Sc)) <= 8 /\
arodata_okP SEGS RLO RHI B (rdW W memc) /\ cmd_ro_ok (rdW W memc) /\
aguard_ok SEGS W memc 0xa7098 0x6045d8 /\
st_nev Sc + EV_SUP_RESP <= EV_MAX /\ blocks_bytes Sc + LIVE_SUP_RESP code <= LIVE_MAX /\
mo_ok MT Sc (XM_SUP_RESP MT code).
Proof.
intros e pos F q c rlp Rx Ox lyc Sc W regsc memc mdc k nm code He Hcode Hh HC.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_ent_facts e He) as (HPRE & HREC0 & Hn8 & HDn & Hev & Hlive & Hmok & Hfrs4 & Hcalls0 & Hperm0).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & Hnev & Hk0 & _).
pose proof HPRE as (HAR0 & _).
pose proof (v29_k1_le_ev (e_R e) (e_D e)) as Hkev.
pose proof (resp_length code Hcode) as Hrl.
(* the live bytes: the recorder's blocks, the line and the copy (verbs_receive_live.v) *)
assert (Hc2 : (length (r_calls Rx) <= 2)%nat).
{ pose proof (v29_calls_le2 reply_code_a (e_R e) (vr_st (e_D e)) Hcalls0) as Hcx.
  unfold vr_h in Hh. unfold VerbsRun.run_step in Hcx. unfold VerbsRun.run_step in Hh.
  rewrite Hh in Hcx. cbn [fst] in Hcx. exact Hcx. }
assert (Hlb : vr_l (e_n e) (e_D e) <= 8192).
{ unfold vr_l. rewrite <- HDn. rewrite (proj2 (verbs_receive_pre.strnlen_upto (e_D e))).
  pose proof (verbs_receive_route.upto_len (fun b => bv_unsigned b =? 0) (e_D e)) as Hu.
  change (Verbs.upto0 (e_D e)) with (Verbs.upto (fun b => bv_unsigned b =? 0) (e_D e)). lia. }
assert (Hcb : Z.of_nat (length (Verbs.line (e_D e))) <= 8192).
{ pose proof (verbs_receive_route.line_len (e_D e)) as Hl. lia. }
assert (Hbb : blocks_bytes Sc <= blocks_bytes (e_S e) +
  (6 * Z.of_nat (length (r_calls Rx)) + 8) * (LMAX + 2) + bsum [vr_lb e q; vr_cb e c]).
{ exact (vr_live_le SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HAR0 HAR Hperm0 Hperm Hrec). }
assert (Hbs : bsum [vr_lb e q; vr_cb e c] <= 16386).
{ unfold bsum, vr_lb, vr_cb. cbn [fold_right snd]. lia. }
assert (Hlm : LMAX = 8192) by reflexivity.
split; [rewrite Hfrs; cbn [length app]; rewrite Nat2Z.inj_succ; lia|].
split; [exact (proj1 Henv)|].
split; [exact (proj1 (proj2 (proj2 Henv)))|].
split; [exact (proj1 (proj2 (proj2 (proj2 Henv))))|].
split; [unfold EV_SUP_RESP, EV_XSTRDUP in *; lia|].
split.
{ unfold LIVE_SUP_RESP, LIVE_XSTRDUP, LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in *.
  assert (Hq : (6 * Z.of_nat (length (r_calls Rx)) + 8) * (LMAX + 2) <= 20 * 8194).
  { rewrite Hlm. apply Z.mul_le_mono_nonneg_r; lia. }
  lia. }
exact (v29_meter_pre e Sc k nm code He Hcode Hmet Hk).
Qed.

Lemma v29_line_le_upto0 : forall D, (length (Verbs.line D) <= length (Verbs.upto0 D))%nat.
Proof.
intros D. unfold Verbs.line, Verbs.trim. rewrite length_rev.
pose proof (verbs_receive_route.dropw_len Verbs.is_trail (rev (Verbs.upto0 D))) as H.
rewrite length_rev in H. exact H.
Qed.

Lemma v29_line_le_l : forall e, vr_ent B MT e ->
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e).
Proof.
intros e He. destruct (v29_ent_facts e He) as (_ & _ & _ & HDn & _).
unfold vr_l. rewrite <- HDn. rewrite (proj2 (verbs_receive_pre.strnlen_upto (e_D e))).
pose proof (v29_line_le_upto0 (e_D e)). lia.
Qed.

(* after sup_resp returned: the text is a block of its own, the frame, the spills, the saves, the blocks and the
   read-only and record facts are kept (the callee's journal has an empty footprint) *)
Lemma v29_call_post : forall (e : vrE) (pc : Z) rlf (P : nat -> Prop) (code : Z) Rx Ox pos F q c tp
  lyc Sc (W : world SEGS) regsc memc mdc k nm rlp
  ly2 S2 (W2 : world SEGS) regs2 mem2 md2 tq,
Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e) ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
- 2 ^ 31 <= code < 2 ^ 31 ->
P (length (Verbs.toks (e_D e))) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) rlp Rx Ox (e_q0 e)
  k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regsc memc mdc ->
vr_line B e q W memc -> vr_copy B e F c tp W memc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  ly2 S2 W2 mem2 md2 (k + EV_SUP_RESP) ->
ajournal SEGS B SUP_RESP_STK (vr_s1 e) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV_SUP_RESP ->
4096 <= tq ->
Permutation (ablocks B ly2 S2) ((tq, Z.of_nat (length (resp code)) + 1) :: ablocks B lyc Sc) ->
astr_atR (rdW W2 mem2) tq (resp code) ->
(forall R O, rec_repA B lyc Sc (rdW W memc) R O -> rec_repA B ly2 S2 (rdW W2 mem2) (fst (sup_resp_m R code)) O) ->
mo_le MT Sc S2 (XM_SUP_RESP MT code) ->
vr_rv regs2 (vr_base B e ++ rlf F q c tq) ->
v29_hdX e pc rlf P W2 (cfg_at SEGS (vr_pc pc) regs2 mem2 md2).
Proof.
intros e pc rlf P code Rx Ox pos F q c tp lyc Sc W regsc memc mdc k nm rlp ly2 S2 W2 regs2 mem2 md2 tq
  Hll Hh Hcode HP HC Hline Hcopy HJ2 HJc Htq Hpq Hstr Hrectr Hmo Hrv2.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_frameF HC) as (Hinf & HAR & HF1 & HF2).
pose proof (v29_stkF HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (v29_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJc as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & G1 & G2 & G3 & G4 & _ & _ & _ & _ & _).
assert (Hnofp : forall a : Z, ~ inFP ([] : list (Z * Z)) a) by (intros a (r & [] & _)).
assert (Hsp2 : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply G1; [lia | lia | apply Hnofp]).
assert (Hblk : forall p n i, In (p, n) (ablocks B lyc Sc) -> In (p, n) (ablocks B ly2 S2) -> 0 <= i < req_size n ->
  rdW W2 mem2 (p + i) = rdW W memc (p + i)) by (intros p n i H1 H2 H3; exact (G2 p n i H1 H2 H3 (Hnofp _))).
assert (Himg : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> rdW W2 mem2 a = rdW W memc a).
{ intros a H1 H2 H3. apply G3; try assumption.
  split; [intros Hs; destruct (sink_closed_pos [] (Forall_nil _) Hs) | apply Hnofp]. }
assert (Hfrm : forall a, (in_zr a (frame_rng lyc (4, pos)) \/
    in_zr a (shadow_addr (frame_addr lyc 4 pos), fs_frame_bytes 4 / 8)) -> rdW W2 mem2 a = rdW W memc a)
  by (intros a Ha; apply (G4 4 pos a Hinf Ha); apply Hnofp).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFA : frame_addr ly2 4 pos = frame_addr lyc 4 pos) by (unfold frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF; reflexivity).
assert (Hqv : vr_qv e = e_q0 e) by (unfold vr_qv, vr_quit; rewrite Hh; reflexivity).
assert (Hxv : vr_x (e_R e) (e_D e) = resp code) by (unfold vr_x; rewrite Hh; reflexivity).
assert (HR1 : vr_R1 (e_R e) (e_D e) = Rx) by (unfold vr_R1; rewrite Hh; reflexivity).
pose proof (resp_length code Hcode) as Hrl.
assert (FB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct Hfr as (HFeq & HFflag & HFsh).
(* the line block and the copy block are live before and after the call *)
assert (HinLb : In (vr_lb e q) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. left. reflexivity. }
assert (HinCb : In (vr_cb e c) (ablocks B lyc Sc)).
{ apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. right. left. reflexivity. }
assert (HinLb2 : In (vr_lb e q) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinLb).
assert (HinCb2 : In (vr_cb e c) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym Hpq)); right; exact HinCb).
exists tq, Ox, pos, F, q, c, tp, ly2, S2, regs2, mem2, md2, (k + EV_SUP_RESP), (nm + 1).
split; [reflexivity|]. split; [exact HP|]. split; [exact Htq|].
split; [rewrite Hxv; exact Hstr|].
split; [|split].
- (* vr_core *)
  split; [exact HJ2|].
  split; [lia|].
  split.
  { exact (v29_meter_post e Sc S2 k nm code Hcode Hmet Hmo). }
  split; [unfold VR_NM_PR, VR_NM_HD in *; lia|].
  split.
  { split; [rewrite EFA; exact HFeq|]. split.
    - rewrite EFL, <- HFflag. apply rdword_ext. intros kk Hkk. apply Hfrm. left.
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq. lia.
    - intros i Hi. rewrite Hfrm; [exact (HFsh i Hi)|]. right. unfold in_zr. cbn [fst snd].
      rewrite FB, <- HFeq. change (1024 / 8) with 128. lia. }
  split; [exact Hrv2|].
  split.
  { intros j r Hj.
    assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbv [vr_saved_regs] in Hjl; cbn [length] in Hjl.
    apply (aval_mem_agree _ _ _ 8 _ (Hsv j r Hj)). intros kk Hkk. apply Hsp2. lia. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in Hsp |- *. intros ov Hov.
    assert (Hob : 0 <= fst ov <= 72).
    { unfold vr_sl3 in Hov. cbn [In] in Hov.
      repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
    apply (aval_mem_agree _ _ _ 8 _ (Hsp ov Hov)). intros kk Hkk.
    replace (vr_s1 e + fst ov + kk) with (vr_s1 e + (fst ov + kk)) by lia. apply Hsp2. lia. }
  split.
  { (* the read-only bytes, the GOT words, the record cells *)
    destruct Henv as (Haro & _).
    assert (HAR2s : AR SEGS B ly2 S2 W2 mem2 md2) by exact (proj1 HJ2).
    assert (Haro2 : arodata_okP SEGS RLO RHI B (rdW W2 mem2)).
    { intros a Hro Ho He'. rewrite Himg; [exact (Haro a Hro Ho He') | | exact Ho | exact He'].
      destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (RRO a Hr)]. }
    pose proof (ROA ly2 S2 W2 mem2 md2 HAR2s Haro2) as Hro2.
    destruct (RECC ly2 S2 W2 mem2 md2 HAR2s) as (Hfl2 & Hgd2 & Her2).
    split; [exact Haro2|]. split; [exact (v29_ro_got _ Hro2)|]. split; [exact Hro2|].
    split; [exact Hgd2|]. split; [exact Hfl2 | exact Her2]. }
  split.
  { rewrite HR1. pose proof (Hrectr Rx Ox Hrec) as Hr2. cbn [sup_resp_m fst] in Hr2. exact Hr2. }
  split; [exact HnO|].
  split.
  { rewrite Hxv. eapply Permutation_trans; [exact Hpq|].
    eapply Permutation_trans; [apply perm_skip; exact Hperm|]. apply Permutation_middle. }
  { rewrite Hqv. intros j Hj. rewrite Himg; [exact (Hquit j Hj) | | |].
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj1 (PROGU _ HPG)).
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj1 (proj2 (PROGU _ HPG))).
    - assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat j)).
      { exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; v29_inl | cbn [fst snd]; lia]. }
      exact (proj2 (proj2 (PROGU _ HPG))). }
- (* the line *)
  destruct Hline as (Hfresh & Hls). split; [exact Hfresh|].
  apply (astr_atR_agree _ _ q _ (vr_l (e_n e) (e_D e) + 1) Hls); [lia|].
  intros kk Hkk. apply (Hblk q (vr_l (e_n e) (e_D e) + 1) kk HinLb HinLb2).
  pose proof (req_size_pos (vr_l (e_n e) (e_D e) + 1) ltac:(lia)). lia.
- (* the copy and tok[] *)
  destruct Hcopy as (Hfresh & Htoks). split; [exact Hfresh|].
  pose proof Htoks as (_ & Hlen & _).
  pose proof (Verbs.toks_length (e_D e)) as Htl.
  apply (v29_atoks_atA_agree _ _ _ _ _ _ _ Htoks).
  + intros kk Hkk. apply Hfrm. left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite FB, <- HFeq.
    rewrite Hlen in Hkk. lia.
  + intros kk Hkk. apply (Hblk c (Z.of_nat (length (Verbs.line (e_D e))) + 1) kk HinCb HinCb2).
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)). lia.
Qed.

End e0.
End f0.
End d0.

(* ------------------------------------------------------------------------------------------------------------
   The main section: the refusal stubs at the entry's FP state fx, the call of sup_resp (an FP-existential callee,
   taken at every FP state as verbs_receive_c.v takes it), the rest at the FP state fx' it returns (section d0's
   lemmas at fx'), and the ten pieces of S29 *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the Section hypotheses: the callee contract of verbs_receive_c.v that this segment reaches (fx-generic, statement
   pass 4), the record facts with cgif's names, and the interface's named premises *)
Hypothesis TSUP_RESP : forall fx0 : YK11.FPState, @tsup_resp_spec fx0 rc SK PI B MT.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis ROA : vr_ro_of_aro B.
Hypothesis RRO : vr_relro_img.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.

Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* rounding mode 0 at the entry FP state: vr_ent's last conjunct *)
Lemma v29_ent_frm0 : forall e, vr_ent B MT e -> frm0 fx.
Proof.
intros e H. unfold vr_ent in H. cbv zeta in H.
repeat lazymatch type of H with _ /\ _ => apply proj2 in H end. exact H.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The call of sup_resp at a refusal stub: from the state at sup_resp's entry (ra = the return pc, a0 = code, the
   kept registers rlk) through tsup_resp_spec (cl_callSF: the callee returns at some FP state fx') to the state at
   the return pc, at fx', where a0 holds the text, a live block of its own *)
Definition v29_resp_post (code : Z) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists q,
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 Permutation (ablocks B ly' S') ((q, Z.of_nat (length (resp code)) + 1) :: ablocks B ly S) /\
 Forall (fun qk => iv_apart q (Z.of_nat (length (resp code)) + 1) (fst qk) (snd qk)) (ablocks B ly S) /\
 In (q, Z.of_nat (length (resp code)) + 1) (ablocks B ly' S') /\ astr_atR (rdW W' mem') q (resp code) /\
 (forall R O, rec_repA B ly S (rdW W mem) R O -> rec_repA B ly' S' (rdW W' mem') (fst (sup_resp_m R code)) O) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_SUP_RESP code /\
 mo_le MT S S' (XM_SUP_RESP MT code).

Lemma v29_pr_call : forall (e : vrE) (retpc : Z) (rlk : Z -> Z -> Z -> list (Z * Z)) (P : nat -> Prop) (code : Z)
  Rx Ox pos F q c tp lyc Sc (W : world SEGS) regs mem md k nm,
vr_ent B MT e ->
vr_h (e_R e) (e_D e) = (Rx, resp code, false) ->
- 2 ^ 31 <= code < 2 ^ 31 ->
P (length (Verbs.toks (e_D e))) ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) ((1, vr_pc retpc) :: (10, code) :: rlk F q c)
  Rx Ox (e_q0 e) k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
0 <= AF_verbs_receive + (retpc - 0x8d480) < 2 ^ 40 -> (AF_verbs_receive + (retpc - 0x8d480)) mod 2 = 0 ->
Forall (fun rv => 18 <= fst rv <= 27) (rlk F q c) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_sup_resp)) mem (seg_rom SEGS)) md)
  (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
     v29_hdX (fx := fq) B MT e retpc (fun F' q' c' tq => (10, tq) :: rlk F' q' c') P W' cf').
Proof.
intros e retpc rlk P code Rx Ox pos F q c tp lyc Sc W regs mem md k nm He Hh Hcode HP HC Hline Hcopy Hrk1 Hrk2 Hcs.
pose proof HC as (HJ & Hk & Hmet & Hnm & Hfr & Hrv & Hsv & Hsp & Henv & Hrec & HnO & Hperm & Hquit).
destruct (v29_call_pre B MT MTL e pos F q c _ Rx Ox lyc Sc W regs mem md k nm code He Hcode Hh HC)
  as (Hfrs8 & Haro & Hro & Hgd & Hev1 & Hlv1 & Hmo1).
pose proof (v29_ent_frm0 e He) as Hfrm.
pose proof (v29_stkF B MT HC) as Hstk.
destruct (v29_s1_bounds e Hstk) as (Hs1a & Hs1b & Hs1c & Hs1d & Hs1e).
destruct (v29_s1_bounds2 e Hstk) as (Hs2a & Hs2b & Hs2c & Hs2d & Hs2e).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (R1 : getr regs 1 = w64 (vr_pc retpc))
  by (apply (v29_rv_in regs _ 1 _ Hrv); apply in_or_app; right; left; reflexivity).
assert (R10 : getr regs 10 = w64 code)
  by (apply (v29_rv_in regs _ 10 _ Hrv); apply in_or_app; right; right; left; reflexivity).
assert (R2 : getr regs 2 = w64 (vr_s1 e)) by (apply (v29_rv_in regs _ 2 _ Hrv); apply in_or_app; left; v29_inl).
assert (R3 : getr regs 3 = w64 (as_gp B)) by (apply (v29_rv_in regs _ 3 _ Hrv); apply in_or_app; left; v29_inl).
assert (R4 : getr regs 4 = w64 (as_tp B)) by (apply (v29_rv_in regs _ 4 _ Hrv); apply in_or_app; left; v29_inl).
assert (R8 : getr regs 8 = w64 (vr_sp0 e)) by (apply (v29_rv_in regs _ 8 _ Hrv); apply in_or_app; left; v29_inl).
assert (Hsp1 : spZ regs = vr_s1 e) by (unfold spZ; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
assert (Hs0 : s0Z regs = vr_sp0 e) by (unfold s0Z; rewrite R8; unfold w64; apply unsigned_lit_small; lia).
(* the frame chain at the call: s0 holds the entry sp, the chain is achain_push on the entry's (v29_achain) *)
destruct (v29_achain B MT e pos F _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regs mem md He HC) as (ch1 & Hch1).
eapply SRr_mono.
{ apply (cl_callSF B LAWS W regs mem (Z_to_bv 64 (BASE + AF_sup_resp)) VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e)
    (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k SUP_RESP_STK [] EV_SUP_RESP (vr_s1 e - vr_sp0 e)
    (w64 (vr_pc retpc)) ch1 (v29_resp_post code lyc Sc W mem) HJ).
  - rewrite Hsp1. lia.
  - exact Hs2b.
  - lia.
  - exact Hs2e.
  - exact Hs2d.
  - exact R3.
  - exact R4.
  - exact R1.
  - unfold w64, vr_pc. apply ret_ok_codeptr_v; [exact Hrk1 | exact Hrk2].
  - unfold w64, vr_pc. rewrite unsigned_lit_small by lia. lia.
  - replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) by lia. rewrite Hs0. exact Hch1.
  - intros HPRE1. eapply SRr_mono.
    { exact (TSUP_RESP fx lyc Sc W regs mem md ch1 code HPRE1 Hfrm Hfrs8 Haro Hro R10 Hcode Hev1 Hlv1 Hmo1). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & HR' & HC' & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. rewrite R1. split; [reflexivity|]. split; [exact HR'|].
    split; [exact HC'|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a (r & [] & _). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc & HP2 & HK).
destruct HK as (tq & Htq10 & Htq & Hpq & Hap & Hin & Hstr & Hrectr & Hbb & Hmo).
replace (vr_sp0 e + (vr_s1 e - vr_sp0 e)) with (vr_s1 e) in HJc by lia.
exists fx'. split; [exact Hfx|].
apply (v29_call_post (fx := fx') B MT MTL ROA RRO RECC PROGU e retpc (fun F' q' c' tq => (10, tq) :: rlk F' q' c') P
  code Rx Ox pos F q c tp lyc Sc W regs mem md k nm _ ly2 S2 W2 regs2 mem2 md2 tq (v29_line_le_l B MT e He)
  Hh Hcode HP HC Hline Hcopy HJ2 HJc ltac:(lia) Hpq Hstr Hrectr Hmo).
cbv beta. apply v29_rv_intro. intros r v Hin'. apply in_app_or in Hin' as [Hin' | [Hin' | Hin']].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin'. cbn in Hin'. destruct Hin' as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (HP2 r Hr). apply (v29_rv_in regs _ _ _ Hrv). apply in_or_app. left. exact Hin'.
- injection Hin' as <- <-. exact Htq10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin') as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (HP2 r Hr). apply (v29_rv_in regs _ _ _ Hrv). apply in_or_app. right. right. right. exact Hin'.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The registers at sup_resp's entry: ra the return pc, a0 the code, the callee-saved registers kept *)
Lemma v29_in15 : forall r, acallee_saved r -> In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Proof. intros r Hr. unfold acallee_saved in Hr. cbn [In]. lia. Qed.

Lemma v29_pres_of_kept : forall (regs regsc : bvmap 5 word),
(forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] ->
  getr regs (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
aregs_preserved regsc regs.
Proof. intros regs regsc H r Hr. exact (H r (v29_in15 r Hr)). Qed.

Lemma v29_rv_call : forall e (regs regsc : bvmap 5 word) rl rlk retpc code,
vr_rv regsc (vr_base B e ++ rl) ->
aregs_preserved regsc regs ->
getr regs (Z_to_bv 5 1) = w64 (vr_pc retpc) ->
getr regs (Z_to_bv 5 10) = w64 code ->
incl rlk rl -> Forall (fun rv => 18 <= fst rv <= 27) rlk ->
vr_rv regs (vr_base B e ++ (1, vr_pc retpc) :: (10, code) :: rlk).
Proof.
intros e regs regsc rl rlk retpc code Hrv Hpr H1 H10 Hinc Hcs.
apply v29_rv_intro. intros r v Hin. apply in_app_or in Hin as [Hin | [Hin | [Hin | Hin]]].
- assert (Hr : acallee_saved r).
  { unfold vr_base in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- _;
    unfold acallee_saved; lia. }
  rewrite (Hpr r Hr). apply (v29_rv_in regsc _ _ _ Hrv). apply in_or_app. left. exact Hin.
- injection Hin as <- <-. exact H1.
- injection Hin as <- <-. exact H10.
- assert (Hr : acallee_saved r).
  { rewrite Forall_forall in Hcs. pose proof (Hcs (r, v) Hin) as Hrr. cbn [fst] in Hrr. unfold acallee_saved. lia. }
  rewrite (Hpr r Hr). apply (v29_rv_in regsc _ _ _ Hrv). apply in_or_app. right. exact (Hinc _ Hin).
Qed.

Lemma v29_m902 : Z_to_bv 64 18446744073709550714 = w64 (-902).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Ltac v29_fa := cbv beta; repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; lia.

(* ------------------------------------------------------------------------------------------------------------
   The refusal stubs: from vr_pr at the stub, the run `li a0,-902; jal sup_resp` (0x8dca0: `jal sup_resp`) to
   sup_resp's entry (no memory read or written), then the call (v29_pr_call) *)
Ltac v29_pr_run HC W regsc memc srcpc srcoff :=
pose proof HC as (HJ & _ & _ & _ & _ & Hrv & _);
remember (Eimg (Ereg regsc [])) as E eqn:HE;
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
assert (HAE : env_agree 32 (Ereg regsc []) E) by (subst E; apply v29_env_agree_Eimg);
assert (HS : st_ok_pi SEGS VAL E (v29_ssr srcoff)
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + srcoff)) memc (seg_rom SEGS)))) by (subst E; apply v29_seed_r);
clear HE;
unfold cfg_at; change (w64 (vr_pc srcpc)) with (Z_to_bv 64 (BASE + srcoff));
paj_run_shc RUNP RUNC HS HJ;
[ apply awr_ok_nil
| lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end;
  let Hmem := fresh "Hmem" in
  lazymatch goal with
  | HFx : frame_of _ _ _ (ms_mem _) |- _ =>
    pose proof (frame_of_read_only _ _ _ _ (eq_refl : rs_read_only [] = true) HFx) as Hmem
  end;
  rewrite Hmem in HJ;
  let Q1 := fresh "Q1" in prreg HS (Z_to_bv 5 1) Q1;
  pose proof (v29_kept_regs E _ _ regsc [] [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] HS HAE
    ltac:(vm_compute; reflexivity)) as KR;
  cbn [ms_regs restrict] in KR;
  pmkst HS; rewrite Hmem;
  rewrite (SIGP CS_sup_resp ltac:(unfold cmd_prog_syms; v29_inl));
  change (cmd_af CS_sup_resp) with AF_sup_resp ].

Lemma v29_pr_a28 : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8da28 W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8da30 (fun F q c tq => (10, tq) :: [(18, q); (21, vr_ntok (e_D e)); (22, F + 32)])
  (vr_pr_ntok 0x8da28) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8da28 (-902)) with [(18, q); (21, vr_ntok (e_D e)); (22, F + 32)] in HC.
v29_pr_run HC W regsc memc 0x8da28 30020.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8da30 (fun F q c => [(18, q); (21, vr_ntok (e_D e)); (22, F + 32)]) (vr_pr_ntok 0x8da28)
  (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8da30 (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

Lemma v29_pr_acc : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8dacc W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8dad4 (fun F q c tq => (10, tq) :: [(18, q); (22, F + 32)])
  (vr_pr_ntok 0x8dacc) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8dacc (-902)) with [(18, q); (22, F + 32)] in HC.
v29_pr_run HC W regsc memc 0x8dacc 30184.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8dad4 (fun F q c => [(18, q); (22, F + 32)]) (vr_pr_ntok 0x8dacc)
  (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8dad4 (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

Lemma v29_pr_c9c : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8dc9c W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8dca4 (fun F q c tq => (10, tq) :: [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8dc9c) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8dc9c (-902))
  with [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8dc9c 30648.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8dca4
  (fun F q c => [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]) (vr_pr_ntok 0x8dc9c)
  (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8dca4 (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

Lemma v29_pr_ca0 : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8dca0 W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8dca4 (fun F q c tq => (10, tq) :: [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8dca0) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
change (vr_rl_pr e F q c 0x8dca0 code)
  with [(10, code); (18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8dca0 30652.
pose proof (v29_kept_regs E _ _ regsc [] [10] HS HAE ltac:(vm_compute; reflexivity)) as KR10.
cbn [ms_regs restrict] in KR10.
apply (v29_pr_call e 0x8dca4
  (fun F q c => [(18, q); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)]) (vr_pr_ntok 0x8dca0)
  code Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8dca4 code Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite (KR10 10 (or_introl eq_refl)).
    apply (v29_rv_in regsc _ 10 code Hrv). apply in_or_app. right. left. reflexivity.
  + intros x Hx. right. exact Hx.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

Lemma v29_pr_d34 : forall e W cf, vr_ent B MT e -> vr_pr B MT e 0x8dd34 W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\
  v29_hdX (fx := fq) B MT e 0x8dd3c (fun F q c tq => (10, tq) :: [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8dd34) W' cf').
Proof.
intros e W cf He H.
destruct H as (code & Rx & Ox & pos & F & q & c & tp & lyc & Sc & regsc & memc & mdc & k & nm &
  -> & Hc902 & Hcode & Hh & Htk & Hntk & HC & Hline & Hcopy).
assert (E902 : code = -902) by (apply Hc902; discriminate). subst code.
change (vr_rl_pr e F q c 0x8dd34 (-902))
  with [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)] in HC.
v29_pr_run HC W regsc memc 0x8dd34 30800.
prreg HS (Z_to_bv 5 10) Q10.
apply (v29_pr_call e 0x8dd3c
  (fun F q c => [(18, q); (19, c); (20, F); (21, vr_ntok (e_D e)); (22, F + 32); (27, shadow_addr F + 4)])
  (vr_pr_ntok 0x8dd34)
  (-902) Rx Ox pos F q c tp lyc Sc W (ms_regs ms) memc mdv k nm He Hh Hcode Hntk).
- apply (v29_core_regs B MT e pos F _ _ _ _ _ _ _ _ _ _ _ _ lyc Sc W regsc memc mdc (ms_regs ms) mdv HC HJ).
  apply (v29_rv_call e (ms_regs ms) regsc _ _ 0x8dd3c (-902) Hrv (v29_pres_of_kept _ _ KR) Q1).
  + rewrite Q10. exact v29_m902.
  + apply incl_refl.
  + v29_fa.
- exact Hline.
- exact Hcopy.
- unfold AF_verbs_receive; lia.
- reflexivity.
- v29_fa.
Qed.

(* ------------------------------------------------------------------------------------------------------------
   The ten pieces of S29: a refusal stub runs at fx up to sup_resp, the move after the call at the FP state fq the
   call returned (section d0's move lemma at fq); the move stubs run at fx *)
Lemma v29_seg_a28 : vr_segF B MT (vr_atpr B MT 0x8da28) (vrF_hd B MT 0x8da34).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_a28 e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2). eapply SRr_mono; [exact (v29_mv_a30 (fx := fq) B MT _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx | exact H3].
Qed.

Lemma v29_seg_acc : vr_segF B MT (vr_atpr B MT 0x8dacc) (vrF_hd B MT 0x8dad4).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_pr_acc e W cf He H)|].
intros W3 c3 _ (fq & Hfx & H3). exists fq. split; [exact Hfx | exact H3].
Qed.

Lemma v29_seg_c9c : vr_segF B MT (vr_atpr B MT 0x8dc9c) (vrF_hd B MT 0x8da40).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_c9c e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2). eapply SRr_mono; [exact (v29_mv_ca4 (fx := fq) B MT _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx | exact H3].
Qed.

Lemma v29_seg_ca0 : vr_segF B MT (vr_atpr B MT 0x8dca0) (vrF_hd B MT 0x8da40).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_ca0 e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2). eapply SRr_mono; [exact (v29_mv_ca4 (fx := fq) B MT _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx | exact H3].
Qed.

Lemma v29_seg_d34 : vr_segF B MT (vr_atpr B MT 0x8dd34) (vrF_hd B MT 0x8da44).
Proof.
intros e W cf He H. eapply SRr_bind; [exact (v29_pr_d34 e W cf He H)|].
intros W2 c2 _ (fq & Hfx & H2). eapply SRr_mono; [exact (v29_mv_d3c (fx := fq) B MT _ e W2 c2 H2)|].
intros W3 c3 _ H3. exists fq. split; [exact Hfx | exact H3].
Qed.

Lemma v29_seg_c34 : vr_seg B MT (vr_athd B MT 0x8dc34) (vr_athd B MT 0x8dae4).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_mv_c34 (fx := fx) B MT (vr_hd_ntok 0x8dc34) e W cf H)|].
intros W3 c3 _ H3. exact H3.
Qed.

Lemma v29_seg_c54 : vr_seg B MT (vr_athd B MT 0x8dc54) (vr_athd B MT 0x8da44).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_mv_c54 (fx := fx) B MT (vr_hd_ntok 0x8dc54) e W cf H)|].
intros W3 c3 _ H3. exact H3.
Qed.

Lemma v29_seg_c94 : vr_seg B MT (vr_athd B MT 0x8dc94) (vr_athd B MT 0x8dae0).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_mv_c94 (fx := fx) B MT (vr_hd_ntok 0x8dc94) e W cf H)|].
intros W3 c3 _ H3. exact H3.
Qed.

Lemma v29_seg_ca4 : vr_seg B MT (vr_athd B MT 0x8dca4) (vr_athd B MT 0x8da40).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_mv_ca4 (fx := fx) B MT (vr_hd_ntok 0x8dca4) e W cf H)|].
intros W3 c3 _ H3. exact H3.
Qed.

Lemma v29_seg_d3c : vr_seg B MT (vr_athd B MT 0x8dd3c) (vr_athd B MT 0x8da44).
Proof.
intros e W cf He H. eapply SRr_mono; [exact (v29_mv_d3c (fx := fx) B MT (vr_hd_ntok 0x8dd3c) e W cf H)|].
intros W3 c3 _ H3. exact H3.
Qed.

Lemma vr_s29 : vr_s29_stmt B MT.
Proof.
exact (conj v29_seg_a28 (conj v29_seg_acc (conj v29_seg_c9c (conj v29_seg_ca0 (conj v29_seg_d34
  (conj v29_seg_c34 (conj v29_seg_c54 (conj v29_seg_c94 (conj v29_seg_ca4 v29_seg_d3c))))))))).
Qed.

End e.
End f.
End d.
