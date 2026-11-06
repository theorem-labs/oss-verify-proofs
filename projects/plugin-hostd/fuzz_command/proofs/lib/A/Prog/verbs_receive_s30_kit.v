(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the kit of the segments S05 (EMPTY) and S30 (JOIN) of the walk of verbs_receive
   on the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_iface.v): the symbolic state seeded at a
   boundary (the registers as atoms, cgif's AChc.v ss_cl; the spill slots one region of the real frame, each slot a
   chunk whose value is an extra atom of the environment), a boundary state moved across a run of plain instructions
   (no store: the memory the run leaves reads as before), the read-only facts of vr_env rebuilt at any allocator state
   from arodata_okP (the interface's ROA and RECC), and the call of reply(fd, text) at the joins through
   cl_callS_wide (PaNoChain.v) and the statement's TREPLY. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCallRun PaCall PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdObj CmdRo CmdBase CmdRep CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import socket_send_c reply_c sup_resp_c xstrdup_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import arg_i_c sup_after_reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_s30_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------
   The symbolic state at a boundary: the registers as atoms (sr_atoms), the spill slots of the real frame as one
   region based at s1 (atom 9), offsets [0, 80), no store window; the i-th listed slot is a chunk whose value is the
   atom 32 + i of the environment *)
Fixpoint vr_chunks (n : nat) (offs : list Z) : list YP09.chunk :=
match offs with
| [] => []
| o :: t => YP09.mkChunk o (CVal 8 (SOff n 0)) :: vr_chunks (S n) t
end.
Definition vr_rg (offs : list Z) : YP09.region := YP09.mkRegion (Some 9%nat) 0 80 0 0 (vr_chunks 32 offs).
Definition vr_vals (sl : list (Z * Z)) : list word := map (fun ov => w64 (snd ov)) sl.
Definition vr_ss (pc : Z) (offs : list Z) : sstate := mkSS pc sr_atoms [vr_rg offs] None (mkFacts [] [] []).

(* a list of disjoint blocks has no duplicate *)
Lemma vr_pw_nodup : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) ->
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> List.NoDup l.
Proof.
induction l as [|x l IH]; intros Hn Hp; [constructor|].
cbn in Hp. destruct Hp as [Hf Hp]. constructor.
- intros Hin. rewrite Forall_forall in Hf.
  specialize (Hf (fst x, req_size (snd x)) (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin)).
  unfold zdisjoint in Hf. cbn in Hf. pose proof (req_size_pos (snd x) (Hn x (or_introl eq_refl))). lia.
- apply IH; [intros b Hb; apply Hn; right; exact Hb | exact Hp].
Qed.
Lemma vr_nodup_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1 l2 x. induction l1 as [|y l1 IH]; intros Hn H1 H2; [destruct H1|].
cbn in Hn. inversion Hn as [|y' l' Hy Hn' E]; subst.
destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH Hn' H1 H2)].
Qed.
Lemma vr_nodup_app_l : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l1.
Proof.
intros X l1 l2. induction l1 as [|y l1 IH]; intros Hn; [constructor|].
cbn in Hn. inversion Hn as [|y' l' Hy Hn' E]; subst. constructor; [|exact (IH Hn')].
intros H. apply Hy. apply in_or_app. left. exact H.
Qed.
Lemma vr_nodup_app_r : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1 l2. induction l1 as [|y l1 IH]; intros Hn; [exact Hn|].
cbn in Hn. inversion Hn; subst. exact (IH H2).
Qed.

Lemma vr_bsum_nonneg : forall l : list (Z * Z), (forall b, In b l -> 0 <= snd b) -> 0 <= bsum l.
Proof.
induction l as [|x l IH]; intros Hp; cbn [bsum fold_right]; [lia|].
pose proof (Hp x (or_introl eq_refl)). assert (0 <= bsum l) by (apply IH; intros b Hb; apply Hp; right; exact Hb).
unfold bsum in *. lia.
Qed.
(* a bound of the sum of the sizes of a duplicate-free sublist *)
Lemma vr_bsum_incl : forall l1 l2 : list (Z * Z), List.NoDup l1 -> incl l1 l2 -> (forall b, In b l2 -> 0 <= snd b) ->
bsum l1 <= bsum l2.
Proof.
induction l1 as [|x l1 IH]; intros l2 Hn Hi Hp.
- cbn [bsum fold_right]. exact (vr_bsum_nonneg l2 Hp).
- inversion Hn as [|x' l' Hx Hn' E]; subst.
  assert (Hx2 : In x l2) by (apply Hi; left; reflexivity).
  apply in_split in Hx2 as (a & b & ->).
  rewrite bsum_cons, bsum_app, bsum_cons.
  assert (H : bsum l1 <= bsum (a ++ b)).
  { apply IH; [exact Hn'| |].
    - intros y Hy. assert (Hy2 : In y (a ++ x :: b)) by (apply Hi; right; exact Hy).
      apply in_app_iff in Hy2 as [Hy2 | [<- | Hy2]]; [apply in_or_app; left; exact Hy2 | contradiction | apply in_or_app; right; exact Hy2].
    - intros y Hy. apply Hp. apply in_app_iff in Hy as [Hy|Hy]; apply in_or_app; [left | right; right]; exact Hy. }
  rewrite bsum_app in H. lia.
Qed.
Lemma vr_bsum_le : forall (l : list (Z * Z)) m, (forall b, In b l -> snd b <= m) -> bsum l <= m * Z.of_nat (length l).
Proof.
induction l as [|x l IH]; intros m Hm; cbn [bsum fold_right length]; [lia|].
pose proof (Hm x (or_introl eq_refl)). assert (bsum l <= m * Z.of_nat (length l)) by (apply IH; intros b Hb; apply Hm; right; exact Hb).
unfold bsum in *. lia.
Qed.

(* a reader that agrees everywhere *)
Lemma vr_rdword_eq : forall (rd rd' : reader) a, (forall x, rd' x = rd x) -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a H. apply rdword_ext. intros k _. apply H. Qed.
Definition vr_pdec : forall u v : Z * Z, {u = v} + {u <> v}.
Proof. decide equality; apply Z.eq_dec. Defined.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the bytes a reader of the memory sees, as the machine's byte view *)
Lemma vr_val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (rdW W mem) a n v -> YI04.val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Hb; cbn [option_map] in H; [|discriminate].
injection H as H. f_equal. replace (YO0f.le_byte v n k) with (YG0f.le_byte v n k) by reflexivity.
rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* a run that stores nothing leaves a memory that reads as before *)
Lemma vr_no_wrange : forall E (rs : smem), Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> forall a, ~ in_wrange E rs a.
Proof.
intros E rs H a (r & Hr & Ha). rewrite Forall_forall in H. specialize (H r Hr). lia.
Qed.
Lemma vr_rdW_frame : forall E rs (W : world SEGS) m m',
frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> (forall a, ~ in_wrange E rs a) ->
forall a, rdW W m' a = rdW W m a.
Proof. intros E rs W m m' HF HW a. unfold aview, mbyte. rewrite (HF (Z_to_bv 64 a) (HW _)). reflexivity. Qed.

(* the spill region is well formed and holds the slots the boundary names *)
Lemma vr_chunks_ok : forall E m base (sl : list (Z * Z)) n,
(forall j ov, nth_error sl j = Some ov -> ew E (n + j)%nat = w64 (snd ov) /\ 0 <= snd ov < 2 ^ 64 /\
  YI04.val_mem SEGS m (base + fst ov) 8 (snd ov)) ->
Forall (YP09.chunk_ok SEGS E m base) (vr_chunks n (map fst sl)).
Proof.
induction sl as [|ov sl IH]; intros n H; cbn [map vr_chunks]; constructor.
- destruct (H 0%nat ov eq_refl) as (H1 & H2 & H3). rewrite Nat.add_0_r in H1.
  apply (YI04.chunk_ok_val SEGS E m base (fst ov) 8%N (SOff n 0) (snd ov)).
  + rewrite denot_lit_U. unfold w64 in H1. rewrite (U_atom E n (snd ov) H1 H2). reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + change (Z.of_N 8) with 8. lia.
  + exact H3.
- apply IH. intros j ov' Hj. replace (S n + j)%nat with (n + S j)%nat by lia. exact (H (S j) ov' Hj).
Qed.

Lemma vr_seed : forall (B : asyms) (e : vrE) (W : world SEGS) (regs : bvmap 5 word) mem pc (sl : list (Z * Z)) (extra : list word),
vr_rv regs (vr_base B e) ->
regions_wf [vr_rg (map fst sl)] = true -> (length sl + 32 < A_TEXT)%nat ->
0 <= vr_s1 e -> vr_s1 e + 80 <= 2 ^ 64 ->
vr_spill e W mem sl -> Forall (fun ov => 0 <= snd ov < 2 ^ 64) sl ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (vr_vals sl ++ extra))) (vr_ss pc (map fst sl))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros B e W regs mem pc sl extra HR Hwf Hlen Hs0 Hs80 HSp Hvr.
rewrite restrict_mkst_fx. unfold vr_ss. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil].
  unfold YP09.region_ok, vr_rg. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  assert (H9r : getr regs (Z_to_bv 5 9) = w64 (vr_s1 e)).
  { unfold vr_rv in HR. rewrite Forall_forall in HR. exact (HR (9, vr_s1 e) ltac:(unfold vr_base; cbn; tauto)). }
  assert (H9 : bv_unsigned (ew (Eimg (Ereg regs (vr_vals sl ++ extra))) 9) = vr_s1 e).
  { rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl).
    rewrite H9r. unfold w64. apply unsigned_lit_small. lia. }
  rewrite H9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply vr_chunks_ok. intros j ov Hj.
  assert (Hjl : (j < length sl)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  split; [|split].
  + rewrite Eimg_low by (clear - Hjl Hlen; unfold A_TEXT in *; lia). unfold Ereg. cbn [ew].
    replace ((32 + j <? 32)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
    replace (32 + j - 32)%nat with j by lia. rewrite app_nth1 by (unfold vr_vals; rewrite length_map; exact Hjl).
    unfold vr_vals. change (Z_to_bv 64 0) with ((fun ov0 : Z * Z => w64 (snd ov0)) (0, 0)).
    rewrite map_nth. cbv beta. erewrite nth_error_nth by exact Hj. reflexivity.
  + rewrite Forall_forall in Hvr. exact (Hvr ov (nth_error_In _ _ Hj)).
  + apply vr_val_mem_of_aval. unfold vr_spill in HSp. rewrite Forall_forall in HSp. exact (HSp ov (nth_error_In _ _ Hj)).
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

(* registers of a boundary list *)
Lemma vr_rv_get : forall (regs : bvmap 5 word) l r v, vr_rv regs l -> In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v.
Proof. intros regs l r v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (r, v) Hin). Qed.
Lemma vr_rv_app : forall (regs : bvmap 5 word) l1 l2, vr_rv regs (l1 ++ l2) <-> vr_rv regs l1 /\ vr_rv regs l2.
Proof. intros regs l1 l2. unfold vr_rv. rewrite Forall_app. tauto. Qed.
Lemma vr_rv_preserved : forall (regs regs' : bvmap 5 word) l, aregs_preserved regs regs' ->
Forall (fun rv => acallee_saved (fst rv)) l -> vr_rv regs l -> vr_rv regs' l.
Proof.
intros regs regs' l HP Hcs H. unfold vr_rv in *. rewrite Forall_forall in *. intros rv Hin.
rewrite (HP (fst rv) (Hcs rv Hin)). exact (H rv Hin).
Qed.
Lemma vr_base_cs : forall B e, Forall (fun rv => acallee_saved (fst rv)) (vr_base B e).
Proof. intros B e. unfold vr_base, acallee_saved. repeat constructor; cbn [fst]; lia. Qed.

(* the saved registers and the frame chain: the caller's chain with verbs_receive's own record on top (s0 = sp0,
   ra at sp0-8, the caller's s0 at sp0-16) *)
Lemma vr_saved_word : forall (e : vrE) (W : world SEGS) mem j r, vr_saved e W mem -> nth_error vr_saved_regs j = Some r ->
rdword (rdW W mem) (vr_sp0 e - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (e_regs e) (Z_to_bv 5 r))).
Proof.
intros e W mem j r H Hj. apply rdword_of_val_mem; [apply vr_val_mem_of_aval; exact (H j r Hj) |].
pose proof (bv_unsigned_in_range 64 (getr (e_regs e) (Z_to_bv 5 r))) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb. exact Hb.
Qed.

(* the events: the handler leaves at least 5 events of the budget (the reply's 3 and the two frees) *)
Lemma vr_k1_ev : forall R D, vr_k1 R D + 5 <= ev_vr R D.
Proof.
intros R D. rewrite ev_vr_eq. unfold vr_k3, vr_k2, ev_after, EV_REPLY, EV_SOCKET_SEND.
destruct (vr_aft D) as [[i v]|]; [|lia].
unfold EV_SUP_AFTER_REPLY, rec_spill_frees, EV_ARG_I, EV_XSTRDUP. destruct (Nat.ltb _ _); lia.
Qed.

(* the symbolic runs: a state that names only the registers; the regions of vr_ss store nothing; the registers a run
   keeps; the boundary lists of registers *)
Definition vr_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Lemma vr_seed0 : forall (W : world SEGS) (regs : bvmap 5 word) mem pc,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (vr_ss0 pc) (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold vr_ss0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Lemma vr_ss_ro : forall pc offs, Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem (vr_ss pc offs)).
Proof. intros pc offs. cbv [vr_ss vr_rg]. cbn. apply Forall_cons; [cbn; lia | apply Forall_nil]. Qed.
Lemma vr_kept_regs : forall E ss ms (regs0 : bvmap 5 word) extra (zs : list Z),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) (map (Z_to_bv 5) zs) = true ->
forall r, In r zs -> getr (ms_regs ms) (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r).
Proof.
intros E ss ms regs0 extra zs HS HA Hl r Hr.
apply (regs_kept_of_st_ok SEGS E ss ms regs0 extra (map (Z_to_bv 5) zs) HS HA Hl). apply in_map. exact Hr.
Qed.
Lemma vr_env_agree : forall (regs : bvmap 5 word) extra, env_agree 32 (Ereg regs extra) (Eimg (Ereg regs extra)).
Proof. intros regs extra. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma vr_rv_intro : forall (regs : bvmap 5 word) l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
(* the line, the copy and a string at a memory that reads the same *)
Lemma vr_aval_eq : forall (rd rd' : reader) a n v, (forall x, rd' x = rd x) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma vr_astr_eq : forall (rd rd' : reader) a s, (forall x, rd' x = rd x) -> astr_atR rd a s -> astr_atR rd' a s.
Proof. intros rd rd' a s E [H1 H2]. split; [intros i Hi; rewrite E; exact (H1 i Hi) | exact H2]. Qed.
Lemma vr_toks_eq : forall (rd rd' : reader) tok ptrs tks cb ncb, (forall x, rd' x = rd x) ->
atoks_atA rd tok ptrs tks cb ncb -> atoks_atA rd' tok ptrs tks cb ncb.
Proof.
intros rd rd' tok ptrs tks cb ncb E (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
- intros i p Hp. exact (vr_aval_eq rd rd' _ 8 p E (H3 i p Hp)).
- intros i p w Hp Hw. destruct (H4 i p w Hp Hw) as (A1 & A2 & A3 & A4).
  split; [exact (vr_astr_eq rd rd' p w E A1) | auto].
Qed.
Lemma vr_line_eq : forall B e q (W : world SEGS) m m', (forall a, rdW W m' a = rdW W m a) ->
vr_line B e q W m -> vr_line B e q W m'.
Proof. intros B e q W m m' E [H1 H2]. split; [exact H1 | exact (vr_astr_eq _ _ q _ E H2)]. Qed.
Lemma vr_copy_eq : forall B e F c tp (W : world SEGS) m m', (forall a, rdW W m' a = rdW W m a) ->
vr_copy B e F c tp W m -> vr_copy B e F c tp W m'.
Proof. intros B e F c tp W m m' E [H1 H2]. split; [exact H1 | exact (vr_toks_eq _ _ _ _ _ _ _ E H2)]. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis RRO : vr_relro_img.
Hypothesis RPG : vr_pg_not_ro.
Hypothesis RECC : vr_rec_cells B.
Hypothesis PROGU : vr_prog_unowned B.
Hypothesis ROA : vr_ro_of_aro B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* every lemma below takes all the section's hypotheses declared before it, so that the segment files apply them
   with a fixed list of arguments *)
Local Set Default Proof Using "All".

Lemma vr_ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply vr_pw_nodup.
- intros [p n] Hb. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hb) as (_ & _ & _ & _ & _ & _ & Hn). cbn. lia.
- destruct (al_sep _ _ LAWS _ _ _ _ _ HAR) as [Hp _]. apply pairwise_app_l in Hp as [Hp _]. exact Hp.
Qed.

(* the GOT words are in cmd_ro_ok (CmdRo.v RO_ptr_a7068 .. RO_ptr_a7080) *)
Lemma vr_aval_of_bytes : forall (rd : reader) a (l : list byte) v,
abytes_atR rd a l -> length l = 8%nat -> (forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) ->
aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hk8. rewrite (H k ltac:(lia)). rewrite Hk by exact Hk8. reflexivity. Qed.
Lemma vr_got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb. decompose [and] Hb. clear Hb.
unfold cmd_got_ok. split; [|split; [|split]];
(eapply vr_aval_of_bytes; [eassumption | reflexivity |];
 intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia).
Qed.

(* vr_env at any allocator state where arodata_okP holds: ROA gives cmd_ro_ok, which holds cmd_got_ok's words, and
   RECC the runtime's cells *)
Lemma vr_env_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> vr_env B W mem.
Proof.
intros ly S W mem md HAR HRO.
pose proof (ROA ly S W mem md HAR HRO) as HC. destruct (RECC ly S W mem md HAR) as (H1 & H2 & H3).
split; [exact HRO|]. split; [exact (vr_got_of_ro _ HC)|]. split; [exact HC|].
split; [exact H2|]. split; [exact H1 | exact H3].
Qed.

(* a boundary state across a run of plain instructions that stores nothing: the journal is the run's, the readers
   agree, the registers are the run's *)
Lemma vr_core_move : forall e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md sl' rl' kmax' nmax' regs' mem' md',
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W mem' md' k ->
(forall a, rdW W mem' a = rdW W mem a) ->
vr_rv regs' (vr_base B e ++ rl') -> incl sl' sl -> kmax <= kmax' -> nmax <= nmax' ->
vr_core B MT e pos F tmps sh sl' rl' Rc Oc qv k kmax' nm nmax' lyc Sc W regs' mem' md'.
Proof.
intros e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regs mem md sl' rl' kmax' nmax' regs' mem' md'
(HJ & Hk & HM & Hn & HFr & HR & HSv & HSp & HEnv & HRec & HD & HP & HQ) HJ' Heq HR' Hsl Hk' Hn'.
assert (Hav : forall a n v, aval_mem (rdW W mem) a n v -> aval_mem (rdW W mem') a n v).
{ intros a n v H kk Hkk. rewrite Heq. exact (H kk Hkk). }
split; [exact HJ'|]. split; [lia|]. split; [exact HM|]. split; [lia|].
split.
{ destruct HFr as (HF1 & HF2 & HF3). split; [exact HF1|]. split; [rewrite (vr_rdword_eq _ _ _ Heq); exact HF2|].
  intros i Hi. rewrite Heq. exact (HF3 i Hi). }
split; [exact HR'|].
split; [intros j r Hj; apply Hav; exact (HSv j r Hj)|].
split; [unfold vr_spill in *; rewrite Forall_forall in *; intros ov Hov; apply Hav; apply HSp; apply Hsl; exact Hov|].
split.
{ destruct HEnv as (HRO & _). apply (vr_env_of_aro lyc Sc W mem' md' (proj1 HJ')).
  intros a H1 H2 H3. rewrite Heq. exact (HRO a H1 H2 H3). }
split; [apply (rec_repA_agree B lyc Sc lyc Sc (rdW W mem) (rdW W mem') Rc Oc HRec); [intros pn _ H; exact H | intros; apply Heq ..]|].
split; [exact HD|]. split; [exact HP|]. apply Hav. exact HQ.
Qed.

(* the footprint of verbs_receive: the program's statics and the recorder's entry blocks *)
Lemma vr_fp_cases : forall e a, inFP (vr_fp e) a ->
inFP cmd_PG a \/ exists p n, In (p, n) (e_O e) /\ p <= a < p + req_size n.
Proof.
intros e a Ha. unfold vr_fp in Ha. apply inFP_app in Ha as [Ha | Ha].
- left. exact Ha.
- right. exact (inFP_ablocks_fp_inv _ _ Ha).
Qed.
Lemma vr_ent_O : forall e, vr_ent B MT e -> forall pn, In pn (e_O e) -> In pn (ablocks B (e_ly e) (e_S e)).
Proof.
intros e He pn Hpn. unfold vr_ent in He. cbv zeta in He.
destruct He as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hpn.
Qed.
Lemma vr_fp_low : forall e, vr_ent B MT e -> forall a, inFP (vr_fp e) a -> 4096 <= a < alloc_ceiling.
Proof.
intros e He a Ha. pose proof asan_consts as (C1 & _).
pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'. destruct He' as ((HAR0 & _) & _).
destruct (vr_fp_cases e a Ha) as [Hg | (p & n & Hpn & Hr)].
- unfold cmd_PG, A_G_REC, A_REC_SPILL, A_G_QUITTING in Hg.
  apply inFP_cons in Hg as [Hg | Hg]; [lia|]. apply inFP_cons in Hg as [Hg | Hg]; [lia|].
  apply inFP_cons in Hg as [Hg | Hg]; [lia | exact (False_ind _ (inFP_nil a Hg))].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 (vr_ent_O e He _ Hpn)) as (_ & H4096 & Hc & _). lia.
Qed.
Lemma vr_fp_closed : forall e, vr_ent B MT e -> ~ YI16.sink_open_fp (vr_fp e).
Proof.
intros e He H0. pose proof (vr_fp_low e He 0 H0). lia.
Qed.

Lemma vr_chain_at : forall e lyc Sc (W : world SEGS) mem md k pos (regs : bvmap 5 word),
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc W mem md k ->
vr_saved e W mem -> getr regs 8 = w64 (vr_sp0 e) ->
exists ch1, achain lyc (rdW W mem) (vr_s1 e) (s0Z regs) ch1.
Proof.
intros e lyc Sc W mem md k pos regs He HJ HSv H8.
pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'. destruct He' as (HPRE & _).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _).
assert (Hs0 : s0Z regs = vr_sp0 e).
{ unfold s0Z. rewrite H8. unfold w64, vr_sp0. apply unsigned_lit_small. lia. }
rewrite Hs0. unfold vr_sp0 in *.
assert (Hs1 : vr_s1 e + 16 <= spZ (e_regs e)).
{ unfold vr_s1, vr_sp0. pose proof (Z.mod_pos_bound (spZ (e_regs e) - 192) 32 ltac:(lia)). lia. }
destruct (Z_lt_le_dec (spZ (e_regs e)) (ly_top (e_ly e) - 16)) as [Hlt | Hge].
- exists ((spZ (e_regs e), raZ (e_regs e), s0Z (e_regs e)) :: e_ch e).
  apply (achain_ly_top (e_ly e) lyc); [exact Etop|].
  apply (achain_push (e_ly e) (rdW (e_W e) (e_mem e)) (rdW W mem) (spZ (e_regs e)) (s0Z (e_regs e)) (raZ (e_regs e))
    (e_ch e) (vr_s1 e) Hch0).
  + lia.
  + intros a Ha. apply F1; [lia | lia |]. intros Hf. pose proof (vr_fp_low e He a Hf). lia.
  + pose proof (vr_saved_word e W mem 0 1 HSv eq_refl) as R0.
    replace (vr_sp0 e - 8 - 8 * Z.of_nat 0) with (spZ (e_regs e) - 8) in R0 by (unfold vr_sp0; lia).
    unfold raZ. exact R0.
  + pose proof (vr_saved_word e W mem 1 8 HSv eq_refl) as R1.
    replace (vr_sp0 e - 8 - 8 * Z.of_nat 1) with (spZ (e_regs e) - 16) in R1 by (unfold vr_sp0; lia).
    unfold s0Z. exact R1.
  + exact Hra40.
  + lia.
  + rewrite Z.mod_divide in Hal16 by lia. apply Z.mod_divide; [lia|]. destruct Hal16 as [z Hz]. exists (2 * z). lia.
  + exact Hlt.
  + exact Hs1.
- exists []. left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* arodata_okP at a state of the journal from the entry: the read-only bytes are image bytes outside the footprint *)
Lemma vr_aro_kept : forall e own lyc Sc (W : world SEGS) mem md k,
vr_ent B MT e ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) own lyc Sc W mem md k ->
arodata_okP SEGS RLO RHI B (rdW W mem).
Proof.
intros e own lyc Sc W mem md k He HJ.
pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'. destruct He' as ((HAR0 & _) & HROD & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Ha Hown Herr.
assert (Himg : in_img SEGS a) by (destruct Ha as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)]).
rewrite (F3 a Himg Hown Herr); [exact (HROD a Ha Hown Herr)|].
apply fp_spares_closed; [exact (vr_fp_closed e He)|].
intros Hf. destruct (vr_fp_cases e a Hf) as [Hg | (p & n & Hpn & Hr)].
- exact (RPG a Hg Ha).
- exact (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR0 (vr_ent_O e He _ Hpn) Hr Himg).
Qed.

(* the parts of a permutation of the live blocks *)
Lemma vr_perm_nodup : forall ly S (W : world SEGS) mem md l, AR SEGS B ly S W mem md ->
Permutation (ablocks B ly S) l -> List.NoDup l.
Proof. intros ly S W mem md l HAR HP. exact (Permutation_NoDup HP (vr_ablocks_nodup ly S W mem md HAR)). Qed.
Lemma vr_nodup_app : forall {X} (l1 l2 : list X), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
List.NoDup (l1 ++ l2).
Proof.
intros X l1 l2. induction l1 as [|y l1 IH]; intros H1 H2 Hd; [exact H2|].
inversion H1 as [|y' l' Hy H1' E]; subst. cbn. constructor.
- intros Hin. apply in_app_iff in Hin as [Hin|Hin]; [exact (Hy Hin) | exact (Hd y (or_introl eq_refl) Hin)].
- apply IH; [exact H1' | exact H2 | intros z Hz; apply Hd; right; exact Hz].
Qed.
Lemma vr_fp1_cases : forall (L : list (Z * Z)) a, inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp L) a ->
(A_G_REC <= a < A_G_REC + REC_SIZE) \/ exists p n, In (p, n) L /\ p <= a < p + req_size n.
Proof.
intros L a Ha. apply inFP_cons in Ha as [Ha | Ha]; [left; exact Ha | right; exact (inFP_ablocks_fp_inv _ _ Ha)].
Qed.
Lemma vr_grec_img : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> in_img SEGS a.
Proof.
intros a Ha. apply (proj1 (PROGU a ltac:(unfold cmd_PG; apply inFP_cons; left; unfold REC_SIZE in Ha; lia))).
Qed.

(* the sum of the sizes of the recorder's own blocks: at most 20 blocks (<= 6 per recorded call, <= 2 calls, plus
   the spill's 6, the answer and the reply), each <= LMAX + 2 *)
Lemma vr_concat_len : forall (ls : list (list (Z * Z))) m, (forall P, In P ls -> (length P <= m)%nat) ->
(length (concat ls) <= m * length ls)%nat.
Proof.
induction ls as [|P ls IH]; intros m Hm; cbn [concat length]; [lia|].
rewrite length_app. pose proof (Hm P (or_introl eq_refl)).
assert (length (concat ls) <= m * length ls)%nat by (apply IH; intros Q HQ; apply Hm; right; exact HQ).
rewrite Nat.mul_succ_r. lia.
Qed.
(* each block the recorder's layout names: size in [0, LMAX + 2] *)
Lemma vr_arep_block_sz : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) -> 0 <= snd pn <= LMAX + 2.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HRp & _) Hin.
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  destruct HC as (_ & C2 & _ & C4 & _).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & _ & HlP & _ & _ & _ & Hargs) & _).
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
  destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HC as (_ & _ & _ & _ & (_ & _ & HlP & _ & _ & _ & Hargs) & _).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Hs; [|apply nth_error_Some in Hk'; contradiction].
    destruct (Hargs k s pn Hs Hk) as (_ & _ & _ & Hsz & _). lia.
  + apply in_app_or in Hin as [Hin | Hin].
    * unfold aanswer_at in HA. destruct (l_answer Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R); [|contradiction]. destruct HA as (_ & _ & _ & Hsz & _). lia.
    * unfold areply_at in HRp. destruct (l_reply Q) as [pn'|]; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R); [|contradiction]. destruct HRp as (_ & _ & _ & _ & _ & Hsz & _). lia.
Qed.
(* the recorder's layout holds at most 20 blocks when it holds at most 2 calls (6 args each, 6 spill, 1 answer, 1 reply) *)
Lemma vr_lay_len : forall bl rd gr sc R Q, arep_at bl rd gr sc R Q -> (length (r_calls R) <= 2)%nat ->
(length (lay_blocks Q) <= 20)%nat.
Proof.
intros bl rd gr sc R Q (_ & _ & _ & HC & _ & _ & _) Hc2.
pose proof HC as (Hc16 & C2 & _ & C4 & C5 & _).
unfold lay_blocks. rewrite !length_app.
assert (Hcc : (length (concat (l_calls Q)) <= 6 * length (l_calls Q))%nat).
{ apply vr_concat_len. intros P HP. apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- C2; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|apply nth_error_Some in Hi'; contradiction].
  destruct (C4 i c P Hc Hi) as ((_ & Hn6 & HlP & _) & _). lia. }
rewrite C2 in Hcc.
assert (Hsp : (length (l_spill Q) <= 6)%nat) by (destruct C5 as (_ & Hspn6 & Hspl & _); lia).
destruct (l_answer Q); destruct (l_reply Q); cbn [oblk length]; lia.
Qed.
Lemma vr_rec_bsum : forall ly S (rd : reader) R O, rec_repA B ly S rd R O ->
List.NoDup O -> (length (r_calls R) <= 2)%nat -> bsum O <= 20 * (LMAX + 2).
Proof.
intros ly S rd R O (Q & HA & HOQ) Hnd Hc2.
assert (Hle : bsum O <= bsum (lay_blocks Q)).
{ apply vr_bsum_incl; [exact Hnd | intros pn Hpn; apply HOQ; exact Hpn |].
  intros pn Hpn. exact (proj1 (vr_arep_block_sz _ _ _ _ _ _ pn HA Hpn)). }
assert (Hb : bsum (lay_blocks Q) <= (LMAX + 2) * Z.of_nat (length (lay_blocks Q))).
{ apply vr_bsum_le. intros pn Hpn. exact (proj2 (vr_arep_block_sz _ _ _ _ _ _ pn HA Hpn)). }
pose proof (vr_lay_len _ _ _ _ _ _ HA Hc2) as Hlen.
assert (Z.of_nat (length (lay_blocks Q)) <= 20) by lia. unfold LMAX in *. lia.
Qed.

(* the live bytes at a join (the three tmp blocks): the recorder's <= 20 blocks, the line (<= 8193), the copy
   (<= 8193) and the reply text (<= 4097), over the entry's budget *)
Lemma vr_hd_live : forall e pos F q c tq nx' sh sl rl Rc O1 qv k kmax nm nmax lyc Sc W regs mem md,
vr_ent B MT e ->
vr_core B MT e pos F [(tq, nx'); vr_lb e q; vr_cb e c] sh sl rl Rc O1 qv k kmax nm nmax lyc Sc W regs mem md ->
(length (r_calls Rc) <= 2)%nat -> nx' <= 4097 ->
blocks_bytes Sc + LIVE_REPLY <= LIVE_MAX.
Proof.
intros e pos F q c tq nx' sh sl rl Rc O1 qv k kmax nm nmax lyc Sc W regs mem md He Hcore Hc2 Hnx.
pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'.
destruct He' as ((HAR0 & _) & _ & _ & _ & _ & _ & _ & Hn8 & HlenD & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlive0 & _).
pose proof Hcore as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & HRec & _ & HP & _).
pose proof (proj1 HJ) as HAR.
rewrite (blocks_bytes_bsum B lyc Sc). rewrite (bsum_perm _ _ HP).
rewrite !bsum_app.
assert (HND : List.NoDup (O1 ++ [(tq, nx'); vr_lb e q; vr_cb e c] ++ e_rest e)) by exact (vr_perm_nodup lyc Sc W mem md _ HAR HP).
assert (HndO1 : List.NoDup O1) by exact (vr_nodup_app_l _ _ HND).
pose proof (vr_rec_bsum lyc Sc (rdW W mem) Rc O1 HRec HndO1 Hc2) as HO1.
assert (Htmp : bsum [(tq, nx'); vr_lb e q; vr_cb e c] <= 4097 + 8193 + 8193).
{ unfold vr_lb, vr_cb, bsum. cbn [fst snd fold_right].
  pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)) as Hl. unfold vr_l in *.
  pose proof (vrm_line_le (e_D e)) as Hln0. rewrite HlenD in Hln0. lia. }
assert (Hrest : bsum (e_rest e) <= blocks_bytes (e_S e)).
{ rewrite (blocks_bytes_bsum B (e_ly e) (e_S e)). rewrite (bsum_perm _ _ HPerm0), bsum_app.
  assert (0 <= bsum (e_O e)).
  { apply vr_bsum_nonneg. intros [p n] Hpn. assert (Hin : In (p, n) (ablocks B (e_ly e) (e_S e)))
      by (apply (Permutation_in _ (Permutation_sym HPerm0)); apply in_or_app; left; exact Hpn).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR0 Hin) as (_ & _ & _ & _ & _ & _ & Hn). cbn. lia. }
  lia. }
unfold LIVE_REPLY, LIVE_SOCKET_SEND, LMAX, LIVE_MAX in *.
unfold LIVE_VERBS_RECEIVE, VERBS_RECEIVE_MALLOCS, VERBS_RECEIVE_REQ in Hlive0. lia.
Qed.

(* reply's contract at every FP state (statement pass 4, verbs_receive_c.v); the joins call it at the section's fx *)
Hypothesis TREPLY : forall fx0 : YK11.FPState, treply_spec (fx := fx0) B MT.
Hypothesis HB : AF0m.CmdBSyms B.
Hypothesis MTL : ameter_laws MT.

(* the meter at the call of reply, the one call shape of the joins (S30) and of S05's reply: reply's account is one
   malloc of at most VERBS_RECEIVE_REQ bytes (socket_send's copy) and two frees (socket_send's and the text's), within
   its EV_REPLY = 3 events; the room for it before the call (the interface's vri_meter_ok) and vr_meter after it
   (vri_meter_step). The meter reasoning of this call shape lives in these three lemmas only. *)
Lemma vr_xm_reply_le : forall nx, 0 < nx <= VERBS_RECEIVE_REQ ->
XM_REPLY MT nx <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 2 * mo_free MT.
Proof.
intros nx Hnx. pose proof (mo_malloc_mono MT MTL nx VERBS_RECEIVE_REQ ltac:(lia)) as Hmx.
unfold XM_REPLY, XM_SOCKET_SEND. replace (0 <? nx) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.

Lemma vr_meter_reply_pre : forall e Sc k nm nx, vr_ent B MT e ->
vr_meter MT e Sc k nm -> k + EV_REPLY <= ev_vr (e_R e) (e_D e) ->
0 < nx <= VERBS_RECEIVE_REQ -> mo_ok MT Sc (XM_REPLY MT nx).
Proof.
intros e Sc k nm nx He HM Hkev Hnx.
exact (vri_meter_ok B MT e Sc k nm (XM_REPLY MT nx) 1 2 EV_REPLY MTL He HM (vr_xm_reply_le nx Hnx)
  ltac:(unfold EV_REPLY, EV_SOCKET_SEND; lia) ltac:(unfold EV_REPLY, EV_SOCKET_SEND; lia) Hkev).
Qed.

Lemma vr_meter_reply_post : forall e Sc S2 k nm nx, vr_meter MT e Sc k nm -> 0 < nx <= VERBS_RECEIVE_REQ ->
mo_le MT Sc S2 (XM_REPLY MT nx) -> vr_meter MT e S2 (k + EV_REPLY) (nm + 1).
Proof.
intros e Sc S2 k nm nx HM Hnx Hmle.
exact (vri_meter_step MT e Sc S2 k nm (XM_REPLY MT nx) 1 2 EV_REPLY MTL HM Hmle (vr_xm_reply_le nx Hnx)
  ltac:(unfold EV_REPLY, EV_SOCKET_SEND; lia) ltac:(unfold EV_REPLY, EV_SOCKET_SEND; lia)).
Qed.

(* the call reply(fd, text) at a join: from the state at reply's entry (ra = the join's return pc, a1 = the text)
   to the state at the return, the text freed, the recorder after socket_send, two more events of the meter *)
Hypothesis SIGP : cmd_sig_prog (PI := PI).
Lemma vr_reply_pc : pa_sigma CS_reply = BASE + AF_reply.
Proof. assert (E : cmd_af CS_reply = AF_reply) by (vm_compute; reflexivity).
rewrite (SIGP CS_reply ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])), E. reflexivity. Qed.
Lemma vr_reply_call : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c tp tq (x : list byte) sl rl R1 O1 qv
  k kmax nm nmax lyc Sc retk kmax' nmax',
vr_ent B MT e ->
vr_core B MT e pos F [(tq, Z.of_nat (length x) + 1); vr_lb e q; vr_cb e c] vr_sh2 sl (rl ++ [(11, tq)]) R1 O1 qv
  k kmax nm nmax lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
Forall (fun rv => acallee_saved (fst rv)) rl ->
Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl ->
4096 <= tq -> astr_atR (rdW W mem) tq x -> Z.of_nat (length x) <= 4096 ->
r_nreplies R1 < 2 ^ 31 - 1 ->
k + EV_REPLY <= ev_vr (e_R e) (e_D e) ->
blocks_bytes Sc + LIVE_REPLY <= LIVE_MAX ->
k + EV_REPLY <= kmax' -> nm + 1 <= nmax' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma CS_reply)) mem (seg_rom SEGS)) md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 O2,
 c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
 aregs_preserved regs regs2 /\
 vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rl (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) O2 qv
   (k + EV_REPLY) kmax' (nm + 1) nmax' ly2 S2 W2 regs2 mem2 md2 /\
 vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2).
Proof.
intros e W regs mem md pos F q c tp tq x sl rl R1 O1 qv k kmax nm nmax lyc Sc retk kmax' nmax'
He Hcore Hline Hcopy Hra Hretk Hretk2 Hcs Hsl Htq4 Hx Hx4 Hnr Hkev Hlive Hk' Hn'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'.
destruct He' as (HPRE & HROD & _ & _ & _ & _ & _ & Hn8 & HlenD & HinD & HnD & _ & _ & _ & _ & _ & _ & _ & _ & HPerm0
  & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _ & Hmok & Hfrm).
pose proof HPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hcore as (HJ & Hk & HM & Hnm0 & HFr & HR & HSv & HSp & HEnv & HRec & HD & HP & HQ).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
destruct HEnv as (HRO & Hgot & Hro & Hguard & Hflag & Herr).
destruct HFr as (HFa & HFw & HFs).
destruct Hline as (Hfl & Hln). destruct Hcopy as (Hfc & Htk).
set (nx := Z.of_nat (length x) + 1) in *.
rewrite vr_reply_pc.
assert (HRS : REPLY_STK = 16464) by (vm_compute; reflexivity).
assert (HVS : REPLY_STK + 208 <= VERBS_RECEIVE_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HEV3 : EV_REPLY = 3) by reflexivity.
change (spZ (e_regs e)) with (vr_sp0 e) in Hal16, Hslo, Hshi, Hbot, Htop.
assert (Hs1r : vr_s1 e = vr_sp0 e - 192 - (vr_sp0 e - 192) mod 32) by reflexivity.
set (sp0 := vr_sp0 e) in *. set (s1 := vr_s1 e) in *.
assert (Hs1b : sp0 - 208 <= s1 <= sp0 - 192 /\ s1 mod 16 = 0).
{ rewrite Hs1r.
  pose proof (Z.div_mod (sp0 - 192) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (sp0 - 192) 32 ltac:(lia)) as M1.
  pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2. rewrite Hal16 in D2.
  split; [lia|].
  replace (sp0 - 192 - (sp0 - 192) mod 32) with ((2 * ((sp0 - 192) / 32)) * 16) by lia.
  apply Z.mod_mul. lia. }
(* the registers at the call *)
apply vr_rv_app in HR as [HRb HRl]. apply vr_rv_app in HRl as [HRl HR11].
assert (R2 : getr regs 2 = w64 s1) by exact (vr_rv_get regs _ 2 s1 HRb ltac:(unfold vr_base; cbn; tauto)).
assert (R3 : getr regs 3 = w64 (as_gp B)) by exact (vr_rv_get regs _ 3 _ HRb ltac:(unfold vr_base; cbn; tauto)).
assert (R4 : getr regs 4 = w64 (as_tp B)) by exact (vr_rv_get regs _ 4 _ HRb ltac:(unfold vr_base; cbn; tauto)).
assert (R8 : getr regs 8 = w64 sp0) by exact (vr_rv_get regs _ 8 _ HRb ltac:(unfold vr_base; cbn; tauto)).
assert (R11 : getr regs 11 = w64 tq) by exact (vr_rv_get regs _ 11 _ HR11 ltac:(left; reflexivity)).
assert (Hspr : spZ regs = sp0 + (s1 - sp0)) by (unfold spZ; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
(* the blocks at the call *)
set (T := [vr_lb e q; vr_cb e c] ++ e_rest e) in *.
assert (HND : List.NoDup (O1 ++ (tq, nx) :: T)) by exact (vr_perm_nodup lyc Sc W mem md _ HAR HP).
assert (HinSc : forall pn, In pn (O1 ++ (tq, nx) :: T) -> In pn (ablocks B lyc Sc))
  by (intros pn H; exact (Permutation_in _ (Permutation_sym HP) H)).
assert (Htq_in : In (tq, nx) (ablocks B lyc Sc)) by (apply HinSc; apply in_or_app; right; left; reflexivity).
assert (HO1 : forall pn, In pn O1 -> In pn (ablocks B lyc Sc)) by (intros pn H; apply HinSc; apply in_or_app; left; exact H).
assert (HTSc : forall pn, In pn T -> In pn (ablocks B lyc Sc)) by (intros pn H; apply HinSc; apply in_or_app; right; right; exact H).
assert (Htq_O1 : ~ In (tq, nx) O1) by (intros H; exact (vr_nodup_disj O1 _ (tq, nx) HND H (or_introl eq_refl))).
assert (HO1T : forall pn, In pn O1 -> ~ In pn T) by (intros pn H1 H2; exact (vr_nodup_disj O1 _ pn HND H1 (or_intror H2))).
assert (HND2 : List.NoDup ((tq, nx) :: T)) by exact (vr_nodup_app_r _ _ HND).
assert (HtqT : ~ In (tq, nx) T) by (inversion HND2; assumption).
assert (HNDT : List.NoDup T) by (inversion HND2; assumption).
assert (Hsep : forall pn pn', In pn (ablocks B lyc Sc) -> In pn' (ablocks B lyc Sc) -> pn <> pn' ->
  fst pn + req_size (snd pn) <= fst pn' \/ fst pn' + req_size (snd pn') <= fst pn).
{ intros [p n] [p' n'] H1 H2 Hne. exact (sep_blocks SEGS B LAWS lyc Sc W mem md p n p' n' HAR H1 H2 Hne). }
assert (Hblk : forall p n, In (p, n) (ablocks B lyc Sc) -> 4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n /\
  in_app p (req_size n)).
{ intros p n H. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR H) as (_ & H1 & H2 & H3 & _ & _ & H4).
  split; [lia|]. split; [lia|]. split; [lia | exact H3]. }
assert (Hap : Forall (fun qk => iv_apart tq nx (fst qk) (snd qk)) O1).
{ apply Forall_forall. intros [p n] Hpn. assert (Hne : (tq, nx) <> (p, n)) by (intros E; rewrite E in Htq_O1; exact (Htq_O1 Hpn)).
  destruct (Hsep _ _ Htq_in (HO1 _ Hpn) Hne) as [Hd | Hd]; cbn [fst snd] in Hd;
  pose proof (req_size_pos nx ltac:(lia)); pose proof (req_size_pos n ltac:(destruct (Hblk p n (HO1 _ Hpn)); lia));
  unfold iv_apart; cbn [fst snd]; lia. }
(* the meter at the call (vr_meter_reply_pre) *)
assert (Hnx : 0 < nx <= VERBS_RECEIVE_REQ) by (unfold nx, VERBS_RECEIVE_REQ; lia).
assert (Hmok1 : mo_ok MT Sc (XM_REPLY MT nx)) by exact (vr_meter_reply_pre e Sc k nm nx He HM Hkev Hnx).
(* the frame chain *)
destruct (vr_chain_at e lyc Sc W mem md k pos regs He HJ HSv R8) as [ch1 Hch].
set (FP1 := (A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp ((tq, nx) :: O1)).
assert (HFP1low : forall a, inFP FP1 a -> 0 < a < alloc_ceiling).
{ intros a Ha. destruct (vr_fp1_cases _ a Ha) as [Hg | (p & n & Hpn & Hr)]; [unfold A_G_REC, REC_SIZE in Hg; lia|].
  assert (HpS : In (p, n) (ablocks B lyc Sc)) by (destruct Hpn as [E | Hpn]; [rewrite <- E; exact Htq_in | exact (HO1 _ Hpn)]).
  destruct (Hblk p n HpS) as (H1 & H2 & _). lia. }
eapply SRr_mono.
{ eapply (cl_callS_wide B LAWS W regs mem (Z_to_bv 64 (BASE + AF_reply)) VERBS_RECEIVE_STK sp0 (vr_fp e) (e_ly e) (e_S e)
    (e_W e) (e_mem e) (e_md e) [(4, pos)] lyc Sc md k REPLY_STK FP1 EV_REPLY (s1 - sp0) (Z_to_bv 64 (BASE + retk)) ch1
    (fun ly' S' W' regs' mem' md' => exists O' : list (Z * Z),
      rec_repA B ly' S' (rdW W' mem') (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) O' /\
      ~ In (tq, nx) (ablocks B ly' S') /\
      (forall pn, In pn (ablocks B lyc Sc) -> ~ In pn O1 -> pn <> (tq, nx) -> In pn (ablocks B ly' S')) /\
      (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B lyc Sc) /\ ~ In pn O1 /\ pn <> (tq, nx)) \/ In pn O') /\
      (forall pn, In pn O' -> In pn O1 \/ ~ In pn (ablocks B lyc Sc)) /\
      blocks_bytes S' <= blocks_bytes Sc + LIVE_REPLY /\
      mo_le MT Sc S' (XM_REPLY MT (Z.of_nat (length x) + 1))) HJ).
  - exact Hspr.
  - rewrite Zminus_mod, (proj2 Hs1b), Hal16. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact R3.
  - exact R4.
  - exact Hra.
  - apply ret_ok_codeptr_v; [lia | exact Hretk2].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (sp0 + (s1 - sp0)) with s1 by lia. exact Hch.
  - intros HPRE1.
    change (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reply)) mem (seg_rom SEGS)) md) with (cfg_at SEGS (BASE + AF_reply) regs mem md).
    eapply SRr_mono.
    { destruct (Hblk tq nx Htq_in) as (Hq1 & Hq2 & _).
      assert (Htq64 : 0 <= tq < 2 ^ 64).
      { pose proof (req_size_pos nx ltac:(unfold nx; lia)) as Hrq. split; [lia|]. clear - Hq2 C1 Hrq. lia. }
      apply (TREPLY fx lyc Sc W regs mem md ch1 tq nx x R1 O1 HPRE1 HRO R11 Htq64 Htq_in Htq_O1 Hap Hx
        ltac:(unfold nx; lia) Hx4 HRec Hnr ltac:(lia) Hlive Hmok1). }
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Hra. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. destruct (vr_fp1_cases _ a Ha) as [Hg | (p & n & Hpn & Hr)].
    + right; right; right; right; left. split; [|split].
      * unfold vr_fp. apply inFP_app. left. apply inFP_cons. left. exact Hg.
      * rewrite (AF0m.ts_prog B HB). unfold AF0m.TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, REC_SIZE in Hg. lia.
      * exact (vr_grec_img a Hg).
    + assert (HpS : In (p, n) (ablocks B lyc Sc)) by (destruct Hpn as [E | Hpn]; [rewrite <- E; exact Htq_in | exact (HO1 _ Hpn)]).
      destruct (in_dec vr_pdec (p, n) (ablocks B (e_ly e) (e_S e))) as [Hent | Hnent].
      * apply (Permutation_in _ HPerm0) in Hent. apply in_app_iff in Hent as [HinO | HinR].
        -- right; left. split; [|exists p, n; split; [exact HpS | exact Hr]].
           unfold vr_fp. apply inFP_app. right. replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n); [exact HinO | lia].
        -- exfalso. assert (HinT : In (p, n) T) by (unfold T; apply in_or_app; right; exact HinR).
           destruct Hpn as [E | Hpn]; [rewrite <- E in HinT; exact (HtqT HinT) | exact (HO1T _ Hpn HinT)].
      * right; right; left. exists p, n. split; [exact HpS | split; [exact Hnent | exact Hr]].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw Hn. exfalso. pose proof (HFP1low a Ha). lia. }
(* the state after the call *)
cbv beta. intros W2 c2 Hwle2' (ly2 & S2 & regs2 & mem2 & md2 & -> & HJo & HJi & HPres & (O' & HRec' & Hgone' & Hkeep & Hincl & Hfresh & _ & Hmle)).
pose proof HJi as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & G1 & G2 & G3 & G4 & _ & _ & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF2 & _).
assert (HF4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W mem md 4 pos HAR HF4) as (Hfr0 & Hfrc & Hfrh).
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity.
(* what the call keeps *)
assert (KS : forall a, s1 <= a < sp0 -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply G1; [lia | lia |]. intros Hf. pose proof (HFP1low a Hf). lia. }
assert (KF : forall a, (F <= a < F + 1024 \/ shadow_addr F <= a < shadow_addr F + 128) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Ha. apply (G4 4 pos a HF4).
  - unfold frame_rng, in_zr. cbn [fst snd]. rewrite Hfb, <- HFa. change (1024 / 8) with 128. lia.
  - intros Hf. destruct (vr_fp1_cases _ a Hf) as [Hg | (p & n & Hpn & Hr)].
    + destruct Ha as [Ha | Ha].
      * exact (frm_img SEGS B LAWS lyc Sc W mem md 4 pos a HAR HF4 ltac:(rewrite <- HFa, Hfb; lia) (vr_grec_img a Hg)).
      * pose proof (shadow_addr_bounds F ltac:(lia)). unfold A_G_REC, REC_SIZE in Hg. lia.
    + assert (HpS : In (p, n) (ablocks B lyc Sc)) by (destruct Hpn as [E | Hpn]; [rewrite <- E; exact Htq_in | exact (HO1 _ Hpn)]).
      destruct (Hblk p n HpS) as (Hp1 & Hp2 & Hp3 & Hp4).
      destruct Ha as [Ha | Ha].
      * pose proof (sep_block_frame SEGS B LAWS lyc Sc W mem md p n 4 pos HAR HpS HF4) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite <- HFa, Hfb in Hd. lia.
      * apply (fshadow_not_app F 128 p (req_size n) a); [lia | lia | exact Hp4 | unfold shadow_addr, SHADOW_OFF in Ha; lia | lia]. }
assert (KB : forall p n i, In (p, n) T -> 0 <= i < req_size n -> rdW W2 mem2 (p + i) = rdW W mem (p + i)).
{ intros p n i HpT Hi. assert (HpS : In (p, n) (ablocks B lyc Sc)) by exact (HTSc _ HpT).
  assert (HpO : ~ In (p, n) O1) by (intros H; exact (HO1T _ H HpT)).
  assert (Hpq : (p, n) <> (tq, nx)) by (intros E; rewrite E in HpT; exact (HtqT HpT)).
  apply (G2 p n i HpS (Hkeep _ HpS HpO Hpq) Hi).
  intros Hf. destruct (vr_fp1_cases _ _ Hf) as [Hg | (p' & n' & Hpn' & Hr')].
  - exact (blk_img SEGS B LAWS lyc Sc W mem md p n (p + i) HAR HpS ltac:(lia) (vr_grec_img _ Hg)).
  - assert (HpS' : In (p', n') (ablocks B lyc Sc)) by (destruct Hpn' as [E | Hpn']; [rewrite <- E; exact Htq_in | exact (HO1 _ Hpn')]).
    assert (Hne : (p, n) <> (p', n')).
    { intros E. rewrite <- E in Hpn'. destruct Hpn' as [E' | Hpn']; [rewrite E' in Hpq; exact (Hpq eq_refl) | exact (HpO Hpn')]. }
    destruct (Hsep _ _ HpS HpS' Hne) as [Hd | Hd]; cbn [fst snd] in Hd; lia. }
assert (KI : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ (A_G_REC <= a < A_G_REC + REC_SIZE) -> rdW W2 mem2 a = rdW W mem a).
{ intros a Hi Ho He0 Hg. apply (G3 a Hi Ho He0). apply fp_spares_closed.
  - intros H0. pose proof (HFP1low 0 H0). lia.
  - intros Hf. destruct (vr_fp1_cases _ _ Hf) as [Hg' | (p & n & Hpn & Hr)]; [exact (Hg Hg')|].
    assert (HpS : In (p, n) (ablocks B lyc Sc)) by (destruct Hpn as [E | Hpn]; [rewrite <- E; exact Htq_in | exact (HO1 _ Hpn)]).
    exact (blk_img SEGS B LAWS lyc Sc W mem md p n a HAR HpS Hr Hi). }
set (O2 := nodup vr_pdec O').
assert (HO2 : forall pn, In pn O2 <-> In pn O') by (intros pn; unfold O2; apply nodup_In).
exists ly2, S2, regs2, mem2, md2, O2. split; [reflexivity|]. split; [exact HPres|].
assert (Hdata : In (e_data e, Z.max (e_n e) 1) T).
{ apply (Permutation_in _ HPerm0) in HinD. apply in_app_iff in HinD as [H | H]; [exact (False_ind _ (HnD H))|].
  unfold T. apply in_or_app. right. exact H. }
split; [|split].
- (* vr_core *)
  split; [exact HJo|]. split; [lia|].
  split.
  { exact (vr_meter_reply_post e Sc S2 k nm nx HM Hnx Hmle). }
  split; [lia|].
  split.
  { split; [unfold frame_addr in *; rewrite EF2; exact HFa|].
    split.
    - assert (Efl : flag_addr ly2 4 pos = flag_addr lyc 4 pos) by (unfold flag_addr; rewrite EF2; reflexivity).
      rewrite Efl, <- HFw. apply rdword_ext. intros kk Hkk. apply KF. lia.
    - intros i Hi. rewrite KF; [exact (HFs i Hi) | right; lia]. }
  split; [apply vr_rv_app; split; [exact (vr_rv_preserved regs regs2 _ HPres (vr_base_cs B e) HRb) | exact (vr_rv_preserved regs regs2 _ HPres Hcs HRl)]|].
  split.
  { intros j r Hj kk Hkk. assert (Hjl : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
    cbn [length vr_saved_regs] in Hjl. rewrite KS; [exact (HSv j r Hj kk Hkk) | fold sp0; lia]. }
  split.
  { unfold vr_spill in *. rewrite Forall_forall in *. intros ov Hov kk Hkk. destruct (Hsl ov Hov) as [Ho1 Ho2].
    rewrite KS; [exact (HSp ov Hov kk Hkk) | fold s1; lia]. }
  split; [exact (vr_env_of_aro ly2 S2 W2 mem2 md2 (proj1 HJo) (vr_aro_kept e _ ly2 S2 W2 mem2 md2 _ He HJo))|].
  split.
  { destruct HRec' as (Q & HA & HOQ). exists Q. split; [exact HA|]. intros pn. rewrite HO2. apply HOQ. }
  split.
  { rewrite HO2. intros H. destruct (Hfresh _ H) as [H1 | H1]; [exact (HO1T _ H1 Hdata) | exact (H1 (HTSc _ Hdata))]. }
  split.
  { apply NoDup_Permutation.
    - exact (vr_ablocks_nodup ly2 S2 W2 mem2 md2 HAR2).
    - apply vr_nodup_app; [unfold O2; apply NoDup_nodup | exact HNDT |].
      intros pn H1 H2. rewrite HO2 in H1. destruct (Hfresh _ H1) as [H3 | H3]; [exact (HO1T _ H3 H2) | exact (H3 (HTSc _ H2))].
    - intros pn. split.
      + intros H. destruct (Hincl pn H) as [(H1 & H2 & H3) | H1].
        * apply in_or_app. right. apply (Permutation_in _ HP) in H1. apply in_app_iff in H1 as [H1 | [H1 | H1]];
          [exact (False_ind _ (H2 H1)) | exact (False_ind _ (H3 (eq_sym H1))) | exact H1].
        * apply in_or_app. left. rewrite HO2. exact H1.
      + intros H. apply in_app_iff in H as [H | H].
        * rewrite HO2 in H. exact (rec_repA_in_blocks B _ _ _ _ _ _ HRec' H).
        * apply Hkeep; [exact (HTSc _ H) | intros H1; exact (HO1T _ H1 H) | intros E; rewrite E in H; exact (HtqT H)]. }
  { intros kk Hkk. assert (HPG : inFP cmd_PG (A_G_QUITTING + Z.of_nat kk)).
    { unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. right. apply inFP_cons. left. lia. }
    destruct (PROGU _ HPG) as (Hi & Ho & He0).
    rewrite KI; [exact (HQ kk Hkk) | exact Hi | exact Ho | exact He0 | unfold A_G_QUITTING, A_G_REC, REC_SIZE; lia]. }
- (* the line block *)
  split; [exact Hfl|].
  assert (HLl : Z.of_nat (length (Verbs.line (e_D e))) <= vr_l (e_n e) (e_D e)).
  { unfold vr_l. rewrite <- HlenD. exact (vrm_line_le (e_D e)). }
  assert (HLpos : 0 <= vr_l (e_n e) (e_D e)) by (unfold vr_l; pose proof (vrm_l_le (e_n e) (e_D e) ltac:(lia)); lia).
  assert (HRQ : req_size (vr_l (e_n e) (e_D e) + 1) = vr_l (e_n e) (e_D e) + 1)
    by (unfold req_size; replace (vr_l (e_n e) (e_D e) + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  assert (HlbT : In (vr_lb e q) T) by (left; reflexivity).
  apply (astr_atR_agree _ _ q _ (Z.of_nat (length (Verbs.line (e_D e))) + 1) Hln); [lia|].
  intros kk Hkk. apply (KB q (vr_l (e_n e) (e_D e) + 1) kk HlbT). rewrite HRQ. lia.
- (* the copy block and tok[] *)
  split; [exact Hfc|].
  destruct Htk as (Ht8 & Htl & Htp & Htw).
  assert (HcbT : In (vr_cb e c) T) by (right; left; reflexivity).
  pose proof (Verbs.toks_length (e_D e)) as Hl64.
  split; [exact Ht8|]. split; [exact Htl|]. split.
  + intros i p Hi. pose proof (Htp i p Hi) as Hv. intros kk Hkk. rewrite KF; [exact (Hv kk Hkk)|].
    assert (Hil : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate). left. lia.
  + intros i p w Hi Hw. destruct (Htw i p w Hi Hw) as (Hs & Hl & Hc1 & Hc2). split; [|split; [exact Hl | split; [exact Hc1 | exact Hc2]]].
    apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
    intros kk Hkk. replace (p + kk) with (c + (p - c + kk)) by lia.
    apply (KB c (Z.of_nat (length (Verbs.line (e_D e))) + 1) (p - c + kk) HcbT).
    pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)). lia.
Qed.

(* seed the symbolic state at a boundary whose spill slots are among vr_sl3's and whose tmps hold the line block
   (q, _) and the copy block (c, _): the slot values are all addressable words (frame, shadow, block starts) *)
Lemma vr_seed_hd : forall e pos F q c tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pcoff,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc ->
In (vr_lb e q) tmps -> In (vr_cb e c) tmps -> incl sl (vr_sl3 F q c) ->
regions_wf [vr_rg (map fst sl)] = true -> (length sl + 32 < A_TEXT)%nat ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (vr_vals sl))) (vr_ss pcoff (map fst sl))
  (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + pcoff)) memc (seg_rom SEGS))).
Proof.
intros e pos F q c tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc W regsc memc mdc pcoff Hcore Hlq Hlc Hsl Hwf Hlen.
pose proof asan_consts as (C1 & _).
pose proof Hcore as (HJ & _ & _ & _ & HFr & HR & _ & HSp & _ & _ & _ & HP & _).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & HS0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
destruct HFr as (HFa & _ & _).
assert (HF4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 4 pos HAR HF4) as (Hf0 & Hfc & _).
assert (Hfb : fs_frame_bytes 4 = 1024) by reflexivity. rewrite Hfb, <- HFa in Hfc. rewrite <- HFa in Hf0.
assert (Hqin : In (vr_lb e q) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; apply in_or_app; left; exact Hlq).
assert (Hcin : In (vr_cb e c) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; apply in_or_app; left; exact Hlc).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hqin) as (_ & Hq0 & Hqc & _ & _ & _ & Hqn). cbn [fst snd] in Hq0, Hqc, Hqn.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hcin) as (_ & Hc0 & Hcc & _ & _ & _ & Hcn). cbn [fst snd] in Hc0, Hcc, Hcn.
unfold vr_lb, vr_cb in Hq0, Hqc, Hc0, Hcc, Hqn, Hcn. cbn [fst snd] in Hq0, Hqc, Hc0, Hcc, Hqn, Hcn.
pose proof (req_size_pos _ (proj1 Hqn)) as [Hqr _]. pose proof (req_size_pos _ (proj1 Hcn)) as [Hcr _].
assert (HshF : 0 <= shadow_addr F /\ shadow_addr F + 8 <= 2 ^ 64).
{ pose proof (shadow_addr_bounds F ltac:(unfold kHighMemEnd in *; lia)) as Hsb.
  unfold kLowMemEnd, kHighShadowEnd in Hsb. lia. }
assert (H3 : Forall (fun ov => 0 <= snd ov < 2 ^ 64) (vr_sl3 F q c)).
{ unfold vr_sl3. repeat (apply Forall_cons; [cbn [snd]; lia|]). apply Forall_nil. }
rewrite <- (app_nil_r (vr_vals sl)).
apply (vr_seed B e W regsc memc pcoff sl []).
- apply vr_rv_app in HR as [HRb _]. exact HRb.
- exact Hwf.
- exact Hlen.
- unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia.
- unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia.
- exact HSp.
- rewrite Forall_forall in H3 |- *. intros ov Hov. exact (H3 ov (Hsl ov Hov)).
Qed.

(* ---------------------------------------------------------------------------------------------------------------
   The joins: the model at a join (the handler kept r_nreplies, recorded at most two calls, and its text is at most
   4096 bytes), the reply at a join with the walk's account, and the jump of a return pc *)
Lemma vr_hd_model : forall e, vr_ent B MT e ->
r_nreplies (vr_R1 (e_R e) (e_D e)) = 0 /\ (length (r_calls (vr_R1 (e_R e) (e_D e))) <= 2)%nat /\
Z.of_nat (length (vr_x (e_R e) (e_D e))) <= 4096.
Proof.
intros e He. pose proof He as He'. unfold vr_ent in He'. cbv zeta in He'.
destruct He' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcalls & _ & _ & Hnrep & _).
unfold vr_R1, vr_x, vr_h.
pose proof (vrm_calls reply_code_a (e_R e) (vr_st (e_D e)) Hcalls) as C.
destruct (VerbsRun.run_step reply_code_a (e_R e) (vr_st (e_D e))) as [[R1 x] qt] eqn:Er. cbn [fst snd] in C |- *.
pose proof (vrm_nrep _ _ _ _ _ _ Er) as N. pose proof (vrm_text _ _ _ _ _ _ Er) as [_ T].
split; [lia|]. split; [exact C|]. lia.
Qed.

Lemma vr_join_call : forall e (W : world SEGS) (regs : bvmap 5 word) mem md pos F q c tp tq sl rl O1 qv k nm lyc Sc retk
  kmax' nmax',
vr_ent B MT e ->
vr_core B MT e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 sl (rl ++ [(11, tq)])
  (vr_R1 (e_R e) (e_D e)) O1 qv k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc W regs mem md ->
vr_line B e q W mem -> vr_copy B e F c tp W mem ->
getr regs 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
Forall (fun rv => acallee_saved (fst rv)) rl ->
Forall (fun ov => 0 <= fst ov /\ fst ov + 8 <= 80) sl ->
4096 <= tq -> astr_atR (rdW W mem) tq (vr_x (e_R e) (e_D e)) ->
vr_k2 (e_R e) (e_D e) <= kmax' -> VR_NM_AR <= nmax' ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pa_sigma CS_reply)) mem (seg_rom SEGS)) md)
(fun W2 c2 => exists ly2 S2 regs2 mem2 md2 O2,
 c2 = mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2 /\
 aregs_preserved regs regs2 /\
 vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 sl rl (vr_R2 (e_R e) (e_D e)) O2 qv
   (k + EV_REPLY) kmax' (nm + 1) nmax' ly2 S2 W2 regs2 mem2 md2 /\
 vr_line B e q W2 mem2 /\ vr_copy B e F c tp W2 mem2).
Proof.
intros e W regs mem md pos F q c tp tq sl rl O1 qv k nm lyc Sc retk kmax' nmax'
He Hcore Hline Hcopy Hra Hretk Hretk2 Hcs Hsl Htq4 Hx Hk2 Hn2.
destruct (vr_hd_model e He) as (Hnr & Hc2 & Hx4).
pose proof Hcore as (_ & Hk & _ & Hnm & _).
pose proof (vr_k1_ev (e_R e) (e_D e)) as Hev.
assert (HEV3 : EV_REPLY = 3) by reflexivity.
apply (vr_reply_call e W regs mem md pos F q c tp tq (vr_x (e_R e) (e_D e)) sl rl (vr_R1 (e_R e) (e_D e)) O1 qv
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc retk kmax' nmax' He Hcore Hline Hcopy Hra Hretk Hretk2 Hcs Hsl Htq4 Hx Hx4).
- rewrite Hnr. lia.
- lia.
- apply (vr_hd_live e pos F q c tq _ vr_sh2 sl (rl ++ [(11, tq)]) (vr_R1 (e_R e) (e_D e)) O1 qv k (vr_k1 (e_R e) (e_D e))
    nm VR_NM_HD lyc Sc W regs mem md He Hcore Hc2). lia.
- unfold vr_k2 in Hk2. lia.
- unfold VR_NM_AR, VR_NM_HD in *. lia.
Qed.

(* the jump of a return pc to a boundary, run from a state that names only the registers *)
Lemma vr_jmp : forall retk stopk,
sym_run_toN_pi pl_tpi FUEL stopk (vr_ss0 retk) = (vr_ss0 stopk, PRS_running) ->
forall W2 (regs2 : bvmap 5 word) mem2 md2 (Q : world SEGS -> config -> Prop) STK sp0 FP ly S W0 mem md own ly2 S2 kk,
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 kk ->
(forall regs3 mem3 md3, (forall r, getr regs3 r = getr regs2 r) -> (forall a, rdW W2 mem3 a = rdW W2 mem2 a) ->
  ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem3 md3 kk ->
  Q W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + stopk)) mem3 (seg_rom SEGS)) md3)) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros retk stopk Hrun W2 regs2 mem2 md2 Q STK sp0 FP ly S W0 mem md own ly2 S2 kk HJ HQ.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs2 []))) by apply Eimg_env.
pose proof (vr_seed0 W2 regs2 mem2 retk) as HS.
eapply (SRr_run_to_pi_AJ B LAWS W2 FUEL stopk (Eimg (Ereg regs2 [])) (vr_ss0 retk) (vr_ss0 stopk) PRS_running _
  STK sp0 FP ly S W0 mem md own ly2 S2 md2 kk Q HEI HS Hrun I HJ).
- apply awr_ok_nil.
- intros ms' mat HS' HJ' HF HFr HG.
  rewrite (st_ok_pi_restrict_mkst (w_H W2) _ (vr_ss0 stopk) ms' HS' eq_refl). cbn [ss_pc vr_ss0].
  apply SRr_ret. apply HQ.
  + intros r. rewrite (st_ok_pi_restrict_reg (w_H W2) _ (vr_ss0 stopk) ms' r HS'). cbn [ss_regs vr_ss0].
    symmetry. exact (regs_ok_Eimg_Ereg regs2 [] r).
  + cbn [ms_mem mkst ss_mem vr_ss0] in HFr. intros a.
    exact (vr_rdW_frame _ [] W2 _ _ HFr (vr_no_wrange _ [] (Forall_nil _)) a).
  + exact HJ'.
Qed.

End e.
End f.
End d.
