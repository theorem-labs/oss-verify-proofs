(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of segment S02 (DUP, 0x8cf9c-0x8cff8) of the ASan+UBSan (image B) walk
   of verbs_receive on plugin-hostd/fuzz_command (lib/B/Prog/verbs_receive_s02.v): the facts of the segment's states
   that read memory the segment does not write (s2_st), where the bytes they read lie, their transport across strndup
   (acall_kept) and across a change of memory that misses them, the seed of a symbolic state at a return, the meter
   after strndup and the event lower bound. The B twin of lib/A/Prog/verbs_receive_s02_k.v
   (a working branch); the event constants are B's, unfolded by HarnessArgsEv.v's ev_unfold. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString RtAlloc04 RtShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_kit.
(* B's event constants and the tactics that unfold them to their values (ev_unfold, rec_unfold, ifs) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import HarnessArgsEv pin_set_words_c reply_c sup_reply_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c verbs_receive_iface.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_s02_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the shadow of the side-stack frame once tok is opened (0x8cfcc), before the store to save's shadow byte (0x8cfd0) *)
Definition vr_shm : list Z := repeat 0xf1 4 ++ repeat 0 64 ++ repeat 0xf2 8 ++ [0xf8] ++ repeat 0xf3 3 ++ repeat 0 48.

Lemma s2_shm_set : forall i, (4 <= i < 68)%nat -> nth i vr_shm 0 = 0.
Proof.
intros i Hi. assert (H : forallb (fun j => Z.eqb (nth j vr_shm 0) 0) (seq 4 64) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_seq. lia.
Qed.
Lemma s2_shm_kept : forall i, (i < 128)%nat -> ~ (4 <= i < 68)%nat -> nth i vr_shm 0 = nth i vr_sh1 0.
Proof.
intros i Hi Hn.
assert (H : forallb (fun j => ((4 <=? j)%nat && (j <? 68)%nat) || Z.eqb (nth j vr_shm 0) (nth j vr_sh1 0)) (seq 0 128) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)).
apply orb_true_iff in H as [H | H].
- apply andb_true_iff in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2. lia.
- apply Z.eqb_eq. exact H.
Qed.
Lemma s2_sh2_of_shm : forall i, (i < 128)%nat -> i <> 76%nat -> nth i vr_sh2 0 = nth i vr_shm 0.
Proof.
intros i Hi Hn.
assert (H : forallb (fun j => (j =? 76)%nat || Z.eqb (nth j vr_sh2 0) (nth j vr_shm 0)) (seq 0 128) = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in H. specialize (H i ltac:(apply in_seq; lia)).
apply orb_true_iff in H as [H | H]; [apply Nat.eqb_eq in H; lia | apply Z.eqb_eq; exact H].
Qed.
Lemma s2_sh2_76 : nth 76 vr_sh2 0 = 0.
Proof. vm_compute. reflexivity. Qed.

(* strndup's memchr premise holds for any start address when the buffer has exactly n bytes *)
Lemma s2_memchr : forall A (D : list byte) (n : Z), n = Z.of_nat (length D) -> StrFun.memchr_ok A 0 n D.
Proof.
intros A D n ->. unfold StrFun.memchr_ok.
destruct (StrFun.find_byte 0 (firstn (Z.to_nat (Z.of_nat (length D))) D)) as [j|]; [left; lia | lia].
Qed.

(* the prefix strndup copies holds no terminator *)
Lemma s2_prefix_no0 : forall (D : list byte) (n : Z), n = Z.of_nat (length D) ->
~ In (Z_to_bv 8 0) (firstn (Z.to_nat (StrFun.strnlen_res n D)) D).
Proof. intros D n Hn. destruct (vr_upto_firstn D n Hn) as [E _]. rewrite E. apply vr_upto0_no0. Qed.

Lemma s2_l_range : forall n D, 0 <= n -> 0 <= vr_l n D <= n.
Proof.
intros n D Hn. unfold vr_l, StrFun.strnlen_res. destruct (StrFun.find_byte 0 (firstn (Z.to_nat n) D)) as [i|] eqn:Fb; [|lia].
destruct (StrFun.find_byte_Some _ _ _ Fb) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.

Lemma s2_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof. intros l l' H. induction H; unfold bsum in *; cbn in *; lia. Qed.

(* the events of a route are never negative: B's constants (HarnessArgsEv.v's ev_unfold) are sums of the
   allocator calls and of record()'s spill-arm frees *)
Lemma s2_ev_route_nn : forall R ln tk s, 0 <= ev_route R ln tk s.
Proof.
intros R ln tk s. unfold ev_route. destruct tk as [|v args]; [ev_unfold; lia|].
match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end;
  [ev_unfold; rec_unfold; cbn; ifs; lia|].
match goal with |- context [if Verbs.list_eqb v ?w then _ else _] => destruct (Verbs.list_eqb v w) end.
- unfold EV_PIN_SET_WORDS. destruct (Verbs.pin_set_words_m ln args); ev_unfold; rec_unfold; cbn;
  ifs; lia.
- destruct s as [c0|c|u i p q|u f l v'|u| |ln' tk']; [|destruct c|..];
  ev_unfold; rec_unfold; cbn; ifs; lia.
Qed.
(* one message spends at least strndup's event *)
Lemma s2_ev_vr_pos : forall R D, 1 <= ev_vr R D.
Proof.
intros R D. unfold ev_vr. destruct (Verbs.receive atoi_a D) as [st af].
pose proof (s2_ev_route_nn R (Verbs.line D) (Verbs.toks D) st) as Hr.
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q].
assert (Ha : 0 <= ev_after (fst (socket_send_m R1 (x ++ [Z_to_bv 8 0]))) af).
{ destruct af as [p|]; ev_unfold; [|lia]. ifs; lia. }
assert (Hrp : EV_REPLY = 3) by reflexivity. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a symbolic state seeded from a machine state: the registers as atoms of their own values, and the given regions *)
Definition s2_ss (pc : Z) (rs : smem) : sstate := mkSS pc sr_atoms rs None (mkFacts [] [] []).
Lemma s2_seed : forall (W : world SEGS) regs mem pc rs,
regions_wf rs = true -> Forall (region_ok SEGS (Eimg (Ereg regs [])) (mrestrict (w_H W) mem)) rs ->
pairwise_disjoint (Eimg (Ereg regs [])) rs ->
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) (s2_ss pc rs)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc rs Hwf Hrs Hpd. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf. - exact Hrs. - exact Hpd.
- split; [exact I | split; exact I].
Qed.
Lemma s2_ew : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
intros regs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma s2_sv_atom : forall (regs : bvmap 5 word) n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
sv_denot (Eimg (Ereg regs [])) (SOff n 0) = w64 v.
Proof. intros regs n r v Hn Hr. cbn [sv_denot]. rewrite (s2_ew regs n r Hn), Hr, Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma s2_rv_keep : forall (regs regs' : bvmap 5 word) l, vr_rv regs l -> aregs_preserved regs regs' ->
Forall (fun rv => acallee_saved (fst rv)) l -> vr_rv regs' l.
Proof.
intros regs regs' l H HP Hc. unfold vr_rv in *. rewrite Forall_forall in *. intros [r v] Hin.
cbn [fst snd]. rewrite (HP r (Hc (r, v) Hin)). exact (H (r, v) Hin).
Qed.
(* a register list of an earlier state, at a later one that agrees on its registers, extended by more registers *)
Lemma s2_rv_from : forall (regs regs' : bvmap 5 word) l l', vr_rv regs l ->
(forall r, In r (map fst l) -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) -> vr_rv regs' l' ->
vr_rv regs' (l ++ l').
Proof.
intros regs regs' l l' H Hs H'. unfold vr_rv in *. apply Forall_app. split; [|exact H'].
rewrite Forall_forall in *. intros [r v] Hin. cbn [fst snd].
rewrite (Hs r) by (apply in_map_iff; exists (r, v); split; [reflexivity | exact Hin]). exact (H (r, v) Hin).
Qed.
Lemma s2_rv_incl : forall (regs : bvmap 5 word) l l', vr_rv regs l -> incl l' l -> vr_rv regs l'.
Proof.
intros regs l l' H Hi. unfold vr_rv in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hi x Hx)).
Qed.
Lemma s2_s1_shape : forall e, vr_sp0 e mod 16 = 0 ->
(vr_s1 e = vr_sp0 e - 192 \/ vr_s1 e = vr_sp0 e - 208) /\ vr_s1 e mod 32 = 0.
Proof.
intros e H. unfold vr_s1. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as D1.
pose proof (Z.div_mod (vr_sp0 e - 192) 32 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)) as M2. split; [lia|].
rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity.
Qed.
Lemma s2_stk_ge : ASTACK + 208 <= VERBS_RECEIVE_STK /\ 4 * ESTACK + 208 <= VERBS_RECEIVE_STK.
Proof.
unfold VERBS_RECEIVE_STK. pose proof (Z.le_max_r VR_CALLEE_STK (Z.max ASTACK (4 * ESTACK))).
pose proof (Z.le_max_l ASTACK (4 * ESTACK)). pose proof (Z.le_max_r ASTACK (4 * ESTACK)). lia.
Qed.
Lemma s2_spill_agree : forall e (W W' : world SEGS) m m' l, vr_spill e W m l ->
(forall ov k, In ov l -> 0 <= k < 8 -> rdW W' m' (vr_s1 e + fst ov + k) = rdW W m (vr_s1 e + fst ov + k)) ->
vr_spill e W' m' l.
Proof.
intros e W W' m m' l H Hk. unfold vr_spill in *. rewrite Forall_forall in *. intros ov Hin.
apply (aval_mem_agree _ _ _ _ _ (H ov Hin)). intros k Hk8. apply Hk; [exact Hin | lia].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis MTL : ameter_laws MT.
Hypothesis RRO : vr_relro_img.
Hypothesis PROGU : vr_prog_unowned B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the read-only bytes are bytes of the image (RRO), so a memory change that keeps the image keeps them *)
Lemma s2_aro_keep : forall (rd rd' : reader), arodata_okP SEGS RLO RHI B rd ->
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) -> rd' a = rd a) ->
arodata_okP SEGS RLO RHI B rd'.
Proof.
intros rd rd' HR Hk a Hro Ho He. rewrite (Hk a); [exact (HR a Hro Ho He) | | exact Ho | exact He].
destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (RRO a Hr)].
Qed.

(* the facts of the segment's states that read only memory the segment does not write: the side-stack frame's place
   and flag pointer, the prologue's saves and spill, the read-only bytes, the recorder and the quit flag *)
Definition s2_st (e : vrE) (pos F : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
F = frame_addr lyc 4 pos /\ rdword (rdW Wc memc) (F + 1016) = Some (flag_addr lyc 4 pos) /\
vr_saved e Wc memc /\ vr_spill e Wc memc (vr_sl1 F) /\ arodata_okP SEGS RLO RHI B (rdW Wc memc) /\
rec_repA B lyc Sc (rdW Wc memc) (e_R e) (e_O e) /\ aval_mem (rdW Wc memc) A_G_QUITTING 4 (e_q0 e).
(* the bytes those facts read *)
Definition s2_keepset (e : vrE) (F a : Z) : Prop :=
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
(F + 1016 <= a < F + 1024) \/ (vr_sp0 e - 104 <= a < vr_sp0 e) \/ (vr_s1 e + 72 <= a < vr_s1 e + 80) \/
(exists p n, In (p, n) (e_O e) /\ p <= a < p + n).

Lemma s2_st_keep : forall e pos F lyc Sc (Wc : world SEGS) memc lyc' Sc' (Wc' : world SEGS) memc',
s2_st e pos F lyc Sc Wc memc ->
frame_addr lyc' 4 pos = frame_addr lyc 4 pos -> flag_addr lyc' 4 pos = flag_addr lyc 4 pos ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc) -> In pn (ablocks B lyc' Sc')) ->
(forall a, s2_keepset e F a -> rdW Wc' memc' a = rdW Wc memc a) ->
s2_st e pos F lyc' Sc' Wc' memc'.
Proof.
intros e pos F lyc Sc Wc memc lyc' Sc' Wc' memc' (EF0 & Hfl & HSv & HSp & HR & HRec & HQ) EF EG HO Hk.
split; [rewrite EF; exact EF0|].
split.
{ rewrite (rdword_ext (rdW Wc memc) (rdW Wc' memc') (F + 1016)); [rewrite EG; exact Hfl|].
  intros k Hk8. apply Hk. right; left. lia. }
split.
{ intros j r Hj. specialize (HSv j r Hj).
  assert (Hj13 : (j < length vr_saved_regs)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbn [length vr_saved_regs] in Hj13.
  apply (aval_mem_agree _ _ _ _ _ HSv). intros k Hk8. apply Hk. right; right; left. lia. }
split.
{ apply (s2_spill_agree e Wc Wc' memc memc' _ HSp). intros ov k Hin Hk8. unfold vr_sl1 in Hin.
  destruct Hin as [<- | []]. cbn [fst]. apply Hk. right; right; right; left. lia. }
split; [apply (s2_aro_keep _ _ HR); intros a H1 H2 H3; apply Hk; left; auto|].
split.
{ apply (rec_repA_agree B lyc Sc lyc' Sc' _ _ _ _ HRec HO).
  - intros k Hk0. apply Hk. left. apply PROGU. exists (A_G_REC, A_G_REC + 960).
    split; [unfold cmd_PG; left; reflexivity | cbn [fst snd]; unfold REC_SIZE in Hk0; lia].
  - intros k Hk0. apply Hk. left. apply PROGU. exists (A_REC_SPILL, A_REC_SPILL + 56).
    split; [unfold cmd_PG; right; left; reflexivity | cbn [fst snd]; unfold SC_SIZE in Hk0; lia].
  - intros [p n] Hpn k Hk0. apply Hk. right; right; right; right. exists p, n. cbn [fst snd] in Hk0 |- *.
    split; [exact Hpn | lia]. }
apply (aval_mem_agree _ _ _ _ _ HQ). intros k Hk4. apply Hk. left. apply PROGU.
exists (A_G_QUITTING, A_G_QUITTING + 4). split; [unfold cmd_PG; right; right; left; reflexivity | cbn [fst snd]; lia].
Qed.

(* the line block's bytes at a memory that agrees on them *)
Lemma s2_line0_agree : forall e q (W : world SEGS) m (W' : world SEGS) m', vr_line0 B e q W m ->
0 <= vr_l (e_n e) (e_D e) ->
(forall k, 0 <= k < vr_l (e_n e) (e_D e) + 1 -> rdW W' m' (q + k) = rdW W m (q + k)) -> vr_line0 B e q W' m'.
Proof.
intros e q W m W' m' [Hf Hb] Hl0 Hk. split; [exact Hf|].
apply (abytes_atR_agree _ _ _ _ (vr_l (e_n e) (e_D e) + 1) Hb); [|exact Hk].
rewrite length_app, length_firstn. cbn [length].
pose proof (Nat.le_min_l (Z.to_nat (vr_l (e_n e) (e_D e))) (length (e_D e))) as Hm.
assert (Hz : Z.of_nat (Z.to_nat (vr_l (e_n e) (e_D e))) = vr_l (e_n e) (e_D e)) by (apply Z2Nat.id; lia). lia.
Qed.

(* where those bytes lie: below the allocation ceiling, out of the shadow band and out of the side-stack frame's words
   below its flag pointer; or in the real frame at or above s1 + 72 *)
Lemma s2_keep_disj : forall e pos F ly S (W : world SEGS) m md a,
AR SEGS B ly S W m md -> In (4, pos) (frames S) -> F = frame_addr ly 4 pos ->
(forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192 ->
s2_keepset e F a ->
(0 <= a < alloc_ceiling /\ ~ (kLowMemEnd <= a < kHighMemBeg) /\ ~ (F <= a < F + 1016)) \/
(vr_s1 e + 72 <= a < vr_sp0 e).
Proof.
intros e pos F ly S W m md a HAR Hfr EF HO Hs1 Hk.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W m md 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
change (fs_frame_bytes 4) with 1024 in Hfc, Hfapp. rewrite <- EF in Hf0, Hfc, Hfapp.
unfold in_app, kLowShadowBeg in Hfapp.
destruct Hk as [(Hi & Ho & He) | [Hfl | [Hsv | [Hsp | (p & n & Hpn & Hp)]]]].
- pose proof (pa_img_range a Hi) as Ha. left. split; [lia|]. split; [lia|].
  intros Hr. apply (frm_img SEGS B LAWS ly S W m md 4 pos a HAR Hfr); [change (fs_frame_bytes 4) with 1024; lia | exact Hi].
- left. split; [lia|]. split; [lia | lia].
- right. lia.
- right. lia.
- pose proof (HO _ Hpn) as Hpb.
  destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hpb) as (_ & Hp4096 & Hpc & Hpapp & _ & _ & Hpn').
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrn].
  unfold in_app, kLowShadowBeg in Hpapp.
  pose proof (sep_block_frame SEGS B LAWS ly S W m md _ _ 4 pos HAR Hpb Hfr) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 4) with 1024 in Hd. rewrite <- EF in Hd.
  left. split; [lia|]. split; [lia | lia].
Qed.

(* the same for the bytes of a block of the walk *)
Lemma s2_blk_disj : forall pos F ly S (W : world SEGS) m md p n a,
AR SEGS B ly S W m md -> In (4, pos) (frames S) -> F = frame_addr ly 4 pos ->
In (p, n) (ablocks B ly S) -> p <= a < p + n ->
0 <= a < alloc_ceiling /\ ~ (kLowMemEnd <= a < kHighMemBeg) /\ ~ (F <= a < F + 1024).
Proof.
intros pos F ly S W m md p n a HAR Hfr EF Hpb Hp.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W m md _ _ HAR Hpb) as (_ & Hp4096 & Hpc & Hpapp & _ & _ & Hpn').
pose proof (req_size_pos n ltac:(lia)) as [_ Hrn].
unfold in_app, kLowShadowBeg in Hpapp.
pose proof (sep_block_frame SEGS B LAWS ly S W m md _ _ 4 pos HAR Hpb Hfr) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 4) with 1024 in Hd. rewrite <- EF in Hd.
split; [lia|]. split; [lia | lia].
Qed.

(* the shadow of the side-stack frame lies in the shadow band *)
Lemma s2_fshadow_band : forall pos F ly S (W : world SEGS) m md i,
AR SEGS B ly S W m md -> In (4, pos) (frames S) -> F = frame_addr ly 4 pos -> 0 <= i < 128 ->
kLowMemEnd <= shadow_addr F + i < kHighMemBeg.
Proof.
intros pos F ly S W m md i HAR Hfr EF Hi.
destruct (frames_bounds SEGS B LAWS ly S W m md 4 pos HAR Hfr) as (Hf0 & Hfc & Hfapp).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite <- EF in Hf0, Hfc.
destruct (vr_shadow_band F 1024 ltac:(lia) ltac:(lia) Hfc) as [Hb1 Hb2].
pose proof (shadow_range_end F 1024 ltac:(lia)) as Hse. change (1024 / 8) with 128 in Hse. lia.
Qed.

(* a block a call adds was not live before it (the live blocks are pairwise apart) *)
Lemma s2_blk_new : forall ly S (W : world SEGS) mem md l x, AR SEGS B ly S W mem md -> ablocks B ly S = l ++ [x] -> ~ In x l.
Proof.
intros ly S W mem md l [p n] HAR E Hin.
assert (Hin2 : In (p, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin2) as (_ & _ & _ & _ & _ & Hpw & Hn).
rewrite E in Hpw. apply in_split in Hin as (l1 & l2 & ->).
assert (Heq : map (fun b : Z * Z => (fst b, req_size (snd b))) ((l1 ++ (p, n) :: l2) ++ [(p, n)]) =
  map (fun b : Z * Z => (fst b, req_size (snd b))) l1 ++ (p, req_size n) ::
  map (fun b : Z * Z => (fst b, req_size (snd b))) l2 ++ (p, req_size n) :: []).
{ rewrite <- app_assoc. rewrite map_app. cbn. rewrite map_app. reflexivity. }
pose proof (pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw Heq) as Hd.
unfold zdisjoint in Hd. cbn in Hd. pose proof (req_size_pos n ltac:(lia)). lia.
Qed.

(* a live block that is none of the recorder's has no byte in this call's footprint *)
Lemma s2_blk_not_fp : forall e ly S (W : world SEGS) m md p n i,
AR SEGS B ly S W m md -> (forall pn, In pn (e_O e) -> In pn (ablocks B ly S)) ->
In (p, n) (ablocks B ly S) -> ~ In (p, n) (e_O e) -> 0 <= i < req_size n -> ~ inFP (vr_fp e) (p + i).
Proof.
intros e ly S W m md p n i HAR HO Hpn HnO Hi (r & Hin & Hr).
unfold vr_fp in Hin. apply in_app_or in Hin as [Hin | Hin].
- assert (Epg : VERBS_RECEIVE_PG = cmd_PG) by reflexivity.
  rewrite Epg in Hin. destruct (PROGU (p + i) (ex_intro _ r (conj Hin Hr))) as (Himg & _).
  exact (blk_img SEGS B LAWS ly S W m md p n (p + i) HAR Hpn ltac:(lia) Himg).
- unfold ablocks_fp in Hin. apply in_map_iff in Hin as ([p' n'] & <- & Hpn'). cbn [fst snd] in Hr.
  assert (Hne : (p', n') <> (p, n)) by (intros Ex; rewrite Ex in Hpn'; exact (HnO Hpn')).
  pose proof (sep_blocks SEGS B LAWS ly S W m md _ _ _ _ HAR (HO _ Hpn') Hpn Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* strndup (acall_kept with its new block): the bytes s2_st reads and the side-stack frame's shadow are kept *)
Lemma s2_keep_call : forall e pos F lyc Sc (W : world SEGS) memT ly2 S2 (W2 : world SEGS) mem2 md2 slo shi res nres,
acall_kept SEGS B lyc Sc W memT W2 mem2 slo shi (fun a => res <= a < res + req_size nres) ->
AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, nres)] ->
In (4, pos) (frames Sc) -> frames S2 = frames Sc -> F = frame_addr lyc 4 pos -> frame_addr ly2 4 pos = F ->
(forall pn, In pn (e_O e) -> In pn (ablocks B lyc Sc)) ->
vr_sp0 e < 2 ^ 64 -> alloc_ceiling <= vr_s1 e -> vr_sp0 e - 224 <= vr_s1 e <= vr_sp0 e - 192 -> shi <= vr_s1 e ->
(forall a, s2_keepset e F a -> rdW W2 mem2 a = rdW W memT a) /\
(forall i, 0 <= i < 128 -> rdW W2 mem2 (shadow_addr F + i) = rdW W memT (shadow_addr F + i)).
Proof.
intros e pos F lyc Sc W memT ly2 S2 W2 mem2 md2 slo shi res nres (K1 & K2 & K3 & K4 & _) HAR2 Hab2 Hfr Hfrs EF EF2 HO
  Hsp64 Hceil Hs1 Hshi.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (Hfr2 : In (4, pos) (frames S2)) by (rewrite Hfrs; exact Hfr).
assert (Hnew : In (res, nres) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
assert (Hold : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly2 S2))
  by (intros pn Hpn; rewrite Hab2; apply in_or_app; left; exact Hpn).
pose proof (s2_blk_new ly2 S2 W2 mem2 md2 _ _ HAR2 Hab2) as Hfresh.
destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 res nres HAR2 Hnew) as (_ & Hr4096 & Hrc & Hrapp & _ & _ & Hrn).
pose proof (req_size_pos nres ltac:(lia)) as [_ Hrq].
unfold in_app, kLowShadowBeg in Hrapp.
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ 4 pos HAR2 Hnew Hfr2) as Hdf.
unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. change (fs_frame_bytes 4) with 1024 in Hdf. rewrite EF2 in Hdf.
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hfr2) as (Hf0 & Hfc & Hfapp).
change (fs_frame_bytes 4) with 1024 in Hfc. rewrite EF2 in Hf0, Hfc.
split.
- intros a Hk. destruct Hk as [(Hi & Ho & He) | [Hfl | [Hsv | [Hsp | (p & n & Hpn & Hp)]]]].
  + exact (K3 a Hi Ho He).
  + apply (K4 4 pos a Hfr).
    * left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. rewrite <- EF. lia.
    * intros Hx. cbv beta in Hx. lia.
  + apply K1; lia.
  + apply K1; lia.
  + pose proof (HO _ Hpn) as Hpb. pose proof (Hold _ Hpb) as Hpb2.
    destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 Hpb2) as (_ & _ & _ & _ & _ & _ & Hpn').
    pose proof (req_size_pos n ltac:(lia)) as [_ Hrnn].
    assert (Hne : (p, n) <> (res, nres)) by (intros Ex; rewrite Ex in Hpb; exact (Hfresh Hpb)).
    pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ _ _ HAR2 Hpb2 Hnew Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd.
    replace a with (p + (a - p)) by lia. apply (K2 p n (a - p) Hpb); [lia|].
    intros Hx. cbv beta in Hx. lia.
- intros i Hi. apply (K4 4 pos (shadow_addr F + i) Hfr).
  + right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 4 / 8) with 128. rewrite <- EF. lia.
  + intros Hx. cbv beta in Hx.
    pose proof (s2_fshadow_band pos F ly2 S2 W2 mem2 md2 i HAR2 Hfr2 (eq_sym EF2) Hi) as Hb. lia.
Qed.

(* strndup's call shape for the meter (the interface's vri_meter_ok and vri_meter_step): one malloc of at most
   VERBS_RECEIVE_REQ bytes, no free, one event (a = 1, b = 0, ev = 1) *)
Lemma s2_strndup_acct : forall n, 0 <= n <= VERBS_RECEIVE_REQ ->
mo_malloc MT n <= 1 * mo_malloc MT VERBS_RECEIVE_REQ + 0 * mo_free MT.
Proof. intros n Hn. pose proof (mo_malloc_mono MT MTL n VERBS_RECEIVE_REQ Hn). lia. Qed.

(* the meter after strndup *)
Lemma s2_meter_malloc : forall e Sc S2 k nm n, vr_meter MT e Sc k nm -> mo_le MT Sc S2 (mo_malloc MT n) ->
0 <= n <= VERBS_RECEIVE_REQ -> vr_meter MT e S2 (k + 1) (nm + 1).
Proof.
intros e Sc S2 k nm n HM H2 Hn.
eapply vri_meter_step with (X := mo_malloc MT n) (a := 1) (b := 0) (ev := 1);
  [exact MTL | exact HM | exact H2 | exact (s2_strndup_acct n Hn) | lia | lia].
Qed.

(* the meter's room for strndup's malloc at the segment's entry, where no event is spent yet *)
Lemma s2_mo_first : forall e Sc k nm c, vr_ent B MT e ->
vr_meter MT e Sc k nm -> k <= 0 -> 0 <= c <= VERBS_RECEIVE_REQ -> mo_ok MT Sc (mo_malloc MT c).
Proof.
intros e Sc k nm c HENT HM Hk Hc.
pose proof (s2_ev_vr_pos (e_R e) (e_D e)) as Hev.
eapply vri_meter_ok with (a := 1) (b := 0) (ev := 1);
  [exact MTL | exact HENT | exact HM | exact (s2_strndup_acct c Hc) | lia | lia | lia].
Qed.

End e.
End f.
End d.
