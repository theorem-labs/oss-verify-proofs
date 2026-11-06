(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: helpers of segment S31 (AFTER, 0x8daf4-0x8db4c) of the walk of verbs_receive on
   the ASan build of plugin-hostd/fuzz_command (lib/A/Prog/verbs_receive_s31.v), on the interface of the fixed
   statements (lib/A/Prog/verbs_receive_iface.v; the read-only range is CmdGlob's CMD_RLO / CMD_RHI): the boundary
   state vr_core carried across a step that changes memory only inside a window below the segment's stack pointer
   and inside the errno cell (a run of the symbolic executor without stores, and the runtime entries strcspn, strncmp
   and atoi through the kit's aj_art_at); the copy block's word array carried the same way; the symbolic state seeded
   from a boundary state (the registers as atoms, tok[0] and tok[1] as the two extra atoms of a read-only region at
   s6 = tok); what a recorder call with the footprint g_rec, record.spill and the recorder's blocks keeps (the shape of
   verbs_receive_s08_lib.v's ck_* lemmas); and list facts about the live blocks. The lemmas live in the module VrS31K
   so that their names meet no other segment's. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import verbs_receive_c verbs_receive_iface verbs_receive_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Module VrS31K.

(* the reader view of a little-endian field is the byte view the symbolic executor's chunks take *)
Lemma aval_val : forall segs (H : word -> bool) (m : word -> option byte) a n v,
aval_mem (aview segs H m) a n v -> val_mem segs (mrestrict H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. pose proof (Hv k Hk) as Hb.
destruct (aview_byte segs H m _ _ Hb) as (b & Hm & Hbv & Hrange). rewrite Hm. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite <- Hbv. rewrite Z.mod_small; [reflexivity|].
change (bv_modulus 8) with 256. exact Hrange.
Qed.

(* the registers a boundary lists *)
Lemma vr_rv_app : forall regs l1 l2, vr_rv regs (l1 ++ l2) <-> vr_rv regs l1 /\ vr_rv regs l2.
Proof. intros regs l1 l2. unfold vr_rv. apply Forall_app. Qed.
Lemma vr_rv_incl : forall regs l l', incl l' l -> vr_rv regs l -> vr_rv regs l'.
Proof. intros regs l l' Hi H. unfold vr_rv in *. rewrite Forall_forall in *. intros x Hx. exact (H x (Hi x Hx)). Qed.
Lemma vr_rv_get : forall regs l n v, vr_rv regs l -> In (n, v) l -> getr regs (Z_to_bv 5 n) = w64 v.
Proof. intros regs l n v H Hin. unfold vr_rv in H. rewrite Forall_forall in H. exact (H (n, v) Hin). Qed.
Lemma vr_rv_intro : forall regs l, (forall r v, In (r, v) l -> getr regs (Z_to_bv 5 r) = w64 v) -> vr_rv regs l.
Proof. intros regs l H. unfold vr_rv. apply Forall_forall. intros [r v] Hin. exact (H r v Hin). Qed.
Lemma vr_rv_pres : forall regs regs' l, aregs_preserved regs regs' ->
Forall (fun rv => acallee_saved (fst rv)) l -> vr_rv regs l -> vr_rv regs' l.
Proof.
intros regs regs' l HP Hcs H. unfold vr_rv in *. rewrite Forall_forall in *. intros x Hx.
rewrite (HP (fst x) (Hcs x Hx)). exact (H x Hx).
Qed.

(* the live blocks are pairwise apart, so none occurs twice *)
Lemma pw_nodup : forall (l : list (Z * Z)),
pairwise zdisjoint (map (fun b => (fst b, req_size (snd b))) l) -> (forall b, In b l -> 0 <= snd b) -> List.NoDup l.
Proof.
induction l as [|x t IH]; intros Hpw Hn; [constructor|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hx Ht]. constructor.
- intros Hin. rewrite Forall_forall in Hx.
  specialize (Hx (fst x, req_size (snd x)) (in_map (fun b => (fst b, req_size (snd b))) t x Hin)).
  pose proof (req_size_pos (snd x) (Hn x (or_introl eq_refl))) as [Hr _]. unfold zdisjoint in Hx. cbn [fst snd] in Hx. lia.
- apply IH; [exact Ht|]. intros b Hb. exact (Hn b (or_intror Hb)).
Qed.
Lemma nodup_app_disj : forall {X} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 x Hnd H1 H2; [destruct H1|].
cbn [app] in Hnd. inversion Hnd as [|y' l' Hy Hnd' E]; subst.
destruct H1 as [<- | H1]; [apply Hy; apply in_or_app; right; exact H2 | exact (IH l2 x Hnd' H1 H2)].
Qed.
Lemma nodup_app_r : forall {X} (l1 l2 : list X), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros X l1. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. cbn in H. apply NoDup_cons_iff in H as [_ Hd].
exact (IH _ Hd).
Qed.
Lemma nodup_app_intro : forall {X} (l1 l2 : list X), List.NoDup l1 -> List.NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
List.NoDup (l1 ++ l2).
Proof.
intros X l1. induction l1 as [|y l1 IH]; intros l2 H1 H2 Hd; [exact H2|]. apply NoDup_cons_iff in H1 as [Hn H1].
cbn. apply NoDup_cons_iff. split.
- intros Hin. apply in_app_or in Hin as [Hin|Hin]; [exact (Hn Hin) | exact (Hd y (or_introl eq_refl) Hin)].
- apply IH; [exact H1 | exact H2 | intros x Hx; apply Hd; right; exact Hx].
Qed.

(* readers that read the same *)
Definition rdeq (rd rd' : reader) : Prop := forall a, rd' a = rd a.
Lemma aval_mem_eq : forall rd rd' a n v, rdeq rd rd' -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v E H k Hk. rewrite E. exact (H k Hk). Qed.
Lemma rdword_eq : forall rd rd' a, rdeq rd rd' -> rdword rd' a = rdword rd a.
Proof. intros rd rd' a E. apply rdword_ext. intros k _. apply E. Qed.

(* the 8-byte value of aval_mem, as rdword reads it *)
Lemma rdword_of_aval : forall (rd : reader) a v, aval_mem rd a 8 v -> 0 <= v < 2 ^ 64 -> rdword rd a = Some v.
Proof.
intros rd a v H Hr. unfold rdword.
assert (B0 : rd a = Some (le_byte v 8 0)) by (rewrite <- (Z.add_0_r a) at 1; exact (H 0%nat ltac:(lia))).
change (rd (a + 1)) with (rd (a + Z.of_nat 1)). change (rd (a + 2)) with (rd (a + Z.of_nat 2)).
change (rd (a + 3)) with (rd (a + Z.of_nat 3)). change (rd (a + 4)) with (rd (a + Z.of_nat 4)).
change (rd (a + 5)) with (rd (a + Z.of_nat 5)). change (rd (a + 6)) with (rd (a + Z.of_nat 6)).
change (rd (a + 7)) with (rd (a + Z.of_nat 7)).
rewrite B0, (H 1%nat), (H 2%nat), (H 3%nat), (H 4%nat), (H 5%nat), (H 6%nat), (H 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

Lemma aval_of_abytes8 : forall rd a l v, abytes_atR rd a l -> length l = 8%nat ->
(forall k, (k < 8)%nat -> bv_unsigned (nth k l (Z_to_bv 8 0)) = le_byte v 8 k) -> aval_mem rd a 8 v.
Proof. intros rd a l v H Hl Hk k Hkk. rewrite (H k ltac:(lia)). rewrite (Hk k Hkk). reflexivity. Qed.
(* cmd_ro_ok holds the four GOT words of cmd_got_ok *)
Lemma got_of_ro : forall rd, cmd_ro_ok rd -> cmd_got_ok rd.
Proof.
intros rd [Hb _]. unfold cmd_ro_bytes in Hb.
assert (G1 : abytes_atR rd 0xa7068 RO_ptr_a7068) by (decompose [and] Hb; assumption).
assert (G2 : abytes_atR rd 0xa7070 RO_ptr_a7070) by (decompose [and] Hb; assumption).
assert (G3 : abytes_atR rd 0xa7078 RO_ptr_a7078) by (decompose [and] Hb; assumption).
assert (G4 : abytes_atR rd 0xa7080 RO_ptr_a7080) by (decompose [and] Hb; assumption).
unfold cmd_got_ok.
split; [apply (aval_of_abytes8 rd _ _ _ G1 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G2 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
split; [apply (aval_of_abytes8 rd _ _ _ G3 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia|].
apply (aval_of_abytes8 rd _ _ _ G4 eq_refl); intros k Hk; do 8 (destruct k as [|k]; [vm_compute; reflexivity|]); lia.
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

Lemma rdeq_of_frame : forall E rs H (m m' : word -> option byte),
frame_of E rs (mrestrict H m) (mrestrict H m') -> Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
rdeq (aview SEGS H m) (aview SEGS H m').
Proof.
intros E rs H m m' Hf Hro a. apply (aview_eq_of SEGS). apply Hf.
intros (r & Hr & Ha). rewrite Forall_forall in Hro. pose proof (Hro r Hr). lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : AF0m.CmdBSyms B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma s31_errno : as_errno B = 0x5e44f4.
Proof. rewrite (AF0m.ts_errno B HB). reflexivity. Qed.

Lemma ablocks_nodup : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. destruct (ablocks B ly S) as [|[p n] l] eqn:El; [constructor|].
assert (Hin : In (p, n) (ablocks B ly S)) by (rewrite El; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite El in Hpw. apply pw_nodup; [exact Hpw|].
intros b Hb. rewrite <- El in Hb. destruct b as [b m].
destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia.
Qed.

(* a memory that agrees with another outside a window [lo, hi) and outside the errno cell *)
Definition kp (W : world SEGS) (m m' : word -> option byte) (lo hi : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ (0x5e44f4 <= a < 0x5e44f8) -> rdW W m' a = rdW W m a.

Lemma cmd_ro_ends_low : forall e, In e cmd_ro_ends -> 0 <= e < 0x8e440.
Proof.
intros e He. assert (Hall : forallb (fun x => (0 <=? x) && (x <? 0x8e440)) cmd_ro_ends = true) by (vm_compute; reflexivity).
rewrite forallb_forall in Hall. specialize (Hall e He). apply andb_true_iff in Hall as [H1 H2].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma abytes_atR_low : forall (rd rd' : reader) p l, abytes_atR rd p l -> 0 <= p ->
p + Z.of_nat (length l) <= 0x5e0000 -> (forall a, 0 <= a < 0x5e0000 -> rd' a = rd a) -> abytes_atR rd' p l.
Proof. intros rd rd' p l H Hp Hl K i Hi. rewrite K by lia. exact (H i Hi). Qed.
(* cmd_ro_ok names image bytes below 0x5e0000 only *)
Lemma cmd_ro_ok_keep : forall (rd rd' : reader), cmd_ro_ok rd -> (forall a, 0 <= a < 0x5e0000 -> rd' a = rd a) -> cmd_ro_ok rd'.
Proof.
intros rd rd' [HBy HT] K. split.
- unfold cmd_ro_bytes in *. decompose [and] HBy. clear HBy.
  repeat split; (eapply abytes_atR_low; [eassumption | lia | apply Z.leb_le; vm_compute; reflexivity | exact K]).
- intros e He a Ha. pose proof (cmd_ro_ends_low e He). pose proof (Z.mod_pos_bound e 8 ltac:(lia)).
  rewrite K by lia. exact (HT e He a Ha).
Qed.

(* every byte arodata_okP names lies in the image or in the fixed read-only range, below 0x606000 *)
Lemma in_roP_low : forall a, in_roP SEGS RLO RHI a -> 0 <= a < 0x606000.
Proof.
intros a [(s & Hs & _ & Hr) | Hr].
- pose proof (pa_img_range a (ex_intro _ s (conj Hs Hr))). lia.
- unfold CMD_RLO, CMD_RHI in Hr. lia.
Qed.

Lemma kp_low : forall W m m' lo hi a, kp W m m' lo hi -> 0 <= a -> a < lo -> a < 2 ^ 64 ->
~ (0x5e44f4 <= a < 0x5e44f8) -> rdW W m' a = rdW W m a.
Proof. intros W m m' lo hi a HK H0 Hl H64 He. apply HK; lia. Qed.

Lemma aro_keep : forall (W : world SEGS) m m' lo hi, arodata_okP SEGS RLO RHI B (rdW W m) -> kp W m m' lo hi ->
0x606000 <= lo -> arodata_okP SEGS RLO RHI B (rdW W m').
Proof.
intros W m m' lo hi HA HK Hlo a Hro Ho He. pose proof (in_roP_low a Hro) as Ha.
assert (He' : ~ (0x5e44f4 <= a < 0x5e44f8)) by (rewrite s31_errno in He; exact He).
rewrite (HK a ltac:(lia) ltac:(lia) He'). exact (HA a Hro Ho He).
Qed.

Lemma env_keep : forall (W : world SEGS) m m' lo hi, vr_env B W m -> kp W m m' lo hi ->
alloc_ceiling <= lo -> (exists ev', rd32 (rdW W m') (as_errno B) ev') -> vr_env B W m'.
Proof.
intros W m m' lo hi (HA & HG & HR & HAG & HF & _) HK Hlo Hev. pose proof asan_consts as (C1 & _).
assert (K : forall a, 0 <= a < 0x5e0000 -> rdW W m' a = rdW W m a) by (intros a Ha; apply (kp_low W m m' lo hi a HK); lia).
split; [exact (aro_keep W m m' lo hi HA HK ltac:(lia))|].
split.
{ destruct HG as (G1 & G2 & G3 & G4).
  split; [|split; [|split]]; (eapply aval_mem_agree; [eassumption|]); intros kk Hkk; apply K; cbn in Hkk; lia. }
split; [exact (cmd_ro_ok_keep _ _ HR K)|].
split.
{ destruct HAG as [H1 (cn & H2)]. split.
  - rewrite (rdword_ext (rdW W m) (rdW W m') 684184); [exact H1|]. intros kk Hkk. apply K. lia.
  - exists cn. rewrite (rdword_ext (rdW W m) (rdW W m') 6309336); [exact H2|]. intros kk Hkk. apply (kp_low W m m' lo hi _ HK); lia. }
split; [rewrite K by lia; exact HF | exact Hev].
Qed.

Lemma toks_len64 : forall D, (length (Verbs.toks D) <= 64)%nat.
Proof. intros D. unfold Verbs.toks. rewrite length_firstn. unfold Verbs.line_words_max. lia. Qed.

(* the copy block's word array: its pointer cells lie in the side-stack frame and its words in the copy block,
   both below the allocation ceiling and away from the errno cell *)
Lemma copy_keep : forall e F c tp lyc Sc (Wc : world SEGS) memc mdc mem2 lo hi pos k,
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc Wc memc mdc k ->
F = frame_addr lyc 4 pos -> In (vr_cb e c) (ablocks B lyc Sc) ->
vr_copy B e F c tp Wc memc -> kp Wc memc mem2 lo hi -> alloc_ceiling <= lo -> vr_copy B e F c tp Wc mem2.
Proof.
intros e F c tp lyc Sc Wc memc mdc mem2 lo hi pos k HJ EF Hcb [Hfr (Hmod & Hlen & Hptr & Hstr)] HK Hlo.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (HF0 & HFc & _).
pose proof (frm_off_imgP B lyc Sc Wc memc mdc 4 pos HAR Hin) as HFo.
change (fs_frame_bytes 4) with 1024 in HFc, HFo. rewrite <- EF in HF0, HFc, HFo. unfold off_img in HFo.
unfold vr_cb in Hcb.
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc _ _ HAR Hcb) as (_ & Hc4096 & Hcc & _).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc _ _ HAR Hcb) as Hco. unfold off_img in Hco.
pose proof (req_size_pos (Z.of_nat (length (Verbs.line (e_D e))) + 1) ltac:(lia)) as [_ Hrq].
pose proof (toks_len64 (e_D e)) as Hl64.
split; [exact Hfr|]. split; [exact Hmod|]. split; [exact Hlen|]. split.
- intros i p Hi. assert (Hil : (i < length tp)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  apply (aval_mem_agree _ _ _ _ _ (Hptr i p Hi)). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk.
  apply (kp_low Wc memc mem2 lo hi _ HK); lia.
- intros i p w Hi Hw. destruct (Hstr i p w Hi Hw) as (Hs & Hw8 & Hcp & Hpe). split; [|split; [exact Hw8 | split; [exact Hcp | exact Hpe]]].
  apply (astr_atR_agree _ _ p w (Z.of_nat (length w) + 1) Hs); [lia|].
  intros kk Hkk. apply (kp_low Wc memc mem2 lo hi _ HK); lia.
Qed.

(* the boundary state across a step that changes memory only in a window [lo, hi) below s1 and in the errno cell,
   keeps the model state and the journal's count, and gives new registers *)
Lemma core_keep : forall e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc regs2 mem2 md2 lo hi,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(4, pos)]
  lyc Sc Wc mem2 md2 k ->
kp Wc memc mem2 lo hi -> alloc_ceiling <= lo -> hi <= vr_s1 e ->
(exists ev', rd32 (rdW Wc mem2) (as_errno B) ev') ->
vr_rv regs2 (vr_base B e ++ rl') ->
Forall (fun ov => 0 <= fst ov <= 128) sl ->
vr_core B MT e pos F tmps sh sl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regs2 mem2 md2.
Proof.
intros e pos F tmps sh sl rl rl' Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc regs2 mem2 md2 lo hi
  HC HJ2 HK Hlo Hhi Herr HRV Hsl.
destruct HC as (HJ & Hk & HM & Hnm & HFR & _ & HSV & HSP & HENV & HREC & HnD & HPERM & HQ).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HTS : VERBS_RECEIVE_STK = 16992) by (vm_compute; reflexivity).
assert (Hs1 : vr_sp0 e - 223 <= vr_s1 e <= vr_sp0 e - 192).
{ unfold vr_s1. pose proof (Z.mod_pos_bound (vr_sp0 e - 192) 32 ltac:(lia)). lia. }
assert (Khi : forall a, vr_s1 e <= a < 2 ^ 64 -> rdW Wc mem2 a = rdW Wc memc a) by (intros a Ha; apply HK; lia).
assert (Kce : forall a, 0 <= a < alloc_ceiling -> ~ (0x5e44f4 <= a < 0x5e44f8) -> rdW Wc mem2 a = rdW Wc memc a)
  by (intros a Ha He; apply (kp_low Wc memc mem2 lo hi a HK); lia).
split; [exact HJ2|]. split; [exact Hk|]. split; [exact HM|]. split; [exact Hnm|].
split.
{ destruct HFR as (EF & Hfw & Hsh).
  assert (Hin : In (4, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS lyc Sc Wc memc mdc 4 pos HAR Hin) as (HF0 & HFc & _).
  pose proof (frm_off_imgP B lyc Sc Wc memc mdc 4 pos HAR Hin) as HFo.
  change (fs_frame_bytes 4) with 1024 in HFc, HFo. rewrite <- EF in HF0, HFc, HFo. unfold off_img in HFo.
  split; [exact EF|]. split.
  - rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem2) (F + 1016)); [exact Hfw|]. intros kk Hkk. apply Kce; lia.
  - intros i Hi. rewrite Kce; [exact (Hsh i Hi)| |]; unfold shadow_addr, SHADOW_OFF;
    pose proof (Z.div_mod F 8 ltac:(lia)); pose proof (Z.mod_pos_bound F 8 ltac:(lia)); lia. }
split; [exact HRV|].
split.
{ intros j r Hj. assert (Hjl : (j < 13)%nat) by (change 13%nat with (length vr_saved_regs); apply nth_error_Some; rewrite Hj; discriminate).
  apply (aval_mem_agree _ _ _ _ _ (HSV j r Hj)). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Khi. lia. }
split.
{ unfold vr_spill in *. rewrite Forall_forall in HSP, Hsl |- *. intros ov Hov. pose proof (Hsl ov Hov).
  apply (aval_mem_agree _ _ _ _ _ (HSP ov Hov)). intros kk Hkk. change (Z.of_nat 8) with 8 in Hkk. apply Khi. lia. }
split; [exact (env_keep Wc memc mem2 lo hi HENV HK Hlo Herr)|].
split.
{ apply (rec_repA_agree B lyc Sc lyc Sc _ _ Rc Oc HREC (fun pn _ H => H)).
  - intros kk Hkk. unfold REC_SIZE in Hkk. apply Kce; unfold A_G_REC; lia.
  - intros kk Hkk. unfold SC_SIZE in Hkk. apply Kce; unfold A_REC_SPILL; lia.
  - intros [p n] Hpn kk Hkk. cbn [fst snd] in *. pose proof (rec_repA_in_blocks B _ _ _ _ _ _ HREC Hpn) as Hb.
    destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc p n HAR Hb) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn).
    pose proof (blk_off_imgP B lyc Sc Wc memc mdc p n HAR Hb) as Ho. unfold off_img in Ho.
    pose proof (req_size_pos n ltac:(lia)) as [_ Hr]. apply Kce; lia. }
split; [exact HnD|]. split; [exact HPERM|].
apply (aval_mem_agree _ _ _ _ _ HQ). intros kk Hkk. change (Z.of_nat 4) with 4 in Hkk. apply Kce; unfold A_G_QUITTING; lia.
Qed.

Lemma core_weaken : forall e pos F tmps sh sl sl' rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc,
vr_core B MT e pos F tmps sh sl rl Rc Oc qv k kmax nm nmax lyc Sc Wc regsc memc mdc ->
incl sl' sl -> incl rl' rl -> kmax <= kmax' -> nmax <= nmax' ->
vr_core B MT e pos F tmps sh sl' rl' Rc Oc qv k kmax' nm nmax' lyc Sc Wc regsc memc mdc.
Proof.
intros e pos F tmps sh sl sl' rl rl' Rc Oc qv k kmax kmax' nm nmax nmax' lyc Sc Wc regsc memc mdc
  (HJ & Hk & HM & Hnm & HFR & HRV & HSV & HSP & HENV & HREC & HnD & HPERM & HQ) Hsl Hrl Hkm Hnx.
split; [exact HJ|]. split; [lia|]. split; [exact HM|]. split; [lia|]. split; [exact HFR|].
split; [exact (vr_rv_incl _ _ _ (incl_app_app (incl_refl _) Hrl) HRV)|].
split; [exact HSV|].
split; [unfold vr_spill in *; rewrite Forall_forall in *; intros x Hx; exact (HSP x (Hsl x Hx))|].
split; [exact HENV|]. split; [exact HREC|]. split; [exact HnD|]. split; [exact HPERM | exact HQ].
Qed.

(* the state at 0x8db50 when no call follows the reply *)
Lemma s31_to_af : forall e O2 pos F q c lyc Sc Wc regsc memc mdc k nm rlx,
vr_aft (e_D e) = None ->
vr_core B MT e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c ++ rlx)
  (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e) k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc Wc regsc memc mdc ->
vr_fresh B e (vr_lb e q) -> vr_fresh B e (vr_cb e c) ->
vr_af B MT e Wc (cfg_at SEGS (vr_pc 0x8db50) regsc memc mdc).
Proof.
intros e O2 pos F q c lyc Sc Wc regsc memc mdc k nm rlx Haft HC Hl Hc.
exists O2, pos, F, q, c, lyc, Sc, regsc, memc, mdc, k, nm.
split; [reflexivity|]. split; [|split; assumption].
assert (E3 : vr_R3 (e_R e) (e_D e) = vr_R2 (e_R e) (e_D e)) by (unfold vr_R3; rewrite Haft; reflexivity).
assert (K3 : vr_k3 (e_R e) (e_D e) = vr_k2 (e_R e) (e_D e)) by (unfold vr_k3, ev_after; rewrite Haft; lia).
rewrite E3, K3. eapply core_weaken; [exact HC | | | lia | unfold VR_NM_AR, VR_NM_AF; lia].
- intros x Hx. unfold vr_sl3. cbn in Hx |- *. destruct Hx as [<- | []]. tauto.
- intros x Hx. apply in_or_app. left. unfold vr_rl_af, vr_rl_ar in *. cbn in Hx |- *. tauto.
Qed.

(* the symbolic state at a boundary of the segment: the registers as atoms, and tok[0], tok[1] (atoms 32 and 33)
   in a read-only region based at s6 = tok *)
Definition tok_region : YP09.region :=
YP09.mkRegion (Some 22%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))].
Definition ss31 (pc : Z) : sstate := mkSS pc sr_atoms [tok_region] None (mkFacts [] [] []).
Definition ssr31 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition E31 (regs : bvmap 5 word) (p0 p1 : Z) : env := Eimg (Ereg regs [w64 p0; w64 p1]).

Lemma ro_ss31 : forall pc, Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) (ss_mem (ss31 pc)).
Proof. intros pc. repeat constructor; cbn; lia. Qed.

Lemma s31_seed : forall (Wc : world SEGS) (regsc : bvmap 5 word) memc pc F p0 p1,
getr regsc 22 = w64 (F + 32) -> 0 <= F -> F + 48 <= 2 ^ 64 ->
aval_mem (rdW Wc memc) (F + 32) 8 p0 -> aval_mem (rdW Wc memc) (F + 40) 8 p1 ->
0 <= p0 < 2 ^ 64 -> 0 <= p1 < 2 ^ 64 ->
st_ok_pi SEGS VAL (E31 regsc p0 p1) (ss31 pc) (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros Wc regsc memc pc F p0 p1 H22 HF0 HF48 H0 H1 Hp0 Hp1.
rewrite restrict_mkst_fx. unfold ss31, E31. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, tok_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite (ew_Eimg_Ereg_nat regsc _ 22 22%bv eq_refl), H22. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val SEGS _ _ (F + 32) 0 8 (SOff 32 0) p0).
    * cbn [sv_denot ew Eimg Ereg Nat.ltb Nat.leb andb nth Nat.sub]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * rewrite Z.add_0_r. exact (aval_val SEGS _ _ _ _ _ H0).
  + apply (chunk_ok_val SEGS _ _ (F + 32) 8 8 (SOff 33 0) p1).
    * cbn [sv_denot ew Eimg Ereg Nat.ltb Nat.leb andb nth Nat.sub]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    * cbn. lia.
    * replace (F + 32 + 8) with (F + 40) by lia. exact (aval_val SEGS _ _ _ _ _ H1).
- cbn. tauto.
- unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor].
Qed.

Lemma s31_seed_r : forall (Wc : world SEGS) (regsc : bvmap 5 word) memc pc,
st_ok_pi SEGS VAL (Eimg (Ereg regsc [])) (ssr31 pc) (restrict (w_H Wc) (mkst regsc (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros Wc regsc memc pc. rewrite restrict_mkst_fx. unfold ssr31. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.

Lemma E31_img : forall regs p0 p1, img_env VAL A_LIM (E31 regs p0 p1).
Proof. intros. unfold E31. apply Eimg_env. Qed.
Lemma E31_agree : forall regs p0 p1, env_agree 32 (Ereg regs [w64 p0; w64 p1]) (E31 regs p0 p1).
Proof. intros. unfold E31. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma E31_32 : forall regs p0 p1, ew (E31 regs p0 p1) 32 = w64 p0.
Proof. intros. reflexivity. Qed.
Lemma E31_33 : forall regs p0 p1, ew (E31 regs p0 p1) 33 = w64 p1.
Proof. intros. reflexivity. Qed.
Lemma E31_reg : forall regs p0 p1 n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (E31 regs p0 p1) n = getr regs r.
Proof. intros regs p0 p1 n r Hn. unfold E31. apply ew_Eimg_Ereg_nat. exact Hn. Qed.
Lemma Er_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma getr_Z2 : forall (r : bvmap 5 word), getr r (Z_to_bv 5 2) = getr r 2.
Proof. intros. reflexivity. Qed.

(* the registers a run leaves as they were: those whose symbolic value is still their own atom *)
Lemma rv_kept : forall E ss ms regsc extra (l : list (Z * Z)),
st_ok SEGS E ss ms -> env_agree 32 (Ereg regsc extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0))
  (map (fun rv => Z_to_bv 5 (fst rv)) l) = true ->
vr_rv regsc l -> vr_rv (ms_regs ms) l.
Proof.
intros E ss ms regsc extra l HS HA Hl H. unfold vr_rv in *. rewrite Forall_forall in *. intros x Hx.
rewrite (regs_kept_of_st_ok SEGS E ss ms regsc extra _ HS HA Hl (Z_to_bv 5 (fst x)) (in_map _ _ _ Hx)). exact (H x Hx).
Qed.

Lemma s1_props : forall e, vr_sp0 e mod 16 = 0 ->
(vr_s1 e - vr_sp0 e) mod 16 = 0 /\ vr_sp0 e - 223 <= vr_s1 e <= vr_sp0 e - 192.
Proof.
intros e H16. unfold vr_s1. set (x := vr_sp0 e - 192). pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as Hm.
pose proof (Z.div_mod x 32 ltac:(lia)) as Hd. pose proof (Z.div_mod (vr_sp0 e) 16 ltac:(lia)) as Hd16.
split; [|unfold x in *; lia].
apply Z.mod_divide; [lia|]. exists (2 * (x / 32) - vr_sp0 e / 16). unfold x in *. lia.
Qed.

Lemma obj_val : forall E i v, img_env VAL A_LIM E -> cmd_val_objs -> (i < length cmd_objs)%nat ->
nth i cmd_objs 0 = v -> (A_OBJ i < A_LIM)%nat -> ew E (A_OBJ i) = w64 v.
Proof.
intros E i v HE HV Hi Hv Hl. rewrite (img_env_atomP E (A_OBJ i) HE) by (unfold A_OBJ, A_TEXT in *; lia).
rewrite (HV i Hi), Hv. reflexivity.
Qed.

Lemma in_shr_chk : forall a n, existsb (fun x => (fst x =? a) && (snd x =? n)) vr_shr = true -> In (a, n) vr_shr.
Proof.
intros a n H. apply existsb_exists in H as ([a' n'] & Hin & Hq). apply andb_true_iff in Hq as [H1 H2].
apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. cbn [fst snd] in *. subst. exact Hin.
Qed.

Lemma tail_lit : forall (W : world SEGS) mem e, cmd_ro_ok (rdW W mem) -> existsb (Z.eqb e) cmd_ro_ends = true ->
atail_vis SEGS W mem e.
Proof.
intros W mem e [_ HT] Hin a Ha. apply existsb_exists in Hin as (e' & He' & Hq). apply Z.eqb_eq in Hq. subst e'.
exact (HT e He' a Ha).
Qed.

(* an image literal the runtime entries read: its bytes, its shadow from the record (vr_shadow_ok) *)
Lemma lit_rd : forall stk (W : world SEGS) regs mem ly S md a l,
AR SEGS B ly S W mem md -> vr_shadow_ok B -> abytes_atR (rdW W mem) a l -> In (a, Z.of_nat (length l)) vr_shr ->
0 < a -> a + Z.of_nat (length l) <= 0x606000 -> 0x606000 <= spZ regs - stk -> 0 < Z.of_nat (length l) < 2 ^ 32 ->
aread_ok SEGS stk W regs mem a (Z.of_nat (length l)).
Proof.
intros stk W regs mem ly S md a l HAR SHOK Hb Hin Ha Hal Hsp Hl. pose proof asan_consts as (C1 & _ & _ & _ & C5).
destruct (SHOK ly S W mem md a _ HAR Hin) as [Hra Hh].
split; [lia|]. split; [lia|]. split; [lia|].
split.
{ intros x Hx. split; [|unfold ascratch_stk; lia].
  specialize (Hb (Z.to_nat (x - a)) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. replace (a + (x - a)) with x in Hb by lia.
  rewrite Hb. discriminate. }
split; [left; unfold kLowMemEnd in *; lia|]. split; [exact Hra | intros _; exact Hh].
Qed.

Lemma aread_ok_sub : forall stk (W : world SEGS) regs mem x n k, aread_ok SEGS stk W regs mem x n -> 0 < k <= n ->
aread_ok SEGS stk W regs mem x k.
Proof.
intros stk W regs mem x n k (Hx & Hn & Hn32 & Hv & Ham & Hra & Hh) Hk.
split; [exact Hx|]. split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hv; lia|].
split; [unfold amem_range in *; lia|]. split; [unfold range_addressable in *; intros y Hy; apply Hra; lia|].
intros Hk0. specialize (Hh ltac:(lia)). unfold shadow_hull_vis in *. intros s Hs. apply Hh.
assert (A1 : shadow_addr (x + k - 1) <= shadow_addr (x + n - 1)) by (unfold shadow_addr; apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
assert (A2 : shadow_addr (x + k - 1) / 8 <= shadow_addr (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.

End e.
End f.
End d.
End VrS31K.
