(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (QI_init takes the launch's placement base, which the reserved ledger's vDSO/vvar pair sits below, and the launch's channel-reader fact for minv, and hands both to KL_init; KL_with_vdso and QI_with_vdso lift KL and QI to the start model, which State.with_vdso gives its vDSO run state). *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1ra X1qu X1qv X1og X1oh X1oi X1r3 X1pe X1r9 X1oa
X1q8 X1po X1pi X1p1 X1oq X1p0 X1or X1ox X1oz X1oy.
Import ListNotations.
Open Scope Z_scope.

Lemma zsum_nonneg' l : (forall x, In x l -> 0 <= x) -> 0 <= zsum l.
Proof. induction l as [|a l IH]; intros H; cbn; [lia|]. pose proof (H a (or_introl eq_refl)). specialize (IH ltac:(intros x Hx; apply H; right; exact Hx)). unfold zsum in IH. lia. Qed.

Lemma CAP_lower P c : (forall c, 0 <= P c) -> 0 <= c -> 14 <= CAP P c.
Proof.
intros HP Hc.
assert (0 <= HOSTSTD P c).
{ unfold HOSTSTD. apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c' & <- & Hc').
assert (G : 0 <= c' < 48) by (unfold guests in Hc'; cbn in Hc'; lia). cbn beta.
destruct (bighost c' =? c); [| apply Z.le_refl]. pose proof (tab_basic_ok c' G) as (_ & CM & _).
apply Z.div_pos; [| lia]. unfold CAP0. pose proof (HP c'). destruct (c' <=? 23); lia. }
unfold CAP, CAP0. pose proof (HP c). destruct (c <=? 23); lia.
Qed.

Lemma NCAP_lower P : (forall c, 0 <= P c) -> 4 <= NCAP P.
Proof.
intros HP. unfold NCAP, NG.
assert (0 <= zsum (map (fun c => (CAP P c + 32) / cmax c + 160) classes)).
{ apply zsum_nonneg'. intros x Hx. apply in_map_iff in Hx as (c & <- & Hc). apply In_classes in Hc. cbn beta.
pose proof (tab_basic_ok c Hc) as (_ & CM & _). pose proof (CAP_lower P c HP ltac:(lia)).
assert (0 <= (CAP P c + 32) / cmax c) by (apply Z.div_pos; lia). lia. }
pose proof (HP 63). lia.
Qed.

Lemma SINV_minit secret ceil resv : SINV x0 (minit secret ceil resv) [].
Proof.
constructor; cbn -[Z.mul Z.add Z.le Z.lt]; try (intros *; intros HH; rewrite lookup_empty in HH; discriminate).
- intros k [].
- intros c. unfold MIS, zcount, zlen. cbn. lia.
- intros c Hc. unfold nsc, gmetas, groups_l. cbn [s_groups minit]. rewrite map_to_list_empty. cbn. lia.
- unfold apages, ncarved, regions_l. cbn [s_regions s_metas minit]. rewrite !map_to_list_empty. unfold zlen. cbn. lia.
- intros H. lia.
Qed.

Lemma gcnt_minit secret ceil resv c : gcnt (minit secret ceil resv) c = 0.
Proof. unfold gcnt. cbn [s_groups minit]. rewrite map_to_list_empty. reflexivity. Qed.

Lemma AQ_minit P secret ceil resv : (forall c, 0 <= P c) -> AQ (minit secret ceil resv) [] P.
Proof.
intros HP. constructor.
- intros c Hc. unfold LR, zcount, zlen. cbn. apply HP.
- intros c Hc. rewrite gcnt_minit. pose proof (CAP_lower P c HP ltac:(lia)). lia.
- unfold n63, zcount, zlen. cbn. apply HP.
- unfold ncarved. cbn [s_metas minit]. rewrite map_to_list_empty. pose proof (NCAP_lower P HP). unfold zlen. cbn. lia.
- exact HP.
Qed.

Lemma reserved_top_ge' : forall l e, In e l -> bv_unsigned (fst e) + bv_unsigned (snd e) <= reserved_top l.
Proof.
induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
cbn [reserved_top]. destruct Hin as [<-|Hin]; cbn [fst snd]; [lia|]. specialize (IH e Hin). lia.
Qed.

Theorem QI_init : forall P segs brk0 mbase sp lim inp,
valid_brk segs brk0 -> 0 < reserved_top (segments_reserved segs) -> valid_sp sp ->
(* the launch's placement base: [State.init_model] reserves the vDSO/vvar pair just
   below it, far above the brk window *)
valid_mmap_base mbase ->
reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling_lo ->
reserved_top (segments_reserved segs) + brk_aslr_max + PGSZ <= 2^40 ->
LBUDGET <= lim ->
(forall c, 0 <= P c) -> PHI P <= LBUDGET ->
(* the launch's reader of the standard channels, which [KL]'s [minv] carries *)
in_channel_reader inp = true ->
QI [] P (ps_init (bv_unsigned sp - stack_max_size) (reservedZ segs)) (init_model (segments_reserved segs) brk0 mbase sp lim inp).
Proof.
intros P segs brk0 mbase sp lim inp Hv Hpos Hsp Hmb Hceil H40 Hlim HP HPHI Hrdr. split; [| unfold R63X, zsum; cbn; lia].
exists (minit 0 (bv_unsigned sp - stack_max_size) (reservedZ segs)), (led_init (bv_unsigned sp - stack_max_size) (reservedZ segs)), [], (fun _ => []).
split; [reflexivity|].
split; [apply INVL_init; [lia| destruct Hsp as (Hsl & Hsh & _); unfold sp_window_lo, sp_window_hi in *; unfold stack_max_size, alloc_ceiling_lo, alloc_ceiling_hi; lia]|].
split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
split; [| split; [| apply Permutation_refl]].
- apply (X1oa.KL_init segs brk0 mbase sp lim inp Hv Hpos Hsp Hmb Hceil H40 Hrdr).
- unfold LI, LIb, PGE, SBK, gm, BB, nomat. rewrite m_vmmaps_init_model. cbn -[Z.pow]. split; [split; [lia| reflexivity]|]. split; [intros e []|].
destruct Hv as (_ & Hhi & _). unfold PGSZ in H40. split; [lia| exact Hlim].
Qed.

(* The start model ([mo0]) is [State.with_vdso] over [State.init_model]: it rebuilds the VM subsystem
   from its own parts with a new vDSO run state, which no field of [KL] reads, so every field holds of
   it by conversion. *)
Lemma KL_with_vdso : forall L pbrk v mo, KL L pbrk mo -> KL L pbrk (with_vdso v mo).
Proof. intros L pbrk v mo []. constructor; assumption. Qed.

(* [QI] reads the model only through [KL] and [LI], whose maps, lazy and materialized lists and kernel
   build [with_vdso] keeps *)
Lemma QI_with_vdso : forall X P s v mo, QI X P s mo -> QI X P s (with_vdso v mo).
Proof.
intros X P s v mo H. unfold QI in *. destruct H as ((st & L & BL & LS & H1 & H2 & H3 & H4 & HK & HL & H5) & HB).
split; [| exact HB]. exists st, L, BL, LS.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [apply KL_with_vdso; exact HK|]. split; [exact HL| exact H5].
Qed.
