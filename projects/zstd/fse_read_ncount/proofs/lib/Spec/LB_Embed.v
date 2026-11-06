(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KLink KEv Relim StepB Gap NFKern LB_Logic LB_Kernel LB_KCount.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Placement.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Lemma vis_flat_L {A} B n (k : resp -> itree node (exc A)) mo (Q : A -> Model -> Prop) (R : A -> Model -> Prop) :
(forall rsp, match k rsp with Ret _ => True | Vis _ _ => False end) ->
etwf (Vis n k) mo Q ->
NF n mo ->
(forall rsp mo' evs a, nstep n mo rsp mo' evs -> k rsp = Ret (Ok a) -> Q a mo' -> R a mo' /\ live mo' <= B) ->
etwl B (Vis n k) mo (fun a mo' => Q a mo' /\ R a mo').
Proof.
intros Hf H HN HR. cbn -[NF] in H |- *. destruct H as [_ Hk]. split; [exact HN|]. intros rsp mo' evs Hst. specialize (Hk rsp mo' evs Hst). specialize (Hf rsp).
destruct (k rsp) as [[|a]|n' k'] eqn:Ek; cbn in Hk |- *; [destruct Hk| | destruct Hf].
destruct (HR rsp mo' evs a Hst Ek Hk) as [HRa HB]. auto.
Qed.
Definition QB (L : mled) (e : ev) (B : Z) : Prop :=
match e with
| EMmap _ len _ flags => flags = MAPF ->
mmap_len len <= RMAX /\ Z.of_nat (length (ld_groups L)) + Z.of_nat (length (ld_metas L)) + 1 <= NMAX
| _ => True
end.
Definition BOUND (L : mled) (e : ev) (B : Z) : Prop :=
(forall z, answer_ok L e z = true -> gm (event_post L e z) + BB (event_post L e z) <= B)
/\ QB L e B.
Ltac flat_shape W :=
unfold mbind, msys, mret, mget, mupd, enode, ebind in W |- *; cbn [ITree.bind fst snd] in W |- *.
Theorem ev_step_L B L e G s0 : frame_ok G -> event_pre L e -> B + 2^26 <= 2^31 ->
mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ LN L mo /\ gm L + BB L <= B /\ G s mo /\ BOUND L e B) (ev_step (ld_atop L) e)
(fun z s mo => ev_step_post L e G s0 z s mo /\ LI (event_post L e z) mo /\ LN (event_post L e z) mo
/\ gm (event_post L e z) + BB (event_post L e z) <= B).
Proof.
intros HG Hpre HB26 s mo (-> & HK & HLI & HLN & HGB & HGs & [HB HQB]).
pose proof (ev_step_spec L e G s0 HG Hpre s0 mo (conj eq_refl (conj HK HGs))) as W.
assert (FIN : forall z mo', answer_ok L e z = true -> LI (event_post L e z) mo' -> live mo' <= B).
{ intros z mo' Ha HL'. apply LI_elim in HL'. unfold live. specialize (HB z Ha). Local Ltac2 Set LiaHints.tbl := fun () => "00?0>10071518162.4317445701900.2118760680663.4318771560569.3125161794962.3326206780447.2829307624784.3329578720343.3337125919698.3138490883658.3539390479616.3647740520350.4059309005398.3759314873579.358651779241.43 00000400<00B00H00N00X00k01701I01R01^01b01k02802KS2Q2S2HB3HL'S4HlenS4HlenS4HKatS5HKtop2CaS4HB263HGB3ST34HLI'S4Hlen2Q22MLS4HB263HLI3HGB3ST2S2Q31H2H0S4HB263HGB1HS2HBS1E2R12R3S1E4Ecur2S11HS4HB263ST24HLI'3PRE".
lia. }
pose proof (kl_minv _ _ _ HK) as Hmi. pose proof (kl_atop _ _ _ HK) as HKtop. pose proof (KL_atop_range _ _ _ HK) as HKat.
destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
-
unfold ev_step in W |- *.
destruct (Z.eqb_spec req 0) as [->|NZ].
+ flat_shape W. eapply vis_flat_L; [| exact W| exact I|].
{ intros rsp. destruct (dec_brk0 rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_brk0 rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate]. assert (Ez : z = x) by congruence. subst x.
destruct Hpre as [[_ Hph]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]].
2:{ exfalso. pose proof (kl_phase _ _ _ HK) as P. rewrite Hph in P. destruct P as (Ecur & _). pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia. }
2:{ exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia. }
pose proof (li_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLI Hph Hst) as HL'.
pose proof (ln_brk0 L (ps_brk s0) mo rsp mo' evs z HK HLN Hph Hst) as HN'.
change (event_post L (EBrk 0) z) with (set_brkph (BPQueried z) L).
split; [split; [exact HL'| split; [exact HN'| exact (HB z Hans)]]| exact (FIN z mo' Hans HL')].
+ flat_shape W. eapply vis_flat_L; [| exact W| exact I|].
{ intros rsp. destruct (dec_brk (ps_brk s0) req rsp) as [[|]|]; reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_brk (ps_brk s0) req rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = match x with BrkGrown => req | BrkSame => ps_brk s0 end) by (destruct x; cbn in Ek; congruence).
destruct Hpre as [[E _]|Hpre]; [exfalso; exact (NZ E)|].
pose proof (li_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLI Hpre Hst Hd) as HL'. rewrite <- Ez in HL'.
pose proof (ln_brk_grow L (ps_brk s0) mo rsp mo' evs req x HK HLN ltac:(pose proof (gm_nonneg L _ _ HK); unfold PGSZ; lia) Hpre Hst Hd) as HN'. rewrite <- Ez in HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB z Hans)]]| exact (FIN z mo' Hans HL')].
-
unfold ev_step in W |- *.
destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
+ change (negb (Z.land MAPF MAP_FIXED_Z =? 0)) with false in *. cbn iota in W |- *.
destruct (HQB eq_refl) as [Q2 Q3].
assert (HNF : NF (NMmap 0 len prot MAPF) mo).
{ pose proof HLN as (CNT & (ST1 & ST2 & ST3) & _). pose proof (LI_elim _ _ HLI) as HLI'.
pose proof (mmap_len_ge len ltac:(lia)) as ML. pose proof alloc_ceiling_lt as Hcl.
assert (HGAP : vm_gap_available (m_vmmaps mo) (mmap_len len) = true).
{ apply (vm_gap_available_intro_N (m_vmmaps mo) (mmap_len len) NMAX RMAX (2^35)); [lia| rewrite <- HKtop, CEIL_val; rewrite alloc_ceiling_lo_val in HKat; lia| | | apply band_arith].
- pose proof (N_band_le L (ps_brk s0) mo HK HLN). pose proof (lcnt_le_len L). lia.
- rewrite live_bytes_app. unfold vm_live_bytes in *. lia. }
destruct (vm_gap_available_find _ _ HGAP) as [aw Hfind].
destruct (vm_find_base_sound _ _ _ Hfind) as (W1 & W2 & W4 & W5).
rewrite <- HKtop in W4.
destruct (mmap_answer_ok_of_free L (ps_brk s0) mo (bv_unsigned aw) len HK Hlen W2 ltac:(rewrite page_size_eq in W1; exact W1) W4
ltac:(rewrite Z_to_bv_bv_unsigned; exact W5)) as [AOK NER].
assert (PRE : gm L + BB L + mmap_len len <= B).
{ specialize (HB (bv_unsigned aw)). unfold answer_ok in HB. change (Z.land MAPF MAP_FIXED =? 0) with true in HB. cbv iota in HB.
specialize (HB AOK). rewrite (mm_post_eq L len prot _ Hprot), NER in HB.
destruct Hprot as [-> | ->]; cbn [Z.eqb PROT_NONE PROT_RW Pos.eqb] in HB;
[rewrite gm_add_meta, BB_set_metas in HB| rewrite gm_add_group, BB_set_groups in HB]; lia. }
apply NF_mmap_anon; [lia| unfold RMAX in Q2; lia| exact Hprot| apply (minv_nolazy mo Hmi)| apply Hmi| lia| exact HGAP]. }
destruct Hprot as [-> | ->].
* change (PROT_NONE =? 0) with true in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W| exact HNF|].
{ intros rsp. destruct (dec_mmap_none (ld_atop L) len [] rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_mmap_none (ld_atop L) len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
pose proof (li_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
pose proof (ln_mmap_none L (ps_brk s0) mo rsp mo' evs len x HK HLN Hlen Hst Hd) as HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB _ Hans)]]| exact (FIN _ mo' Hans HL')].
* change (PROT_RW =? 0) with false in *. cbn iota in W |- *. flat_shape W. eapply vis_flat_L; [| exact W| exact HNF|].
{ intros rsp. destruct (dec_mmap (ld_atop L) len [] rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
destruct (dec_mmap (ld_atop L) len [] rsp) as [x|] eqn:Hd; cbn in Ek; [| discriminate].
assert (Ez : z = mm_val x) by (destruct x; cbn; congruence). subst z.
pose proof (li_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLI Hlen Hst Hd) as HL'.
pose proof (ln_mmap_rw L (ps_brk s0) mo rsp mo' evs len x HK HLN Hlen Hst Hd) as HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB _ Hans)]]| exact (FIN _ mo' Hans HL')].
+ change (negb (Z.land MAPFX MAP_FIXED_Z =? 0)) with true in *. cbn iota in W |- *. flat_shape W.
destruct (fixed_gate_facts L cur (ps_brk s0) mo HK Hph) as (Ea & Ecur & Pa & Ca & Aa & Rf & Mc).
eapply vis_flat_L; [| exact W| apply (NF_mmap_fixed (round_up_pg cur) mo Pa ltac:(unfold PGSZ in *; lia) Aa Rf Mc)|].
{ intros rsp. destruct (dec_mmap_fixed (round_up_pg cur) PGSZ rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLI Hph Hst) as HL'.
pose proof (ln_mmap_fixed L (ps_brk s0) mo rsp mo' evs cur z HK HLN Hph Hst) as HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB _ Hans)]]| exact (FIN _ mo' Hans HL')].
-
unfold ev_step in W |- *. destruct Hpre as (Hq & l0 & Hin & Hlen). flat_shape W. eapply vis_flat_L; [| exact W| exact I|].
{ intros rsp. destruct (dec_munmap addr len rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLI Hin Hlen Hst) as HL'.
pose proof (ln_munmap L (ps_brk s0) mo rsp mo' evs addr l0 len z HK HLN Hin Hlen Hst) as HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB _ Hans)]]| exact (FIN _ mo' Hans HL')].
-
unfold ev_step in W |- *. destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). flat_shape W.
destruct (mprotect_gate_facts L (ps_brk s0) mo b l k HK Hin Hk) as (F1 & F2 & F3 & F4 & F5).
eapply vis_flat_L; [| exact W| |].
2:{ apply (NF_mprotect (b + (1 + k) * PGSZ) mo F1 F2 F3 F4 F5); [| exact Hmi].
pose proof HLN as (_ & (_ & ST2 & _) & _). apply LI_elim in HLI. lia. }
{ intros rsp. destruct (dec_mprotect_rw (b + (1 + k) * PGSZ) PGSZ rsp); reflexivity. }
intros rsp mo' evs [z s'] Hst Ek [Hans HP]. cbn [fst snd] in *.
pose proof (li_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLI Hin Hk Hst) as HL'.
pose proof (ln_mprotect L (ps_brk s0) mo rsp mo' evs b l k z HK HLN Hin Hk Hst) as HN'.
split; [split; [exact HL'| split; [exact HN'| exact (HB _ Hans)]]| exact (FIN _ mo' Hans HL')].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Fixpoint qtree {R} (B : Z) (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
match t with
| SRet r => Post L r
| SVis e k => event_pre L e /\ BOUND L e B /\ forall z, answer_ok L e z = true -> qtree B (event_post L e z) (k z) Post
end.
Theorem membedL {R} B (t : stree ev Z R) : forall (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
frame_ok G -> qtree B L t Post -> B + 2^26 <= 2^31 ->
mspecL B (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ LI L mo /\ LN L mo /\ gm L + BB L <= B /\ G s mo) (membed (ld_atop L) t)
(fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ LI L' mo /\ LN L' mo /\ gm L' + BB L' <= B /\ G s mo
/\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
induction t as [r|e k IH]; intros Post G L s0 HG Hq HB26.
- cbn [membed]. apply mspecL_ret. intros s mo (-> & HK & HL & HN & HGB & HGs). exists L. split; [constructor|]. cbn in Hq. split; [exact Hq|]. split; [exact HK|]. split; [exact HL|]. split; [exact HN|]. split; [exact HGB|]. split; [exact HGs|]. auto.
- cbn [membed]. cbn in Hq. destruct Hq as (Hpre & HB & Hk).
eapply mspecL_bind.
{ eapply mspecL_pre; [apply (ev_step_L B L e G s0 HG Hpre HB26)|]. intros s mo (-> & HK & HL & HN & HGB & HGs). split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HN|]. split; [exact HGB|]. split; [exact HGs| exact HB]. }
intros z. apply mspecL_pointwise. intros s1 mo1 ((Hans & HK1 & HG1 & Hm & Hfa & Hso) & HL1 & HN1 & HGB1).
rewrite <- (event_post_atop L e z).
eapply mspecL_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans) HB26)| |].
+ intros s mo [-> ->]. split; [reflexivity|]. auto 10.
+ intros r s mo (L' & Hp & HP & HK & HL' & HN' & HGB' & HG' & Hm' & Hfa' & Hso'). exists L'. split; [econstructor; eauto|].
split; [exact HP|]. split; [exact HK|]. split; [exact HL'|]. split; [exact HN'|]. split; [exact HGB'|]. split; [exact HG'|]. repeat split; congruence.
Qed.
