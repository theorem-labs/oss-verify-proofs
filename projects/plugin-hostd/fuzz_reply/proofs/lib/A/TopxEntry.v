(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10 (a Theorem Labs lane, a Theorem Labs lane's TOPX group ENTRY): top_x's Section hypothesis HFP_pro
   (W_LLVMFuzzerTestOneInput_top_x.v:320 at integ bb9dae5d905, SEG_PRO's entry facts) as a LEMMA.

   HFP_pro's three conclusions at the entry cx:
   (1) the live blocks split into the input block, g_src's table (T, ATABLE) when T <> 0, g_out's buffer
       aout_blks cap out, and a rest;
   (2) / (3) the table's and the buffer's bytes, over their request size, lie in the journal footprint lf_FP fr_FP cx.
   Sources: (1) the pre's input clause ((n = 0 /\ ..) \/ (0 < n .. /\ In (p, n) (ablocks ..))) and its LAST clause HB
   (_cut_x.v:103, _cut.v's eighth clause: NoDup (input ++ fr_hblks W mem) /\ incl (fr_hblks W mem) (ablocks ..)),
   with fr_hblks W mem computed from ra_rel's and aout_at's cells (g_src = T, g_capout = cap, g_out = out); a NoDup
   list included in a list is a permutation prefix of it.  (2) / (3) the footprint covers the harness blocks: FPCOV
   below.

   PREMISES BEYOND HFP_pro's TEXT, both Section hypotheses here and both discharged at the instance in this file:
   - BLK (the cell values T, cap, out are below 2^64, so the 8-byte cells read back as rdword): a live block's address
     and size are nonnegative with p + n < 2 ^ 64.  At ARx := ARcf /\ Hp = [] it is arcf_blk below (YG0dcf.v's
     AR_blocks_law_cf: 4096 <= p, p + req_size n <= alloc_ceiling, 0 <= n).
   - FPCOV (fr_FP is top_x's Variable, so HFP_pro's (2) / (3) hold only for a footprint that covers the harness
     blocks): every block (b, s) of fr_hblks W mem has its range (b, b + s) in fr_FP regs ly S W mem.  The footprint
     of record, lib/A/ACfn_cf.v:61-66 fr_FP (a working branch 5ab58d26200; not on integ), is fr_hblks's two
    matches with (G, ATABLE) -> (G, G + ATABLE) and (o, c) -> (o, o + c); fr_FP_text_cov below proves FPCOV for that
    body word for word, so FPCOV at ACfn_cf.fr_FP is `fun regs ly S W mem b H => fr_FP_text_cov W mem b H`.  While
    fr_FP stays top_x's Variable, the plug of HFP_pro := hfp_pro_x .. arcf_blk FPCOV carries FPCOV as a top_x
    hypothesis, which the driver discharges with that one line when it sets fr_FP := ACfn_cf.fr_FP.
  SATISFIABILITY (VERIFY rule 10): ra_rel / aout_at at the entry are what the pre's fr_gi conjunct already states
  (_cut.v:150-151), so they add no constraint; the pre's HB clause holds at the first call's entry (_cut.v:257-265
  fr_hb_pre_of_image: fr_hblks = [] there); BLK holds at every ARcf state (arcf_blk); FPCOV holds at ACfn_cf.fr_FP
  (fr_FP_text_cov).
  ROOM ROUND (ROOM-TEXTS.md (sha256 767baa12f13c; internal record) (e)): fr_lib_pre_cf_x carries XCNT (ReplyCnt.xcnt_ok) and CAPOUT after HB (lib/A/W_LLVMFuzzerTestOneInput_cut_x.v:104-110
  on a working branch e1bf3549b61); pre_facts' one positional destruct names HB as `(HND & HINC)` and
  skips the two clauses after it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep W_contract.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require W_frame.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* a NoDup list included in a list is a prefix of a permutation of it *)
Lemma perm_of_nodup_incl : forall (l a : list (Z * Z)), List.NoDup l -> incl l a -> exists rest, Permutation a (l ++ rest).
Proof.
  induction l as [|x l IH]; intros a Hnd Hinc.
  - exists a. reflexivity.
  - apply List.NoDup_cons_iff in Hnd as [Hx Hnd'].
    destruct (in_split x a (Hinc x (or_introl eq_refl))) as (a1 & a2 & ->).
    destruct (IH (a1 ++ a2) Hnd') as (rest & Hp).
    { intros y Hy. assert (Hya : In y (a1 ++ x :: a2)) by exact (Hinc y (or_intror Hy)).
      apply in_app_or in Hya as [Hya | [Hya | Hya]]; apply in_or_app; [left; exact Hya | | right; exact Hya].
      subst y. exfalso. exact (Hx Hy). }
    exists rest. cbn [app]. eapply perm_trans; [apply Permutation_sym, Permutation_middle|]. apply perm_skip. exact Hp.
Qed.

Section e.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Notation segs := tfibsegs.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variables LIBROOM NP : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
(* a live block's address and size are in range (at the instance: arcf_blk) *)
Hypothesis BLK : forall ly S Hp (W : world segs) mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  0 <= p /\ 0 <= n /\ p + n < 2 ^ 64.
(* the footprint covers the harness blocks (at ACfn_cf.fr_FP: fr_FP_text_cov below) *)
Hypothesis FPCOV : forall regs ly S (W : world segs) mem b, In b (fr_hblks W mem) ->
  In (fst b, fst b + snd b) (fr_FP regs ly S W mem).

(* the pre's facts this file reads: the entry's ARx, the input clause and HB.  The one positional destruct of
   fr_lib_pre_cf_x (at the room text: ... STKR, HB, XCNT, CAPOUT) *)
Lemma pre_facts : forall cx Hp,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ARx (c_ly cx) (c_S cx) Hp (c_W cx) (c_mem cx) (c_md cx) /\
  ((c_n cx = 0 /\ c_p cx = A_EMPTY) \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)))) /\
  List.NoDup ((if c_n cx =? 0 then [] else [(c_p cx, c_n cx)]) ++ fr_hblks (c_W cx) (c_mem cx)) /\
  incl (fr_hblks (c_W cx) (c_mem cx)) (ablocks B (c_ly cx) (c_S cx)).
Proof.
  intros cx Hp (_ & HAF & _ & _ & _ & Hin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HND & HINC) & _ & _).
  split; [exact (proj1 HAF)|]. split; [exact Hin|]. split; [exact HND | exact HINC].
Qed.

(* an 8-byte cell that holds a value below 2^64 reads back as rdword *)
Lemma cell_rdword : forall (W : world segs) mem a v,
  val_mem segs (arm W mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs (w_H W) mem) a = Some v.
Proof. intros W mem a v Hv Hr. exact (W_frame.rdword_of_val_mem segs (w_H W) mem a v Hv Hr). Qed.

(* fr_hblks at the entry, from the relay's and the stream's cells *)
Lemma hblks_eq : forall ly S Hp (W : world segs) mem md T c O mx cap out,
  ARx ly S Hp W mem md ->
  ra_rel B fr_RG ly S W mem T [] ->
  aout_at B fr_RG ly S W mem c O mx (Z.of_nat (length O)) cap out ->
  fr_hblks W mem = (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out.
Proof.
  intros ly S Hp W mem md T c O mx cap out HAR HRA HAO.
  assert (HT : rdword (aview segs (w_H W) mem) (rg_src fr_RG) = Some T).
  { destruct HRA as [(-> & _ & Hv & _) | (Hv & _ & _ & _ & _ & _ & _ & Hin & _)].
    - apply cell_rdword; [exact Hv | lia].
    - destruct (BLK ly S Hp W mem md T ATABLE HAR Hin) as (H0 & H1 & H2).
      apply cell_rdword; [exact Hv | unfold ATABLE in *; lia]. }
  destruct HAO as (_ & _ & _ & _ & Hcap & _ & Hout & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & Hco).
  assert (HC : rdword (aview segs (w_H W) mem) (rg_capout fr_RG) = Some cap /\
               rdword (aview segs (w_H W) mem) (rg_out fr_RG) = Some out).
  { destruct Hco as [(-> & -> & _) | (Hc & _ & Hin & _)].
    - split; (apply cell_rdword; [assumption | lia]).
    - destruct (BLK ly S Hp W mem md out cap HAR Hin) as (H0 & H1 & H2).
      split; (apply cell_rdword; [assumption | lia]). }
  destruct HC as (Hc & Ho).
  unfold fr_hblks. cbv zeta. rewrite HT, Ho, Hc. unfold aout_blks. reflexivity.
Qed.

(* top_x's HFP_pro, at a footprint that covers the harness blocks *)
Lemma hfp_pro_x : forall cx Hp T c O mx cap out,
  lf_base_x B MT XM_LIB RLO RHI fr_live_pre LIBROOM NP G_fr ARx cx Hp ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
Proof.
  intros cx Hp T c O mx cap out HB HRA HAO.
  destruct (pre_facts cx Hp HB) as (HAR & Hin & HND & HINC).
  pose proof (hblks_eq _ _ _ _ _ _ _ _ _ _ _ _ HAR HRA HAO) as EH.
  assert (HIN : incl (input_blks cx) (ablocks B (c_ly cx) (c_S cx))).
  { unfold input_blks. intros b Hb. destruct (c_n cx =? 0) eqn:En; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hin as [(Hn & _) | (_ & Hi)]; [apply Z.eqb_neq in En; lia | exact Hi]. }
  split; [|split].
  - destruct (perm_of_nodup_incl (input_blks cx ++ fr_hblks (c_W cx) (c_mem cx)) (ablocks B (c_ly cx) (c_S cx)))
      as (rest & Hp').
    + exact HND.
    + intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [exact (HIN b Hb) | exact (HINC b Hb)].
    + exists rest. rewrite EH, <- !app_assoc in Hp'. exact Hp'.
  - intros HT0 a Ha. exists (T, T + ATABLE). split; [|cbn [fst snd]; unfold req_size, ATABLE in *; cbn in Ha; lia].
    unfold lf_FP. apply (FPCOV _ _ _ _ _ (T, ATABLE)). rewrite EH. apply in_or_app. left.
    destruct (T =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction | left; reflexivity].
  - intros b Hb a Ha. unfold aout_blks in Hb. destruct (cap =? 0) eqn:E; [destruct Hb|].
    destruct Hb as [<- | []]. apply Z.eqb_neq in E. cbn [fst snd] in Ha |- *.
    assert (Er : req_size cap = cap) by (unfold req_size; destruct (cap =? 0) eqn:E'; [apply Z.eqb_eq in E'; lia | reflexivity]).
    rewrite Er in Ha. exists (out, out + cap). split; [|cbn [fst snd]; lia].
    unfold lf_FP. apply (FPCOV _ _ _ _ _ (out, cap)). rewrite EH. apply in_or_app. right.
    unfold aout_blks. apply Z.eqb_neq in E. rewrite E. left. reflexivity.
Qed.
End e.

(* ---- FPCOV at the footprint of record: the body of lib/A/ACfn_cf.v:61-66 fr_FP (a working branch 5ab58d26200),
   word for word with fr_globals = fr_RG (_cut.v:104), so ACfn_cf.fr_FP regs ly S W mem is this term by delta and
   FPCOV there is `fun regs ly S W mem b H => fr_FP_text_cov W mem b H` ---- *)
Lemma fr_FP_text_cov : forall (W : world tfibsegs) mem b, In b (fr_hblks W mem) ->
  In (fst b, fst b + snd b)
    (let rd := aview tfibsegs (w_H W) mem in
     (match rdword rd (rg_src fr_globals) with Some G => if G =? 0 then [] else [(G, G + ATABLE)] | None => [] end) ++
     (match rdword rd (rg_out fr_globals), rdword rd (rg_capout fr_globals) with
      | Some o, Some c => if c =? 0 then [] else [(o, o + c)] | _, _ => [] end)).
Proof.
  intros W mem b Hb. unfold fr_hblks, fr_RG in Hb. cbv zeta in Hb |- *.
  apply in_app_or in Hb as [Hb | Hb]; apply in_or_app; [left | right].
  - destruct (rdword (aview tfibsegs (w_H W) mem) (rg_src fr_globals)) as [G|]; [|destruct Hb].
    destruct (G =? 0); [destruct Hb | destruct Hb as [<- | []]; left; reflexivity].
  - destruct (rdword (aview tfibsegs (w_H W) mem) (rg_out fr_globals)) as [o|]; [|destruct Hb].
    destruct (rdword (aview tfibsegs (w_H W) mem) (rg_capout fr_globals)) as [c|]; [|destruct Hb].
    destruct (c =? 0); [destruct Hb | destruct Hb as [<- | []]; left; reflexivity].
Qed.

(* ---- BLK at the cf instance (YG0dcf.v:617 AR_blocks_law_cf through AR_laws_ok_cf) ---- *)
Section inst.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma arcf_blk : forall ly S Hp (W : world tfibsegs) mem md p n,
  ARcf (ci := CfImg_A) (cp := CfParams_reply) tfibsegs TfibB ly S Hp W mem md /\ Hp = [] -> In (p, n) (ablocks TfibB ly S) ->
  0 <= p /\ 0 <= n /\ p + n < 2 ^ 64.
Proof.
  intros ly S Hp W mem md p n [H _] Hin.
  destruct (YG0dcf.alc_blocks _ _ (AR_laws_ok_cf (cp := CfParams_reply) tfibsegs TfibB) ly S Hp W mem md p n H Hin)
    as (_ & Hp4 & Hceil & _ & _ & _ & Hn).
  assert (Hr : n <= req_size n) by (unfold req_size; destruct (n =? 0) eqn:E; [apply Z.eqb_eq in E; lia | lia]).
  pose proof (YM05.alloc_ceiling_lt (rc := rc)) as Hc.
  lia.
Qed.
End inst.
