(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Disp_word.v, with its module paths and module names changed; 116 of its 154 lines of code are new or changed and 465 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Caw102A_Kit.v, with its module paths and module names changed; 228 of its 306 lines of code are new or changed and 76 lines of the source are left out. *)
(* fuzz_preset lib/B, the #102 re-walk of tx_put on image B' (asan-ubsan build): segment S_END (row
   TPB-END), the epilogue and the return, from the cut TP_PC_END (+400) to the text's caller-window post.
   rule 24: proves function tx_put (kind: segment lemma of the ASan B' walk; reuse search: the internal file REWALK-102-PLAN.md
   section T3, proof-index CONFIRM: no released ASan walk of tx_put).
   PROVES tp_seg_END_ok : forall P, srr_inv_laws segs P -> tp_seg_END B SK CTX0 P (TxPut102B_Base.v :428-431,
   blob c4c364d5da35). P is never unfolded: the one engine run goes through the runner twin paj_run_x_inv (YC1fPx.v)
   with the law PLAW, premise the cut's P mem3; the return leaves the memory as it is, so the post's P is the run's.
   THE CODE (B' listing lib/B/Listing_prog.v 8bcc2c9e7809, slots TP_SLOT + 100 .. TP_SLOT + 114; DERIVED byte offsets
   from the entry 0x851d0):
     +400  ld ra, 104(sp)   +404 ld s0, 96(sp)   +408 ld s1, 88(sp)   +412 ld s2, 80(sp)   +416 ld s3, 72(sp)
     +420  ld s4, 64(sp)    +424 ld s5, 56(sp)   +428 ld s6, 48(sp)   +432 ld s7, 40(sp)   +436 ld s8, 32(sp)
     +440  ld s9, 24(sp)    +444 ld s10, 16(sp)  +448 ld s11, 8(sp)   (the cut's thirteen tp_saved words)
     +452  addi sp, sp, 112 (sp = the entry sp0)
     +456  ret              (to raZ (tp_regs D): paj_ret_at)
   ONE symbolic run +400 -> +456 over the frame [sp0 - 112, sp0) (atom 2 is sp0, the thirteen saved words atoms
   33 .. 45, atom 32 the shadow base), read-only (no store: the memory after the run is the cut's, frame_of_read_only).
   The post: ra = the entry ra (afn_pre_x's ret_ok), aregs_preserved from the thirteen restored registers, sp = sp0
   and the kept gp / tp (tp_kregs), the widened journal from tp_J at its budget (rebased for the run, ajournal_x_materialize, unbased), the caller window
   [sp0, sp0 + dw) outside FP from tp_K's stack clause, the body tp_Qb from the cut's tp_Q.
   REFUTED SITES: none (no branch in +400 .. +456).
   NAMED ARGUMENTS: none. SECTION HYPOTHESES: none; the law srr_inv_laws segs P is the statement's own premise
   (owner: the top, TxPut102B_Top.v, which instantiates P := tp_mn D by tp_mn_laws). Instance bindings only otherwise
   (the base's TP_PrhImg / TP_PAListing / TP_RL; the allocator laws LAWS := AR_laws_x_xs (AR_laws_ok_cf),
   as FuzzFreeB.v / Caw102A_WA6.v). tp_img is not read: the epilogue touches no image fact.
   MODEL: lib/A/Prog/Caw102A_WA6.v + Caw102A_Kit.v (the A' epilogue of
   check_as_written on the same engine), frame 80 / four words there, frame 112 / thirteen words here; the frame kit
   below is that Kit's Section bld at B_prog_listing and TP_FRAME.
   Numerals: 400 / 456 (DERIVED offsets, in TP_PC_END), -104 .. -8 (DERIVED: the ld offsets 8 .. 104 minus the frame
   112), 8 (LENGTH: a word), 32 / 33 / 200 (DERIVED: the engine's atom numbering), 2 ^ 46 / 2 ^ 47 / 2 ^ 4 (the stack
   atom's range and alignment, astk_ok), 2 ^ 44 (the shadow span), 2 ^ 64 (word range), register numbers 1 2 3 4 8 9
   18-27 (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallcf YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YC1fPx YSRrMemnorm YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PLB102.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import TxPut102B_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
(* the PLAIN build's sink instance is loaded transitively here; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the frame kit (Caw102A_Kit.v's Section bld at TP_FRAME): the frame region BELOW the entry sp sp0 (atom 2 holds
   sp0, sp is the term SOff 2 (-112)), its chunks the saved words as atoms 33, 34, .. ---- *)
Fixpoint tpe_fchunks (k : nat) (offs : list (Z * N)) : list YP09.chunk :=
  match offs with
  | [] => []
  | (o, w) :: r => YP09.mkChunk o (CVal w (SOff k 0)) :: tpe_fchunks (S k) r
  end.
Definition tpe_fregion (offs : list (Z * N)) (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- TP_FRAME) 0 wlo whi (tpe_fchunks 33 offs).
Definition tpe_sr : list sv := sr_set sr_atoms 2%bv (SOff 2 (- TP_FRAME)).
(* the epilogue's frame words, in address order: s11 at sp0 - 104 .. s0 at sp0 - 16, ra at sp0 - 8 (atoms 33 .. 45) *)
Definition tpe_offs : list (Z * N) :=
  [(-104, 8%N); (-96, 8%N); (-88, 8%N); (-80, 8%N); (-72, 8%N); (-64, 8%N); (-56, 8%N);
   (-48, 8%N); (-40, 8%N); (-32, 8%N); (-24, 8%N); (-16, 8%N); (-8, 8%N)].
Definition tpe_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

(* the callee-saved registers are the entry's when each of them is (Caw102A_WA6.v caw6_aregs) *)
Ltac tpe_inbv := repeat (first [left; apply bv_eq; reflexivity | right]).
Lemma tpe_aregs : forall (regs regs' : bvmap 5 word),
  (forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. unfold acallee_saved in Hr.
assert (E : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct E as [-> | E]; [apply H; tpe_inbv |]). subst r. apply H; tpe_inbv.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instances TP_PrhImg TP_PAListing TP_RL.
#[local] Notation segs := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable SK : YI16.sink_head.
Variable CTX0 : list (list Z).
(* the allocator's laws: AR_laws_ok_cf (YG0lawscf.v), at YGcallcf's bridge (as FuzzFreeB.v) *)
Let LAWS : AR_laws_x segs B (ARcfx B) cf_head := AR_laws_x_xs segs B (AR_laws_ok_cf segs B).

(* ---- the frame kit, image part ---- *)
Fixpoint tpe_vals_ok (m : word -> option byte) (sp : Z) (offs : list (Z * N)) (vals : list Z) : Prop :=
  match offs, vals with
  | [], [] => True
  | (o, w) :: r, v :: vs =>
      val_mem segs m (sp + o) (N.to_nat w) v /\ 0 <= v < 2 ^ (8 * Z.of_N w) /\ Z.of_N w <= 8 /\
      tpe_vals_ok m sp r vs
  | _, _ => False
  end.
Definition tpe_Ee (regs : bvmap 5 word) (sp0 : Z) (vals : list Z) : env :=
  @Eimg _ B_prog_listing PA (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))).
Lemma tpe_fchunks_ok : forall E m sp offs vals k,
  (forall i, (i < length offs)%nat -> ew E (k + i) = Z_to_bv 64 (nth i vals 0)) ->
  tpe_vals_ok m sp offs vals -> Forall (YP09.chunk_ok segs E m sp) (tpe_fchunks k offs).
Proof.
intros E m sp offs. induction offs as [|[o w] r IH]; intros vals k He Hv; [constructor|].
destruct vals as [|v vs]; [destruct Hv|]. destruct Hv as (Hm & Hr & Hw & Hv).
constructor.
- apply (chunk_ok_val segs E m sp o w (SOff k 0) v); [| exact Hr | exact Hw | exact Hm].
  cbn [sv_denot]. specialize (He 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in He. rewrite He.
  cbn [nth]. rewrite Z.add_0_r, unsigned_lit_small by (split; [lia|]; apply (Z.lt_le_trans _ _ _ (proj2 Hr)); apply Z.pow_le_mono_r; lia).
  reflexivity.
- apply (IH vs (S k)); [| exact Hv].
  intros i Hi. specialize (He (S i) ltac:(cbn; lia)). rewrite <- Nat.add_succ_comm in He. exact He.
Qed.
Lemma tpe_getr_upd_other : forall regs (r r' : bv 5) w, r' <> r -> getr (regupd regs r w) r' = getr regs r'.
Proof.
intros regs r r' w Hne. unfold getr, regupd. destruct (bv_eqb r' 0); [reflexivity|].
unfold reg_get. rewrite bvmap_get_set_other by (intros Heq; apply Hne; symmetry; exact Heq). reflexivity.
Qed.
Lemma tpe_getr_upd_same : forall regs (r : bv 5) w, bv_eqb r 0 = false -> getr (regupd regs r w) r = w.
Proof. intros regs r w H. unfold getr, regupd. rewrite H. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.
Lemma tpe_Ee_sp : forall regs sp0 vals, ew (tpe_Ee regs sp0 vals) 2 = Z_to_bv 64 sp0.
Proof.
intros regs sp0 vals. unfold tpe_Ee. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). apply tpe_getr_upd_same. reflexivity.
Qed.
Lemma tpe_Ee_val : forall regs sp0 vals i, (i < 200)%nat -> ew (tpe_Ee regs sp0 vals) (33 + i) = Z_to_bv 64 (nth i vals 0).
Proof.
intros regs sp0 vals i Hi. unfold tpe_Ee. rewrite Eimg_low by (unfold A_TEXT; lia).
replace (33 + i)%nat with (32 + S i)%nat by lia. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
(* regs_ok at sp = SOff 2 (-112) over the env whose atom 2 is sp0 *)
Lemma tpe_regs_ok_e : forall regs sp0 vals, spZ regs = sp0 - TP_FRAME -> TP_FRAME <= sp0 < 2 ^ 64 ->
  regs_ok (tpe_Ee regs sp0 vals) tpe_sr regs.
Proof.
intros regs sp0 vals Hsp Hsp0 r'.
pose proof (regs_ok_Eimg_Ereg (L := B_prog_listing) (PI := PA) (regupd regs 2%bv (Z_to_bv 64 sp0))
  (map (Z_to_bv 64) (SHADOW_OFF :: vals)) r') as H.
fold (tpe_Ee regs sp0 vals) in H.
unfold tpe_sr, sr_set. change (bv_eqb 2%bv 0%bv) with false. cbv iota.
unfold getr, regupd, sr_get in *.
destruct (bv_eqb r' 0) eqn:Hr'0; [exact H|].
rewrite nth_sr_upd.
destruct (Nat.eqb (ridx r') (ridx 2%bv)) eqn:Hi.
- apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'.
  cbn [sv_denot]. rewrite tpe_Ee_sp. unfold spZ in Hsp. unfold TP_FRAME in *.
  rewrite unsigned_lit_small by lia.
  unfold getr in Hsp. change (bv_eqb 2%bv 0%bv) with false in Hsp. cbv iota in Hsp.
  apply bv_eq. rewrite unsigned_lit_small by lia. lia.
- apply Nat.eqb_neq in Hi.
  unfold reg_get in *. rewrite bvmap_get_set_other in H by (intros Heq; apply Hi; rewrite Heq; reflexivity).
  exact H.
Qed.
(* the frame state of a cut at listing offset pc: the frame region below sp0, facts G *)
Lemma tpe_st_ok_e : forall (W : world segs) regs mem pc sp0 offs vals wlo whi G,
  regions_wf [tpe_fregion offs wlo whi] = true -> (length offs <= 100)%nat ->
  spZ regs = sp0 - TP_FRAME -> TP_FRAME <= sp0 < 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at segs (mrestrict (w_H W) mem) (sp0 + o)) ->
  tpe_vals_ok (mrestrict (w_H W) mem) sp0 offs vals ->
  facts_ok (tpe_Ee regs sp0 vals) G ->
  st_ok_pi segs VAL (tpe_Ee regs sp0 vals) (mkSS pc tpe_sr [tpe_fregion offs wlo whi] None G)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc sp0 offs vals wlo whi G Hwf Hlen Hsp Hsp0 Hwr Hvals HG.
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- exact (tpe_regs_ok_e regs sp0 vals Hsp Hsp0).
- exact Hwf.
- assert (Hb : base_val (tpe_Ee regs sp0 vals) (Some 2%nat) = sp0)
    by (cbn [base_val]; rewrite tpe_Ee_sp; apply unsigned_lit_small; unfold TP_FRAME in *; lia).
  constructor; [|constructor]. unfold region_ok, tpe_fregion.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite Hb.
  split; [unfold TP_FRAME in *; lia|]. split; [lia|]. split; [exact Hwr|].
  apply (tpe_fchunks_ok _ _ _ offs vals 33); [| exact Hvals].
  intros i Hi. apply tpe_Ee_val. lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
(* the frame env's agreement with the register file below atom 32, kept by every later havoc above it *)
Lemma tpe_Ee_agree : forall regs sp0 vals,
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) (tpe_Ee regs sp0 vals).
Proof. intros regs sp0 vals. unfold tpe_Ee. split; [intros i Hi; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* the kept registers gp / tp of the end state, read off its symbolic state over the kit's env (atom 2 = sp0) *)
Lemma tpe_kregs_st : forall D (H : word -> bool) E ss ms regs sp0 vals,
  st_ok_pi segs VAL E ss (restrict H ms) ->
  env_agree 32 (Ereg (regupd regs 2%bv (Z_to_bv 64 sp0)) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [3; 4]%bv = true ->
  tp_kregs D regs -> tp_kregs D (ms_regs ms).
Proof.
intros D H E ss ms regs sp0 vals HS HA Hl Hk r Hr.
assert (Hne : r <> 2%bv).
{ intros ->. cbn [In] in Hr.
  repeat (destruct Hr as [Hr | Hr]; [apply (f_equal bv_unsigned) in Hr; vm_compute in Hr; discriminate |]). exact Hr. }
pose proof (regs_kept_of_st_ok_pi (L := B_prog_listing) (PI := PA) E ss (restrict H ms) _ _ _ HS HA Hl r Hr) as X.
cbn [restrict ms_regs] in X. rewrite X. rewrite tpe_getr_upd_other by exact Hne. exact (Hk r Hr).
Qed.

(* an atom of the saved words is the entry register its chunk holds (tpe_Ee_val at index i) *)
Ltac tpe_ev Ex vs i :=
  subst Ex vs; rewrite (tpe_Ee_val _ _ _ i ltac:(lia)); cbn [nth]; try unfold raZ; apply Z_to_bv_bv_unsigned.

(* ---- THE SEGMENT ---- *)
Lemma tp_seg_END_ok : forall P, srr_inv_laws segs P -> tp_seg_END B SK CTX0 P.
Proof.
intros P PLAW D ly3 S3 Hp3 W3 regs3 mem3 md3 k HAT _ HPM.
destruct HAT as (WS & HBUD & (Hpre & HJ & HK & Hkr & Hsp & HSV & EHp & HROD3) & HQ).
pose proof Hpre as ((HAFN & _ & _ & _) & _).
pose proof HAFN as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (@YM05.alloc_ceiling_value rc) as Hceilv.
unfold tp_JR, tp_sp0 in HJ. unfold tp_sp0 in Hsp. unfold TP_FRAME in Hsp.
unfold tp_KR, tp_sp0 in HK.
unfold tp_saved, tp_sp0 in HSV.
destruct HSV as (V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27).
assert (Rsp : 2 ^ 46 <= spZ (tp_regs D) <= 2 ^ 47) by lia.
set (vals := [bv_unsigned (getr (tp_regs D) 27); bv_unsigned (getr (tp_regs D) 26);
              bv_unsigned (getr (tp_regs D) 25); bv_unsigned (getr (tp_regs D) 24);
              bv_unsigned (getr (tp_regs D) 23); bv_unsigned (getr (tp_regs D) 22);
              bv_unsigned (getr (tp_regs D) 21); bv_unsigned (getr (tp_regs D) 20);
              bv_unsigned (getr (tp_regs D) 19); bv_unsigned (getr (tp_regs D) 18);
              bv_unsigned (getr (tp_regs D) 9); bv_unsigned (getr (tp_regs D) 8); raZ (tp_regs D)]).
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 27)) as R27.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 26)) as R26.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 25)) as R25.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 24)) as R24.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 23)) as R23.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 22)) as R22.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 21)) as R21.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 20)) as R20.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 19)) as R19.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 18)) as R18.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 9)) as R9.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 8)) as R8.
pose proof (bv_unsigned_in_range _ (getr (tp_regs D) 1)) as R1.
unfold bv_modulus in R27, R26, R25, R24, R23, R22, R21, R20, R19, R18, R9, R8, R1.
change (2 ^ Z.of_N 64) with (2 ^ 64) in R27, R26, R25, R24, R23, R22, R21, R20, R19, R18, R9, R8, R1.
assert (HS : st_ok_pi segs VAL (tpe_Ee regs3 (spZ (tp_regs D)) vals)
  (mkSS (TP_OFF + TP_PC_END) tpe_sr [tpe_fregion tpe_offs 0 0] None tpe_facts)
  (restrict (w_H W3) (YK11.mkst regs3 (Z_to_bv 64 (BASE + (TP_OFF + TP_PC_END))) mem3 (YK11.seg_rom segs)))).
{ apply tpe_st_ok_e.
  - vm_compute. reflexivity.
  - cbn. lia.
  - unfold TP_FRAME. lia.
  - unfold TP_FRAME. lia.
  - intros o Ho. lia.
  - cbn [tpe_vals_ok tpe_offs vals].
    replace (spZ (tp_regs D) + -104) with (spZ (tp_regs D) - 104) by lia.
    replace (spZ (tp_regs D) + -96) with (spZ (tp_regs D) - 96) by lia.
    replace (spZ (tp_regs D) + -88) with (spZ (tp_regs D) - 88) by lia.
    replace (spZ (tp_regs D) + -80) with (spZ (tp_regs D) - 80) by lia.
    replace (spZ (tp_regs D) + -72) with (spZ (tp_regs D) - 72) by lia.
    replace (spZ (tp_regs D) + -64) with (spZ (tp_regs D) - 64) by lia.
    replace (spZ (tp_regs D) + -56) with (spZ (tp_regs D) - 56) by lia.
    replace (spZ (tp_regs D) + -48) with (spZ (tp_regs D) - 48) by lia.
    replace (spZ (tp_regs D) + -40) with (spZ (tp_regs D) - 40) by lia.
    replace (spZ (tp_regs D) + -32) with (spZ (tp_regs D) - 32) by lia.
    replace (spZ (tp_regs D) + -24) with (spZ (tp_regs D) - 24) by lia.
    replace (spZ (tp_regs D) + -16) with (spZ (tp_regs D) - 16) by lia.
    replace (spZ (tp_regs D) + -8) with (spZ (tp_regs D) - 8) by lia.
    change (8 * Z.of_N 8) with 64. change (Z.of_N 8) with 8. change (N.to_nat 8) with 8%nat.
    unfold raZ in *. repeat split; try assumption; lia.
  - unfold facts_ok, tpe_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [|split; exact I].
    split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite tpe_Ee_sp, unsigned_lit_small by lia.
    change (2 ^ 4) with 16. split; [lia|]. split; [exact Hal16 | lia]. }
unfold tp_cfg. replace (tp_pc TP_PC_END) with (BASE + (TP_OFF + TP_PC_END)) by (unfold tp_pc; lia).
set (E := tpe_Ee regs3 (spZ (tp_regs D)) vals) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold tpe_Ee; apply Eimg_env).
assert (SHOK : sh_ok segs (SOff 32 0) [] E (mrestrict (w_H W3) mem3)) by (unfold sh_ok; apply Forall_nil).
assert (HAG : env_agree 32 (Ereg (regupd regs3 2%bv (Z_to_bv 64 (spZ (tp_regs D)))) (map (Z_to_bv 64) (SHADOW_OFF :: vals))) E)
  by (subst E; apply tpe_Ee_agree).
(* the thirteen saved words' atoms are the entry's registers *)
assert (E33 : ew E 33 = getr (tp_regs D) 27) by tpe_ev E vals 0%nat.
assert (E34 : ew E 34 = getr (tp_regs D) 26) by tpe_ev E vals 1%nat.
assert (E35 : ew E 35 = getr (tp_regs D) 25) by tpe_ev E vals 2%nat.
assert (E36 : ew E 36 = getr (tp_regs D) 24) by tpe_ev E vals 3%nat.
assert (E37 : ew E 37 = getr (tp_regs D) 23) by tpe_ev E vals 4%nat.
assert (E38 : ew E 38 = getr (tp_regs D) 22) by tpe_ev E vals 5%nat.
assert (E39 : ew E 39 = getr (tp_regs D) 21) by tpe_ev E vals 6%nat.
assert (E40 : ew E 40 = getr (tp_regs D) 20) by tpe_ev E vals 7%nat.
assert (E41 : ew E 41 = getr (tp_regs D) 19) by tpe_ev E vals 8%nat.
assert (E42 : ew E 42 = getr (tp_regs D) 18) by tpe_ev E vals 9%nat.
assert (E43 : ew E 43 = getr (tp_regs D) 9) by tpe_ev E vals 10%nat.
assert (E44 : ew E 44 = getr (tp_regs D) 8) by tpe_ev E vals 11%nat.
assert (E45 : ew E 45 = getr (tp_regs D) 1) by tpe_ev E vals 12%nat.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ (tp_regs D))) by (subst E; apply tpe_Ee_sp).
clearbody E.
(* the END cut is after the GROW's realloc: its journal and keep are at wle' segs RZ_cf, and the run is over that
   relation (the runners over R); the final ret is a plain SRr step, lifted (YA0nH.SRr_SRrG) *)
unfold SRr'.
pose (RUN := @paj_run_x_invR fx rc SK B_prog_listing TP_PAListing PA B prh_pst _ _ LAWS P PLAW
  (wle' segs YGcfRehidePost.RZ_cf) (wle'_refl segs YGcfRehidePost.RZ_cf) (wle'_trans segs YGcfRehidePost.RZ_cf)).
pose (RET := @paj_ret_at fx rc B_prog_listing TP_PAListing PA).
(* +400 .. +452: the thirteen restores, addi sp, sp, 112; stop at the ret (+456). The runner reads an empty-budget
   journal: the cut's, rebased (YCbqGwild.ajournal_xw_rebase; the run is read-only, the post's journal is the cut's) *)
pose proof (ajournal_xw_rebaseR (SK := SK) segs B prh_pst _ (wle' segs YGcfRehidePost.RZ_cf)
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HJr.
paj_run_tok_x_inv RUN HS HJr SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ intros a (rg & Hin & Hrg). cbn in Hin. destruct Hin as [<- | []]. cbn in Hrg. lia. }
lazymatch type of HF with frame_of _ ?rs _ _ =>
  pose proof (frame_of_read_only _ rs _ _ ltac:(vm_compute; reflexivity) HF) as Emem end.
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
rewrite E45 in Q1. rewrite E44 in Q8. rewrite E43 in Q9. rewrite E42 in Q18. rewrite E41 in Q19.
rewrite E40 in Q20. rewrite E39 in Q21. rewrite E38 in Q22. rewrite E37 in Q23. rewrite E36 in Q24.
rewrite E35 in Q25. rewrite E34 in Q26. rewrite E33 in Q27. rewrite E2 in Q2.
assert (HKP : tp_kregs D (ms_regs ms))
  by exact (tpe_kregs_st D (w_H W3) E _ ms regs3 (spZ (tp_regs D)) vals HS HAG ltac:(vm_compute; reflexivity) Hkr).
assert (HAREGS : aregs_preserved (tp_regs D) (ms_regs ms)).
{ apply tpe_aregs. intros rr Hrr. cbn [In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr];
    [first [ assumption
           | (rewrite Q2; unfold spZ; apply Z_to_bv_bv_unsigned)
           | solve [apply HKP; first [left; reflexivity | right; left; reflexivity]] ] |]).
  destruct Hrr. }
rewrite Emem in HJr.
(* the caller window [sp0, sp0 + dw) outside FP: tp_K's stack clause, the window's bounds from the widened journal *)
assert (HWIN : forall a, spZ (tp_regs D) <= a < spZ (tp_regs D) + tp_dw D ->
  ~ inFP (prhtx_fp (tp_t D) (tp_b0 D) (tp_cap0 D)) a ->
  aview segs (w_H W3) mem3 a = aview segs (w_H (tp_W D)) (tp_mem D) a).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Jal & Jstk0 & Jceil & Jslo & Jshi & J47 & _) & _).
  pose proof HK as (_ & _ & _ & _ & _ & K1 & _).
  intros a Ha Hf. apply K1; [lia | lia | exact Hf]. }
(* +456: the return to the entry ra *)
apply (SRr_SRrG segs (wle' segs YGcfRehidePost.RZ_cf) (wle_wle' segs YGcfRehidePost.RZ_cf)).
eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [cfg_ms]. split; [| exact HPM].
rewrite Emem. unfold tp_text_postW, fpostWbR, fpostW_xbR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (YK11.mkst ?rg _ ?m _) ?d = _ /\ _ =>
  exists ly3, S3, Hp3, rg, m, d, k, WS end.
split; [rewrite Q1, Hra; reflexivity|].
split; [exact HBUD|].
split.
{ (* the journal at the budget WS, its model materialized: the runner's (rebased) journal, materialized, unbased
     back to the cut's budget WS by the cut journal's wild clause *)
  eapply (ajournal_xw_unbase0R (SK := SK) segs B prh_pst _ (wle' segs YGcfRehidePost.RZ_cf));
    [|exact (ajxR_wild HJ)].
  apply (ajournal_x_materializeR (SK := SK) segs B prh_pst _ LAWS (@pa_segs_low _ _ PA)).
  exact HJr. }
split; [exact HWIN|].
split; [exact HAREGS|].
unfold tp_Qb. exact HQ.
Qed.

End s.
